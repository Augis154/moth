#include "sema.h"

#include "ast.h"
#include "common.h"
#include "lib/arena.h"
#include "lib/array.h"
#include "lib/str_table.h"
#include "types.h"

#include <assert.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

__attribute__((format(printf, 3, 4))) static void sema_error(SemaContext *ctx, SourceLoc loc, const char *format, ...) {
  ctx->comp_unit->had_error = true;

  va_list args;
  va_start(args, format);

  fprintf(stderr, "[line %u] Error: ", loc.line);
  vfprintf(stderr, format, args);
  fprintf(stderr, "\n");

  va_end(args);
}

// Scope management functions

// Opens a nested scope; returns the start of the enclosing one, which `scope_exit` takes back.
static uint32_t scope_enter(SemaContext *ctx) {
  uint32_t outer_start = ctx->scope_start;

  ctx->scope_start = da_len(ctx->locals);
  ctx->scope_depth++;

  return outer_start;
}

// Closes the current scope: its locals stop being visible, but the symbols stay allocated.
static void scope_exit(SemaContext *ctx, uint32_t outer_start) {
  assert(ctx->scope_depth > 0 && "the global scope is never closed");

  da_set_len(ctx->locals, ctx->scope_start);
  ctx->scope_start = outer_start;
  ctx->scope_depth--;
}

// Allocates a symbol; `name` must be interned. It is not added to any scope. A local of an aggregate type always lives
// in memory.
static Symbol *symbol_new(SemaContext *ctx, const char *name, SymbolKind kind, Type *type, SourceLoc loc) {
  Symbol *sym = arena_alloc(&ctx->comp_unit->arena, sizeof(Symbol));
  *sym = (Symbol){
    .kind = kind,
    .id = ctx->next_symbol_id++,
    .loc = loc,
    .name = name,
    .type = type,
  };

  if (kind == SYMBOL_LOCAL_VAR && type_is_aggregate(type)) {
    sym->local.in_memory = true;
  }

  return sym;
}

// Finds `name` declared directly in the current scope; `name` must be interned. The global scope is large, so it is
// indexed by the compilation unit's symbol table; nested scopes are small and scanned linearly.
static Symbol *scope_lookup_current(SemaContext *ctx, const char *name) {
  if (ctx->scope_depth == 0) {
    return st_get(&ctx->comp_unit->symbol_table, name);
  }

  for (size_t i = da_len(ctx->locals); i > ctx->scope_start; i--) {
    Symbol *sym = ctx->locals[i - 1];
    if (sym->name == name) {
      return sym;
    }
  }

  return NULL;
}

// Finds `name` in the current scope or any enclosing one (names are interned, so pointers are compared).
static Symbol *scope_lookup(SemaContext *ctx, const char *name) {
  for (size_t i = da_len(ctx->locals); i > 0; i--) {
    Symbol *sym = ctx->locals[i - 1];
    if (sym->name == name) {
      return sym;
    }
  }

  return st_get(&ctx->comp_unit->symbol_table, name);
}

// Whether a type name can refer to `sym`: a variable that failed to declare is skipped, so it hides no type.
static bool symbol_names_type(const Symbol *sym) {
  return sym->kind == SYMBOL_TYPE || sym->type != type_error;
}

// Finds the symbol a type name refers to.
static Symbol *scope_lookup_type_name(SemaContext *ctx, const char *name) {
  for (size_t i = da_len(ctx->locals); i > 0; i--) {
    Symbol *sym = ctx->locals[i - 1];
    if (sym->name == name && symbol_names_type(sym)) {
      return sym;
    }
  }

  Symbol *sym = st_get(&ctx->comp_unit->symbol_table, name);

  return sym && symbol_names_type(sym) ? sym : NULL;
}

// Declares `name` in the current scope; returns NULL if it is already declared there. Every name that reaches sema
// is interned: the parser interns identifiers, and `sema_init_builtins` the builtin type names.
static Symbol *scope_insert(SemaContext *ctx, const char *name, SymbolKind kind, Type *type, SourceLoc loc) {
  assert(st_intern(&ctx->comp_unit->intern_table, name) == name && "scope_insert: name is not interned");

  if (scope_lookup_current(ctx, name)) {
    return NULL;
  }

  Symbol *sym = symbol_new(ctx, name, kind, type, loc);

  if (ctx->scope_depth == 0) {
    st_set(&ctx->comp_unit->symbol_table, name, sym);
  } else {
    da_append(ctx->locals, sym);
  }

  return sym;
}

// Reports that a declaration repeats the name of `existing`, with the line of the first declaration. A builtin type has
// no source line.
static void sema_error_redeclaration(SemaContext *ctx, SourceLoc loc, const Symbol *existing_sym) {
  if (existing_sym->loc.line == 0) {
    sema_error(ctx, loc, "'%s' is a builtin type and cannot be redeclared", existing_sym->name);
  } else {
    sema_error(
      ctx, loc, "Redeclaration of '%s'. Previous declaration at line %u", existing_sym->name, existing_sym->loc.line);
  }
}

// Declares a local or parameter, or reports an error and returns NULL if its name is visible already or names a type.
// The name is then declared as the error type, so its uses report nothing more. A function can be shadowed.
static Symbol *sema_declare_local(SemaContext *ctx, const char *name, Type *type, SourceLoc loc) {
  Symbol *existing_sym = scope_lookup_current(ctx, name);

  // The name was used before this declaration, which was reported already; the declaration takes the placeholder over
  if (existing_sym && existing_sym->kind == SYMBOL_LOCAL_VAR && existing_sym->local.is_placeholder) {
    existing_sym->type = type;
    existing_sym->loc = loc;
    existing_sym->local = (SymbolLocal){.in_memory = type_is_aggregate(type)};
    return existing_sym;
  }

  if (!existing_sym) {
    Symbol *visible_sym = scope_lookup(ctx, name);
    bool is_type = visible_sym && visible_sym->kind == SYMBOL_TYPE;
    bool is_local = visible_sym && visible_sym->kind == SYMBOL_LOCAL_VAR && !visible_sym->local.is_placeholder;

    existing_sym = is_type || is_local ? visible_sym : NULL;
  }

  if (existing_sym) {
    sema_error_redeclaration(ctx, loc, existing_sym);
    scope_insert(ctx, name, SYMBOL_LOCAL_VAR, type_error, loc);
    return NULL;
  }

  return scope_insert(ctx, name, SYMBOL_LOCAL_VAR, type, loc);
}

// Returns `type` if a value of it can be stored, which a variable, parameter or field needs; otherwise reports it and
// returns the error type. `what` names the declaration, such as "variable".
static Type *sema_require_storage(SemaContext *ctx, SourceLoc loc, const char *what, const char *name, Type *type) {
  if (type_has_storage(type)) {
    return type;
  }

  sema_error(ctx, loc, "Cannot declare %s '%s' of type '%s'", what, name, type_display_name(type));
  return type_error;
}

static inline size_t align_to(size_t offset, size_t align) {
  return (offset + align - 1) & ~(align - 1);
}

// Expression types

Type *sema_expr_type(const SemaContext *ctx, const AstExpr *expr) {
  return expr->id < da_len(ctx->expr_types) ? ctx->expr_types[expr->id] : NULL;
}

// Whether `expr` denotes a location that can be assigned to.
static bool is_lvalue(const SemaContext *ctx, const AstExpr *expr) {
  if (!expr) return false;

  switch (expr->kind) {
  case AST_EXPR_IDENTIFIER: {
    Symbol *sym = expr->expr_identifier.symbol;
    if (!sym) return false;

    return sym->kind == SYMBOL_GLOBAL_VAR || sym->kind == SYMBOL_LOCAL_VAR;
  }
  case AST_EXPR_DEREF:
    return true;

  case AST_EXPR_SUBSCRIPT: {
    const AstExpr *target = expr->expr_subscript.target;
    return type_is_slice(sema_expr_type(ctx, target)) || is_lvalue(ctx, target);
  }
  case AST_EXPR_MEMBER: {
    const AstExpr *object = expr->expr_member.object;
    return type_is_pointer(sema_expr_type(ctx, object)) || is_lvalue(ctx, object);
  }

  default:
    return false;
  }
}

// Whether `expr` is an array or a struct literal: a fresh value that is never a place.
static bool is_composite_literal(const AstExpr *expr) {
  return expr->kind == AST_EXPR_ARRAY_LITERAL || expr->kind == AST_EXPR_STRUCT_LITERAL;
}

// Names the kind of expression for diagnostics, e.g. "a literal".
static const char *describe_expr(const AstExpr *expr) {
  switch (expr->kind) {
  case AST_EXPR_LITERAL:
    return "a literal";
  case AST_EXPR_IDENTIFIER:
    return "a name";

  case AST_EXPR_ARRAY_LITERAL:
    return "an array literal";
  case AST_EXPR_STRUCT_LITERAL:
    return "a struct literal";

  case AST_EXPR_ADDR_OF:
    return "an address-of expression";
  case AST_EXPR_DEREF:
    return "a dereference";
  case AST_EXPR_SUBSCRIPT:
    return "a subscript";
  case AST_EXPR_SLICE:
    return "a slice";
  case AST_EXPR_MEMBER:
    return "a member access";
  case AST_EXPR_CALL:
    return "a function call result";

  case AST_EXPR_UNARY:
  case AST_EXPR_BINARY:
    return "an operator expression";
  case AST_EXPR_LOGICAL:
    return "a logical operator expression";
  case AST_EXPR_CAST:
    return "a cast";

  case AST_EXPR_ASSIGN:
    return "an assignment";

  case AST_EXPR_INVALID:
    return "an invalid expression";
  }

  UNREACHABLE("describe_expr: unhandled expression kind");
}

// Nodes created during sema (implicit casts) have ids past the table, so it grows on demand.
static void sema_set_expr_type(SemaContext *ctx, const AstExpr *expr, Type *type) {
  size_t old_len = da_len(ctx->expr_types);

  if (expr->id >= old_len) {
    da_set_len(ctx->expr_types, expr->id + 1);
    for (size_t i = old_len; i < da_len(ctx->expr_types); i++) {
      ctx->expr_types[i] = NULL;
    }
  }

  ctx->expr_types[expr->id] = type;
}

// Constant folding

// Whether `expr` is an integer or character literal; its sign and magnitude are stored in `negative` and `magnitude`.
static bool sema_int_literal_parts(const AstExpr *expr, bool *negative, uint64_t *magnitude) {
  if (expr->kind != AST_EXPR_LITERAL) {
    return false;
  }

  const AstExprLiteral *literal_expr = &expr->expr_literal;

  switch (literal_expr->kind) {
  case AST_LITERAL_INT:
    *negative = literal_expr->int_value.negative;
    *magnitude = literal_expr->int_value.magnitude;
    return true;
  case AST_LITERAL_CHAR:
    *negative = false;
    *magnitude = literal_expr->code_point;
    return true;

  case AST_LITERAL_FLOAT:
  case AST_LITERAL_STRING:
  case AST_LITERAL_TRUE:
  case AST_LITERAL_FALSE:
  case AST_LITERAL_NULL:
  case AST_LITERAL_UNDEF:
    return false;
  }

  UNREACHABLE("sema_int_literal_parts: unhandled literal kind");
}

// Whether `expr` is an integer or character literal that fits an int64; its value is stored in `value`.
static bool sema_int_literal(const AstExpr *expr, int64_t *value) {
  bool negative;
  uint64_t magnitude;

  if (!sema_int_literal_parts(expr, &negative, &magnitude)) return false;
  if (magnitude > (negative ? (uint64_t)INT64_MAX + 1 : (uint64_t)INT64_MAX)) return false;

  *value = (int64_t)(negative ? 0 - magnitude : magnitude);
  return true;
}

// An integer literal of `value`.
static AstExprLiteral sema_make_int_literal(int64_t value) {
  bool negative = value < 0;
  uint64_t magnitude = negative ? 0 - (uint64_t)value : (uint64_t)value;

  return (AstExprLiteral){.kind = AST_LITERAL_INT, .int_value = {.magnitude = magnitude, .negative = negative}};
}

// Computes `op operand`; false when the result is not representable.
static bool sema_fold_unary(UnaryOp op, int64_t operand, int64_t *result) {
  switch (op) {
  case UNOP_NEGATE:
    return !__builtin_sub_overflow((int64_t)0, operand, result);
  case UNOP_BIT_NOT:
    *result = ~operand;
    return true;

  case UNOP_NOT:
  case UNOP_COUNT:
    return false;
  }

  UNREACHABLE("sema_fold_unary: unhandled operator");
}

// Computes `left op right`; false when the operator has no integer result or the result is not representable.
static bool sema_fold_binary(BinaryOp op, int64_t left, int64_t right, int64_t *result) {
  switch (op) {
  case BINOP_ADD:
    return !__builtin_add_overflow(left, right, result);
  case BINOP_SUB:
    return !__builtin_sub_overflow(left, right, result);
  case BINOP_MUL:
    return !__builtin_mul_overflow(left, right, result);
  case BINOP_DIV:
    if (right == 0 || (left == INT64_MIN && right == -1)) return false;
    *result = left / right;
    return true;

  case BINOP_BIT_OR:
    *result = left | right;
    return true;
  case BINOP_BIT_XOR:
    *result = left ^ right;
    return true;
  case BINOP_BIT_AND:
    *result = left & right;
    return true;
  case BINOP_SHL:
    if (right < 0 || right >= 63 || left < 0 || left > (INT64_MAX >> right)) return false;
    *result = left << right;
    return true;
  case BINOP_SHR:
    if (right < 0 || right >= 64) return false;
    *result = left >> right;
    return true;

  case BINOP_LESS:
  case BINOP_GREATER:
  case BINOP_EQ:
  case BINOP_NOT_EQ:
  case BINOP_LESS_EQ:
  case BINOP_GREATER_EQ:
  case BINOP_COUNT:
    return false;
  }

  UNREACHABLE("sema_fold_binary: unhandled operator");
}

// Replaces an untyped integer expression whose operands are integer literals by the literal of its value.
static void sema_fold_constant(AstExpr *expr) {
  AstExprLiteral literal;
  int64_t value;

  switch (expr->kind) {
  case AST_EXPR_UNARY: {
    const AstExpr *operand_expr = expr->expr_unary.operand;

    // Negating an integer literal flips its sign, so it also covers 2^63, which no int64 holds
    if (expr->expr_unary.op == UNOP_NEGATE && operand_expr->kind == AST_EXPR_LITERAL &&
        operand_expr->expr_literal.kind == AST_LITERAL_INT) {
      literal = operand_expr->expr_literal;
      literal.int_value.negative = !literal.int_value.negative && literal.int_value.magnitude != 0;
      break;
    }

    int64_t operand;
    if (!sema_int_literal(operand_expr, &operand)) return;
    if (!sema_fold_unary(expr->expr_unary.op, operand, &value)) return;

    literal = sema_make_int_literal(value);
    break;
  }

  case AST_EXPR_BINARY: {
    int64_t left, right;
    if (!sema_int_literal(expr->expr_binary.left, &left)) return;
    if (!sema_int_literal(expr->expr_binary.right, &right)) return;
    if (!sema_fold_binary(expr->expr_binary.op, left, right, &value)) return;

    literal = sema_make_int_literal(value);
    break;
  }

  default:
    return;
  }

  expr->kind = AST_EXPR_LITERAL;
  expr->expr_literal = literal;
}

// Implicit conversions

// Gives an untyped expression (and the untyped operands it is built from) a concrete type. An integer literal must fit
// the integer type it takes.
static void sema_concretize(SemaContext *ctx, AstExpr *expr, Type *target) {
  if (!type_is_untyped(sema_expr_type(ctx, expr))) {
    return;
  }

  sema_set_expr_type(ctx, expr, target);

  switch (expr->kind) {
  case AST_EXPR_LITERAL: {
    bool negative;
    uint64_t magnitude;
    if (type_is_integer(target) && !type_is_internal(target) && sema_int_literal_parts(expr, &negative, &magnitude) &&
        !type_int_fits(target, negative, magnitude)) {
      if (expr->expr_literal.kind != AST_LITERAL_CHAR) {
        sema_error(ctx,
                   expr->loc,
                   "Value %s%lu does not fit in '%s'",
                   negative ? "-" : "",
                   (unsigned long)magnitude,
                   type_display_name(target));
      } else if (magnitude >= 32 && magnitude < 127) {
        sema_error(ctx,
                   expr->loc,
                   "Character '%c' (%lu) does not fit in '%s'",
                   (char)magnitude,
                   (unsigned long)magnitude,
                   type_display_name(target));
      } else {
        sema_error(ctx,
                   expr->loc,
                   "Character U+%04lX does not fit in '%s'",
                   (unsigned long)magnitude,
                   type_display_name(target));
      }
    }
    break;
  }

  case AST_EXPR_UNARY:
    sema_concretize(ctx, expr->expr_unary.operand, target);
    break;

  case AST_EXPR_BINARY:
    sema_concretize(ctx, expr->expr_binary.left, target);
    sema_concretize(ctx, expr->expr_binary.right, target);
    break;

  default:
    break;
  }
}

// Makes `*slot` usable as `to_type`: untyped expressions take the concrete type, others get an implicit cast node.
static void sema_coerce(SemaContext *ctx, AstExpr **slot, Type *to_type) {
  AstExpr *expr = *slot;
  Type *from_type = sema_expr_type(ctx, expr);

  if (from_type == type_error || to_type == type_error) {
    return;
  }

  if (type_is_untyped(from_type)) {
    sema_concretize(ctx, expr, type_default(to_type));
    return;
  }

  if (!type_equals(from_type, to_type)) {
    AstExpr *cast = ast_expr_new(&ctx->comp_unit->arena, AST_EXPR_CAST, expr->loc);
    cast->expr_cast.operand = expr;
    cast->expr_cast.implicit = true;
    sema_set_expr_type(ctx, cast, to_type);

    *slot = cast;
  }
}

// Array types

// The largest size of an array in bytes, so that every element offset fits a signed 32-bit displacement.
#define ARRAY_MAX_SIZE INT32_MAX

// Builds `[length]elem_type`, or reports an error and gives type_error if its elements have no size or it is too large.
static Type *sema_array_of(SemaContext *ctx, SourceLoc loc, Type *elem_type, uint64_t length) {
  if (elem_type == type_error) {
    return type_error;
  }

  if (elem_type->size == 0) {
    sema_error(ctx, loc, "Cannot make an array of '%s'", type_display_name(elem_type));
    return type_error;
  }

  if (length > ARRAY_MAX_SIZE / elem_type->size) {
    sema_error(ctx, loc, "Array of %llu '%s' is too large", (unsigned long long)length, type_display_name(elem_type));
    return type_error;
  }

  // The size check above keeps the length within 32 bits.
  return type_array_of(&ctx->comp_unit->arena, elem_type, (uint32_t)length);
}

// Expression semantic analysis functions

// Types a literal
static Type *sema_expr_literal(SemaContext *ctx, AstExpr *expr) {
  switch (expr->expr_literal.kind) {
  case AST_LITERAL_INT:
    return type_untyped_int;
  case AST_LITERAL_FLOAT:
    return type_untyped_float;
  case AST_LITERAL_CHAR:
    return type_untyped_int;
  case AST_LITERAL_STRING:
    return type_slice_of(&ctx->comp_unit->arena, type_u8);

  case AST_LITERAL_TRUE:
  case AST_LITERAL_FALSE:
    return type_bool;

  case AST_LITERAL_NULL:
    return type_null;
  case AST_LITERAL_UNDEF:
    return type_undef;
  }

  sema_error(ctx, expr->loc, "Unknown literal type");
  return type_error;
}

// Resolves a name to a variable; type and function names are not values.
static Type *sema_expr_identifier(SemaContext *ctx, AstExpr *expr) {
  AstExprIdentifier *identifier_expr = &expr->expr_identifier;

  Symbol *sym = scope_lookup(ctx, identifier_expr->name);
  if (!sym) {
    sema_error(ctx, expr->loc, "Undefined identifier '%s'", identifier_expr->name);

    Symbol *placeholder_sym = scope_insert(ctx, identifier_expr->name, SYMBOL_LOCAL_VAR, type_error, expr->loc);
    placeholder_sym->local.is_placeholder = true;
    return type_error;
  }

  if (sym->kind == SYMBOL_TYPE) {
    sema_error(ctx, expr->loc, "'%s' is a type, not a value", identifier_expr->name);
    return type_error;
  }

  if (sym->kind == SYMBOL_FUNCTION) {
    sema_error(ctx, expr->loc, "'%s' is a function, not a value (did you mean to call it?)", identifier_expr->name);
    return type_error;
  }

  identifier_expr->symbol = sym;
  return sym->type;
}

// Reports a literal error unless `report` is off (used when the length is only probed).
static void sema_literal_error(SemaContext *ctx, bool report, SourceLoc loc, const char *message) {
  if (report) sema_error(ctx, loc, "%s", message);
}

// Length of an array literal (-1 if none). Sets each list element's `index`; element without an index follows last.
static int64_t sema_array_literal_length(SemaContext *ctx, AstExpr *expr, bool report) {
  AstExprArrayLiteral *array_literal_expr = &expr->expr_array_literal;

  if (array_literal_expr->is_repeat) {
    AstExpr *length_expr = array_literal_expr->repeat.length_expr;

    if (length_expr->kind != AST_EXPR_LITERAL || length_expr->expr_literal.kind != AST_LITERAL_INT) {
      sema_literal_error(ctx, report, length_expr->loc, "Array repeat length must be an integer literal");
      return -1;
    }

    int64_t length;
    if (!sema_int_literal(length_expr, &length) || length <= 0 || length > UINT32_MAX) {
      sema_literal_error(ctx, report, length_expr->loc, "Array length must be between 1 and 2^32 - 1");
      return -1;
    }

    return length;
  }

  AstArrayElement *elements = array_literal_expr->list.elements;
  uint32_t element_count = array_literal_expr->list.element_count;
  int64_t next_index = 0;
  int64_t length = 0;

  for (uint32_t i = 0; i < element_count; i++) {
    AstExpr *index_expr = elements[i].index_expr;

    if (index_expr) {
      if (index_expr->kind != AST_EXPR_LITERAL || index_expr->expr_literal.kind != AST_LITERAL_INT) {
        sema_literal_error(ctx, report, index_expr->loc, "Array index must be an integer literal");
        return -1;
      }

      if (!sema_int_literal(index_expr, &next_index) || next_index < 0 || next_index >= UINT32_MAX) {
        sema_literal_error(ctx, report, index_expr->loc, "Array index is out of range");
        return -1;
      }
    }

    if (next_index >= UINT32_MAX) {
      sema_literal_error(ctx, report, elements[i].loc, "Array index is out of range");
      return -1;
    }

    elements[i].index = (uint32_t)next_index++;
    if (next_index > length) length = next_index;
  }

  if (array_literal_expr->list.is_sparse) {
    for (uint32_t i = 0; i < element_count; i++) {
      for (uint32_t j = 0; j < i; j++) {
        if (elements[i].index == elements[j].index) {
          sema_literal_error(ctx, report, elements[i].loc, "Array index is initialized twice");
          return -1;
        }
      }
    }
  }

  if (length == 0) {
    sema_literal_error(ctx, report, expr->loc, "An array literal needs at least one element");
    return -1;
  }

  return length;
}

// The slot of the value for element `i`; a repeat literal has a single value shared by every element.
static AstExpr **array_literal_value_slot(AstExpr *expr, uint32_t i) {
  AstExprArrayLiteral *array_literal_expr = &expr->expr_array_literal;

  return array_literal_expr->is_repeat ? &array_literal_expr->repeat.value
                                       : &array_literal_expr->list.elements[i].value;
}

// Converts a literal value of `type` to `elem_type`
static bool sema_literal_value_coerce(SemaContext *ctx, AstExpr **slot, Type *type, Type *elem_type, uint32_t i) {
  if (type == type_error) {
    return false;
  }

  if (!type_can_widen_to(type, elem_type)) {
    sema_error(ctx,
               (*slot)->loc,
               "Array element %u of type '%s' cannot convert to '%s'",
               i,
               type_display_name(type),
               type_display_name(elem_type));
    return false;
  }

  sema_coerce(ctx, slot, elem_type);
  return true;
}

// Types `[a, b]`, `[i: a]` and `[v; n]`: values convert to the element type of `hint`, or to their common type.
static Type *sema_expr_array_literal(SemaContext *ctx, AstExpr *expr, Type *hint) {
  AstExprArrayLiteral *array_literal_expr = &expr->expr_array_literal;

  bool is_repeat = array_literal_expr->is_repeat;

  int64_t length = sema_array_literal_length(ctx, expr, true);
  if (length < 0) {
    return type_error;
  }

  uint32_t value_count = is_repeat ? 1 : array_literal_expr->list.element_count;

  if (hint == type_error) {
    for (uint32_t i = 0; i < value_count; i++) {
      sema_expr(ctx, *array_literal_value_slot(expr, i));
    }
    return type_error;
  }

  if (hint && type_is_slice(hint)) {
    hint = sema_array_of(ctx, expr->loc, hint->slice.elem_type, length);
    if (hint == type_error) {
      return type_error;
    }
  }

  Type *elem_type = NULL;

  if (hint) {
    if (!type_is_array(hint)) {
      sema_error(ctx, expr->loc, "Cannot convert an array literal to '%s'", type_display_name(hint));
      return type_error;
    }

    bool is_sparse = !is_repeat && array_literal_expr->list.is_sparse;
    if (is_sparse ? length > hint->array.length : length != hint->array.length) {
      sema_error(ctx,
                 expr->loc,
                 "Array literal has %lld elements, but '%s' has %u",
                 (long long)length,
                 type_display_name(hint),
                 hint->array.length);
      return type_error;
    }

    elem_type = hint->array.elem_type;
  } else {
    // Without a hint the element type is the common type of the values
    for (uint32_t i = 0; i < value_count; i++) {
      AstExpr *value = *array_literal_value_slot(expr, i);
      Type *type = sema_expr(ctx, value);
      if (type == type_error) {
        return type_error;
      }

      Type *common_type = !elem_type || type_equals(elem_type, type) ? type : type_common(elem_type, type);
      if (!common_type) {
        sema_error(ctx,
                   value->loc,
                   "Array element %u of type '%s' does not match '%s'",
                   i,
                   type_display_name(type),
                   type_display_name(elem_type));
        return type_error;
      }

      elem_type = common_type;
    }

    elem_type = type_default(elem_type);
  }

  bool values_ok = true;

  for (uint32_t i = 0; i < value_count; i++) {
    AstExpr **slot = array_literal_value_slot(expr, i);
    Type *type = hint ? sema_expr_hint(ctx, *slot, elem_type) : sema_expr_type(ctx, *slot);
    values_ok &= sema_literal_value_coerce(ctx, slot, type, elem_type, i);
  }

  if (!values_ok) {
    return type_error;
  }

  return hint ? hint : sema_array_of(ctx, expr->loc, elem_type, length);
}

// Reports initialiser `index` of a struct literal if an earlier one names the same field; returns whether it does.
static bool sema_is_duplicate_literal_field(SemaContext *ctx, const AstExprStructLiteral *struct_literal_expr,
                                            Type *struct_type, uint32_t index) {
  const AstExprStructLiteralField *field = &struct_literal_expr->fields[index];

  for (uint32_t i = 0; i < index; i++) {
    if (struct_literal_expr->fields[i].name != field->name) continue;

    sema_error(ctx,
               field->loc,
               "Duplicate field '%s' in struct literal for '%s'. Previous initialiser at line %u",
               field->name,
               type_display_name(struct_type),
               struct_literal_expr->fields[i].loc.line);
    return true;
  }

  return false;
}

// Types `Name.{ field: value, ... }`: each value converts to its field's type and an omitted field is zero.
static Type *sema_expr_struct_literal(SemaContext *ctx, AstExpr *expr, Type *hint) {
  AstExprStructLiteral *struct_literal_expr = &expr->expr_struct_literal;

  uint32_t field_count = struct_literal_expr->field_count;

  if (hint == type_error) {
    for (uint32_t i = 0; i < field_count; i++) {
      sema_expr(ctx, struct_literal_expr->fields[i].value);
    }
    return type_error;
  }

  AstType *ast_type = struct_literal_expr->type;
  Type *struct_type = hint;

  if (ast_type) {
    struct_type = sema_type(ctx, ast_type);

    if (struct_type == type_error) {
      return type_error;
    }

    if (!type_is_struct(struct_type)) {
      sema_error(ctx, ast_type->loc, "Type '%s' is not a struct", type_display_name(struct_type));
      return type_error;
    }
  } else {
    if (!hint) {
      sema_error(ctx, expr->loc, "Cannot type a struct literal without a struct name or a type hint");
      return type_error;
    }

    if (!type_is_struct(struct_type)) {
      sema_error(ctx, expr->loc, "Cannot convert a struct literal to '%s'", type_display_name(struct_type));
      return type_error;
    }
  }

  for (uint32_t i = 0; i < field_count; i++) {
    AstExprStructLiteralField *field = &struct_literal_expr->fields[i];

    TypeField type_field;

    if (!type_find_field(&ctx->comp_unit->arena, struct_type, field->name, &type_field)) {
      sema_error(ctx, field->loc, "Struct '%s' has no field '%s'", type_display_name(struct_type), field->name);
      continue;
    }

    if (sema_is_duplicate_literal_field(ctx, struct_literal_expr, struct_type, i)) {
      continue;
    }

    Type *field_type = sema_expr_hint(ctx, field->value, type_field.type);

    if (field_type == type_error) {
      continue;
    }

    if (!type_can_widen_to(field_type, type_field.type)) {
      sema_error(ctx,
                 field->loc,
                 "Field '%s' of struct '%s' expects type '%s', but got '%s'",
                 field->name,
                 type_display_name(struct_type),
                 type_display_name(type_field.type),
                 type_display_name(field_type));
      continue;
    }

    sema_coerce(ctx, &field->value, type_field.type);
    field->offset = type_field.offset;
  }

  return struct_type;
}

// Types `&x`: an lvalue operand, giving a pointer to it. A variable whose address is taken lives in memory.
static Type *sema_expr_addr_of(SemaContext *ctx, AstExpr *expr) {
  AstExpr *operand = expr->expr_addr_of.operand;

  if (is_composite_literal(operand)) {
    sema_error(ctx, expr->loc, "Cannot take the address of %s", describe_expr(operand));
    return type_error;
  }

  Type *operand_type = sema_expr(ctx, operand);

  if (operand_type != type_error && !is_lvalue(ctx, operand)) {
    sema_error(ctx, expr->loc, "Cannot take the address of %s", describe_expr(operand));
    return type_error;
  }

  if (operand_type == type_error) {
    return type_error;
  }

  if (operand->kind == AST_EXPR_IDENTIFIER) {
    Symbol *sym = operand->expr_identifier.symbol;
    assert(sym->kind == SYMBOL_LOCAL_VAR && "sema rejects type and function names as values");
    sym->local.in_memory = true;
  }

  return type_pointer_to(&ctx->comp_unit->arena, operand_type);
}

// Types `p.*`: the operand must be a pointer to a type with storage.
static Type *sema_expr_deref(SemaContext *ctx, AstExpr *expr) {
  AstExpr *operand = expr->expr_deref.operand;
  Type *operand_type = sema_expr(ctx, operand);

  if (operand_type == type_error) {
    return type_error;
  }

  if (operand_type->kind != TYPE_KIND_POINTER) {
    sema_error(ctx, expr->loc, "Cannot dereference non-pointer type '%s'", type_display_name(operand_type));
    return type_error;
  }

  if (!type_has_storage(operand_type->pointer.base_type)) {
    sema_error(ctx, expr->loc, "Cannot dereference '%s'", type_display_name(operand_type));
    return type_error;
  }

  return operand_type->pointer.base_type;
}

// Types `xs[i]`: the target must be an array or a slice and the index an integer, which is converted to i64.
static Type *sema_expr_subscript(SemaContext *ctx, AstExpr *expr) {
  AstExprSubscript *subscript_expr = &expr->expr_subscript;

  Type *target_type = sema_expr(ctx, subscript_expr->target);
  Type *index_type = sema_expr(ctx, subscript_expr->index);

  if (target_type == type_error || index_type == type_error) {
    return type_error;
  }

  if (!type_is_array_like(target_type)) {
    sema_error(ctx, expr->loc, "Cannot subscript non-array type '%s'", type_display_name(target_type));
    return type_error;
  }

  if (!type_is_integer(index_type)) {
    sema_error(ctx, expr->loc, "Array index must be an integer, got '%s'", type_display_name(index_type));
    return type_error;
  }

  int64_t index_value;
  bool index_is_const = sema_int_literal(subscript_expr->index, &index_value);

  if (target_type->kind == TYPE_KIND_ARRAY && index_is_const &&
      (index_value < 0 || (uint64_t)index_value >= target_type->array.length)) {
    sema_error(ctx,
               subscript_expr->index->loc,
               "Array index %lld is out of bounds for '%s'",
               (long long)index_value,
               type_display_name(target_type));
    return type_error;
  }

  sema_coerce(ctx, &subscript_expr->index, type_i64);

  return type_elem(target_type);
}

// Types a slice bound: it must be an integer, which is converted to i64. Returns false after reporting an error.
static bool sema_slice_bound(SemaContext *ctx, AstExpr **slot, const char *which) {
  assert(slot && *slot && "sema_slice_bound: bound is missing");

  Type *type = sema_expr(ctx, *slot);

  if (type == type_error) {
    return false;
  }

  if (!type_is_integer(type)) {
    sema_error(ctx, (*slot)->loc, "Slice %s index must be an integer, got '%s'", which, type_display_name(type));
    return false;
  }

  sema_coerce(ctx, slot, type_i64);
  return true;
}

// Reports constant bounds that are negative, past the end of an array, or out of order. Returns false after an error.
static bool sema_check_slice_bounds(SemaContext *ctx, AstExpr *expr, Type *target_type) {
  assert(type_is_array_like(target_type) && "sema_check_slice_bounds: target is neither an array nor a slice");

  AstExprSlice *slice_expr = &expr->expr_slice;

  AstExpr *bounds[] = {slice_expr->start, slice_expr->end};
  const char *names[] = {"start", "end"};
  int64_t values[2] = {0, 0};
  bool is_const[2] = {false, false};

  for (int i = 0; i < 2; i++) {
    if (!bounds[i] || !sema_int_literal(bounds[i], &values[i])) {
      continue;
    }

    is_const[i] = true;

    bool past_end = type_is_array(target_type) && (uint64_t)values[i] > target_type->array.length;
    if (values[i] < 0 || past_end) {
      sema_error(ctx,
                 bounds[i]->loc,
                 "Slice %s index %lld is out of bounds for '%s'",
                 names[i],
                 (long long)values[i],
                 type_display_name(target_type));
      return false;
    }
  }

  if (is_const[0] && is_const[1] && values[0] > values[1]) {
    sema_error(ctx,
               expr->loc,
               "Slice start index %lld is greater than end index %lld",
               (long long)values[0],
               (long long)values[1]);
    return false;
  }

  return true;
}

// Types `xs[start:end]`: the target must be an array or a slice and each bound that is present an integer, which is
// converted to i64. The result is a slice of the same element type.
static Type *sema_expr_slice(SemaContext *ctx, AstExpr *expr) {
  AstExprSlice *slice_expr = &expr->expr_slice;

  Type *target_type = sema_expr(ctx, slice_expr->target);

  if (target_type == type_error) {
    return type_error;
  }

  if (!type_is_array_like(target_type)) {
    sema_error(ctx, expr->loc, "Cannot slice non-array type '%s'", type_display_name(target_type));
    return type_error;
  }

  if (slice_expr->start && !sema_slice_bound(ctx, &slice_expr->start, "start")) {
    return type_error;
  }

  if (slice_expr->end && !sema_slice_bound(ctx, &slice_expr->end, "end")) {
    return type_error;
  }

  if (!sema_check_slice_bounds(ctx, expr, target_type)) {
    return type_error;
  }

  return type_slice_of(&ctx->comp_unit->arena, type_elem(target_type));
}

// Types `object.member`. The length of an array is a constant, so `xs.len` becomes an integer literal.
static Type *sema_expr_member(SemaContext *ctx, AstExpr *expr) {
  AstExprMember *member_expr = &expr->expr_member;

  Type *object_type = sema_expr(ctx, member_expr->object);
  if (object_type == type_error) {
    return type_error;
  }

  if (type_is_pointer(object_type)) {
    object_type = object_type->pointer.base_type;
  }

  if (type_is_array(object_type) && strcmp(member_expr->member, "len") == 0) {
    int64_t length = object_type->array.length;

    expr->kind = AST_EXPR_LITERAL;
    expr->expr_literal = sema_make_int_literal(length);

    return type_i64;
  }

  TypeField field = {0};
  bool found = type_find_field(&ctx->comp_unit->arena, object_type, member_expr->member, &field);

  if (!found) {
    sema_error(
      ctx, expr->loc, "Type '%s' has no field named '%s'", type_display_name(object_type), member_expr->member);
    return type_error;
  }

  member_expr->offset = field.offset;

  return field.type;
}

// Analyses the arguments of a call that could not be resolved, so that errors inside them are still reported.
static void sema_call_args(SemaContext *ctx, AstExpr *expr) {
  AstExprCall *call_expr = &expr->expr_call;

  for (uint32_t i = 0; i < call_expr->arg_count; i++) {
    sema_expr(ctx, call_expr->args[i]);
  }
}

// The type a variadic argument of `type` is passed as, with the C default promotions; NULL when it cannot be passed.
// `type` is concrete: untyped arguments are defaulted first.
static Type *variadic_promoted_type(Type *type) {
  switch (type->kind) {
  case TYPE_KIND_U8:
  case TYPE_KIND_U16:
  case TYPE_KIND_I8:
  case TYPE_KIND_I16:
  case TYPE_KIND_I32:
  case TYPE_KIND_BOOL:
    return type_i32;
  case TYPE_KIND_U32:
    return type_u32;
  case TYPE_KIND_U64:
    return type_u64;
  case TYPE_KIND_I64:
    return type_i64;

  case TYPE_KIND_F32:
  case TYPE_KIND_F64:
    return type_f64;

  case TYPE_KIND_POINTER:
    return type;

  case TYPE_KIND_STRUCT:
    return type;

  case TYPE_KIND_UNTYPED_INT:
  case TYPE_KIND_UNTYPED_FLOAT:
  case TYPE_KIND_NULL:
  case TYPE_KIND_ARRAY:
  case TYPE_KIND_SLICE:
  case TYPE_KIND_ERROR:
  case TYPE_KIND_VOID:
  case TYPE_KIND_UNDEF:
  case TYPE_KIND_FUNCTION:
    return NULL;
  }

  UNREACHABLE("variadic_promoted_type: unhandled type kind");
}

// Types a call: the callee must be a function and each argument converts to its parameter type. The extra arguments of
// a variadic callee are promoted as in C.
static Type *sema_expr_call(SemaContext *ctx, AstExpr *expr) {
  AstExprCall *call_expr = &expr->expr_call;

  AstExpr *callee = call_expr->callee;

  if (callee->kind != AST_EXPR_IDENTIFIER) {
    sema_error(ctx, expr->loc, "Function calls must be made to identifiers");
    sema_call_args(ctx, expr);
    return type_error;
  }

  Symbol *func_sym = scope_lookup(ctx, callee->expr_identifier.name);

  if (!func_sym) {
    sema_error(ctx, expr->loc, "Undefined function '%s'", callee->expr_identifier.name);
    sema_call_args(ctx, expr);
    return type_error;
  }

  // A name whose declaration failed is declared as the error type, and was reported already
  if (func_sym->kind == SYMBOL_LOCAL_VAR && func_sym->type == type_error) {
    sema_call_args(ctx, expr);
    return type_error;
  }

  if (func_sym->kind != SYMBOL_FUNCTION) {
    const char *what = func_sym->kind == SYMBOL_TYPE ? "a type" : "a variable";

    if (func_sym->loc.line == 0) {
      sema_error(ctx, expr->loc, "'%s' is a builtin type, not a function", callee->expr_identifier.name);
    } else {
      sema_error(ctx,
                 expr->loc,
                 "'%s' is %s (declared at line %u), not a function",
                 callee->expr_identifier.name,
                 what,
                 func_sym->loc.line);
    }

    sema_call_args(ctx, expr);
    return type_error;
  }

  callee->expr_identifier.symbol = func_sym;

  TypeFunction *func_type = &func_sym->type->function;

  bool is_variadic = func_type->is_variadic;
  uint32_t fixed_count = func_type->param_count;
  uint32_t arg_count = call_expr->arg_count;

  if (is_variadic ? arg_count < fixed_count : arg_count != fixed_count) {
    sema_error(ctx,
               expr->loc,
               "Function '%s' expects %s%u arguments, but %u were provided",
               callee->expr_identifier.name,
               is_variadic ? "at least " : "",
               fixed_count,
               arg_count);
    sema_call_args(ctx, expr);
    return type_error;
  }

  bool args_ok = true;

  for (uint32_t i = 0; i < fixed_count; i++) {
    AstExpr *arg_expr = call_expr->args[i];
    Type *expected_type = func_type->param_types[i];
    Type *arg_type = sema_expr_hint(ctx, arg_expr, expected_type);

    if (arg_type == type_error) {
      args_ok = false;
      continue;
    }

    if (!type_can_widen_to(arg_type, expected_type)) {
      sema_error(ctx,
                 arg_expr->loc,
                 "Argument %u of function '%s' expects type '%s', but got '%s'",
                 i + 1,
                 callee->expr_identifier.name,
                 type_display_name(expected_type),
                 type_display_name(arg_type));
      args_ok = false;
      continue;
    }

    sema_coerce(ctx, &call_expr->args[i], expected_type);
  }

  for (uint32_t i = fixed_count; i < arg_count; i++) {
    AstExpr *arg_expr = call_expr->args[i];
    Type *arg_type = sema_expr(ctx, arg_expr);

    if (arg_type == type_error) {
      args_ok = false;
      continue;
    }

    Type *promoted = variadic_promoted_type(type_default(arg_type));
    if (!promoted) {
      sema_error(ctx, arg_expr->loc, "Cannot pass '%s' as a variadic argument", type_display_name(arg_type));
      args_ok = false;
      continue;
    }

    sema_coerce(ctx, &call_expr->args[i], promoted);
  }

  return args_ok ? func_type->return_type : type_error;
}

// Types `-x`, `!x` and `~x`: numeric, bool and integer operands respectively.
static Type *sema_expr_unary(SemaContext *ctx, AstExpr *expr) {
  AstExprUnary *unary_expr = &expr->expr_unary;

  Type *operand_type = sema_expr(ctx, unary_expr->operand);

  if (operand_type == type_error) {
    return type_error;
  }

  switch (unary_expr->op) {
  case UNOP_NEGATE:
    if (!type_is_numeric(operand_type)) {
      sema_error(
        ctx, expr->loc, "Unary '-' operator requires a numeric type, got '%s'", type_display_name(operand_type));
      return type_error;
    }

    return operand_type;

  case UNOP_NOT:
    if (!type_is_bool(operand_type)) {
      sema_error(ctx, expr->loc, "Unary '!' operator requires 'bool' type, got '%s'", type_display_name(operand_type));
      return type_error;
    }

    return operand_type;

  case UNOP_BIT_NOT:
    if (!type_is_integer(operand_type)) {
      sema_error(
        ctx, expr->loc, "Unary '~' operator requires an integer type, got '%s'", type_display_name(operand_type));
      return type_error;
    }

    return operand_type;

  case UNOP_COUNT:
    sema_error(ctx, expr->loc, "Invalid unary operator");
    return type_error;
  }

  sema_error(ctx, expr->loc, "Unknown unary operator");
  return type_error;
}

// Types `ptr + int`, `int + ptr`, `ptr - int` (the pointer type) and `ptr - ptr` (i64, counted in elements).
static Type *sema_pointer_arithmetic(SemaContext *ctx, AstExpr *expr, Type *left_type, Type *right_type) {
  AstExprBinary *binary_expr = &expr->expr_binary;

  BinaryOp op = binary_expr->op;
  bool left_is_ptr = type_is_pointer(left_type);
  bool right_is_ptr = type_is_pointer(right_type);

  if (op != BINOP_ADD && op != BINOP_SUB) {
    sema_error(ctx, expr->loc, "Pointer arithmetic only supports + and -");
    return type_error;
  }

  Type *ptr_type = left_is_ptr ? left_type : right_type;
  if (!type_has_storage(ptr_type->pointer.base_type)) {
    sema_error(
      ctx, expr->loc, "Cannot do arithmetic on a pointer to '%s'", type_display_name(ptr_type->pointer.base_type));
    return type_error;
  }

  if (left_is_ptr && right_is_ptr) {
    if (op == BINOP_ADD) {
      sema_error(ctx, expr->loc, "Cannot add two pointers");
      return type_error;
    }

    if (!type_equals(left_type, right_type)) {
      sema_error(
        ctx, expr->loc, "Cannot subtract '%s' from '%s'", type_display_name(right_type), type_display_name(left_type));
      return type_error;
    }

    return type_i64;
  }

  if (right_is_ptr && op == BINOP_SUB) {
    sema_error(ctx, expr->loc, "Cannot subtract a pointer from '%s'", type_display_name(left_type));
    return type_error;
  }

  Type *offset_type = left_is_ptr ? right_type : left_type;
  if (!type_is_integer(offset_type)) {
    sema_error(ctx, expr->loc, "Pointer arithmetic needs an integer offset, got '%s'", type_display_name(offset_type));
    return type_error;
  }

  sema_coerce(ctx, left_is_ptr ? &binary_expr->right : &binary_expr->left, type_i64);

  return ptr_type;
}

// Checks the operands, converts both to a common type; arithmetic yields that type, comparisons bool.
static Type *sema_expr_binary(SemaContext *ctx, AstExpr *expr) {
  AstExprBinary *binary_expr = &expr->expr_binary;

  Type *left_type = sema_expr(ctx, binary_expr->left);
  Type *right_type = sema_expr(ctx, binary_expr->right);

  if (left_type == type_error || right_type == type_error) {
    return type_error;
  }

  switch (binary_expr->op) {
  case BINOP_ADD:
  case BINOP_SUB:
  case BINOP_MUL:
  case BINOP_DIV: {
    if (type_is_pointer(left_type) || type_is_pointer(right_type)) {
      return sema_pointer_arithmetic(ctx, expr, left_type, right_type);
    }

    if (!type_is_numeric(left_type) || !type_is_numeric(right_type)) {
      sema_error(ctx,
                 expr->loc,
                 "Arithmetic operators require numeric operands, got '%s' and '%s'",
                 type_display_name(left_type),
                 type_display_name(right_type));
      return type_error;
    }

    Type *common_type = type_common(left_type, right_type);
    if (!common_type) {
      sema_error(ctx,
                 expr->loc,
                 "Incompatible types for arithmetic (got '%s' and '%s')",
                 type_display_name(left_type),
                 type_display_name(right_type));
      return type_error;
    }

    int64_t divisor;
    if (binary_expr->op == BINOP_DIV && sema_int_literal(binary_expr->right, &divisor) && divisor == 0) {
      sema_error(ctx, binary_expr->right->loc, "Division by zero");
      return type_error;
    }

    // Untyped operands stay untyped so a later consumer can pick the concrete type.
    if (!type_is_untyped(common_type)) {
      sema_coerce(ctx, &binary_expr->left, common_type);
      sema_coerce(ctx, &binary_expr->right, common_type);
    }

    return common_type;
  }

  case BINOP_EQ:
  case BINOP_NOT_EQ: {
    if (!type_is_comparable(left_type) || !type_is_comparable(right_type)) {
      Type *bad_type = type_is_comparable(left_type) ? right_type : left_type;
      sema_error(ctx, expr->loc, "Type '%s' cannot be compared for equality", type_display_name(bad_type));
      return type_error;
    }

    Type *common_type = type_common(left_type, right_type);
    if (!common_type) {
      sema_error(ctx,
                 expr->loc,
                 "Incompatible types for equality: '%s' and '%s'",
                 type_display_name(left_type),
                 type_display_name(right_type));
      return type_error;
    }

    sema_coerce(ctx, &binary_expr->left, type_default(common_type));
    sema_coerce(ctx, &binary_expr->right, type_default(common_type));

    return type_bool;
  }

  case BINOP_LESS:
  case BINOP_GREATER:
  case BINOP_LESS_EQ:
  case BINOP_GREATER_EQ: {
    if (!type_is_orderable(left_type) || !type_is_orderable(right_type)) {
      sema_error(ctx,
                 expr->loc,
                 "Comparisons require ordered types, got '%s' and '%s'",
                 type_display_name(left_type),
                 type_display_name(right_type));
      return type_error;
    }

    Type *common_type = type_common(left_type, right_type);
    if (!common_type) {
      sema_error(
        ctx, expr->loc, "Cannot compare '%s' with '%s'", type_display_name(left_type), type_display_name(right_type));
      return type_error;
    }

    sema_coerce(ctx, &binary_expr->left, type_default(common_type));
    sema_coerce(ctx, &binary_expr->right, type_default(common_type));

    return type_bool;
  }

  case BINOP_BIT_OR:
  case BINOP_BIT_XOR:
  case BINOP_BIT_AND: {
    if (!type_is_integer(left_type) || !type_is_integer(right_type)) {
      sema_error(ctx,
                 expr->loc,
                 "Bitwise operators require integer operands, got '%s' and '%s'",
                 type_display_name(left_type),
                 type_display_name(right_type));
      return type_error;
    }

    Type *common_type = type_common(left_type, right_type);
    if (!common_type) {
      sema_error(ctx,
                 expr->loc,
                 "Incompatible types for bitwise operation: '%s' and '%s'",
                 type_display_name(left_type),
                 type_display_name(right_type));
      return type_error;
    }

    if (!type_is_untyped(common_type)) {
      sema_coerce(ctx, &binary_expr->left, common_type);
      sema_coerce(ctx, &binary_expr->right, common_type);
    }

    return common_type;
  }

  case BINOP_SHL:
  case BINOP_SHR: {
    if (!type_is_integer(left_type) || !type_is_integer(right_type)) {
      sema_error(ctx,
                 expr->loc,
                 "Shift operators require integer operands, got '%s' and '%s'",
                 type_display_name(left_type),
                 type_display_name(right_type));
      return type_error;
    }

    return left_type;
  }

  case BINOP_COUNT:
    sema_error(ctx, expr->loc, "Invalid binary operator");
    return type_error;
  }

  sema_error(ctx, expr->loc, "Unknown binary operator");
  return type_error;
}

// Types `a && b` and `a || b`: both operands must be bool.
static Type *sema_expr_logical(SemaContext *ctx, AstExpr *expr) {
  AstExprLogical *logical_expr = &expr->expr_logical;

  Type *left_type = sema_expr(ctx, logical_expr->left);
  Type *right_type = sema_expr(ctx, logical_expr->right);

  if (left_type == type_error || right_type == type_error) {
    return type_error;
  }

  if (!type_is_bool(left_type) || !type_is_bool(right_type)) {
    sema_error(ctx,
               expr->loc,
               "Logical operators require 'bool' operands, got '%s' and '%s'",
               type_display_name(left_type),
               type_display_name(right_type));
    return type_error;
  }

  return type_bool;
}

// Types a cast node. Implicit casts are created by sema_coerce() with their type already set.
static Type *sema_expr_cast(SemaContext *ctx, AstExpr *expr) {
  AstExprCast *cast_expr = &expr->expr_cast;

  if (cast_expr->implicit) {
    return sema_expr_type(ctx, expr);
  }

  assert(cast_expr->target_type && "Missing cast target");

  AstExpr *operand = cast_expr->operand;
  Type *from_type = sema_expr(ctx, operand);
  Type *to_type = sema_type(ctx, cast_expr->target_type);

  if (from_type == type_error || to_type == type_error) {
    return to_type;
  }

  bool from_is_value = type_is_numeric(from_type) || from_type == type_bool;

  if (from_is_value && type_is_numeric(to_type)) {
    if (type_is_untyped(from_type)) {
      sema_concretize(ctx, operand, type_can_widen_to(from_type, to_type) ? to_type : type_default(from_type));
    }
    return to_type;
  }

  if (from_type == type_null && type_is_pointer(to_type)) {
    sema_concretize(ctx, operand, to_type);
    return to_type;
  }

  if (type_is_pointer(from_type) && (type_is_pointer(to_type) || to_type == type_i64)) {
    return to_type;
  }

  if (from_type == type_i64 && type_is_pointer(to_type)) {
    return to_type;
  }

  if (type_is_array(from_type) && type_is_slice(to_type) && type_can_widen_to(from_type, to_type)) {
    return to_type;
  }

  if (type_equals(from_type, to_type) && from_type != type_void) {
    return to_type;
  }

  if (to_type == type_bool && type_is_numeric(from_type)) {
    sema_error(ctx, expr->loc, "Cannot cast from '%s' to 'bool'. Use x != 0", type_display_name(from_type));
    return type_error;
  }

  sema_error(ctx, expr->loc, "Cannot cast from '%s' to '%s'", type_display_name(from_type), type_display_name(to_type));
  return type_error;
}

// Types `target = value`: the target must be an lvalue that is not an array, and the value converts to its type.
static Type *sema_expr_assign(SemaContext *ctx, AstExpr *expr) {
  AstExprAssign *assign_expr = &expr->expr_assign;

  AstExpr *target = assign_expr->target;

  if (is_composite_literal(target)) {
    sema_expr(ctx, assign_expr->value);
    sema_error(ctx, expr->loc, "Invalid assignment target: %s cannot be assigned to", describe_expr(target));
    return type_error;
  }

  if (target->kind == AST_EXPR_IDENTIFIER) {
    Symbol *sym = scope_lookup(ctx, target->expr_identifier.name);

    if (sym && sym->kind != SYMBOL_LOCAL_VAR && sym->kind != SYMBOL_GLOBAL_VAR) {
      sema_expr(ctx, assign_expr->value);
      sema_error(ctx,
                 expr->loc,
                 "Invalid assignment target: '%s' is %s, not a variable",
                 target->expr_identifier.name,
                 sym->kind == SYMBOL_TYPE ? "a type" : "a function");
      return type_error;
    }
  }

  Type *target_type = sema_expr(ctx, target);
  Type *value_type = sema_expr_hint(ctx, assign_expr->value, target_type);

  if (target_type != type_error && !is_lvalue(ctx, target)) {
    sema_error(ctx, expr->loc, "Invalid assignment target: %s cannot be assigned to", describe_expr(target));
    return type_error;
  }

  if (target_type == type_error || value_type == type_error) {
    return type_error;
  }

  if (target->kind == AST_EXPR_IDENTIFIER) {
    Symbol *target_sym = target->expr_identifier.symbol;
    if (!target_sym || (target_sym->kind != SYMBOL_LOCAL_VAR && target_sym->kind != SYMBOL_GLOBAL_VAR)) {
      sema_error(ctx, expr->loc, "Invalid assignment target: '%s' is not a variable", target->expr_identifier.name);
      return type_error;
    }
  }

  if (!type_can_widen_to(value_type, target_type)) {
    sema_error(
      ctx, expr->loc, "Cannot assign '%s' to '%s'", type_display_name(value_type), type_display_name(target_type));
    return type_error;
  }

  sema_coerce(ctx, &assign_expr->value, target_type);

  return target_type;
}

// Analyses an expression, records its type and returns it.
Type *sema_expr(SemaContext *ctx, AstExpr *expr) {
  assert(expr && "sema_expr called without an expression");

  Type *result_type = NULL;

  switch (expr->kind) {
  case AST_EXPR_LITERAL:
    result_type = sema_expr_literal(ctx, expr);
    break;

  case AST_EXPR_IDENTIFIER:
    result_type = sema_expr_identifier(ctx, expr);
    break;

  case AST_EXPR_ARRAY_LITERAL:
    result_type = sema_expr_array_literal(ctx, expr, NULL);
    break;

  case AST_EXPR_STRUCT_LITERAL:
    result_type = sema_expr_struct_literal(ctx, expr, NULL);
    break;

  case AST_EXPR_ADDR_OF:
    result_type = sema_expr_addr_of(ctx, expr);
    break;

  case AST_EXPR_DEREF:
    result_type = sema_expr_deref(ctx, expr);
    break;

  case AST_EXPR_SUBSCRIPT:
    result_type = sema_expr_subscript(ctx, expr);
    break;

  case AST_EXPR_SLICE:
    result_type = sema_expr_slice(ctx, expr);
    break;

  case AST_EXPR_MEMBER:
    result_type = sema_expr_member(ctx, expr);
    break;

  case AST_EXPR_CALL:
    result_type = sema_expr_call(ctx, expr);
    break;

  case AST_EXPR_UNARY:
    result_type = sema_expr_unary(ctx, expr);
    break;

  case AST_EXPR_BINARY:
    result_type = sema_expr_binary(ctx, expr);
    break;

  case AST_EXPR_LOGICAL:
    result_type = sema_expr_logical(ctx, expr);
    break;

  case AST_EXPR_CAST:
    result_type = sema_expr_cast(ctx, expr);
    break;

  case AST_EXPR_ASSIGN:
    result_type = sema_expr_assign(ctx, expr);
    break;

  case AST_EXPR_INVALID:
    sema_set_expr_type(ctx, expr, type_error);
    return type_error;
  }

  assert(result_type && "every expression kind produces a type");

  sema_set_expr_type(ctx, expr, result_type);

  if (result_type == type_untyped_int) {
    sema_fold_constant(expr);
  }

  return result_type;
}

// Like sema_expr, but `hint` is the type the expression will be converted to.
Type *sema_expr_hint(SemaContext *ctx, AstExpr *expr, Type *hint) {
  assert(expr && "sema_expr_hint called without an expression");

  Type *result_type = NULL;

  // Only the literals use the hint: the type of an array or a struct literal comes from the context
  switch (expr->kind) {
  case AST_EXPR_ARRAY_LITERAL:
    result_type = sema_expr_array_literal(ctx, expr, hint);
    break;

  case AST_EXPR_STRUCT_LITERAL:
    result_type = sema_expr_struct_literal(ctx, expr, hint);
    break;

  default:
    return sema_expr(ctx, expr);
  }

  sema_set_expr_type(ctx, expr, result_type);

  return result_type;
}

// Statement semantic analysis functions

// Analyses the statements of a block in the current scope.
static void sema_block_stmts(SemaContext *ctx, AstStmt *stmt) {
  assert(stmt->kind == AST_STMT_BLOCK && "sema_block_stmts: statement is not a block");

  AstStmtBlock *block_stmt = &stmt->stmt_block;

  for (uint32_t i = 0; i < block_stmt->stmt_count; i++) {
    sema_stmt(ctx, block_stmt->stmts[i]);
  }
}

static void sema_stmt_block(SemaContext *ctx, AstStmt *stmt) {
  uint32_t outer_start = scope_enter(ctx);

  sema_block_stmts(ctx, stmt);

  scope_exit(ctx, outer_start);
}

static void sema_stmt_expression(SemaContext *ctx, AstStmt *stmt) {
  Type *type = sema_expr(ctx, stmt->stmt_expression.expression);

  if (type == type_undef) {
    sema_error(ctx, stmt->loc, "'undef' can only initialize a variable");
  }
}

// Resolves `[_]T` and analyses the initializer: a literal against the full type, other values first for their length.
static Type *sema_inferred_array_type(SemaContext *ctx, AstType *ast_type, AstExpr *init) {
  if (!init) {
    sema_error(ctx, ast_type->loc, "Array with inferred length '[_]' must have an initializer");
    return type_error;
  }

  Type *elem_type = sema_type(ctx, ast_type->type_array.elem_type);
  Type *array_type = NULL;

  // A literal knows its length before it is analysed, so it gets the full type as its hint
  int64_t literal_length = init->kind == AST_EXPR_ARRAY_LITERAL ? sema_array_literal_length(ctx, init, false) : -1;

  if (elem_type == type_error) {
    array_type = type_error;
  } else if (literal_length > 0) {
    array_type = sema_array_of(ctx, init->loc, elem_type, literal_length);
  }

  Type *init_type = sema_expr_hint(ctx, init, array_type);

  if (array_type) {
    return array_type;
  }

  if (init_type == type_error) {
    return type_error;
  }

  if (!type_is_array(init_type)) {
    sema_error(ctx, init->loc, "Cannot initialize array with non-array type '%s'", type_display_name(init_type));
    return type_error;
  }

  return sema_array_of(ctx, init->loc, elem_type, init_type->array.length);
}

// Resolves a local variable's annotation (NULL if none) and analyses the initializer against it.
static Type *sema_local_var_type(SemaContext *ctx, AstStmt *stmt) {
  AstStmtLocalVar *local_var_stmt = &stmt->stmt_local_var;

  AstType *declared_ast_type = local_var_stmt->type;
  AstExpr *init = local_var_stmt->init;

  if (declared_ast_type && declared_ast_type->kind == AST_TYPE_ARRAY && !declared_ast_type->type_array.length_expr) {
    return sema_inferred_array_type(ctx, declared_ast_type, init);
  }

  Type *expected_type = declared_ast_type ? sema_type(ctx, declared_ast_type) : NULL;

  if (init) {
    sema_expr_hint(ctx, init, expected_type);
  }

  return expected_type;
}

// Declares a variable; the type comes from the annotation or the initializer, which is converted to it. `undef` needs
// an annotation and is not converted.
static void sema_stmt_local_var(SemaContext *ctx, AstStmt *stmt) {
  AstStmtLocalVar *local_var_stmt = &stmt->stmt_local_var;

  Type *expected_type = sema_local_var_type(ctx, stmt);
  Type *init_type = local_var_stmt->init ? sema_expr_type(ctx, local_var_stmt->init) : NULL;

  Type *var_type = expected_type ? expected_type : type_default(init_type);
  assert(var_type && "the parser requires a type annotation or an initializer");

  bool is_undef = init_type == type_undef;
  local_var_stmt->is_undef = is_undef;

  if (is_undef && !expected_type) {
    sema_error(
      ctx, stmt->loc, "Cannot infer type of variable '%s' from an undefined initializer", local_var_stmt->name);
    var_type = type_error;
  }

  var_type = sema_require_storage(ctx, stmt->loc, "variable", local_var_stmt->name, var_type);

  if (expected_type && init_type && !is_undef && !type_can_widen_to(init_type, var_type)) {
    sema_error(ctx,
               stmt->loc,
               "Cannot implicitly convert '%s' to '%s'",
               type_display_name(init_type),
               type_display_name(var_type));

    sema_declare_local(ctx, local_var_stmt->name, type_error, stmt->loc);
    return;
  }

  if (local_var_stmt->init && !is_undef) {
    sema_coerce(ctx, &local_var_stmt->init, var_type);
  }

  local_var_stmt->symbol = sema_declare_local(ctx, local_var_stmt->name, var_type, stmt->loc);
}

static void sema_stmt_return(SemaContext *ctx, AstStmt *stmt) {
  AstStmtReturn *return_stmt = &stmt->stmt_return;

  Type *expected_type = ctx->current_function->symbol->type->function.return_type;
  Type *actual_type = type_void;

  if (return_stmt->value) {
    actual_type = sema_expr_hint(ctx, return_stmt->value, expected_type);
  }

  if (!type_can_widen_to(actual_type, expected_type)) {
    sema_error(ctx,
               stmt->loc,
               "Function '%s' expects return type '%s', but got incompatible '%s'",
               ctx->current_function->name,
               type_display_name(expected_type),
               type_display_name(actual_type));
    return;
  }

  if (return_stmt->value) {
    sema_coerce(ctx, &return_stmt->value, expected_type);
  }
}

static void sema_stmt_break(SemaContext *ctx, AstStmt *stmt) {
  if (ctx->loop_depth == 0) {
    sema_error(ctx, stmt->loc, "'break' statement not within a loop");
  }
}

static void sema_stmt_continue(SemaContext *ctx, AstStmt *stmt) {
  if (ctx->loop_depth == 0) {
    sema_error(ctx, stmt->loc, "'continue' statement not within a loop");
  }
}

static void sema_stmt_if(SemaContext *ctx, AstStmt *stmt) {
  AstStmtIf *if_stmt = &stmt->stmt_if;

  Type *condition_type = sema_expr(ctx, if_stmt->condition);
  if (condition_type != type_bool && condition_type != type_error) {
    sema_error(ctx,
               if_stmt->condition->loc,
               "Condition in 'if' must be of type 'bool', got '%s'",
               type_display_name(condition_type));
  }

  sema_stmt(ctx, if_stmt->then_branch);
  if (if_stmt->else_branch) {
    sema_stmt(ctx, if_stmt->else_branch);
  }
}

static void sema_stmt_while(SemaContext *ctx, AstStmt *stmt) {
  AstStmtWhile *while_stmt = &stmt->stmt_while;

  Type *condition_type = sema_expr(ctx, while_stmt->condition);
  if (condition_type != type_bool && condition_type != type_error) {
    sema_error(ctx,
               while_stmt->condition->loc,
               "Condition in 'while' must be of type 'bool', got '%s'",
               type_display_name(condition_type));
  }

  ctx->loop_depth++;
  sema_stmt(ctx, while_stmt->body);
  ctx->loop_depth--;
}

// Analyses a statement.
void sema_stmt(SemaContext *ctx, AstStmt *stmt) {
  assert(ctx->current_function && "statements only appear inside functions");

  switch (stmt->kind) {
  case AST_STMT_BLOCK:
    return sema_stmt_block(ctx, stmt);
  case AST_STMT_EXPRESSION:
    return sema_stmt_expression(ctx, stmt);
  case AST_STMT_LOCAL_VAR:
    return sema_stmt_local_var(ctx, stmt);

  case AST_STMT_RETURN:
    return sema_stmt_return(ctx, stmt);
  case AST_STMT_BREAK:
    return sema_stmt_break(ctx, stmt);
  case AST_STMT_CONTINUE:
    return sema_stmt_continue(ctx, stmt);

  case AST_STMT_IF:
    return sema_stmt_if(ctx, stmt);
  case AST_STMT_WHILE:
    return sema_stmt_while(ctx, stmt);

  case AST_STMT_INVALID:
    return sema_error(ctx, stmt->loc, "Invalid statement");
  }

  sema_error(ctx, stmt->loc, "Unknown statement type");
}

// Declaration semantic analysis functions

// Declarations are analysed in three stages: declare puts every name in scope, resolve works out types and layouts on
// demand, and check analyses the function bodies.

// Declare: names

// Declares a top-level name and links its symbol to `decl`. A redeclaration is reported and gets a symbol that is in
// no scope, so the declaration can still be analysed.
static Symbol *sema_declare(SemaContext *ctx, AstDecl *decl, const char *name, SymbolKind kind, Type *type) {
  Symbol *sym = scope_insert(ctx, name, kind, type, decl->loc);
  if (!sym) {
    sema_error_redeclaration(ctx, decl->loc, scope_lookup_current(ctx, name));
    sym = symbol_new(ctx, name, kind, type, decl->loc);
  }

  sym->decl = decl;

  return sym;
}

// Declares a function with an empty type, which `sema_resolve_function` fills in.
static void sema_declare_function(SemaContext *ctx, AstDecl *decl) {
  AstDeclFunction *func_decl = &decl->decl_function;

  Type *func_type = arena_alloc(&ctx->comp_unit->arena, sizeof(Type));
  *func_type = (Type){
    .kind = TYPE_KIND_FUNCTION,
    .name = func_decl->name,
  };

  func_decl->symbol = sema_declare(ctx, decl, func_decl->name, SYMBOL_FUNCTION, func_type);
}

// Declares a struct with an empty type, which `sema_resolve_struct` fills in. Types that name it by pointer can
// already refer to that type.
static void sema_declare_struct(SemaContext *ctx, AstDecl *decl) {
  AstDeclStruct *struct_decl = &decl->decl_struct;

  Type *struct_type = arena_alloc(&ctx->comp_unit->arena, sizeof(Type));
  *struct_type = (Type){
    .kind = TYPE_KIND_STRUCT,
    .name = struct_decl->name,
  };

  struct_decl->symbol = sema_declare(ctx, decl, struct_decl->name, SYMBOL_TYPE, struct_type);
}

static void sema_declare_decl(SemaContext *ctx, AstDecl *decl) {
  switch (decl->kind) {
  case AST_DECL_FUNCTION:
    sema_declare_function(ctx, decl);
    break;

  case AST_DECL_STRUCT:
    sema_declare_struct(ctx, decl);
    break;

  case AST_DECL_INVALID:
    sema_error(ctx, decl->loc, "Invalid declaration");
    break;
  }
}

// Resolve: types

// Resolves the signature of a function into the type that was declared for it.
static void sema_resolve_function(SemaContext *ctx, AstDecl *decl) {
  AstDeclFunction *func_decl = &decl->decl_function;
  Symbol *sym = func_decl->symbol;

  Type *return_type = sema_type(ctx, func_decl->return_type);

  Type **param_types = arena_alloc(&ctx->comp_unit->arena, sizeof(Type *) * func_decl->param_count);
  for (uint32_t i = 0; i < func_decl->param_count; i++) {
    AstParam *param = &func_decl->params[i];
    param_types[i] = sema_require_storage(ctx, param->loc, "parameter", param->name, sema_type(ctx, param->type));
  }

  *sym->type = (Type){
    .kind = TYPE_KIND_FUNCTION,
    .name = func_decl->name,
    .function =
      {
        .return_type = return_type,
        .param_types = param_types,
        .param_count = func_decl->param_count,
        .is_variadic = func_decl->is_variadic,
      },
  };
}

// Reports field `index` of a struct if an earlier field has the same name; returns whether it is a duplicate.
static bool sema_is_duplicate_field(SemaContext *ctx, const AstDeclStruct *struct_decl, uint32_t index) {
  const AstStructField *field = &struct_decl->fields[index];

  for (uint32_t i = 0; i < index; i++) {
    if (struct_decl->fields[i].name != field->name) continue;

    sema_error(ctx,
               field->loc,
               "Duplicate field '%s' in struct '%s'. Previous declaration at line %u",
               field->name,
               struct_decl->name,
               struct_decl->fields[i].loc.line);
    return true;
  }

  return false;
}

// Lays out the fields of a struct into the type that was declared for it. A struct with an invalid field gets a dummy
// size, so its uses report nothing more.
static void sema_resolve_struct(SemaContext *ctx, AstDecl *decl) {
  AstDeclStruct *struct_decl = &decl->decl_struct;
  Symbol *sym = struct_decl->symbol;

  uint32_t field_count = struct_decl->field_count;
  TypeField *fields = arena_alloc(&ctx->comp_unit->arena, sizeof(TypeField) * field_count);

  uint32_t current_offset = 0;
  uint32_t max_align = 1;
  bool fields_ok = true;

  if (field_count == 0) {
    sema_error(ctx, decl->loc, "Struct '%s' has no fields", struct_decl->name);
    fields_ok = false;
  }

  for (uint32_t i = 0; i < field_count; i++) {
    AstStructField *field = &struct_decl->fields[i];

    Type *field_type = sema_require_storage(ctx, field->loc, "field", field->name, sema_type(ctx, field->type));

    if (sema_is_duplicate_field(ctx, struct_decl, i)) {
      field_type = type_error;
    }

    if (field_type == type_error) {
      fields_ok = false;
    }

    current_offset = align_to(current_offset, field_type->alignment);

    fields[i] = (TypeField){.name = field->name, .type = field_type, .offset = current_offset};

    current_offset += field_type->size;
    max_align = field_type->alignment > max_align ? field_type->alignment : max_align;
  }

  uint32_t total_size = align_to(current_offset, max_align);
  total_size = total_size > 0 || fields_ok ? total_size : 1;

  *sym->type = (Type){
    .kind = TYPE_KIND_STRUCT,
    .name = struct_decl->name,
    .size = total_size,
    .alignment = max_align,
    .structure =
      {
        .fields = fields,
        .field_count = field_count,
      },
  };
}

// Resolves the type of the declaration `sym` names, once. Returns false if the declaration needs itself to be
// resolved, so a struct that contains itself by value is reported.
static bool sema_resolve_symbol(SemaContext *ctx, Symbol *sym) {
  assert(sym && "sema_resolve_symbol: symbol is NULL");

  if (sym->resolve_state == SYMBOL_STATE_RESOLVED) return true;

  if (sym->resolve_state == SYMBOL_STATE_RESOLVING) {
    sema_error(ctx, sym->loc, "'%s' depends on itself", sym->name);
    return false;
  }

  // Builtin types, locals and parameters have nothing to resolve
  if (!sym->decl) return true;

  sym->resolve_state = SYMBOL_STATE_RESOLVING;

  switch (sym->decl->kind) {
  case AST_DECL_FUNCTION:
    sema_resolve_function(ctx, sym->decl);
    break;

  case AST_DECL_STRUCT:
    sema_resolve_struct(ctx, sym->decl);
    break;

  case AST_DECL_INVALID:
    UNREACHABLE("sema_resolve_symbol: invalid declaration");
  }

  sym->resolve_state = SYMBOL_STATE_RESOLVED;
  return true;
}

// Check: function bodies

// Declares the parameters in a new scope and analyses the function body.
static void sema_check_function(SemaContext *ctx, AstDecl *decl) {
  AstDeclFunction *func_decl = &decl->decl_function;
  assert(func_decl->symbol && "declare creates the symbol of every function");

  AstDeclFunction *prev_func_decl = ctx->current_function;

  if (func_decl->is_extern) {
    return;
  }

  ctx->current_function = func_decl;
  uint32_t outer_start = scope_enter(ctx);

  Type *func_type = func_decl->symbol->type;

  for (uint32_t i = 0; i < func_decl->param_count; i++) {
    AstParam *param = &func_decl->params[i];
    Type *param_type = func_type->function.param_types[i];

    Symbol *sym = sema_declare_local(ctx, param->name, param_type, param->loc);
    if (!sym) continue;

    sym->local.is_param = true;
    param->symbol = sym;
  }

  // The body shares the scope of the parameters, so a local cannot repeat the name of a parameter
  sema_block_stmts(ctx, func_decl->body);

  scope_exit(ctx, outer_start);
  ctx->current_function = prev_func_decl;
}

static void sema_check_decl(SemaContext *ctx, AstDecl *decl) {
  switch (decl->kind) {
  case AST_DECL_FUNCTION:
    sema_check_function(ctx, decl);
    break;

  case AST_DECL_STRUCT:
  case AST_DECL_INVALID:
    break;
  }
}

// Type semantic analysis functions

static Type *sema_type_impl(SemaContext *ctx, AstType *ast_type, bool need_complete);

// Resolves a type name such as i32.
static Type *sema_type_named(SemaContext *ctx, AstType *ast_type, bool need_complete) {
  AstTypeNamed *named_ast_type = &ast_type->type_named;
  assert(named_ast_type->name && "the parser always provides the name of a named type");

  Symbol *sym = scope_lookup_type_name(ctx, named_ast_type->name);
  if (!sym) {
    sema_error(ctx, ast_type->loc, "Undefined type '%s'", named_ast_type->name);
    return type_error;
  }

  if (need_complete && !sema_resolve_symbol(ctx, sym)) {
    return type_error;
  }

  if (sym->kind != SYMBOL_TYPE) {
    const char *what = sym->kind == SYMBOL_FUNCTION ? "a function" : "a variable";
    sema_error(
      ctx, ast_type->loc, "'%s' is %s, not a type (declared at line %u)", named_ast_type->name, what, sym->loc.line);
    return type_error;
  }

  return sym->type;
}

// Resolves `*T`.
static Type *sema_type_pointer(SemaContext *ctx, AstType *ast_type, bool need_complete) {
  UNUSED(need_complete);

  Type *base_type = sema_type_impl(ctx, ast_type->type_pointer.base_type, false);

  if (base_type == type_error) {
    return type_error;
  }

  return type_pointer_to(&ctx->comp_unit->arena, base_type);
}

// Resolves `[N]T`: the length must be a positive integer literal.
static Type *sema_type_array(SemaContext *ctx, AstType *ast_type, bool need_complete) {
  AstTypeArray *array_ast_type = &ast_type->type_array;

  if (!array_ast_type->length_expr) {
    sema_error(ctx, ast_type->loc, "Array with inferred length '[_]' must have an initializer");
    return type_error;
  }

  Type *elem_type = sema_type_impl(ctx, array_ast_type->elem_type, need_complete);
  Type *length_type = sema_expr(ctx, array_ast_type->length_expr);

  if (elem_type == type_error || length_type == type_error) {
    return type_error;
  }

  if (!type_is_integer(length_type)) {
    sema_error(ctx,
               array_ast_type->length_expr->loc,
               "Array length must be an integer, got '%s'",
               type_display_name(length_type));
    return type_error;
  }

  if (array_ast_type->length_expr->kind != AST_EXPR_LITERAL) {
    sema_error(ctx, array_ast_type->length_expr->loc, "Array length must be an integer literal");
    return type_error;
  }

  bool negative;
  uint64_t length;
  if (!sema_int_literal_parts(array_ast_type->length_expr, &negative, &length)) {
    UNREACHABLE("sema_type_array: an integer literal has an integer value");
  }

  if (negative || length == 0) {
    sema_error(ctx, array_ast_type->length_expr->loc, "Array length must be greater than zero");
    return type_error;
  }

  return sema_array_of(ctx, array_ast_type->length_expr->loc, elem_type, length);
}

// Resolves `[]T`.
static Type *sema_type_slice(SemaContext *ctx, AstType *ast_type, bool need_complete) {
  UNUSED(need_complete);

  Type *elem_type = sema_type_impl(ctx, ast_type->type_slice.elem_type, false);

  if (elem_type == type_error) {
    return type_error;
  }

  if (type_is_void(elem_type)) {
    sema_error(ctx, ast_type->loc, "Cannot make a slice of 'void'");
    return type_error;
  }

  return type_slice_of(&ctx->comp_unit->arena, elem_type);
}

static Type *sema_type_impl(SemaContext *ctx, AstType *ast_type, bool need_complete) {
  if (!ast_type) {
    return type_void;
  }

  switch (ast_type->kind) {
  case AST_TYPE_INVALID:
    sema_error(ctx, ast_type->loc, "Invalid type");
    return type_error;
  case AST_TYPE_NAMED:
    return sema_type_named(ctx, ast_type, need_complete);
  case AST_TYPE_POINTER:
    return sema_type_pointer(ctx, ast_type, need_complete);
  case AST_TYPE_ARRAY:
    return sema_type_array(ctx, ast_type, need_complete);
  case AST_TYPE_SLICE:
    return sema_type_slice(ctx, ast_type, need_complete);
  }

  sema_error(ctx, ast_type->loc, "Unknown type kind");
  return type_error;
}

// Resolves a written type to a Type: no type means void.
Type *sema_type(SemaContext *ctx, AstType *ast_type) {
  return sema_type_impl(ctx, ast_type, true);
}

// Semantic analysis functions

// Declares the builtin types that can be named in source; they have no source line.
static void sema_init_builtins(SemaContext *ctx) {
#define TYPE_DEFINE(kind, size, ident)                                   \
  if (!type_is_internal(type_##ident)) {                                 \
    const char *name = st_intern(&ctx->comp_unit->intern_table, #ident); \
    scope_insert(ctx, name, SYMBOL_TYPE, type_##ident, (SourceLoc){0});  \
  }
  TYPES_BUILTIN(TYPE_DEFINE)
#undef TYPE_DEFINE
}

void sema_init(SemaContext *ctx, CompilationUnit *comp_unit) {
  ctx->comp_unit = comp_unit;
  ctx->locals = NULL;
  ctx->scope_start = 0;
  ctx->scope_depth = 0;
  ctx->next_symbol_id = 1;
  ctx->loop_depth = 0;

  ctx->expr_types = NULL;
  da_set_len(ctx->expr_types, ast_expr_count() + 1);
  for (size_t i = 0; i < da_len(ctx->expr_types); i++) {
    ctx->expr_types[i] = NULL;
  }

  sema_init_builtins(ctx);
}

void sema_free(SemaContext *ctx) {
  da_free(ctx->locals);
  da_free(ctx->expr_types);
}

// The symbol a declaration introduced.
static Symbol *decl_symbol(const AstDecl *decl) {
  switch (decl->kind) {
  case AST_DECL_FUNCTION:
    return decl->decl_function.symbol;

  case AST_DECL_STRUCT:
    return decl->decl_struct.symbol;

  case AST_DECL_INVALID:
    break;
  }

  UNREACHABLE("decl_symbol: invalid declaration");
}

// Runs the three stages over all declarations: declare, resolve and check.
void sema_program(SemaContext *ctx, AstProgram *program) {
  for (uint32_t i = 0; i < program->decl_count; i++) {
    sema_declare_decl(ctx, program->decls[i]);
  }

  for (uint32_t i = 0; i < program->decl_count; i++) {
    sema_resolve_symbol(ctx, decl_symbol(program->decls[i]));
  }

  for (uint32_t i = 0; i < program->decl_count; i++) {
    sema_check_decl(ctx, program->decls[i]);
  }
}
