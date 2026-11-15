#include "gen_ir.h"

#include "ast.h"
#include "common.h"
#include "ir.h"
#include "lib/array.h"
#include "sema.h"
#include "types.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static IrType get_ir_type(IrGenContext *ctx, Type *type);

// Context and type helpers

static inline IrFunction *get_current_function(IrGenContext *ctx) {
  return &ctx->module->functions[ctx->current_function_index];
}

// The id of the aggregate with these fields, added on first use. `alignment` always comes from the `Type` it lays out.
static IrAggId get_agg_id(IrGenContext *ctx, uint32_t alignment, const IrAggField *fields, uint32_t field_count) {
  IrModule *module = ctx->module;

  for (uint32_t i = 0; i < da_len(module->aggregates); i++) {
    IrAggregate *agg = &module->aggregates[i];
    if (da_len(agg->fields) != field_count) {
      continue;
    }

    bool matches = true;
    for (uint32_t j = 0; j < field_count; j++) {
      if (agg->fields[j].count != fields[j].count || !ir_type_equals(agg->fields[j].type, fields[j].type)) {
        matches = false;
        break;
      }
    }

    if (matches) {
      return (IrAggId){i};
    }
  }

  char *name = arena_alloc(&ctx->comp_unit->arena, 16);
  snprintf(name, 16, "agg%zu", da_len(module->aggregates));

  IrAggregate agg = {.name = name, .alignment = alignment, .fields = NULL};
  for (uint32_t i = 0; i < field_count; i++) {
    da_append(agg.fields, fields[i]);
  }
  da_append(module->aggregates, agg);

  return (IrAggId){(uint32_t)da_len(module->aggregates) - 1};
}

// The id of the aggregate with the layout of array `type`; nested arrays are flattened.
static IrAggId get_array_agg_id(IrGenContext *ctx, Type *type) {
  assert(type_is_array(type) && "get_array_agg_id: type is not an array");

  uint32_t count = 1;
  Type *element = type;
  while (type_is_array(element)) {
    count *= element->array.length;
    element = element->array.elem_type;
  }

  IrAggField field = {.type = get_ir_type(ctx, element), .count = count};
  return get_agg_id(ctx, type->alignment, &field, 1);
}

// The id of the aggregate with the layout of slice `type`, `{ptr, len}`; all slices share it.
static IrAggId get_slice_agg_id(IrGenContext *ctx, Type *type) {
  assert(type_is_slice(type) && "get_slice_agg_id: type is not a slice");

  IrAggField fields[] = {{.type = IR_PTR, .count = 1}, {.type = IR_I64, .count = 1}};
  return get_agg_id(ctx, type->alignment, fields, 2);
}

// The id of the aggregate with the layout of struct `type`: its fields, in declaration order.
static IrAggId get_struct_agg_id(IrGenContext *ctx, Type *type) {
  assert(type_is_struct(type) && "get_struct_agg_id: type is not a struct");

  IrAggField *fields = NULL;

  for (uint32_t i = 0; i < type->structure.field_count; i++) {
    IrAggField field = {.type = get_ir_type(ctx, type->structure.fields[i].type), .count = 1};
    da_append(fields, field);
  }

  IrAggId agg_id = get_agg_id(ctx, type->alignment, fields, da_len(fields));
  da_free(fields);

  return agg_id;
}

// The id of the data item with these bytes and alignment, added on first use. Items with the same size and contents
// are shared.
static IrDataId get_data_id(IrGenContext *ctx, uint8_t *bytes, uint32_t size, uint32_t alignment) {
  IrModule *module = ctx->module;

  for (uint32_t i = 0; i < da_len(module->data); i++) {
    IrData *data = &module->data[i];
    if (data->size == size && memcmp(data->bytes, bytes, size) == 0) {
      return (IrDataId){i};
    }
  }

  char *name = arena_alloc(&ctx->comp_unit->arena, 16);
  snprintf(name, 16, "data%zu", da_len(module->data));

  IrData data = {.name = name, .bytes = bytes, .size = size, .alignment = alignment};
  da_append(module->data, data);

  return (IrDataId){(uint32_t)da_len(module->data) - 1};
}

static IrType get_ir_type(IrGenContext *ctx, Type *type) {
  assert(type && "expression has no type; sema did not analyse it");

  switch (type->kind) {
  case TYPE_KIND_U8:
    return IR_U8;
  case TYPE_KIND_U16:
    return IR_U16;
  case TYPE_KIND_U32:
    return IR_U32;
  case TYPE_KIND_U64:
    return IR_U64;

  case TYPE_KIND_I8:
    return IR_I8;
  case TYPE_KIND_I16:
    return IR_I16;
  case TYPE_KIND_I32:
    return IR_I32;
  case TYPE_KIND_I64:
    return IR_I64;

  case TYPE_KIND_BOOL:
    return IR_INT(1, false);

  case TYPE_KIND_F32:
    return IR_F32;
  case TYPE_KIND_F64:
    return IR_F64;

  case TYPE_KIND_UNTYPED_INT:
    return IR_I32;
  case TYPE_KIND_UNTYPED_FLOAT:
    return IR_F64;
  case TYPE_KIND_NULL:
    return IR_PTR;

  case TYPE_KIND_POINTER:
    return IR_PTR;

  case TYPE_KIND_ARRAY:
    return IR_AGG(get_array_agg_id(ctx, type));
  case TYPE_KIND_SLICE:
    return IR_AGG(get_slice_agg_id(ctx, type));
  case TYPE_KIND_STRUCT:
    return IR_AGG(get_struct_agg_id(ctx, type));

  case TYPE_KIND_ERROR:
  case TYPE_KIND_VOID:
  case TYPE_KIND_UNDEF:
  case TYPE_KIND_FUNCTION:
    return IR_VOID;
  }

  return IR_I32;
}

// Registers, labels and symbols

// A new register of IR type `ir_type` in the current function; its id is its index in `reg_types`.
static IrReg new_reg(IrGenContext *ctx, IrType ir_type) {
  IrFunction *func = get_current_function(ctx);
  IrReg reg = {.id = (uint32_t)da_len(func->reg_types)};

  da_append(func->reg_types, ir_type);

  return reg;
}

// A new register for a value of the Moth type `type`.
static IrReg new_reg_for(IrGenContext *ctx, Type *type) {
  return new_reg(ctx, get_ir_type(ctx, type));
}

static IrLabel new_label(IrGenContext *ctx) {
  return (IrLabel){.id = ctx->next_label++};
}

// Binds `sym` to the register that holds it, or to the address of its slot when it lives in memory.
static void bind_symbol_reg(IrGenContext *ctx, Symbol *sym, IrReg reg) {
  assert(sym != NULL && "cannot map NULL symbol");
  assert(sym->id < da_len(ctx->symbol_to_reg) && "symbol id outside the register table");
  assert(ctx->symbol_to_reg[sym->id].id == IR_NULL_REG.id && "symbol is already mapped");

  ctx->symbol_to_reg[sym->id] = reg;
}

// The register `sym` was bound to.
static IrReg get_symbol_reg(IrGenContext *ctx, Symbol *sym) {
  assert(sym != NULL && "cannot get NULL symbol");
  assert(sym->id < da_len(ctx->symbol_to_reg) && "symbol id outside the register table");

  IrReg reg = ctx->symbol_to_reg[sym->id];
  assert(reg.id != IR_NULL_REG.id && "symbol was never mapped to a register");

  return reg;
}

// Low-level emitters

// Appends an instruction to the current function; code after a jump or return is dropped until the next label.
static void append_instr(IrGenContext *ctx, IrInstr instr) {
  if (instr.op == IR_OP_LABEL) {
    ctx->block_terminated = false;
  }

  if (ctx->block_terminated) {
    return;
  }

  IrFunction *func = get_current_function(ctx);
  da_append(func->instrs, instr);

  if (instr.op == IR_OP_JUMP || instr.op == IR_OP_RETURN) {
    ctx->block_terminated = true;
  }
}

#define emit_ir_instr(ctx, ir_op, ...) append_instr(ctx, (IrInstr){.op = (ir_op), __VA_ARGS__})

static IrReg emit_int_const(IrGenContext *ctx, int64_t value, IrType ir_type) {
  IrReg result = new_reg(ctx, ir_type);

  emit_ir_instr(ctx, IR_OP_LOAD_INT, .res = result, .int_lit = value);

  return result;
}

// Reads a value of `type` from the address `addr`: a scalar is loaded, an aggregate is its address.
static IrReg emit_load(IrGenContext *ctx, IrReg addr, Type *type) {
  if (type_is_aggregate(type)) {
    return addr;
  }

  IrReg value = new_reg_for(ctx, type);
  emit_ir_instr(ctx, IR_OP_LOAD, .res = value, .arg1 = addr);

  return value;
}

// Writes `value` of `type` to the address `addr`: an aggregate is copied, a scalar stored.
static void emit_store(IrGenContext *ctx, IrReg value, IrReg addr, Type *value_type) {
  if (type_is_aggregate(value_type)) {
    emit_ir_instr(ctx, IR_OP_MEMCPY, .arg1 = value, .arg2 = addr, .int_lit = value_type->size);
    return;
  }

  emit_ir_instr(ctx, IR_OP_STORE, .arg1 = value, .arg2 = addr);
}

// The offset in bytes of `index` elements of `elem_size` bytes. The index is an i64.
static IrReg emit_scaled_offset(IrGenContext *ctx, IrReg index, int64_t elem_size) {
  if (elem_size == 1) {
    return index;
  }

  IrReg size = emit_int_const(ctx, elem_size, IR_I64);
  IrReg bytes = new_reg(ctx, IR_I64);

  emit_ir_instr(ctx, IR_OP_MUL, .res = bytes, .arg1 = index, .arg2 = size);

  return bytes;
}

// The address `byte_offset` bytes past `base`; an offset of 0 is `base` itself.
static IrReg emit_addr_offset(IrGenContext *ctx, IrReg base, int64_t byte_offset) {
  assert(base.id != IR_NULL_REG.id && "emit_addr_offset: base is NULL");
  assert(byte_offset >= 0 && "emit_addr_offset: byte_offset is negative");

  if (byte_offset == 0) {
    return base;
  }

  IrReg offset = emit_int_const(ctx, byte_offset, IR_I64);
  IrReg addr = new_reg(ctx, IR_PTR);

  emit_ir_instr(ctx, IR_OP_ADD, .res = addr, .arg1 = base, .arg2 = offset);

  return addr;
}

// The address of element `index` of the elements at `base`.
static IrReg emit_elem_addr(IrGenContext *ctx, IrReg base, IrReg index, int64_t elem_size) {
  assert(base.id != IR_NULL_REG.id && "emit_elem_addr: base is NULL");
  assert(index.id != IR_NULL_REG.id && "emit_elem_addr: index is NULL");
  assert(elem_size > 0 && "emit_elem_addr: elements have no size");

  IrReg offset = emit_scaled_offset(ctx, index, elem_size);
  IrReg addr = new_reg(ctx, IR_PTR);

  emit_ir_instr(ctx, IR_OP_ADD, .res = addr, .arg1 = base, .arg2 = offset);

  return addr;
}

// Loads the field of type `field_type` that is `field_offset` bytes into the aggregate at `object`.
static IrReg emit_field_load(IrGenContext *ctx, IrReg object, uint32_t field_offset, Type *field_type) {
  assert(object.id != IR_NULL_REG.id && "emit_field_load: object is NULL");

  return emit_load(ctx, emit_addr_offset(ctx, object, field_offset), field_type);
}

// Stores `value` into `count` consecutive elements at `base`; `count` must be at least 1.
static void emit_fill(IrGenContext *ctx, IrReg base, IrReg value, Type *elem_type, uint32_t count) {
  uint32_t elem_size = elem_type->size;

  IrReg size = emit_int_const(ctx, elem_size, IR_I64);
  IrReg total = emit_int_const(ctx, (int64_t)count * elem_size, IR_I64);

  // The count is at least 1, so the loop is tested at the bottom
  IrReg end = new_reg(ctx, IR_PTR);
  emit_ir_instr(ctx, IR_OP_ADD, .res = end, .arg1 = base, .arg2 = total);

  IrReg addr = new_reg(ctx, IR_PTR);
  emit_ir_instr(ctx, IR_OP_COPY, .res = addr, .arg1 = base);

  IrLabel loop_start = new_label(ctx);
  IrLabel loop_end = new_label(ctx);

  emit_ir_instr(ctx, IR_OP_LABEL, .target = loop_start);
  emit_store(ctx, value, addr, elem_type);

  // ptr += elem_size, repeating while ptr < end
  IrReg next_addr = new_reg(ctx, IR_PTR);
  emit_ir_instr(ctx, IR_OP_ADD, .res = next_addr, .arg1 = addr, .arg2 = size);
  emit_ir_instr(ctx, IR_OP_COPY, .res = addr, .arg1 = next_addr);

  IrReg condition = new_reg(ctx, IR_I32);
  emit_ir_instr(ctx, IR_OP_CMP_LT, .res = condition, .arg1 = addr, .arg2 = end);
  emit_ir_instr(ctx, IR_OP_JNZ, .arg1 = condition, .target_true = loop_start, .target_false = loop_end);

  emit_ir_instr(ctx, IR_OP_LABEL, .target = loop_end);
}

// Zeroes a value of `type` at `base` with stores as wide as its alignment allows; the size of a type is a multiple
// of its alignment.
static void emit_zero(IrGenContext *ctx, IrReg base, Type *type) {
  Type *unit_type = type->alignment >= 8 ? type_i64 : type->alignment >= 4 ? type_i32 : type_bool;
  IrReg zero = emit_int_const(ctx, 0, IR_INT(unit_type->size, false));
  emit_fill(ctx, base, zero, unit_type, type->size / unit_type->size);
}

// Reserves an entry-block stack slot for a value of `type`; the address is typed as the aggregate if it is one.
static IrReg queue_entry_alloc(IrGenContext *ctx, Type *type) {
  IrReg slot = new_reg(ctx, type_is_aggregate(type) ? get_ir_type(ctx, type) : IR_PTR);

  IrInstr alloc_instr = {
    .op = IR_OP_ALLOC,
    .res = slot,
    .alloc = {.size = type->size, .alignment = type->alignment},
  };
  da_append(ctx->entry_allocs, alloc_instr);

  return slot;
}

// Builds a slice of type `slice_type` in a new stack slot from its data pointer and length; yields the slot's address.
static IrReg emit_slice_value(IrGenContext *ctx, Type *slice_type, IrReg ptr, IrReg len) {
  assert(type_is_slice(slice_type) && "emit_slice_value: type is not a slice");
  assert(ptr.id != IR_NULL_REG.id && "emit_slice_value: ptr is NULL");
  assert(len.id != IR_NULL_REG.id && "emit_slice_value: len is NULL");

  IrReg slice_addr = queue_entry_alloc(ctx, slice_type);

  emit_ir_instr(ctx, IR_OP_STORE, .arg1 = ptr, .arg2 = slice_addr);

  IrReg len_addr = emit_addr_offset(ctx, slice_addr, SLICE_LEN_OFFSET);
  emit_ir_instr(ctx, IR_OP_STORE, .arg1 = len, .arg2 = len_addr);

  return slice_addr;
}

// Conversions

// Returns `reg` with the IR type `ir_type`, copying it to a new register only when the type differs.
static IrReg retype_reg(IrGenContext *ctx, IrReg reg, IrType ir_type) {
  if (ir_type_equals(get_current_function(ctx)->reg_types[reg.id], ir_type)) {
    return reg;
  }

  IrReg result = new_reg(ctx, ir_type);

  emit_ir_instr(ctx, IR_OP_COPY, .res = result, .arg1 = reg);

  return result;
}

// IR op that converts a value of IR type `from_ir_type` to IR type `to_ir_type`.
static IrOp conversion_op(IrType from_ir_type, IrType to_ir_type) {
  // Pointers, aggregates (their address) and i64 have the same representation; only the register's type changes.
  bool from_wide = from_ir_type.kind == IR_TYPE_PTR || from_ir_type.kind == IR_TYPE_AGG ||
                   (from_ir_type.kind == IR_TYPE_INT && from_ir_type.size == 8);
  bool to_wide = to_ir_type.kind == IR_TYPE_PTR || to_ir_type.kind == IR_TYPE_AGG ||
                 (to_ir_type.kind == IR_TYPE_INT && to_ir_type.size == 8);
  if (from_wide && to_wide) return IR_OP_COPY;

  bool from_float = ir_type_is_float(from_ir_type);
  bool to_float = ir_type_is_float(to_ir_type);

  if (!from_float && !to_float) {
    if (from_ir_type.size <= 4 && to_ir_type.size <= 4) {
      bool needs_extend =
        to_ir_type.size < 4 && (from_ir_type.size > to_ir_type.size || from_ir_type.is_signed != to_ir_type.is_signed);
      return needs_extend ? IR_OP_TRUNC : IR_OP_COPY;
    }

    if (from_ir_type.size >= to_ir_type.size) return IR_OP_TRUNC;
    return from_ir_type.is_signed ? IR_OP_SEXT : IR_OP_ZEXT;
  }

  if (!from_float) return IR_OP_ITOF;
  if (to_float) return from_ir_type.size < to_ir_type.size ? IR_OP_FEXT : IR_OP_FTRUNC;
  return IR_OP_FTOI;
}

// Converts the array at `array_addr` to a slice that points at it and has the array's length.
static IrReg emit_array_to_slice(IrGenContext *ctx, IrReg array_addr, Type *array_type, Type *slice_type) {
  assert(type_is_array(array_type) && "emit_array_to_slice: type is not an array");
  assert(type_is_slice(slice_type) && "emit_array_to_slice: target type is not a slice");
  assert(type_equals(type_elem(array_type), type_elem(slice_type)) && "emit_array_to_slice: element types differ");

  // The data pointer is stored as a scalar, so the address cannot be typed as the aggregate
  IrReg ptr = retype_reg(ctx, array_addr, IR_PTR);
  IrReg len = emit_int_const(ctx, array_type->array.length, IR_I64);

  return emit_slice_value(ctx, slice_type, ptr, len);
}

// Converts `value` from `from_type` to `to_type`; the same IR type needs no instruction.
static IrReg emit_cast_if_needed(IrGenContext *ctx, IrReg value, Type *from_type, Type *to_type) {
  IrType from_ir_type = get_ir_type(ctx, from_type);
  IrType to_ir_type = get_ir_type(ctx, to_type);

  if (ir_type_equals(from_ir_type, to_ir_type)) {
    return value;
  }

  if (type_is_array(from_type) && type_is_slice(to_type)) {
    return emit_array_to_slice(ctx, value, from_type, to_type);
  }

  assert(!ir_type_is_void(from_ir_type) && !ir_type_is_void(to_ir_type) && "cast between non-value types");

  IrReg result = new_reg_for(ctx, to_type);

  emit_ir_instr(ctx, conversion_op(from_ir_type, to_ir_type), .res = result, .arg1 = value);

  return result;
}

// Expression handling

static IrReg emit_expr(IrGenContext *ctx, AstExpr *expr);

static inline Type *expr_type(IrGenContext *ctx, AstExpr *expr) {
  return sema_expr_type(ctx->sema_ctx, expr);
}

static IrOp get_unary_ir_op(UnaryOp op) {
  switch (op) {
  case UNOP_NEGATE:
    return IR_OP_NEGATE;
  case UNOP_NOT:
    return IR_OP_NOT;
  case UNOP_BIT_NOT:
    return IR_OP_BIT_NOT;

  case UNOP_COUNT:
    UNREACHABLE("get_unary_ir_op: UNOP_COUNT is not a valid operator");
  }

  UNREACHABLE("get_unary_ir_op: unhandled unary operator");
}

static IrOp get_binary_ir_op(BinaryOp op) {
  switch (op) {
  case BINOP_ADD:
    return IR_OP_ADD;
  case BINOP_SUB:
    return IR_OP_SUB;
  case BINOP_MUL:
    return IR_OP_MUL;
  case BINOP_DIV:
    return IR_OP_DIV;

  case BINOP_LESS:
    return IR_OP_CMP_LT;
  case BINOP_GREATER:
    return IR_OP_CMP_GT;
  case BINOP_EQ:
    return IR_OP_CMP_EQ;
  case BINOP_NOT_EQ:
    return IR_OP_CMP_NE;
  case BINOP_LESS_EQ:
    return IR_OP_CMP_LE;
  case BINOP_GREATER_EQ:
    return IR_OP_CMP_GE;

  case BINOP_BIT_OR:
    return IR_OP_BIT_OR;
  case BINOP_BIT_XOR:
    return IR_OP_BIT_XOR;
  case BINOP_BIT_AND:
    return IR_OP_BIT_AND;
  case BINOP_SHL:
    return IR_OP_SHL;
  case BINOP_SHR:
    return IR_OP_SHR;

  case BINOP_COUNT:
    UNREACHABLE("get_binary_ir_op: BINOP_COUNT is not a valid operator");
  }

  UNREACHABLE("get_binary_ir_op: unhandled binary operator");
}

// The id of the data item for a string literal: its `len` bytes and the zero byte that follows them. `data` must be
// NUL-terminated, as strings from the intern table are.
static IrDataId get_string_data_id(IrGenContext *ctx, const char *data, uint32_t len) {
  return get_data_id(ctx, (uint8_t *)data, len + 1, 1);
}

// Yields a slice of the string's data and its length, which does not count the terminating zero byte.
static IrReg emit_expr_literal_string(IrGenContext *ctx, AstExpr *expr) {
  AstExprLiteral *literal_expr = &expr->expr_literal;

  const char *data = literal_expr->string_value.data;
  uint32_t length = literal_expr->string_value.length;

  IrDataId data_id = get_string_data_id(ctx, data, length);

  IrReg ptr = new_reg_for(ctx, type_void_ptr);
  emit_ir_instr(ctx, IR_OP_GLOBAL_ADDR, .res = ptr, .data = data_id);

  IrReg len = emit_int_const(ctx, length, IR_I64);

  return emit_slice_value(ctx, expr_type(ctx, expr), ptr, len);
}

// The value of an integer, character, bool or null literal.
static int64_t literal_int_value(const AstExprLiteral *literal_expr) {
  switch (literal_expr->kind) {
  case AST_LITERAL_INT:
    return literal_expr->int_value;
  case AST_LITERAL_CHAR:
    return literal_expr->code_point;
  case AST_LITERAL_TRUE:
    return 1;
  case AST_LITERAL_FALSE:
  case AST_LITERAL_NULL:
    return 0;

  case AST_LITERAL_UNDEF:
    UNREACHABLE("literal_int_value: a declaration skips its undef initializer");
  case AST_LITERAL_FLOAT:
  case AST_LITERAL_STRING:
    UNREACHABLE("literal_int_value: the literal has no integer value");
  }

  UNREACHABLE("literal_int_value: unhandled literal kind");
}

// Emits a literal: a number, character or bool is a constant in a register; a string is a slice of data.
static IrReg emit_expr_literal(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_literal: expr is NULL");

  AstExprLiteral *literal_expr = &expr->expr_literal;

  if (literal_expr->kind == AST_LITERAL_STRING) {
    return emit_expr_literal_string(ctx, expr);
  }

  Type *type = expr_type(ctx, expr);
  IrReg result = new_reg_for(ctx, type);

  if (ir_type_is_float(get_ir_type(ctx, type))) {
    double float_value =
      literal_expr->kind == AST_LITERAL_FLOAT ? literal_expr->float_value : (double)literal_int_value(literal_expr);
    emit_ir_instr(ctx, IR_OP_LOAD_FLOAT, .res = result, .float_lit = float_value);
  } else {
    emit_ir_instr(ctx, IR_OP_LOAD_INT, .res = result, .int_lit = literal_int_value(literal_expr));
  }

  return result;
}

// A register variable is its register; a scalar in memory is loaded; an aggregate is the address of its slot.
static IrReg emit_expr_identifier(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_identifier: expr is NULL");

  Symbol *sym = expr->expr_identifier.symbol;
  IrReg reg = get_symbol_reg(ctx, sym);

  return sym->local.in_memory ? emit_load(ctx, reg, sym->type) : reg;
}

// Builds `[a, b, ...]` in a new stack slot, storing each element at its offset, and yields the slot's address.
static IrReg emit_expr_array_literal(IrGenContext *ctx, AstExpr *expr) {
  AstExprArrayLiteral *array_literal_expr = &expr->expr_array_literal;

  Type *array_type = expr_type(ctx, expr);
  uint32_t length = array_type->array.length;

  Type *elem_type = array_type->array.elem_type;
  uint32_t elem_size = elem_type->size;

  IrReg array_addr = queue_entry_alloc(ctx, array_type);

  if (array_literal_expr->is_repeat) {

    IrReg value = emit_expr(ctx, array_literal_expr->repeat.value);
    emit_fill(ctx, array_addr, value, elem_type, length);

    return array_addr;
  }

  uint32_t element_count = array_literal_expr->list.element_count;

  if (element_count < array_type->array.length) {
    emit_zero(ctx, array_addr, array_type);
  }

  for (uint32_t i = 0; i < element_count; i++) {
    AstArrayElement *element = &array_literal_expr->list.elements[i];
    IrReg value = emit_expr(ctx, element->value);

    int64_t byte_offset = (int64_t)element->index * elem_size;
    IrReg elem_addr = emit_addr_offset(ctx, array_addr, byte_offset);

    emit_store(ctx, value, elem_addr, elem_type);
  }

  return array_addr;
}

// The address of `target[index]`.
static IrReg emit_array_access(IrGenContext *ctx, AstExpr *target_expr, AstExpr *index_expr) {
  IrReg target = emit_expr(ctx, target_expr);
  IrReg index = emit_expr(ctx, index_expr);

  Type *target_type = expr_type(ctx, target_expr);

  if (type_is_slice(target_type)) {
    target = emit_field_load(ctx, target, SLICE_PTR_OFFSET, type_void_ptr);
  }

  return emit_elem_addr(ctx, target, index, type_elem(target_type)->size);
}

// The address of the storage an lvalue denotes: the slot of a variable in memory, the pointer of `p.*`, the element
// of `xs[i]` or the field of `s.f`.
static IrReg emit_lvalue_addr(IrGenContext *ctx, AstExpr *expr) {
  switch (expr->kind) {
  case AST_EXPR_IDENTIFIER: {
    Symbol *sym = expr->expr_identifier.symbol;
    assert((sym->local.in_memory || type_is_aggregate(sym->type)) && "a variable in a register has no address");

    return get_symbol_reg(ctx, sym);
  }

  case AST_EXPR_DEREF:
    return emit_expr(ctx, expr->expr_deref.operand);

  case AST_EXPR_SUBSCRIPT:
    return emit_array_access(ctx, expr->expr_subscript.target, expr->expr_subscript.index);

  case AST_EXPR_MEMBER: {
    IrReg object = emit_expr(ctx, expr->expr_member.object);

    return emit_addr_offset(ctx, object, expr->expr_member.offset);
  }

  default:
    UNREACHABLE("emit_lvalue_addr: sema only accepts an lvalue here");
  }
}

// `&x` is the address of the lvalue `x`; sema puts every variable whose address is taken in memory.
static IrReg emit_expr_addr_of(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_addr_of: expr is NULL");

  return retype_reg(ctx, emit_lvalue_addr(ctx, expr->expr_addr_of.operand), IR_PTR);
}

// Loads the value `p.*` points to; a value that is an aggregate is yielded as its address.
static IrReg emit_expr_deref(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_deref: expr is NULL");

  IrReg ptr = emit_expr(ctx, expr->expr_deref.operand);

  return emit_load(ctx, ptr, expr_type(ctx, expr));
}

// Loads `xs[i]`; an element that is itself an aggregate is yielded as its address.
static IrReg emit_expr_subscript(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_subscript: expr is NULL");

  AstExprSubscript *subscript_expr = &expr->expr_subscript;

  IrReg elem_addr = emit_array_access(ctx, subscript_expr->target, subscript_expr->index);

  return emit_load(ctx, elem_addr, expr_type(ctx, expr));
}

// Emits `xs[start:end]` for an array or a slice; a missing start is 0 and a missing end is the length of `xs`.
static IrReg emit_expr_slice(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_slice: expr is NULL");

  AstExprSlice *slice_expr = &expr->expr_slice;

  Type *slice_type = expr_type(ctx, expr);
  Type *target_type = expr_type(ctx, slice_expr->target);
  assert(type_is_array_like(target_type) && "sema allows only arrays and slices to be sliced");

  bool is_array = type_is_array(target_type);

  IrReg target = emit_expr(ctx, slice_expr->target);
  IrReg data = is_array ? target : emit_field_load(ctx, target, SLICE_PTR_OFFSET, type_void_ptr);

  IrReg start = slice_expr->start ? emit_expr(ctx, slice_expr->start) : emit_int_const(ctx, 0, IR_I64);

  IrReg end;
  if (slice_expr->end) {
    end = emit_expr(ctx, slice_expr->end);
  } else if (is_array) {
    end = emit_int_const(ctx, target_type->array.length, IR_I64);
  } else {
    end = emit_field_load(ctx, target, SLICE_LEN_OFFSET, type_i64);
  }

  IrReg base = emit_elem_addr(ctx, data, start, type_elem(slice_type)->size);

  IrReg len = new_reg(ctx, IR_I64);
  emit_ir_instr(ctx, IR_OP_SUB, .res = len, .arg1 = end, .arg2 = start);

  return emit_slice_value(ctx, slice_type, base, len);
}

// Emits `object.member` by loading the field that sema found; the length of an array is folded into a literal by sema.
static IrReg emit_expr_member(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_member: expr is NULL");

  AstExprMember *member_expr = &expr->expr_member;
  assert(!type_is_array(expr_type(ctx, member_expr->object)) && "sema folds the members of an array");

  IrReg object = emit_expr(ctx, member_expr->object);

  return emit_field_load(ctx, object, member_expr->offset, expr_type(ctx, expr));
}

// Emits a call with its argument registers; the result register has the callee's return type.
static IrReg emit_expr_call(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_call: expr is NULL");

  AstExprCall *call_expr = &expr->expr_call;

  IrReg *args = NULL;
  uint32_t arg_count = call_expr->arg_count;

  AstExpr *callee_expr = call_expr->callee;
  assert(callee_expr->expr_identifier.symbol && "emit_expr_call: sema did not resolve the callee");

  const TypeFunction *func_type = &callee_expr->expr_identifier.symbol->type->function;

  if (arg_count > 0) {
    args = arena_alloc(&ctx->comp_unit->arena, sizeof(IrReg) * arg_count);

    for (uint32_t i = 0; i < arg_count; i++) {
      AstExpr *arg_expr = call_expr->args[i];

      // The ABI type of an argument comes from its register, so an aggregate address has to be typed as the aggregate
      IrReg arg = emit_expr(ctx, arg_expr);
      args[i] = retype_reg(ctx, arg, get_ir_type(ctx, expr_type(ctx, arg_expr)));
    }
  }

  IrReg result = new_reg_for(ctx, expr_type(ctx, expr));

  emit_ir_instr(ctx,
                IR_OP_CALL,
                .res = result,
                .call = {
                  .callee = callee_expr->expr_identifier.name,
                  .args = args,
                  .arg_count = arg_count,
                  .is_variadic = func_type->is_variadic,
                  .fixed_count = func_type->param_count,
                });

  return result;
}

static IrReg emit_expr_unary(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_unary: expr is NULL");

  AstExprUnary *unary_expr = &expr->expr_unary;

  IrReg operand = emit_expr(ctx, unary_expr->operand);
  IrReg result = new_reg_for(ctx, expr_type(ctx, expr));

  emit_ir_instr(ctx, get_unary_ir_op(unary_expr->op), .res = result, .arg1 = operand);

  return result;
}

// `ptr +- int` moves by whole elements and `ptr - ptr` counts them, so offsets are scaled by the pointee size.
static IrReg emit_pointer_arithmetic(IrGenContext *ctx, AstExpr *expr) {
  AstExprBinary *binary_expr = &expr->expr_binary;

  AstExpr *left_expr = binary_expr->left;
  AstExpr *right_expr = binary_expr->right;
  Type *left_type = expr_type(ctx, left_expr);
  Type *right_type = expr_type(ctx, right_expr);

  IrReg left = emit_expr(ctx, left_expr);
  IrReg right = emit_expr(ctx, right_expr);

  bool left_is_ptr = type_is_pointer(left_type);
  bool right_is_ptr = type_is_pointer(right_type);

  Type *ptr_type = left_is_ptr ? left_type : right_type;
  int64_t elem_size = ptr_type->pointer.base_type->size;

  if (left_is_ptr && right_is_ptr) {
    IrReg bytes = new_reg(ctx, IR_I64);

    emit_ir_instr(ctx, IR_OP_SUB, .res = bytes, .arg1 = left, .arg2 = right);

    if (elem_size == 1) {
      return bytes;
    }

    IrReg size = emit_int_const(ctx, elem_size, IR_I64);
    IrReg count = new_reg(ctx, IR_I64);

    emit_ir_instr(ctx, IR_OP_DIV, .res = count, .arg1 = bytes, .arg2 = size);

    return count;
  }

  IrReg ptr = left_is_ptr ? left : right;
  IrReg offset = left_is_ptr ? right : left;

  offset = emit_scaled_offset(ctx, offset, elem_size);

  IrReg result = new_reg(ctx, IR_PTR);

  emit_ir_instr(ctx, get_binary_ir_op(binary_expr->op), .res = result, .arg1 = ptr, .arg2 = offset);

  return result;
}

static IrReg emit_expr_binary(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_binary: expr is NULL");

  AstExprBinary *binary_expr = &expr->expr_binary;

  BinaryOp op = binary_expr->op;
  bool is_arithmetic = op == BINOP_ADD || op == BINOP_SUB;
  if (is_arithmetic &&
      (type_is_pointer(expr_type(ctx, binary_expr->left)) || type_is_pointer(expr_type(ctx, binary_expr->right)))) {
    return emit_pointer_arithmetic(ctx, expr);
  }

  IrReg left = emit_expr(ctx, binary_expr->left);
  IrReg right = emit_expr(ctx, binary_expr->right);
  IrReg result = new_reg_for(ctx, expr_type(ctx, expr));

  emit_ir_instr(ctx, get_binary_ir_op(binary_expr->op), .res = result, .arg1 = left, .arg2 = right);

  return result;
}

// `&&` and `||` evaluate the right operand only when the left one does not decide the result.
static IrReg emit_expr_logical(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_logical: expr is NULL");

  AstExprLogical *logical_expr = &expr->expr_logical;

  LogicalOp op = logical_expr->op;

  IrLabel right_label = new_label(ctx);
  IrLabel end_label = new_label(ctx);
  IrReg result = new_reg_for(ctx, expr_type(ctx, expr));

  IrReg left = emit_expr(ctx, logical_expr->left);

  emit_ir_instr(ctx, IR_OP_COPY, .res = result, .arg1 = left);

  switch (op) {
  case LOGIC_OR: {
    emit_ir_instr(ctx, IR_OP_JZ, .arg1 = result, .target_true = right_label, .target_false = end_label);
    break;
  }
  case LOGIC_AND: {
    emit_ir_instr(ctx, IR_OP_JNZ, .arg1 = result, .target_true = right_label, .target_false = end_label);
    break;
  }

  default:
    UNREACHABLE("emit_expr_logical: unhandled logical operator");
  }

  emit_ir_instr(ctx, IR_OP_LABEL, .target = right_label);

  IrReg right = emit_expr(ctx, logical_expr->right);

  emit_ir_instr(ctx, IR_OP_COPY, .res = result, .arg1 = right);

  emit_ir_instr(ctx, IR_OP_LABEL, .target = end_label);

  return result;
}

static IrReg emit_expr_cast(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_cast: expr is NULL");

  AstExpr *operand_expr = expr->expr_cast.operand;
  IrReg operand = emit_expr(ctx, operand_expr);

  return emit_cast_if_needed(ctx, operand, expr_type(ctx, operand_expr), expr_type(ctx, expr));
}

// Copies the value into a variable that lives in a register, or stores it through the address of any other target;
// yields the value.
static IrReg emit_expr_assign(IrGenContext *ctx, AstExpr *expr) {
  assert(expr && "emit_expr_assign: expr is NULL");

  AstExprAssign *assign_expr = &expr->expr_assign;

  AstExpr *target_expr = assign_expr->target;
  AstExpr *value_expr = assign_expr->value;

  if (target_expr->kind == AST_EXPR_IDENTIFIER) {
    Symbol *sym = target_expr->expr_identifier.symbol;

    if (!sym->local.in_memory && !type_is_aggregate(sym->type)) {
      IrReg value = emit_expr(ctx, value_expr);

      emit_ir_instr(ctx, IR_OP_COPY, .res = get_symbol_reg(ctx, sym), .arg1 = value);

      return value;
    }
  }

  IrReg target_addr = emit_lvalue_addr(ctx, target_expr);
  IrReg value = emit_expr(ctx, value_expr);

  emit_store(ctx, value, target_addr, expr_type(ctx, target_expr));

  return value;
}

static IrReg emit_expr(IrGenContext *ctx, AstExpr *expr) {
  if (!expr) {
    return IR_NULL_REG;
  }

  switch (expr->kind) {
  case AST_EXPR_LITERAL:
    return emit_expr_literal(ctx, expr);

  case AST_EXPR_IDENTIFIER:
    return emit_expr_identifier(ctx, expr);

  case AST_EXPR_ARRAY_LITERAL:
    return emit_expr_array_literal(ctx, expr);

  case AST_EXPR_ADDR_OF:
    return emit_expr_addr_of(ctx, expr);

  case AST_EXPR_DEREF:
    return emit_expr_deref(ctx, expr);

  case AST_EXPR_SUBSCRIPT:
    return emit_expr_subscript(ctx, expr);

  case AST_EXPR_SLICE:
    return emit_expr_slice(ctx, expr);

  case AST_EXPR_MEMBER:
    return emit_expr_member(ctx, expr);

  case AST_EXPR_CALL:
    return emit_expr_call(ctx, expr);

  case AST_EXPR_UNARY:
    return emit_expr_unary(ctx, expr);

  case AST_EXPR_BINARY:
    return emit_expr_binary(ctx, expr);

  case AST_EXPR_LOGICAL:
    return emit_expr_logical(ctx, expr);

  case AST_EXPR_CAST:
    return emit_expr_cast(ctx, expr);

  case AST_EXPR_ASSIGN:
    return emit_expr_assign(ctx, expr);

  case AST_EXPR_INVALID:
    UNREACHABLE("emit_expr: AST_EXPR_INVALID reached IR generation");
  }

  UNREACHABLE("emit_expr: unhandled expression kind");
}

// Statement handling

static void emit_stmt(IrGenContext *ctx, AstStmt *stmt);

static void emit_stmt_block(IrGenContext *ctx, AstStmt *stmt) {
  assert(stmt && "emit_stmt_block: stmt is NULL");

  AstStmtBlock *block_stmt = &stmt->stmt_block;

  for (uint32_t i = 0; i < block_stmt->stmt_count; i++) {
    AstStmt *inner_stmt = block_stmt->stmts[i];
    emit_stmt(ctx, inner_stmt);
  }
}

static void emit_stmt_expression(IrGenContext *ctx, AstStmt *stmt) {
  assert(stmt && "emit_stmt_expression: stmt is NULL");

  emit_expr(ctx, stmt->stmt_expression.expression);
}

// Declares a variable in a register or a memory slot; it is zeroed unless the initializer is `undef`.
static void emit_stmt_local_var(IrGenContext *ctx, AstStmt *stmt) {
  assert(stmt && "emit_stmt_local_var: stmt is NULL");

  AstStmtLocalVar *local_var_stmt = &stmt->stmt_local_var;

  Symbol *sym = local_var_stmt->symbol;
  IrReg reg = sym->local.in_memory ? queue_entry_alloc(ctx, sym->type) : new_reg_for(ctx, sym->type);

  bind_symbol_reg(ctx, sym, reg);

  if (local_var_stmt->is_undef) {
    return;
  }

  IrReg init = emit_expr(ctx, local_var_stmt->init);

  if (init.id == IR_NULL_REG.id) {
    if (type_is_aggregate(sym->type)) {
      emit_zero(ctx, reg, sym->type);
      return;
    }

    init = new_reg_for(ctx, sym->type);

    if (ir_type_is_float(get_ir_type(ctx, sym->type))) {
      emit_ir_instr(ctx, IR_OP_LOAD_FLOAT, .res = init, .float_lit = 0.0);
    } else {
      emit_ir_instr(ctx, IR_OP_LOAD_INT, .res = init, .int_lit = 0);
    }
  }

  if (sym->local.in_memory) {
    emit_store(ctx, init, reg, sym->type);

    return;
  }

  emit_ir_instr(ctx, IR_OP_COPY, .res = reg, .arg1 = init);
}

static void emit_stmt_return(IrGenContext *ctx, AstStmt *stmt) {
  assert(stmt && "emit_stmt_return: stmt is NULL");

  IrReg value = emit_expr(ctx, stmt->stmt_return.value);

  emit_ir_instr(ctx, IR_OP_RETURN, .arg1 = value);
}

static void emit_stmt_break(IrGenContext *ctx, AstStmt *stmt) {
  UNUSED(stmt);
  assert(stmt && "emit_stmt_break: stmt is NULL");
  assert(ctx->current_loop && "emit_stmt_break: break statement not within a loop");

  emit_ir_instr(ctx, IR_OP_JUMP, .target = ctx->current_loop->break_label);
}

static void emit_stmt_continue(IrGenContext *ctx, AstStmt *stmt) {
  UNUSED(stmt);
  assert(stmt && "emit_stmt_continue: stmt is NULL");
  assert(ctx->current_loop && "emit_stmt_continue: continue statement not within a loop");

  emit_ir_instr(ctx, IR_OP_JUMP, .target = ctx->current_loop->continue_label);
}

static void emit_stmt_if(IrGenContext *ctx, AstStmt *stmt) {
  assert(stmt && "emit_stmt_if: stmt is NULL");

  AstStmtIf *if_stmt = &stmt->stmt_if;

  IrLabel then_label = new_label(ctx);
  IrLabel end_label = new_label(ctx);
  IrLabel else_label = if_stmt->else_branch ? new_label(ctx) : end_label;

  // Conditional jump
  IrReg condition = emit_expr(ctx, if_stmt->condition);

  emit_ir_instr(ctx, IR_OP_JNZ, .arg1 = condition, .target_true = then_label, .target_false = else_label);

  // Then branch
  emit_ir_instr(ctx, IR_OP_LABEL, .target = then_label);

  emit_stmt(ctx, if_stmt->then_branch);

  // Jump to end if the then branch is not terminated
  if (!ctx->block_terminated) {
    emit_ir_instr(ctx, IR_OP_JUMP, .target = end_label);
  }

  // Else branch
  if (if_stmt->else_branch) {
    emit_ir_instr(ctx, IR_OP_LABEL, .target = else_label);

    emit_stmt(ctx, if_stmt->else_branch);
  }

  emit_ir_instr(ctx, IR_OP_LABEL, .target = end_label);
}

static void emit_stmt_while(IrGenContext *ctx, AstStmt *stmt) {
  assert(stmt && "emit_stmt_while: stmt is NULL");

  AstStmtWhile *while_stmt = &stmt->stmt_while;

  IrLabel start_label = new_label(ctx);
  IrLabel fallthrough_label = new_label(ctx);
  IrLabel end_label = new_label(ctx);

  LoopLabels loop_labels = {
    .continue_label = start_label,
    .break_label = end_label,
    .parent = ctx->current_loop,
  };
  ctx->current_loop = &loop_labels;

  emit_ir_instr(ctx, IR_OP_LABEL, .target = start_label);

  IrReg condition = emit_expr(ctx, while_stmt->condition);

  emit_ir_instr(ctx, IR_OP_JNZ, .arg1 = condition, .target_true = fallthrough_label, .target_false = end_label);

  emit_ir_instr(ctx, IR_OP_LABEL, .target = fallthrough_label);

  emit_stmt(ctx, while_stmt->body);

  if (!ctx->block_terminated) {
    emit_ir_instr(ctx, IR_OP_JUMP, .target = start_label);
  }

  emit_ir_instr(ctx, IR_OP_LABEL, .target = end_label);

  ctx->current_loop = loop_labels.parent;
}

static void emit_stmt(IrGenContext *ctx, AstStmt *stmt) {
  assert(stmt && "emit_stmt: stmt is NULL");

  switch (stmt->kind) {
  case AST_STMT_BLOCK:
    return emit_stmt_block(ctx, stmt);
  case AST_STMT_EXPRESSION:
    return emit_stmt_expression(ctx, stmt);
  case AST_STMT_LOCAL_VAR:
    return emit_stmt_local_var(ctx, stmt);

  case AST_STMT_RETURN:
    return emit_stmt_return(ctx, stmt);
  case AST_STMT_BREAK:
    return emit_stmt_break(ctx, stmt);
  case AST_STMT_CONTINUE:
    return emit_stmt_continue(ctx, stmt);

  case AST_STMT_IF:
    return emit_stmt_if(ctx, stmt);
  case AST_STMT_WHILE:
    return emit_stmt_while(ctx, stmt);

  case AST_STMT_INVALID:
    UNREACHABLE("emit_stmt: AST_STMT_INVALID reached IR generation");
  }

  UNREACHABLE("emit_stmt: unhandled statement kind");
}

// Declaration handling
static void emit_decl(IrGenContext *ctx, AstDecl *decl);

// Emits a function: parameters become registers (or slots), then the body, then the entry-block allocations.
static void emit_decl_function(IrGenContext *ctx, AstDecl *decl) {
  assert(decl && "emit_decl_function: decl is NULL");

  AstDeclFunction *func_decl = &decl->decl_function;

  if (func_decl->is_extern) {
    return;
  }

  ctx->next_label = 1;
  ctx->current_loop = NULL;
  ctx->block_terminated = false;

  Type *return_type = func_decl->symbol->type->function.return_type;

  IrFunction new_func = {
    .name = func_decl->name,
    .return_type = get_ir_type(ctx, return_type),
    .params = NULL,
    .param_count = func_decl->param_count,
    .instrs = NULL,
    .reg_types = NULL,
  };

  da_append(new_func.reg_types, IR_VOID);
  da_append(ctx->module->functions, new_func);

  ctx->current_function_index = da_len(ctx->module->functions) - 1;

  uint32_t param_count = func_decl->param_count;

  if (param_count > 0) {
    IrFunction *func = get_current_function(ctx);
    func->params = arena_alloc(&ctx->comp_unit->arena, sizeof(IrReg) * param_count);

    for (uint32_t i = 0; i < param_count; i++) {
      Symbol *sym = func_decl->params[i].symbol;
      IrReg param = new_reg_for(ctx, sym->type);
      IrReg slot = param;

      if (sym->local.in_memory) {
        slot = queue_entry_alloc(ctx, sym->type);
        emit_store(ctx, param, slot, sym->type);
      }

      func->params[i] = param;
      bind_symbol_reg(ctx, sym, slot);
    }
  }

  emit_stmt(ctx, func_decl->body);

  if (!ctx->block_terminated) {
    emit_ir_instr(ctx, IR_OP_RETURN, .arg1 = IR_NULL_REG);
  }

  IrFunction *func = get_current_function(ctx);
  for (size_t i = da_len(ctx->entry_allocs); i > 0; i--) {
    da_insert(func->instrs, 0, ctx->entry_allocs[i - 1]);
  }
  da_set_len(ctx->entry_allocs, 0);
}

static void emit_decl(IrGenContext *ctx, AstDecl *decl) {
  assert(decl && "emit_decl: decl is NULL");

  switch (decl->kind) {
  case AST_DECL_FUNCTION:
    return emit_decl_function(ctx, decl);

  case AST_DECL_STRUCT:
    return;

  case AST_DECL_INVALID:
    UNREACHABLE("emit_decl: AST_DECL_INVALID reached IR generation");
  }

  UNREACHABLE("emit_decl: unhandled declaration kind");
}

// IR generation public functions

void gen_ir_init(IrGenContext *ctx, CompilationUnit *comp_unit, SemaContext *sema_ctx) {
  ctx->comp_unit = comp_unit;
  ctx->sema_ctx = sema_ctx;

  ctx->module = NULL;
  ctx->current_function_index = 0;

  ctx->next_label = 1;

  ctx->current_loop = NULL;
  ctx->block_terminated = false;

  ctx->entry_allocs = NULL;
  ctx->symbol_to_reg = NULL;
  da_set_len(ctx->symbol_to_reg, ctx->sema_ctx->next_symbol_id);
  for (size_t i = 0; i < da_len(ctx->symbol_to_reg); i++) {
    ctx->symbol_to_reg[i] = IR_NULL_REG;
  }
}

void gen_ir_free(IrGenContext *ctx) {
  for (size_t i = 0; i < da_len(ctx->module->functions); i++) {
    IrFunction *func = &ctx->module->functions[i];
    da_free(func->instrs);
    da_free(func->reg_types);
  }

  for (size_t i = 0; i < da_len(ctx->module->aggregates); i++) {
    da_free(ctx->module->aggregates[i].fields);
  }

  da_free(ctx->module->data);
  da_free(ctx->module->aggregates);
  da_free(ctx->module->functions);
  da_free(ctx->symbol_to_reg);
  da_free(ctx->entry_allocs);
}

void gen_ir(IrGenContext *ctx, AstProgram *program) {
  if (!program) {
    return;
  }

  ctx->module = arena_calloc(&ctx->comp_unit->arena, sizeof(IrModule));

  for (uint32_t i = 0; i < program->decl_count; i++) {
    emit_decl(ctx, program->decls[i]);
  }
}
