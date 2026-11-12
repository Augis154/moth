#ifndef SEMA_H
#define SEMA_H

#include "ast.h"
#include "common.h"
#include "compiler.h"
#include "lib/arena.h"

#include <stdint.h>

typedef enum {
  SYMBOL_LOCAL_VAR,
  SYMBOL_GLOBAL_VAR,
  SYMBOL_FUNCTION,
  SYMBOL_TYPE,
} SymbolKind;

typedef enum {
  SYMBOL_STATE_UNRESOLVED,
  SYMBOL_STATE_RESOLVING,
  SYMBOL_STATE_RESOLVED,
} SymbolState;

typedef struct {
  bool is_param;
  bool in_memory;
  bool is_placeholder;
} SymbolLocal;

// A named entity, and the source of truth for what a name means. The AST points at its symbol and the symbol at its
// type; a type never points back.
struct Symbol_ {
  SymbolKind kind;
  uint32_t id;

  const char *name;
  Type *type;

  SourceLoc loc;

  SymbolState resolve_state;

  union {
    SymbolLocal local; // SYMBOL_LOCAL_VAR
    AstDecl *decl;     // SYMBOL_FUNCTION and SYMBOL_TYPE: the declaration, NULL for a builtin type
  };
};

typedef struct {
  CompilationUnit *comp_unit;

  Symbol **locals;      // Every local that is visible now, innermost last; globals are in the symbol table
  uint32_t scope_start; // Index in `locals` where the current scope begins
  uint32_t scope_depth; // 0 is the global scope

  AstDeclFunction *current_function;

  uint32_t next_symbol_id;
  uint32_t loop_depth;

  Type **expr_types;
} SemaContext;

void sema_init(SemaContext *ctx, CompilationUnit *comp_unit);
void sema_free(SemaContext *ctx);

Type *sema_expr_type(const SemaContext *ctx, const AstExpr *expr);

Type *sema_expr(SemaContext *ctx, AstExpr *expr);
Type *sema_expr_hint(SemaContext *ctx, AstExpr *expr, Type *hint);
void sema_stmt(SemaContext *ctx, AstStmt *stmt);
Type *sema_type(SemaContext *ctx, AstType *type);

void sema_program(SemaContext *ctx, AstProgram *program);

#endif // SEMA_H