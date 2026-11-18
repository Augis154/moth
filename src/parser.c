#include "parser.h"

#include "ast.h"
#include "common.h"
#include "lib/arena.h"
#include "lib/array.h"
#include "token.h"

#include <assert.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum {
  PREC_NONE = 0,
  PREC_ASSIGNMENT, // =
  PREC_LOGIC_OR,   // ||
  PREC_LOGIC_AND,  // &&
  PREC_EQUALITY,   // == !=
  PREC_COMPARISON, // < > <= >=
  PREC_BIT_OR,     // |
  PREC_BIT_XOR,    // ^
  PREC_BIT_AND,    // &
  PREC_SHIFT,      // << >>
  PREC_TERM,       // + -
  PREC_FACTOR,     // * /
  PREC_CAST,       // as
  PREC_PREFIX,     // ! ~ - &
  PREC_POSTFIX,    // . .* .{ () []
} Precedence;

typedef AstExpr *(*ParsePrefixFn)(Parser *parser);
typedef AstExpr *(*ParseInfixFn)(Parser *parser, AstExpr *left);

typedef struct {
  Precedence precedence;
  ParsePrefixFn prefix;
  ParseInfixFn infix;
} ParseRule;

static const ParseRule rules[TOKEN_COUNT];

static const ParseRule *get_rule(TokenKind kind) {
  assert(kind < TOKEN_COUNT && "get_rule: not a token kind");
  return &rules[kind];
}

// Reports a parse error at `token` and enters panic mode; further errors are suppressed until synchronize. `format`
// and the arguments after it work like printf.
__attribute__((format(printf, 3, 4))) static void error_at(Parser *parser, Token token, const char *format, ...) {
  if (parser->panic_mode) return;

  parser->panic_mode = true;
  parser->comp_unit->had_error = true;

  fprintf(stderr, "[line %u] Error", token.loc.line);

  if (token.kind == TOKEN_EOF) {
    fprintf(stderr, " at end");
  } else if (token.kind == TOKEN_ERROR) {
    // Nothing to print
  } else {
    fprintf(stderr, " at '%.*s'", (int)token.lexeme_len, token.lexeme);
  }

  fprintf(stderr, ": ");

  va_list args;
  va_start(args, format);
  vfprintf(stderr, format, args);
  va_end(args);

  fprintf(stderr, "\n");
}

// Moves to the next token, reporting and skipping lexer error tokens.
static void advance(Parser *parser) {
  parser->previous = parser->current;

  for (;;) {
    parser->current = lexer_get_token(&parser->lexer);

    if (parser->current.kind != TOKEN_ERROR) {
      break;
    }

    error_at(parser, parser->current, "%s", parser->current.lexeme);
    free((void *)parser->current.lexeme);
  }
}

static inline bool check(Parser *parser, TokenKind kind) {
  return parser->current.kind == kind;
}

static bool match(Parser *parser, TokenKind kind) {
  if (!check(parser, kind)) return false;
  advance(parser);
  return true;
}

static bool consume(Parser *parser, TokenKind kind, const char *message) {
  if (match(parser, kind)) return true;
  error_at(parser, parser->previous, "%s", message);
  return false;
}

// Consumes the token of `kind` that the caller's dispatcher has already seen.
static void expect(Parser *parser, TokenKind kind) {
  assert(check(parser, kind) && "expect: the dispatcher did not check the token");
  advance(parser);
}

static const char *parse_identifier_name(Parser *parser, Token token) {
  if (token.kind != TOKEN_IDENT) {
    error_at(parser, token, "Expected identifier.");
    return NULL;
  }

  return st_intern_len(&parser->comp_unit->intern_table, token.lexeme, token.lexeme_len);
}

// Error recovery

// Whether `kind` starts a statement or a declaration; such a token never occurs inside an expression or a type.
static bool starts_statement(TokenKind kind) {
  switch (kind) {
  case TOKEN_LBRACE:
  case TOKEN_VAR:
  case TOKEN_FN:
  case TOKEN_STRUCT:
  case TOKEN_EXTERN:
  case TOKEN_IF:
  case TOKEN_WHILE:
  case TOKEN_RETURN:
  case TOKEN_BREAK:
  case TOKEN_CONTINUE:
    return true;

  default:
    return false;
  }
}

// Skips to a likely statement boundary (after ';', or before '}' or the start of a statement) and leaves panic mode.
static void synchronize(Parser *parser) {
  parser->panic_mode = false;

  while (!check(parser, TOKEN_EOF)) {
    if (parser->previous.kind == TOKEN_SEMICOLON) return;
    if (check(parser, TOKEN_RBRACE) || starts_statement(parser->current.kind)) return;

    advance(parser);
  }
}

// Skips to the next top-level declaration ('fn', 'struct' or 'extern') and leaves panic mode.
static void synchronize_top_level(Parser *parser) {
  parser->panic_mode = false;

  while (true) {
    switch (parser->current.kind) {
    case TOKEN_EOF:
    case TOKEN_FN:
    case TOKEN_STRUCT:
    case TOKEN_EXTERN:
      return;

    default:
      break;
    }

    advance(parser);
  }
}

// Skips to the end of the current list element: the `,` after it, or the token that closes the list. Nested brackets
// are skipped, and a `;` or the start of a statement ends the search, since the list is not closed then.
static void skip_to_element_end(Parser *parser) {
  uint32_t depth = 0;

  while (!check(parser, TOKEN_EOF)) {
    TokenKind kind = parser->current.kind;

    if (starts_statement(kind)) return;

    bool closes = kind == TOKEN_RPAREN || kind == TOKEN_RBRACKET || kind == TOKEN_RBRACE;
    if (depth == 0 && (closes || kind == TOKEN_COMMA || kind == TOKEN_SEMICOLON)) return;

    if (kind == TOKEN_LPAREN || kind == TOKEN_LBRACKET || kind == TOKEN_DOT_LBRACE) depth++;
    if (closes) depth--;

    advance(parser);
  }
}

// Skips the rest of a list up to and including `close`; it stops early where `skip_to_element_end` does.
static void skip_list_rest(Parser *parser, TokenKind close) {
  do {
    skip_to_element_end(parser);
  } while (match(parser, TOKEN_COMMA));

  match(parser, close);
}

// Whether a list element `parsed` without an error. A bad element is skipped and panic mode left, so that the next
// element reports its own errors.
static bool list_element_ok(Parser *parser, bool parsed) {
  if (parsed && !parser->panic_mode) return true;

  skip_to_element_end(parser);
  parser->panic_mode = false;

  return false;
}

// Consumes the `close` of a list whose elements were `elements_ok`. A list with an error is skipped to its end and
// leaves panic mode set, so that the statement around it is resynchronized.
static bool list_close(Parser *parser, TokenKind close, bool elements_ok, const char *message) {
  if (elements_ok && match(parser, close)) return true;

  if (elements_ok) error_at(parser, parser->previous, "%s", message);

  skip_list_rest(parser, close);
  parser->panic_mode = true;

  return false;
}

// Literal decoding functions

// The value of the hexadecimal digit `c`, or -1 when it is not one.
static int8_t hex_value(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

// Decodes the UTF-8 character at *cursor into a code point and advances past it. Returns false for a truncated
// sequence, a stray continuation byte, an overlong form, a surrogate or a value above U+10FFFF.
static bool decode_utf8_char(const char **cursor, const char *end, uint32_t *code_point) {
  const uint8_t *bytes = (const uint8_t *)*cursor;

  size_t length;
  uint32_t min_value;

  if (bytes[0] < 0x80) {
    length = 1;
    min_value = 0;
    *code_point = bytes[0];
  } else if ((bytes[0] & 0xE0) == 0xC0) {
    length = 2;
    min_value = 0x80;
    *code_point = bytes[0] & 0x1F;
  } else if ((bytes[0] & 0xF0) == 0xE0) {
    length = 3;
    min_value = 0x800;
    *code_point = bytes[0] & 0x0F;
  } else if ((bytes[0] & 0xF8) == 0xF0) {
    length = 4;
    min_value = 0x10000;
    *code_point = bytes[0] & 0x07;
  } else {
    return false;
  }

  if ((size_t)(end - *cursor) < length) return false;

  for (size_t i = 1; i < length; i++) {
    if ((bytes[i] & 0xC0) != 0x80) return false;
    *code_point = (*code_point << 6) | (bytes[i] & 0x3F);
  }

  if (*code_point < min_value || *code_point > 0x10FFFF) return false;
  if (*code_point >= 0xD800 && *code_point <= 0xDFFF) return false;

  *cursor += length;
  return true;
}

// Writes the UTF-8 encoding of `code_point` to `out`, which has room for 4 bytes, and returns its length.
static size_t encode_utf8_char(uint32_t code_point, char *out) {
  if (code_point < 0x80) {
    out[0] = (char)code_point;
    return 1;
  }

  if (code_point < 0x800) {
    out[0] = (char)(0xC0 | (code_point >> 6));
    out[1] = (char)(0x80 | (code_point & 0x3F));
    return 2;
  }

  if (code_point < 0x10000) {
    out[0] = (char)(0xE0 | (code_point >> 12));
    out[1] = (char)(0x80 | ((code_point >> 6) & 0x3F));
    out[2] = (char)(0x80 | (code_point & 0x3F));
    return 3;
  }

  out[0] = (char)(0xF0 | (code_point >> 18));
  out[1] = (char)(0x80 | ((code_point >> 12) & 0x3F));
  out[2] = (char)(0x80 | ((code_point >> 6) & 0x3F));
  out[3] = (char)(0x80 | (code_point & 0x3F));
  return 4;
}

// Decodes the `{XXXX}` of a `\u{XXXX}` escape (1 to 6 hex digits of a Unicode scalar value) at *cursor into
// `code_point` and advances past it. Returns false when it is malformed, a surrogate or above U+10FFFF.
static bool decode_unicode_escape(const char **cursor, const char *end, uint32_t *code_point) {
  const char *current = *cursor;

  if (current >= end || *current != '{') return false;
  current++;

  uint32_t value = 0;
  size_t digits = 0;

  while (current < end && *current != '}') {
    int8_t digit = hex_value(*current);
    if (digit < 0 || digits == 6) return false;

    value = (value << 4) | (uint32_t)digit;
    digits++;
    current++;
  }

  if (current >= end || digits == 0) return false;
  if (value > 0x10FFFF || (value >= 0xD800 && value <= 0xDFFF)) return false;

  *cursor = current + 1;
  *code_point = value;
  return true;
}

// Decodes the escape after a '\\' at *cursor into `value` and advances past it; false after an error. `is_unicode`
// (optional) tells whether `value` is a `\u{...}` code point rather than a byte.
static bool decode_escape(Parser *parser, const char **cursor, const char *end, uint32_t *value, bool *is_unicode) {
  if (is_unicode) *is_unicode = false;

  if (*cursor >= end) {
    error_at(parser, parser->previous, "Incomplete escape sequence at the end of the literal.");
    return false;
  }

  char c = *(*cursor)++;

  switch (c) {
  case 'n':
    *value = '\n';
    return true;
  case 'r':
    *value = '\r';
    return true;
  case 't':
    *value = '\t';
    return true;
  case '\\':
    *value = '\\';
    return true;
  case '\'':
    *value = '\'';
    return true;
  case '"':
    *value = '"';
    return true;
  case '0':
    *value = '\0';
    return true;

  case 'x': {
    if (end - *cursor < 2) break;

    int8_t high = hex_value((*cursor)[0]);
    int8_t low = hex_value((*cursor)[1]);
    if (high < 0 || low < 0) break;

    *cursor += 2;
    *value = (uint32_t)(high << 4 | low);
    return true;
  }

  case 'u':
    if (!decode_unicode_escape(cursor, end, value)) break;

    if (is_unicode) *is_unicode = true;
    return true;

  default:
    break;
  }

  if (c == 'x') {
    error_at(parser, parser->previous, "Invalid '\\x' escape; expected two hex digits.");
  } else if (c == 'u') {
    error_at(parser, parser->previous, "Invalid '\\u' escape; expected '\\u{...}' with a valid code point.");
  } else {
    error_at(parser, parser->previous, "Unknown escape sequence '\\%c'.", c);
  }

  return false;
}

// Decodes the escapes and validates the UTF-8 of a string's text into an arena buffer; NULL after an error.
static const char *escape_str(Parser *parser, const char *str, size_t str_len, size_t *escaped_len) {
  // No escape or character takes more bytes in the result than in the source, so str_len is enough
  char *esc_str = arena_alloc(&parser->comp_unit->arena, str_len);
  size_t esc_len = 0;

  const char *cursor = str;
  const char *end = str + str_len;

  while (cursor < end) {
    if (*cursor != '\\') {
      const char *start = cursor;
      uint32_t code_point;

      if (!decode_utf8_char(&cursor, end, &code_point)) {
        error_at(parser, parser->previous, "Invalid UTF-8 in string literal.");
        return NULL;
      }

      memcpy(esc_str + esc_len, start, (size_t)(cursor - start));
      esc_len += (size_t)(cursor - start);
      continue;
    }

    cursor++;

    uint32_t value;
    bool is_unicode;
    if (!decode_escape(parser, &cursor, end, &value, &is_unicode)) {
      return NULL;
    }

    if (is_unicode) {
      esc_len += encode_utf8_char(value, esc_str + esc_len);
    } else {
      esc_str[esc_len++] = (char)value;
    }
  }

  *escaped_len = esc_len;
  return esc_str;
}

// Expression parsing functions

// expression := prefix { infix expression }  -- keeps parsing infix operators of at least `precedence`.
static AstExpr *parse_precedence(Parser *parser, Precedence precedence) {
  ParsePrefixFn prefix_rule = get_rule(parser->current.kind)->prefix;

  if (!prefix_rule) {
    error_at(parser, parser->current, "Expected expression.");
    return NULL;
  }

  advance(parser);

  AstExpr *left = prefix_rule(parser);

  while (precedence <= get_rule(parser->current.kind)->precedence) {
    advance(parser);

    ParseInfixFn infix_rule = get_rule(parser->previous.kind)->infix;
    assert(infix_rule && "parse_precedence: a token with a precedence has no infix rule");

    left = infix_rule(parser, left);
  }

  return left;
}

static UnaryOp get_unary_op(TokenKind kind) {
  switch (kind) {
  case TOKEN_MINUS:
    return UNOP_NEGATE;
  case TOKEN_BANG:
    return UNOP_NOT;
  case TOKEN_TILDE:
    return UNOP_BIT_NOT;

  default:
    UNREACHABLE("get_unary_op: not a unary operator");
  }
}

static BinaryOp get_binary_op(TokenKind kind) {
  switch (kind) {
  case TOKEN_PLUS:
    return BINOP_ADD;
  case TOKEN_MINUS:
    return BINOP_SUB;
  case TOKEN_STAR:
    return BINOP_MUL;
  case TOKEN_SLASH:
    return BINOP_DIV;

  case TOKEN_EQ:
    return BINOP_EQ;
  case TOKEN_NOT_EQ:
    return BINOP_NOT_EQ;
  case TOKEN_LESS:
    return BINOP_LESS;
  case TOKEN_GREATER:
    return BINOP_GREATER;
  case TOKEN_LESS_EQ:
    return BINOP_LESS_EQ;
  case TOKEN_GREATER_EQ:
    return BINOP_GREATER_EQ;

  case TOKEN_PIPE:
    return BINOP_BIT_OR;
  case TOKEN_CARET:
    return BINOP_BIT_XOR;
  case TOKEN_AMP:
    return BINOP_BIT_AND;
  case TOKEN_SHL:
    return BINOP_SHL;
  case TOKEN_SHR:
    return BINOP_SHR;

  default:
    UNREACHABLE("get_binary_op: not a binary operator");
  }
}

static LogicalOp get_logical_op(TokenKind kind) {
  switch (kind) {
  case TOKEN_OR:
    return LOGIC_OR;
  case TOKEN_AND:
    return LOGIC_AND;

  default:
    UNREACHABLE("get_logical_op: not a logical operator");
  }
}

// INT  -- decimal, 0xHEX or 0bBINARY digits, with optional '_' separators.
static AstExpr *parse_expr_literal_int(Parser *parser) {
  uint8_t base = 10;

  Token token = parser->previous;
  const char *start = token.lexeme;
  const char *end = start + token.lexeme_len;

  if (token.lexeme_len >= 2 && start[0] == '0') {
    if (start[1] == 'x' || start[1] == 'X') {
      base = 16;
      start += 2;
    } else if (start[1] == 'b' || start[1] == 'B') {
      base = 2;
      start += 2;
    }
  }

  uint64_t value = 0;
  uint32_t digit_count = 0;

  for (const char *current = start; current < end; current++) {
    char c = *current;
    if (c == '_') {
      continue;
    }

    int8_t digit = hex_value(c);
    if (digit < 0 || digit >= base) {
      error_at(parser, token, "Invalid character in integer literal.");
      return NULL;
    }

    if (value > (UINT64_MAX - (uint64_t)digit) / base) {
      error_at(parser, token, "Integer literal is too large.");
      return NULL;
    }

    value = value * base + (uint64_t)digit;
    digit_count++;
  }

  if (digit_count == 0) {
    error_at(parser, token, "Integer literal has no digits.");
    return NULL;
  }

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_LITERAL, token.loc);
  expr->expr_literal.kind = AST_LITERAL_INT;
  expr->expr_literal.int_value.magnitude = value;

  return expr;
}

// FLOAT  -- digits '.' digits with optional '_' separators, or digits with an 'f' suffix.
static AstExpr *parse_expr_literal_float(Parser *parser) {
  Token token = parser->previous;

  ArenaMark mark = arena_mark(&parser->comp_unit->arena);
  char *digits = arena_alloc(&parser->comp_unit->arena, token.lexeme_len + 1);
  size_t digit_count = 0;

  for (size_t i = 0; i < token.lexeme_len; i++) {
    if (token.lexeme[i] != '_') digits[digit_count++] = token.lexeme[i];
  }
  digits[digit_count] = '\0';

  double value = strtod(digits, NULL);
  arena_rollback(&parser->comp_unit->arena, mark);

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_LITERAL, token.loc);
  expr->expr_literal.kind = AST_LITERAL_FLOAT;
  expr->expr_literal.float_value = value;

  return expr;
}

// CHAR  -- a single UTF-8 character or escape sequence between single quotes; the value is its code point.
static AstExpr *parse_expr_literal_char(Parser *parser) {
  const char *cursor = parser->previous.lexeme + 1;
  const char *end = parser->previous.lexeme + parser->previous.lexeme_len - 1;

  if (cursor == end) {
    error_at(parser, parser->previous, "Empty character literal.");
    return NULL;
  }

  uint32_t code_point;

  if (*cursor == '\\') {
    cursor++;

    if (!decode_escape(parser, &cursor, end, &code_point, NULL)) {
      return NULL;
    }
  } else if (!decode_utf8_char(&cursor, end, &code_point)) {
    error_at(parser, parser->previous, "Invalid UTF-8 in character literal.");
    return NULL;
  }

  if (cursor != end) {
    error_at(parser, parser->previous, "A character literal must hold a single character.");
    return NULL;
  }

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_LITERAL, parser->previous.loc);
  expr->expr_literal.kind = AST_LITERAL_CHAR;
  expr->expr_literal.code_point = code_point;

  return expr;
}

// STRING  -- text between double quotes, with escape sequences; the value is its bytes.
static AstExpr *parse_expr_literal_string(Parser *parser) {
  size_t str_len = parser->previous.lexeme_len;

  ArenaMark mark = arena_mark(&parser->comp_unit->arena);

  size_t escaped_len;
  const char *string_data = escape_str(parser, parser->previous.lexeme + 1, str_len - 2, &escaped_len);
  if (string_data == NULL) {
    arena_rollback(&parser->comp_unit->arena, mark);
    return NULL;
  }

  if (escaped_len > UINT32_MAX) {
    error_at(parser, parser->previous, "String literal is too long.");
    arena_rollback(&parser->comp_unit->arena, mark);
    return NULL;
  }

  string_data = st_intern_len(&parser->comp_unit->intern_table, string_data, escaped_len);
  arena_rollback(&parser->comp_unit->arena, mark);

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_LITERAL, parser->previous.loc);
  expr->expr_literal.kind = AST_LITERAL_STRING;
  expr->expr_literal.string_value.data = string_data;
  expr->expr_literal.string_value.length = (uint32_t)escaped_len;

  return expr;
}

// 'true' | 'false' | 'null' | 'undef'
static AstExpr *parse_expr_literal_keyword(Parser *parser) {
  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_LITERAL, parser->previous.loc);

  switch (parser->previous.kind) {
  case TOKEN_TRUE:
    expr->expr_literal.kind = AST_LITERAL_TRUE;
    break;
  case TOKEN_FALSE:
    expr->expr_literal.kind = AST_LITERAL_FALSE;
    break;
  case TOKEN_NULL:
    expr->expr_literal.kind = AST_LITERAL_NULL;
    break;
  case TOKEN_UNDEF:
    expr->expr_literal.kind = AST_LITERAL_UNDEF;
    break;
  default:
    UNREACHABLE("parse_expr_literal_keyword: not a keyword literal");
  }

  return expr;
}

// IDENT
static AstExpr *parse_expr_identifier(Parser *parser) {
  const char *identifier_name = parse_identifier_name(parser, parser->previous);
  if (!identifier_name) return NULL;

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_IDENTIFIER, parser->previous.loc);
  expr->expr_identifier.name = identifier_name;

  return expr;
}

// [ expression ':' ] expression  -- one element of an array literal; `first` is its first expression when the caller
// has parsed it already. Returns false after reporting an error.
static bool parse_array_literal_element(Parser *parser, AstExpr *first, AstArrayElement *element) {
  if (!first) first = parse_expr(parser);
  if (!first) return false;

  AstExpr *index_expr = NULL;
  AstExpr *value = first;

  if (match(parser, TOKEN_COLON)) {
    index_expr = first;
    value = parse_expr(parser);
    if (!value) return false;
  }

  *element = (AstArrayElement){
    .index_expr = index_expr,
    .value = value,
    .loc = value->loc,
  };

  return true;
}

// '[' [ element { ',' element } [ ',' ] ] ']' | '[' expression ';' expression ']'  -- the '[' is already consumed.
// A bad element is skipped, so every element can report its own error.
static AstExpr *parse_expr_array_literal(Parser *parser) {
  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_ARRAY_LITERAL, parser->previous.loc);
  AstExprArrayLiteral *array_literal_expr = &expr->expr_array_literal;

  if (match(parser, TOKEN_RBRACKET)) {
    return expr;
  }

  AstExpr *first = parse_expr(parser);
  if (!first) {
    skip_to_element_end(parser);
    match(parser, TOKEN_SEMICOLON);
    skip_list_rest(parser, TOKEN_RBRACKET);
    return NULL;
  }

  // Repeat syntax: [val; count]
  if (match(parser, TOKEN_SEMICOLON)) {
    AstExpr *length_expr = parse_expr(parser);
    if (!length_expr) {
      skip_list_rest(parser, TOKEN_RBRACKET);
      return NULL;
    }

    array_literal_expr->is_repeat = true;
    array_literal_expr->repeat.value = first;
    array_literal_expr->repeat.length_expr = length_expr;

    if (!consume(parser, TOKEN_RBRACKET, "Expected ']' after array repeat length.")) return NULL;

    return expr;
  }

  AstArrayElement *elements = NULL;
  bool elements_ok = true;

  // Parse elements (sequential or sparse)
  do {
    AstArrayElement element;
    bool element_ok = parse_array_literal_element(parser, first, &element);

    if (list_element_ok(parser, element_ok)) {
      da_append(elements, element);
      if (element.index_expr) array_literal_expr->list.is_sparse = true;
    } else {
      elements_ok = false;
    }

    first = NULL;
  } while (match(parser, TOKEN_COMMA) && !check(parser, TOKEN_RBRACKET));

  if (!list_close(parser, TOKEN_RBRACKET, elements_ok, "Expected ']' after array elements.")) {
    da_free(elements);
    return NULL;
  }

  uint32_t element_count = da_len(elements);
  array_literal_expr->list.elements =
    arena_copy_array(&parser->comp_unit->arena, elements, element_count, sizeof(AstArrayElement));
  array_literal_expr->list.element_count = element_count;
  da_free(elements);

  return expr;
}

// IDENT ':' expression  -- one initialiser of a struct literal. Returns false after reporting an error.
static bool parse_struct_literal_field(Parser *parser, AstExprStructLiteralField *field) {
  SourceLoc field_loc = parser->current.loc;

  if (!match(parser, TOKEN_IDENT)) {
    error_at(parser, parser->current, "Expected struct literal field name.");
    return false;
  }

  const char *field_name = parse_identifier_name(parser, parser->previous);
  if (!field_name) return false;

  if (!consume(parser, TOKEN_COLON, "Expected ':' after struct literal field name.")) return false;

  AstExpr *value = parse_expr(parser);
  if (!value) return false;

  *field = (AstExprStructLiteralField){
    .name = field_name,
    .value = value,
    .loc = field_loc,
  };

  return true;
}

// [ field { ',' field } [ ',' ] ] '}'  -- a struct literal after its '.{', with `ast_type` NULL when the type comes
// from context. A bad field is skipped, so every field can report its own error.
static AstExpr *parse_struct_literal(Parser *parser, AstType *ast_type, SourceLoc start_loc) {
  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_STRUCT_LITERAL, start_loc);
  expr->expr_struct_literal.type = ast_type;

  AstExprStructLiteralField *fields = NULL;
  bool fields_ok = true;

  while (!check(parser, TOKEN_RBRACE) && !check(parser, TOKEN_EOF)) {
    AstExprStructLiteralField field;
    bool field_ok = parse_struct_literal_field(parser, &field);

    if (list_element_ok(parser, field_ok)) {
      da_append(fields, field);
    } else {
      fields_ok = false;
    }

    if (!match(parser, TOKEN_COMMA)) break;
  }

  if (!list_close(parser, TOKEN_RBRACE, fields_ok, "Expected '}' after struct literal fields.")) {
    da_free(fields);
    return NULL;
  }

  uint32_t field_count = da_len(fields);
  expr->expr_struct_literal.fields =
    arena_copy_array(&parser->comp_unit->arena, fields, field_count, sizeof(AstExprStructLiteralField));
  expr->expr_struct_literal.field_count = field_count;
  da_free(fields);

  return expr;
}

// IDENT '.{' ... '}'  -- the '.{' is already consumed.
static AstExpr *parse_expr_struct_literal_named(Parser *parser, AstExpr *left) {
  if (!left) return NULL;

  if (left->kind != AST_EXPR_IDENTIFIER) {
    error_at(parser, parser->previous, "Expected struct type name before '.{'.");
    skip_list_rest(parser, TOKEN_RBRACE);
    return NULL;
  }

  AstType *ast_type = ast_type_new(&parser->comp_unit->arena, AST_TYPE_NAMED, left->loc);
  ast_type->type_named.name = left->expr_identifier.name;

  return parse_struct_literal(parser, ast_type, left->loc);
}

// '.{' ... '}'  -- the '.{' is already consumed; the struct type comes from context.
static AstExpr *parse_expr_struct_literal_inferred(Parser *parser) {
  return parse_struct_literal(parser, NULL, parser->previous.loc);
}

// '(' expression ')'  -- the '(' is already consumed.
static AstExpr *parse_grouping(Parser *parser) {
  AstExpr *expr = parse_expr(parser);

  consume(parser, TOKEN_RPAREN, "Expected ')' after expression.");

  return expr;
}

// '&' expression
static AstExpr *parse_expr_addr_of(Parser *parser) {
  SourceLoc start_loc = parser->previous.loc;

  AstExpr *operand = parse_precedence(parser, PREC_PREFIX);
  if (!operand) return NULL;

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_ADDR_OF, start_loc);
  expr->expr_addr_of.operand = operand;

  return expr;
}

// expression '.*'  -- the '.*' is already consumed.
static AstExpr *parse_expr_deref(Parser *parser, AstExpr *left) {
  if (!left) return NULL;

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_DEREF, left->loc);
  expr->expr_deref.operand = left;

  return expr;
}

// expression '[' ( expression | [ expression ] ':' [ expression ] ) ']'  -- the '[' is already consumed.
// A subscript `xs[i]`, or a slice `xs[start:end]` where either bound may be left out.
static AstExpr *parse_expr_subscript(Parser *parser, AstExpr *left) {
  if (!left) return NULL;

  AstExpr *index = NULL;
  if (!check(parser, TOKEN_COLON)) {
    index = parse_expr(parser);
    if (!index) return NULL;
  }

  if (match(parser, TOKEN_COLON)) {
    AstExpr *end_index = NULL;

    if (!check(parser, TOKEN_RBRACKET)) {
      end_index = parse_expr(parser);
      if (!end_index) return NULL;
    }

    consume(parser, TOKEN_RBRACKET, "Expected ']' after slice index.");

    AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_SLICE, left->loc);
    expr->expr_slice.target = left;
    expr->expr_slice.start = index;
    expr->expr_slice.end = end_index;

    return expr;
  }

  consume(parser, TOKEN_RBRACKET, "Expected ']' after subscript index.");

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_SUBSCRIPT, left->loc);
  expr->expr_subscript.target = left;
  expr->expr_subscript.index = index;

  return expr;
}

// expression '.' IDENT  -- the '.' is already consumed.
static AstExpr *parse_expr_member(Parser *parser, AstExpr *left) {
  if (!left) return NULL;

  consume(parser, TOKEN_IDENT, "Expected member name after '.'.");

  const char *member = parse_identifier_name(parser, parser->previous);
  if (!member) return NULL;

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_MEMBER, left->loc);
  expr->expr_member.object = left;
  expr->expr_member.member = member;

  return expr;
}

// callee '(' [ expression { ',' expression } [ ',' ] ] ')'  -- the '(' is already consumed.
// A bad argument is skipped, so every argument can report its own error.
static AstExpr *parse_expr_call(Parser *parser, AstExpr *left) {
  if (!left) return NULL;

  AstExpr **args = NULL;
  bool args_ok = true;

  while (!check(parser, TOKEN_RPAREN) && !check(parser, TOKEN_EOF)) {
    AstExpr *arg = parse_expr(parser);

    if (list_element_ok(parser, arg != NULL)) {
      da_append(args, arg);
    } else {
      args_ok = false;
    }

    if (!match(parser, TOKEN_COMMA)) break;
  }

  if (!list_close(parser, TOKEN_RPAREN, args_ok, "Expected ')' after function arguments.")) {
    da_free(args);
    return NULL;
  }

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_CALL, left->loc);
  expr->expr_call.callee = left;

  uint32_t arg_count = da_len(args);
  expr->expr_call.args = arena_copy_array(&parser->comp_unit->arena, args, arg_count, sizeof(AstExpr *));
  expr->expr_call.arg_count = arg_count;
  da_free(args);

  return expr;
}

// ( '-' | '!' | '~' ) expression
static AstExpr *parse_expr_unary(Parser *parser) {
  SourceLoc start_loc = parser->previous.loc;
  TokenKind operator = parser->previous.kind;

  AstExpr *operand = parse_precedence(parser, PREC_PREFIX);
  if (!operand) return NULL;

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_UNARY, start_loc);
  expr->expr_unary.op = get_unary_op(operator);
  expr->expr_unary.operand = operand;

  return expr;
}

// left OP right, where OP is an arithmetic, comparison, bitwise or shift operator; left-associative.
static AstExpr *parse_expr_binary(Parser *parser, AstExpr *left) {
  TokenKind operator = parser->previous.kind;

  const ParseRule *rule = get_rule(operator);
  AstExpr *right = parse_precedence(parser, rule->precedence + 1);
  if (!left || !right) return NULL;

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_BINARY, left->loc);
  expr->expr_binary.op = get_binary_op(operator);
  expr->expr_binary.left = left;
  expr->expr_binary.right = right;

  return expr;
}

// left ( '&&' | '||' ) right  -- left-associative.
static AstExpr *parse_expr_logical(Parser *parser, AstExpr *left) {
  TokenKind operator = parser->previous.kind;

  const ParseRule *rule = get_rule(operator);
  AstExpr *right = parse_precedence(parser, rule->precedence + 1);
  if (!left || !right) return NULL;

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_LOGICAL, left->loc);
  expr->expr_logical.op = get_logical_op(operator);
  expr->expr_logical.left = left;
  expr->expr_logical.right = right;

  return expr;
}

// expression 'as' type  -- the 'as' is already consumed.
static AstExpr *parse_expr_cast(Parser *parser, AstExpr *left) {
  if (!left) return NULL;

  AstType *ast_type = parse_type(parser);
  if (!ast_type) return NULL;

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_CAST, left->loc);
  expr->expr_cast.operand = left;
  expr->expr_cast.target_type = ast_type;

  return expr;
}

// target '=' expression  -- right-associative; sema checks that the target can be assigned to.
static AstExpr *parse_expr_assign(Parser *parser, AstExpr *left) {
  if (!left) return NULL;

  AstExpr *right = parse_precedence(parser, PREC_ASSIGNMENT);
  if (!right) return NULL;

  AstExpr *expr = ast_expr_new(&parser->comp_unit->arena, AST_EXPR_ASSIGN, left->loc);
  expr->expr_assign.target = left;
  expr->expr_assign.value = right;

  return expr;
}

// expression := assignment  -- the lowest precedence level.
AstExpr *parse_expr(Parser *parser) {
  return parse_precedence(parser, PREC_ASSIGNMENT);
}

// Statement parsing functions

// '{' { statement } '}'  -- NULL when the '{' is missing, so that what follows stays in the enclosing block.
static AstStmt *parse_stmt_block(Parser *parser) {
  SourceLoc start_loc = parser->current.loc;

  if (!consume(parser, TOKEN_LBRACE, "Expected '{' to start block.")) return NULL;

  AstStmt **stmts = NULL;

  while (!check(parser, TOKEN_RBRACE) && !check(parser, TOKEN_EOF)) {
    const char *stmt_start = parser->current.lexeme;

    AstStmt *inner_stmt = parse_stmt(parser);
    if (inner_stmt) {
      da_append(stmts, inner_stmt);
    }

    if (parser->panic_mode) {
      synchronize(parser);

      // A token no statement can start with, such as `)`, must not keep the loop from moving on
      if (parser->current.lexeme == stmt_start && !check(parser, TOKEN_RBRACE) && !check(parser, TOKEN_EOF)) {
        advance(parser);
      }
    }
  }

  consume(parser, TOKEN_RBRACE, "Expected '}' to end block.");

  AstStmt *stmt = ast_stmt_new(&parser->comp_unit->arena, AST_STMT_BLOCK, start_loc);

  AstStmt **stmt_array = arena_copy_array(&parser->comp_unit->arena, stmts, da_len(stmts), sizeof(AstStmt *));

  stmt->stmt_block.stmts = stmt_array;
  stmt->stmt_block.stmt_count = da_len(stmts);
  da_free(stmts);

  return stmt;
}

// expression ';'
static AstStmt *parse_stmt_expression(Parser *parser) {
  SourceLoc start_loc = parser->current.loc;

  AstExpr *expr = parse_expr(parser);

  consume(parser, TOKEN_SEMICOLON, "Expected ';' after expression.");

  if (!expr) return NULL;

  AstStmt *stmt = ast_stmt_new(&parser->comp_unit->arena, AST_STMT_EXPRESSION, start_loc);
  stmt->stmt_expression.expression = expr;

  return stmt;
}

// 'var' IDENT [ ':' type ] [ '=' expression ] ';'  -- needs a type or an initializer.
static AstStmt *parse_stmt_local_var(Parser *parser) {
  expect(parser, TOKEN_VAR);
  consume(parser, TOKEN_IDENT, "Expected variable name after 'var'.");

  Token name_token = parser->previous;

  AstType *ast_type = NULL;
  bool has_type = match(parser, TOKEN_COLON);
  if (has_type) ast_type = parse_type(parser);

  AstExpr *init = NULL;
  bool has_init = match(parser, TOKEN_ASSIGN);
  if (has_init) init = parse_expr(parser);

  consume(parser, TOKEN_SEMICOLON, "Expected ';' after variable declaration.");

  if (!has_type && !has_init) {
    error_at(parser,
             name_token,
             "Variable '%.*s' must have either a type annotation or an initializer.",
             (int)name_token.lexeme_len,
             name_token.lexeme);
    return NULL;
  }

  const char *var_name = parse_identifier_name(parser, name_token);
  if (!var_name || (has_type && !ast_type) || (has_init && !init)) return NULL;

  AstStmt *stmt = ast_stmt_new(&parser->comp_unit->arena, AST_STMT_LOCAL_VAR, name_token.loc);
  stmt->stmt_local_var.name = var_name;
  stmt->stmt_local_var.type = ast_type;
  stmt->stmt_local_var.init = init;

  return stmt;
}

// 'return' [ expression ] ';'
static AstStmt *parse_stmt_return(Parser *parser) {
  SourceLoc start_loc = parser->current.loc;

  expect(parser, TOKEN_RETURN);

  AstExpr *value = NULL;
  bool has_value = !check(parser, TOKEN_SEMICOLON);
  if (has_value) value = parse_expr(parser);

  consume(parser, TOKEN_SEMICOLON, "Expected ';' after return statement.");

  if (has_value && !value) return NULL;

  AstStmt *stmt = ast_stmt_new(&parser->comp_unit->arena, AST_STMT_RETURN, start_loc);
  stmt->stmt_return.value = value;

  return stmt;
}

// 'break' ';'
static AstStmt *parse_stmt_break(Parser *parser) {
  SourceLoc start_loc = parser->current.loc;

  expect(parser, TOKEN_BREAK);
  consume(parser, TOKEN_SEMICOLON, "Expected ';' after 'break' statement.");

  AstStmt *stmt = ast_stmt_new(&parser->comp_unit->arena, AST_STMT_BREAK, start_loc);
  return stmt;
}

// 'continue' ';'
static AstStmt *parse_stmt_continue(Parser *parser) {
  SourceLoc start_loc = parser->current.loc;

  expect(parser, TOKEN_CONTINUE);
  consume(parser, TOKEN_SEMICOLON, "Expected ';' after 'continue' statement.");

  AstStmt *stmt = ast_stmt_new(&parser->comp_unit->arena, AST_STMT_CONTINUE, start_loc);
  return stmt;
}

// 'if' expression block [ 'else' statement ]  -- the else branch is usually a block or another if.
static AstStmt *parse_stmt_if(Parser *parser) {
  SourceLoc start_loc = parser->current.loc;

  expect(parser, TOKEN_IF);

  AstExpr *condition = parse_expr(parser);

  if (!check(parser, TOKEN_LBRACE)) {
    error_at(parser, parser->previous, "Expected '{' after 'if' condition.");
  }

  AstStmt *then_branch = parse_stmt_block(parser);
  if (!then_branch) return NULL;

  AstStmt *else_branch = NULL;
  bool has_else = match(parser, TOKEN_ELSE);
  if (has_else) else_branch = parse_stmt(parser);

  if (!condition || (has_else && !else_branch)) return NULL;

  AstStmt *stmt = ast_stmt_new(&parser->comp_unit->arena, AST_STMT_IF, start_loc);
  stmt->stmt_if.condition = condition;
  stmt->stmt_if.then_branch = then_branch;
  stmt->stmt_if.else_branch = else_branch;

  return stmt;
}

// 'while' expression block
static AstStmt *parse_stmt_while(Parser *parser) {
  SourceLoc start_loc = parser->current.loc;

  expect(parser, TOKEN_WHILE);

  AstExpr *condition = parse_expr(parser);

  if (!check(parser, TOKEN_LBRACE)) {
    error_at(parser, parser->previous, "Expected '{' after 'while' condition.");
  }

  AstStmt *body = parse_stmt_block(parser);
  if (!condition || !body) return NULL;

  AstStmt *stmt = ast_stmt_new(&parser->comp_unit->arena, AST_STMT_WHILE, start_loc);
  stmt->stmt_while.condition = condition;
  stmt->stmt_while.body = body;

  return stmt;
}

// statement := block | local_var | return | break | continue | if | while | expression ';'
AstStmt *parse_stmt(Parser *parser) {
  switch (parser->current.kind) {
  case TOKEN_LBRACE:
    return parse_stmt_block(parser);
  case TOKEN_VAR:
    return parse_stmt_local_var(parser);

  // A misplaced declaration is parsed where it stands, so that one error covers all of it
  case TOKEN_FN:
  case TOKEN_STRUCT:
  case TOKEN_EXTERN:
    error_at(parser, parser->current, "Declarations are only allowed at the top level.");
    parse_decl(parser);
    return NULL;

  // So is the statement after an 'else' that follows no 'if'
  case TOKEN_ELSE:
    error_at(parser, parser->current, "'else' has no matching 'if'.");
    advance(parser);
    parse_stmt(parser);
    return NULL;

  case TOKEN_RETURN:
    return parse_stmt_return(parser);
  case TOKEN_BREAK:
    return parse_stmt_break(parser);
  case TOKEN_CONTINUE:
    return parse_stmt_continue(parser);

  case TOKEN_IF:
    return parse_stmt_if(parser);
  case TOKEN_WHILE:
    return parse_stmt_while(parser);

  default:
    return parse_stmt_expression(parser);
  }
}

// Declaration parsing functions

// IDENT ':' type  -- the shape of a parameter and of a struct field; `what` names it in errors. Returns false after
// reporting an error.
static bool parse_typed_name(Parser *parser, const char *what, const char **name, AstType **ast_type) {
  if (!match(parser, TOKEN_IDENT)) {
    error_at(parser, parser->current, "Expected %s name.", what);
    return false;
  }

  *name = parse_identifier_name(parser, parser->previous);
  if (!*name) return false;

  if (!match(parser, TOKEN_COLON)) {
    error_at(parser, parser->previous, "Expected ':' after %s name.", what);
    return false;
  }

  *ast_type = parse_type(parser);

  return *ast_type != NULL;
}

// 'struct' IDENT '{' [ field { ',' field } [ ',' ] ] '}'  where field := IDENT ':' type
static AstDecl *parse_decl_struct(Parser *parser) {
  SourceLoc start_loc = parser->current.loc;

  expect(parser, TOKEN_STRUCT);
  consume(parser, TOKEN_IDENT, "Expected struct name after 'struct'.");

  const char *struct_name = parse_identifier_name(parser, parser->previous);
  if (!struct_name) return NULL;

  if (!consume(parser, TOKEN_LBRACE, "Expected '{' after struct name.")) return NULL;

  AstStructField *fields = NULL;
  bool fields_ok = true;

  // A bad field is skipped, so every field can report its own error
  while (!check(parser, TOKEN_RBRACE) && !check(parser, TOKEN_EOF)) {
    SourceLoc field_loc = parser->current.loc;

    const char *field_name;
    AstType *field_ast_type;
    bool field_ok = parse_typed_name(parser, "field", &field_name, &field_ast_type);

    if (list_element_ok(parser, field_ok)) {
      AstStructField field = {
        .name = field_name,
        .type = field_ast_type,
        .loc = field_loc,
      };
      da_append(fields, field);
    } else {
      fields_ok = false;
    }

    if (!match(parser, TOKEN_COMMA)) break;
  }

  if (!list_close(parser, TOKEN_RBRACE, fields_ok, "Expected '}' after struct declaration.")) {
    da_free(fields);
    return NULL;
  }

  uint32_t field_count = da_len(fields);
  AstStructField *field_array =
    arena_copy_array(&parser->comp_unit->arena, fields, field_count, sizeof(AstStructField));
  da_free(fields);

  AstDecl *decl = ast_decl_new(&parser->comp_unit->arena, AST_DECL_STRUCT, start_loc);
  decl->decl_struct.name = struct_name;
  decl->decl_struct.fields = field_array;
  decl->decl_struct.field_count = field_count;

  return decl;
}

// [ 'extern' ] 'fn' IDENT '(' [ param { ',' param } [ ',' '...' | ',' ] ] ')' [ ':' type ] ( block | ';' )
// The ';' form and the '...' parameter are only for 'extern', whose keyword parse_decl_extern has consumed.
static AstDecl *parse_decl_function(Parser *parser, bool is_extern) {
  SourceLoc start_loc = parser->current.loc;

  expect(parser, TOKEN_FN);
  consume(parser, TOKEN_IDENT, "Expected function name after 'fn'.");

  const char *func_name = parse_identifier_name(parser, parser->previous);
  if (!func_name) return NULL;

  consume(parser, TOKEN_LPAREN, "Expected '(' after function name.");

  AstParam *params = NULL;
  bool params_ok = true;
  bool is_variadic = false;

  // A bad parameter is skipped, so every parameter and the body can report their own errors
  while (!check(parser, TOKEN_RPAREN) && !check(parser, TOKEN_EOF)) {
    SourceLoc param_loc = parser->current.loc;

    if (match(parser, TOKEN_ELLIPSIS)) {
      if (!is_extern) {
        error_at(parser, parser->previous, "Only extern functions can be variadic.");
      }

      if (params_ok && da_len(params) < 1) {
        error_at(parser, parser->previous, "A variadic function needs at least one regular parameter.");
      }

      is_variadic = true;
      break;
    }

    const char *param_name;
    AstType *param_ast_type;
    bool param_ok = parse_typed_name(parser, "parameter", &param_name, &param_ast_type);

    if (list_element_ok(parser, param_ok)) {
      AstParam param = {
        .name = param_name,
        .type = param_ast_type,
        .loc = param_loc,
      };
      da_append(params, param);
    } else {
      params_ok = false;
    }

    if (!match(parser, TOKEN_COMMA)) break;
  }

  if (!list_close(parser, TOKEN_RPAREN, params_ok, "Expected ')' after function parameters.")) {
    params_ok = false;
  }

  uint32_t param_count = da_len(params);
  AstParam *param_array = arena_copy_array(&parser->comp_unit->arena, params, param_count, sizeof(AstParam));
  da_free(params);

  AstType *return_ast_type = NULL;
  bool has_return_type = match(parser, TOKEN_COLON);
  if (has_return_type) return_ast_type = parse_type(parser);

  AstStmt *func_body = NULL;

  if (is_extern) {
    consume(parser, TOKEN_SEMICOLON, "Expected ';' after extern function declaration.");
  } else if (check(parser, TOKEN_SEMICOLON)) {
    error_at(parser, parser->previous, "Function '%s' has no body; add one or declare it 'extern'.", func_name);
    return NULL;
  } else {
    if (check(parser, TOKEN_LBRACE)) parser->panic_mode = false;

    func_body = parse_stmt_block(parser);
    if (!func_body) return NULL;
  }

  if (!params_ok || (has_return_type && !return_ast_type)) return NULL;

  AstDecl *decl = ast_decl_new(&parser->comp_unit->arena, AST_DECL_FUNCTION, start_loc);
  decl->decl_function.name = func_name;
  decl->decl_function.body = func_body;
  decl->decl_function.return_type = return_ast_type;

  decl->decl_function.params = param_array;
  decl->decl_function.param_count = param_count;

  decl->decl_function.is_extern = is_extern;
  decl->decl_function.is_variadic = is_variadic;

  return decl;
}

// 'extern' function_declaration  -- a declaration without a body, defined outside this program.
static AstDecl *parse_decl_extern(Parser *parser) {
  expect(parser, TOKEN_EXTERN);

  switch (parser->current.kind) {
  case TOKEN_FN:
    return parse_decl_function(parser, true);

  default:
    error_at(parser, parser->previous, "Expected 'fn' after 'extern'.");
  }

  return NULL;
}

// declaration := struct | function | 'extern' function  -- recovers to the next declaration on anything else.
AstDecl *parse_decl(Parser *parser) {
  switch (parser->current.kind) {
  case TOKEN_STRUCT:
    return parse_decl_struct(parser);

  case TOKEN_FN:
    return parse_decl_function(parser, false);

  case TOKEN_EXTERN:
    return parse_decl_extern(parser);

  default:
    error_at(parser, parser->current, "Expected declaration.");
    synchronize_top_level(parser);
  }

  return NULL;
}

// Type parsing functions

// IDENT  -- a named type such as i32.
static AstType *parse_type_named(Parser *parser) {
  SourceLoc start_loc = parser->current.loc;

  expect(parser, TOKEN_IDENT);

  const char *type_name = parse_identifier_name(parser, parser->previous);
  if (!type_name) return NULL;

  AstType *ast_type = ast_type_new(&parser->comp_unit->arena, AST_TYPE_NAMED, start_loc);
  ast_type->type_named.name = type_name;

  return ast_type;
}

// '*' type
static AstType *parse_type_pointer(Parser *parser) {
  SourceLoc start_loc = parser->current.loc;

  expect(parser, TOKEN_STAR);

  AstType *base_ast_type = parse_type(parser);
  if (!base_ast_type) return NULL;

  AstType *ast_type = ast_type_new(&parser->comp_unit->arena, AST_TYPE_POINTER, start_loc);
  ast_type->type_pointer.base_type = base_ast_type;

  return ast_type;
}

// '[' [ expression | '_' ] ']' type  -- an array, or a slice when the brackets are empty.
static AstType *parse_type_array(Parser *parser) {
  SourceLoc start_loc = parser->current.loc;

  expect(parser, TOKEN_LBRACKET);

  if (match(parser, TOKEN_RBRACKET)) {
    AstType *elem_ast_type = parse_type(parser);
    if (!elem_ast_type) return NULL;

    AstType *ast_type = ast_type_new(&parser->comp_unit->arena, AST_TYPE_SLICE, start_loc);
    ast_type->type_slice.elem_type = elem_ast_type;

    return ast_type;
  }

  AstExpr *length_expr = NULL;
  if (!match(parser, TOKEN_UNDERSCORE)) {
    length_expr = parse_expr(parser);
    if (!length_expr) return NULL;
  }

  consume(parser, TOKEN_RBRACKET, "Expected ']' after array length.");

  AstType *elem_ast_type = parse_type(parser);
  if (!elem_ast_type) return NULL;

  AstType *ast_type = ast_type_new(&parser->comp_unit->arena, AST_TYPE_ARRAY, start_loc);
  ast_type->type_array.elem_type = elem_ast_type;
  ast_type->type_array.length_expr = length_expr;

  return ast_type;
}

// type := IDENT | '*' type | '[' [ expression | '_' ] ']' type  -- reports an error when no type starts here.
AstType *parse_type(Parser *parser) {
  switch (parser->current.kind) {
  case TOKEN_IDENT:
    return parse_type_named(parser);
  case TOKEN_STAR:
    return parse_type_pointer(parser);
  case TOKEN_LBRACKET:
    return parse_type_array(parser);

  default:
    error_at(parser, parser->current, "Expected type.");
    return NULL;
  }
}

// Parser public functions

// Sets up the lexer and reads the first token into the lookahead.
void parser_init(Parser *parser, CompilationUnit *comp_unit) {
  parser->comp_unit = comp_unit;
  lexer_init(&parser->lexer, comp_unit);

  parser->panic_mode = false;

  advance(parser);
}

// program := { declaration } EOF
AstProgram *parse_program(Parser *parser) {
  AstDecl **decls = NULL;

  while (!check(parser, TOKEN_EOF)) {
    AstDecl *decl = parse_decl(parser);
    if (decl) {
      da_append(decls, decl);
    }

    if (parser->panic_mode) {
      synchronize_top_level(parser);
    }
  }

  AstProgram *program = arena_calloc(&parser->comp_unit->arena, sizeof(AstProgram));

  AstDecl **decl_array = arena_copy_array(&parser->comp_unit->arena, decls, da_len(decls), sizeof(AstDecl *));

  program->decls = decl_array;
  program->decl_count = da_len(decls);

  da_free(decls);

  return program;
}

// Parse rules

// Entries run from the loosest infix operator to the tightest, mirroring Precedence; prefix-only tokens stay PREC_NONE.
static const ParseRule rules[TOKEN_COUNT] = {
  // Operands
  [TOKEN_IDENT] = {PREC_NONE, parse_expr_identifier, NULL},
  [TOKEN_INT] = {PREC_NONE, parse_expr_literal_int, NULL},
  [TOKEN_FLOAT] = {PREC_NONE, parse_expr_literal_float, NULL},
  [TOKEN_CHAR] = {PREC_NONE, parse_expr_literal_char, NULL},
  [TOKEN_STRING] = {PREC_NONE, parse_expr_literal_string, NULL},

  [TOKEN_TRUE] = {PREC_NONE, parse_expr_literal_keyword, NULL},
  [TOKEN_FALSE] = {PREC_NONE, parse_expr_literal_keyword, NULL},
  [TOKEN_NULL] = {PREC_NONE, parse_expr_literal_keyword, NULL},
  [TOKEN_UNDEF] = {PREC_NONE, parse_expr_literal_keyword, NULL},

  // Prefix-only operators
  [TOKEN_BANG] = {PREC_NONE, parse_expr_unary, NULL},
  [TOKEN_TILDE] = {PREC_NONE, parse_expr_unary, NULL},

  // Assignment
  [TOKEN_ASSIGN] = {PREC_ASSIGNMENT, NULL, parse_expr_assign},

  // Logical
  [TOKEN_OR] = {PREC_LOGIC_OR, NULL, parse_expr_logical},
  [TOKEN_AND] = {PREC_LOGIC_AND, NULL, parse_expr_logical},

  // Equality
  [TOKEN_EQ] = {PREC_EQUALITY, NULL, parse_expr_binary},
  [TOKEN_NOT_EQ] = {PREC_EQUALITY, NULL, parse_expr_binary},

  // Comparison
  [TOKEN_LESS] = {PREC_COMPARISON, NULL, parse_expr_binary},
  [TOKEN_GREATER] = {PREC_COMPARISON, NULL, parse_expr_binary},
  [TOKEN_LESS_EQ] = {PREC_COMPARISON, NULL, parse_expr_binary},
  [TOKEN_GREATER_EQ] = {PREC_COMPARISON, NULL, parse_expr_binary},

  // Bitwise and shifts; '&' is also the prefix address-of
  [TOKEN_PIPE] = {PREC_BIT_OR, NULL, parse_expr_binary},
  [TOKEN_CARET] = {PREC_BIT_XOR, NULL, parse_expr_binary},
  [TOKEN_AMP] = {PREC_BIT_AND, parse_expr_addr_of, parse_expr_binary},
  [TOKEN_SHL] = {PREC_SHIFT, NULL, parse_expr_binary},
  [TOKEN_SHR] = {PREC_SHIFT, NULL, parse_expr_binary},

  // Additive; '-' is also the prefix negation
  [TOKEN_PLUS] = {PREC_TERM, NULL, parse_expr_binary},
  [TOKEN_MINUS] = {PREC_TERM, parse_expr_unary, parse_expr_binary},

  // Multiplicative
  [TOKEN_STAR] = {PREC_FACTOR, NULL, parse_expr_binary},
  [TOKEN_SLASH] = {PREC_FACTOR, NULL, parse_expr_binary},

  // Cast
  [TOKEN_AS] = {PREC_CAST, NULL, parse_expr_cast},

  // Postfix and grouping; '(' is the call operator and also starts a parenthesised expression
  [TOKEN_LPAREN] = {PREC_POSTFIX, parse_grouping, parse_expr_call},
  [TOKEN_LBRACKET] = {PREC_POSTFIX, parse_expr_array_literal, parse_expr_subscript},
  [TOKEN_DOT_LBRACE] = {PREC_POSTFIX, parse_expr_struct_literal_inferred, parse_expr_struct_literal_named},
  [TOKEN_DOT] = {PREC_POSTFIX, NULL, parse_expr_member},
  [TOKEN_DEREF] = {PREC_POSTFIX, NULL, parse_expr_deref},
};
