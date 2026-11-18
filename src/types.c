#include "types.h"
#include "common.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Builtin types

// A builtin is aligned to its size; one without storage gets 1, so that aligning to it is always valid.
#define TYPE_DEFINE(type_kind, type_size, ident)                                                           \
  static Type type_##ident##_def = {                                                                       \
    .kind = type_kind, .size = type_size, .alignment = (type_size) > 0 ? (type_size) : 1, .name = #ident};
TYPES_BUILTIN(TYPE_DEFINE)
#undef TYPE_DEFINE

#define TYPE_PTRS(kind, size, ident) Type *const type_##ident = &type_##ident##_def;
TYPES_BUILTIN(TYPE_PTRS)
#undef TYPE_PTRS

static Type type_void_ptr_def = {
  .kind = TYPE_KIND_POINTER,
  .size = 8,
  .name = "*void",
  .pointer = {.base_type = &type_void_def},
};
Type *const type_void_ptr = &type_void_ptr_def;

// What kind a type is

bool type_is_void(Type *type) {
  return type == type_void;
}

bool type_is_bool(Type *type) {
  if (!type) return false;
  if (type == type_error) return true;
  return type == type_bool;
}

bool type_is_integer(Type *type) {
  return type_is_unsigned_integer(type) || type_is_signed_integer(type);
}

bool type_is_signed_integer(Type *type) {
  if (!type) return false;
  if (type == type_error) return true;
  return type == type_i8 || type == type_i16 || type == type_i32 || type == type_i64 || type == type_untyped_int;
}

bool type_is_unsigned_integer(Type *type) {
  if (!type) return false;
  if (type == type_error) return true;
  return type == type_u8 || type == type_u16 || type == type_u32 || type == type_u64 || type == type_untyped_int;
}

bool type_is_float(Type *type) {
  if (!type) return false;
  if (type == type_error) return true;
  return type == type_f64 || type == type_f32 || type == type_untyped_float;
}

bool type_is_numeric(Type *type) {
  if (!type) return false;
  if (type == type_error) return true;
  return type_is_integer(type) || type_is_float(type);
}

bool type_is_pointer(Type *type) {
  if (!type) return false;
  return type->kind == TYPE_KIND_POINTER;
}

bool type_is_array(Type *type) {
  if (!type) return false;
  return type->kind == TYPE_KIND_ARRAY;
}

bool type_is_slice(Type *type) {
  if (!type) return false;
  return type->kind == TYPE_KIND_SLICE;
}

bool type_is_struct(Type *type) {
  if (!type) return false;
  return type->kind == TYPE_KIND_STRUCT;
}

bool type_is_array_like(Type *type) {
  return type_is_array(type) || type_is_slice(type);
}

bool type_has_fields(Type *type) {
  return type_is_struct(type) || type_is_slice(type);
}

bool type_is_aggregate(Type *type) {
  return type_is_array(type) || type_is_slice(type) || type_is_struct(type);
}

// Compiler-internal types

bool type_is_untyped(Type *type) {
  return type == type_untyped_int || type == type_untyped_float || type == type_null || type == type_undef;
}

bool type_is_internal(Type *type) {
  return type == type_error || type_is_untyped(type);
}

// Properties

bool type_has_storage(Type *type) {
  if (!type) return false;
  return type == type_error || type->size > 0;
}

const char *type_display_name(Type *type) {
  switch (type->kind) {
  case TYPE_KIND_UNTYPED_INT:
    return "integer literal";
  case TYPE_KIND_UNTYPED_FLOAT:
    return "float literal";

  case TYPE_KIND_ERROR:
  case TYPE_KIND_U8:
  case TYPE_KIND_U16:
  case TYPE_KIND_U32:
  case TYPE_KIND_U64:
  case TYPE_KIND_I8:
  case TYPE_KIND_I16:
  case TYPE_KIND_I32:
  case TYPE_KIND_I64:
  case TYPE_KIND_BOOL:
  case TYPE_KIND_F32:
  case TYPE_KIND_F64:
  case TYPE_KIND_NULL:
  case TYPE_KIND_VOID:
  case TYPE_KIND_UNDEF:
  case TYPE_KIND_POINTER:
  case TYPE_KIND_ARRAY:
  case TYPE_KIND_SLICE:
  case TYPE_KIND_STRUCT:
  case TYPE_KIND_FUNCTION:
    return type->name;
  }

  UNREACHABLE("type_display_name: unhandled type kind");
}

bool type_int_fits(Type *type, bool negative, uint64_t magnitude) {
  switch (type->kind) {
  case TYPE_KIND_U8:
    return !negative && magnitude <= UINT8_MAX;
  case TYPE_KIND_U16:
    return !negative && magnitude <= UINT16_MAX;
  case TYPE_KIND_U32:
    return !negative && magnitude <= UINT32_MAX;
  case TYPE_KIND_U64:
    return !negative;

  // A signed type holds one more negative magnitude than positive
  case TYPE_KIND_I8:
    return magnitude <= (negative ? (uint64_t)INT8_MAX + 1 : (uint64_t)INT8_MAX);
  case TYPE_KIND_I16:
    return magnitude <= (negative ? (uint64_t)INT16_MAX + 1 : (uint64_t)INT16_MAX);
  case TYPE_KIND_I32:
    return magnitude <= (negative ? (uint64_t)INT32_MAX + 1 : (uint64_t)INT32_MAX);
  case TYPE_KIND_I64:
    return magnitude <= (negative ? (uint64_t)INT64_MAX + 1 : (uint64_t)INT64_MAX);

  case TYPE_KIND_BOOL:
    return !negative && magnitude <= 1;

  case TYPE_KIND_F32:
  case TYPE_KIND_F64:
  case TYPE_KIND_UNTYPED_INT:
  case TYPE_KIND_UNTYPED_FLOAT:
  case TYPE_KIND_NULL:
  case TYPE_KIND_POINTER:
  case TYPE_KIND_ARRAY:
  case TYPE_KIND_SLICE:
  case TYPE_KIND_STRUCT:
  case TYPE_KIND_ERROR:
  case TYPE_KIND_VOID:
  case TYPE_KIND_UNDEF:
  case TYPE_KIND_FUNCTION:
    return false;
  }

  UNREACHABLE("type_int_fits: unhandled type kind");
}

// Which operators a type supports

bool type_is_comparable(Type *type) {
  if (!type) return false;
  if (type == type_error) return true;
  return type_is_numeric(type) || type_is_bool(type) || type_is_pointer(type) || type == type_null;
}

bool type_is_orderable(Type *type) {
  if (!type) return false;
  if (type == type_error) return true;
  return type_is_numeric(type) || type_is_pointer(type);
}

// Relations between types

bool type_equals(Type *a, Type *b) {
  if (a == b) return true;
  if (!a || !b) return false;
  if (a == type_error || b == type_error) return true;

  if (type_is_pointer(a) && type_is_pointer(b)) {
    return type_equals(a->pointer.base_type, b->pointer.base_type);
  }

  if (type_is_array(a) && type_is_array(b)) {
    return a->array.length == b->array.length && type_equals(a->array.elem_type, b->array.elem_type);
  }

  if (type_is_slice(a) && type_is_slice(b)) {
    return type_equals(type_elem(a), type_elem(b));
  }

  return false;
}

// Implicit conversions: every value of `from_type` is representable in `to_type`
bool type_can_widen_to(Type *from_type, Type *to_type) {
  if (!from_type || !to_type) return false;
  if (type_equals(from_type, to_type)) return true;

  if (from_type == type_null) return type_is_pointer(to_type);
  if (to_type == type_null) return false;

  if (to_type == type_untyped_int) return false;
  if (to_type == type_untyped_float) return from_type == type_untyped_int;

  if (from_type == type_untyped_int) return type_is_integer(to_type) || type_is_float(to_type);
  if (from_type == type_untyped_float) return type_is_float(to_type);

  if (type_is_integer(from_type) && type_is_integer(to_type)) {
    if (type_is_signed_integer(from_type)) return type_is_signed_integer(to_type) && to_type->size >= from_type->size;
    return type_is_unsigned_integer(to_type) ? to_type->size >= from_type->size : to_type->size > from_type->size;
  }

  if (type_is_float(from_type) && type_is_float(to_type)) {
    return to_type->size >= from_type->size;
  }

  if (type_is_integer(from_type) && type_is_float(to_type)) {
    return to_type->size >= from_type->size;
  }

  // Any pointer converts implicitly to `*void`; the way back needs an explicit cast.
  if (type_is_pointer(from_type) && type_is_pointer(to_type)) {
    return type_is_void(to_type->pointer.base_type);
  }

  // An array converts to a pointer to its elements (or to `*void`); it is already represented by its address.
  if (type_is_array(from_type) && type_is_pointer(to_type)) {
    return type_is_void(to_type->pointer.base_type) ||
           type_equals(from_type->array.elem_type, to_type->pointer.base_type);
  }

  if (type_is_array(from_type) && type_is_slice(to_type)) {
    return type_equals(from_type->array.elem_type, type_elem(to_type));
  }

  return false;
}

Type *type_common(Type *a, Type *b) {
  if (a == b) return a;

  if (type_is_pointer(a) && type_is_pointer(b)) {
    if (type_can_widen_to(a, b)) return b;
    if (type_can_widen_to(b, a)) return a;
    return NULL;
  }

  if (a == type_null && type_is_pointer(b)) return b;
  if (b == type_null && type_is_pointer(a)) return a;

  if (!type_is_numeric(a) || !type_is_numeric(b)) return NULL;

  if (type_can_widen_to(a, b)) return b;
  if (type_can_widen_to(b, a)) return a;

  return NULL;
}

// Building and deriving types

Type *type_pointer_to(CompilationUnit *comp_unit, Type *base_type) {
  size_t name_len = strlen(base_type->name) + 2;
  char *name = arena_alloc(&comp_unit->arena, name_len);
  snprintf(name, name_len, "*%s", base_type->name);

  Type *ptr_type = arena_alloc(&comp_unit->arena, sizeof(Type));
  *ptr_type = (Type){
    .kind = TYPE_KIND_POINTER,
    .name = name,
    .size = 8,
    .alignment = 8,
    .pointer = {.base_type = base_type},
  };

  return ptr_type;
}

Type *type_array_of(CompilationUnit *comp_unit, Type *elem_type, uint32_t length) {
  size_t name_len = strlen(elem_type->name) + 16;
  char *name = arena_alloc(&comp_unit->arena, name_len);
  snprintf(name, name_len, "[%u]%s", length, elem_type->name);

  Type *array_type = arena_alloc(&comp_unit->arena, sizeof(Type));
  *array_type = (Type){
    .kind = TYPE_KIND_ARRAY,
    .name = name,
    .size = elem_type->size * length,
    .alignment = elem_type->alignment,
    .array = {.elem_type = elem_type, .length = length},
  };

  return array_type;
}

typedef struct {
  Type type;
  TypeField fields[2];
} SliceType;

Type *type_slice_of(CompilationUnit *comp_unit, Type *elem_type) {
  size_t name_len = strlen(elem_type->name) + 3;
  char *name = arena_alloc(&comp_unit->arena, name_len);
  snprintf(name, name_len, "[]%s", elem_type->name);

  const char *ptr_name = st_intern(&comp_unit->intern_table, "ptr");
  const char *len_name = st_intern(&comp_unit->intern_table, "len");

  SliceType *slice = arena_alloc(&comp_unit->arena, sizeof(SliceType));
  Type *ptr_type = type_pointer_to(comp_unit, elem_type);

  slice->fields[SLICE_PTR_INDEX] = (TypeField){.name = ptr_name, .type = ptr_type, .offset = 0};
  slice->fields[SLICE_LEN_INDEX] = (TypeField){.name = len_name, .type = type_i64, .offset = type_void_ptr->size};

  slice->type = (Type){
    .kind = TYPE_KIND_SLICE,
    .name = name,
    .size = type_void_ptr->size + type_i64->size,
    .alignment = type_void_ptr->alignment,
    .structure = {.fields = slice->fields, .field_count = 2},
  };

  return &slice->type;
}

Type *type_elem(Type *type) {
  assert(type_is_array_like(type) && "type_elem: type is neither an array nor a slice");

  return type_is_array(type) ? type->array.elem_type : SLICE_ELEM_TYPE(type);
}

Type *type_default(Type *type) {
  if (type == type_untyped_int) return type_i32;
  if (type == type_untyped_float) return type_f64;
  if (type == type_null) return type_void_ptr;
  return type;
}

bool type_find_field(Type *type, const char *name, TypeField *field) {
  if (!type_has_fields(type)) {
    return false;
  }

  for (uint32_t i = 0; i < type->structure.field_count; i++) {
    if (type->structure.fields[i].name != name) continue;

    *field = type->structure.fields[i];
    return true;
  }

  return false;
}
