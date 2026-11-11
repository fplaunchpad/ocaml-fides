/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*   FIDES software sanitizer: wrappers for the OCaml C API (Stage 4).    */
/*   Rules follow Resources/model.pdf; see Implementation/DECISIONS.md.   */
/*                                                                        */
/**************************************************************************/

/* Trusted runtime code, never instrumented (D30).

   Sanitized C holds tagged words (Index | Cookie | low address bits), which
   the uninstrumented runtime cannot dereference. The pass therefore sends
   every call sanitized C makes to a function listed in caml/fides_api.def to
   caml_fides_w_<name> instead: a wrapper with the same C type. The pass
   leaves the wrapper's pointer arguments tagged, so the wrapper can check
   them. A wrapper:

   - checks each `value` argument with caml_fides_value_cause (immediate and
     bare words pass until Stage 5; a tagged word must name a live OCaml
     block at its promoted address) and strips its tag;
   - checks each pointer it reads through (the D9 load check) and decodes it;
   - calls the real function.

   This is the model's runtime-service contract (D79, Data/RuntimeCall.lean):
   the obligation sits in trusted code at the entry of the service. */

#define CAML_INTERNALS

#include "caml/mlvalues.h"
#include "caml/memory.h"
#include "caml/alloc.h"
#include "caml/callback.h"
#include "caml/fail.h"
#include "caml/custom.h"
#include <stdarg.h>
#include <stdio.h>
#include "caml/fides_ffi.h"
#include "caml/fides.h"

/* Primitives that stubs call directly but that no public header declares. */
CAMLextern value caml_bytes_set(value, value, value);
CAMLextern value caml_string_set(value, value, value);
CAMLextern value caml_bytes_set16(value, value, value);
CAMLextern value caml_bytes_set32(value, value, value);
CAMLextern value caml_bytes_set64(value, value, value);
CAMLextern value caml_fill_bytes(value, value, value, value);
CAMLextern value caml_blit_bytes(value, value, value, value, value);
CAMLextern value caml_blit_string(value, value, value, value, value);
CAMLextern value caml_array_set(value, value, value);
CAMLextern value caml_array_unsafe_set(value, value, value);
CAMLextern value caml_floatarray_set(value, value, value);
CAMLextern value caml_floatarray_unsafe_set(value, value, value);
CAMLextern value caml_gc_minor(value);
CAMLextern value caml_gc_major(value);
CAMLextern value caml_gc_full_major(value);
CAMLextern value caml_gc_compaction(value);

/* Wrappers live in their own section, so that the pass can recognise a
   wrapper target at an indirect call by its address. */
#define WRAPPER \
  __attribute__((section("fides_wrap_text"), visibility("hidden"), used))

#define VAL(v, fn)  caml_fides_demote((v), "pass a value to " #fn)
#define PTR(p, fn)  caml_fides_load_arg((p), "pass a pointer to " #fn)

/* The values of an array argument (caml_callbackN, caml_raise_with_args),
   each read through the load check and checked, into [buf]. */
static void vals(value *buf, value *args, int n, const char *action)
{
  for (int i = 0; i < n; i++) {
    value *p = caml_fides_load_arg(&args[i], action);
    buf[i] = caml_fides_demote(*p, action);
  }
}

/* ---------------------------------------------------------------------- */
/* Reading a value                                                        */

WRAPPER mlsize_t caml_fides_w_caml_string_length(value s)
{ return caml_string_length(VAL(s, caml_string_length)); }

WRAPPER int caml_fides_w_caml_string_is_c_safe(value s)
{ return caml_string_is_c_safe(VAL(s, caml_string_is_c_safe)); }

WRAPPER mlsize_t caml_fides_w_caml_array_length(value a)
{ return caml_array_length(VAL(a, caml_array_length)); }

/* The result points into the runtime's own table: bare, so C may read the
   closure through it but not write (D3). */
WRAPPER const value *caml_fides_w_caml_named_value(char const *name)
{ return caml_named_value(PTR(name, caml_named_value)); }

WRAPPER value caml_fides_w_caml_hash_variant(char const *tag)
{ return caml_hash_variant(PTR(tag, caml_hash_variant)); }

/* ---------------------------------------------------------------------- */
/* GC primitives                                                          */

WRAPPER value caml_fides_w_caml_gc_minor(value v)
{ return caml_gc_minor(VAL(v, caml_gc_minor)); }

WRAPPER value caml_fides_w_caml_gc_major(value v)
{ return caml_gc_major(VAL(v, caml_gc_major)); }

WRAPPER value caml_fides_w_caml_gc_full_major(value v)
{ return caml_gc_full_major(VAL(v, caml_gc_full_major)); }

WRAPPER value caml_fides_w_caml_gc_compaction(value v)
{ return caml_gc_compaction(VAL(v, caml_gc_compaction)); }

/* ---------------------------------------------------------------------- */
/* Callbacks                                                              */

/* The closure and each argument are checked and stripped. Open question E
   (whether a callback also revokes its arguments' entries, as the model's
   demoteArg does) waits for the PI; until then nothing is revoked. The
   result reaches C bare. An array of arguments is copied into a buffer in
   this trusted frame. The real caml_callbackN_exn roots what it still needs
   (the arguments after the first three, with Begin_roots_block,
   callback.c:280); the first three are passed on before any allocation. */

WRAPPER value caml_fides_w_caml_callback(value f, value a)
{ return caml_callback(VAL(f, caml_callback), VAL(a, caml_callback)); }

WRAPPER value caml_fides_w_caml_callback2(value f, value a, value b)
{
  return caml_callback2(VAL(f, caml_callback2), VAL(a, caml_callback2),
                        VAL(b, caml_callback2));
}

WRAPPER value caml_fides_w_caml_callback3(value f, value a, value b, value c)
{
  return caml_callback3(VAL(f, caml_callback3), VAL(a, caml_callback3),
                        VAL(b, caml_callback3), VAL(c, caml_callback3));
}

WRAPPER value caml_fides_w_caml_callbackN(value f, int n, value args[])
{
  value buf[n > 0 ? n : 1];
  vals(buf, args, n, "pass a value to caml_callbackN");
  return caml_callbackN(VAL(f, caml_callbackN), n, buf);
}

WRAPPER value caml_fides_w_caml_callback_exn(value f, value a)
{ return caml_callback_exn(VAL(f, caml_callback_exn), VAL(a, caml_callback_exn)); }

WRAPPER value caml_fides_w_caml_callback2_exn(value f, value a, value b)
{
  return caml_callback2_exn(VAL(f, caml_callback2_exn),
                            VAL(a, caml_callback2_exn),
                            VAL(b, caml_callback2_exn));
}

WRAPPER value caml_fides_w_caml_callback3_exn(value f, value a, value b,
                                              value c)
{
  return caml_callback3_exn(VAL(f, caml_callback3_exn),
                            VAL(a, caml_callback3_exn),
                            VAL(b, caml_callback3_exn),
                            VAL(c, caml_callback3_exn));
}

WRAPPER value caml_fides_w_caml_callbackN_exn(value f, int n, value args[])
{
  value buf[n > 0 ? n : 1];
  vals(buf, args, n, "pass a value to caml_callbackN_exn");
  return caml_callbackN_exn(VAL(f, caml_callbackN_exn), n, buf);
}

WRAPPER caml_result caml_fides_w_caml_callback_res(value f, value a)
{ return caml_callback_res(VAL(f, caml_callback_res), VAL(a, caml_callback_res)); }

WRAPPER caml_result caml_fides_w_caml_callback2_res(value f, value a, value b)
{
  return caml_callback2_res(VAL(f, caml_callback2_res),
                            VAL(a, caml_callback2_res),
                            VAL(b, caml_callback2_res));
}

WRAPPER caml_result caml_fides_w_caml_callback3_res(value f, value a, value b,
                                                    value c)
{
  return caml_callback3_res(VAL(f, caml_callback3_res),
                            VAL(a, caml_callback3_res),
                            VAL(b, caml_callback3_res),
                            VAL(c, caml_callback3_res));
}

WRAPPER caml_result caml_fides_w_caml_callbackN_res(value f, int n,
                                                    value args[])
{
  value buf[n > 0 ? n : 1];
  vals(buf, args, n, "pass a value to caml_callbackN_res");
  return caml_callbackN_res(VAL(f, caml_callbackN_res), n, buf);
}

/* ---------------------------------------------------------------------- */
/* Field stores (D15)                                                     */

/* The model's StoreFieldRuntimeContract (Data/RuntimeCall.lean): the store
   changes one field of a block, and only memory C already had authority
   over; D55's storeFieldValueOk: the value is an immediate or a pointer to
   an OCaml block, stored demoted.

   - Destination in a scannable OCaml block: C may not store there itself
     (D43), but this is the trusted path for exactly such stores. So: the
     access check alone (C holds the block, the field is in it), D10 (never
     into OCaml static data), the field boundary, then the real function on
     the bare address, which applies the write barrier.
   - Any other destination (a no-scan OCaml block, C memory): the full store
     check, as if C stored there itself, then a plain store. C could have made
     that store directly, so allowing it here grants nothing.
   - A bare destination authorises nothing (D3): it traps either way. */
static void store_field(volatile value *fp, value v, int init,
                        const char *dest_action, const char *value_action)
{
  uintptr_t w = (uintptr_t)fp, a;
  uint32_t i = Fides_index(w);
  const struct fides_entry *e = caml_fides_entry(i);
  int cause;
  if (i != 0 && e->cookie != 0
      && (e->kind == FIDES_KIND_OCAML || e->kind == FIDES_KIND_OCAML_STATIC)
      && Fides_block_tag(e->base) < FIDES_NO_SCAN_TAG) {
    cause = caml_fides_access_cause(w, sizeof(value), &a);
    if (cause < 0 && e->kind == FIDES_KIND_OCAML_STATIC)
      cause = FIDES_OCAML_STATIC_WRITE;
    if (cause < 0 && (a - e->base) % sizeof(value) != 0)
      cause = FIDES_FIELD_MISALIGNED;
    if (cause >= 0)
      caml_fides_trap((enum fides_cause)cause, dest_action, w, sizeof(value),
                      NULL);
    value raw = caml_fides_demote(v, value_action);
    if (init) caml_initialize((volatile value *)a, raw);
    else caml_modify((volatile value *)a, raw);
    return;
  }
  cause = caml_fides_store_cause(w, sizeof(value), &a);
  if (cause >= 0)
    caml_fides_trap((enum fides_cause)cause, dest_action, w, sizeof(value),
                    NULL);
  *(volatile value *)a = caml_fides_demote(v, value_action);
}

WRAPPER void caml_fides_w_caml_modify(volatile value *fp, value v)
{
  store_field(fp, v, 0, "caml_modify of a field",
              "store a value with caml_modify");
}

WRAPPER void caml_fides_w_caml_initialize(volatile value *fp, value v)
{
  store_field(fp, v, 1, "caml_initialize of a field",
              "store a value with caml_initialize");
}

/* ---------------------------------------------------------------------- */
/* Allocation (D16)                                                       */

/* The new block reaches C tagged (caml_fides_own_fresh). Arguments that the
   real function stores into it are checked and stored bare. */
#define FRESH(v) caml_fides_own_fresh(v)

WRAPPER value caml_fides_w_caml_alloc(mlsize_t n, tag_t tag)
{ return FRESH(caml_alloc(n, tag)); }

/* caml_alloc_small leaves the fields uninitialised. The frame roots the
   block as soon as it is minted, so a collection before C initialises it
   would trace whatever the minor heap held there: the wrapper fills the
   fields with Val_unit first, as caml_alloc does. */
WRAPPER value caml_fides_w_caml_alloc_small(mlsize_t n, tag_t tag)
{
  value v = caml_alloc_small(n, tag);
  if (tag < No_scan_tag)
    for (mlsize_t i = 0; i < n; i++) Field(v, i) = Val_unit;
  return FRESH(v);
}

WRAPPER value caml_fides_w_caml_alloc_tuple(mlsize_t n)
{ return FRESH(caml_alloc_tuple(n)); }

WRAPPER value caml_fides_w_caml_alloc_string(mlsize_t len)
{ return FRESH(caml_alloc_string(len)); }

WRAPPER value caml_fides_w_caml_alloc_initialized_string(mlsize_t len,
                                                         const char *p)
{
  return FRESH(caml_alloc_initialized_string(
      len, PTR(p, caml_alloc_initialized_string)));
}

WRAPPER value caml_fides_w_caml_alloc_float_array(mlsize_t len)
{ return FRESH(caml_alloc_float_array(len)); }

#define A(v, fn) VAL(v, fn)
WRAPPER value caml_fides_w_caml_alloc_1(tag_t t, value a)
{ return FRESH(caml_alloc_1(t, A(a, caml_alloc_1))); }

WRAPPER value caml_fides_w_caml_alloc_2(tag_t t, value a, value b)
{ return FRESH(caml_alloc_2(t, A(a, caml_alloc_2), A(b, caml_alloc_2))); }

WRAPPER value caml_fides_w_caml_alloc_3(tag_t t, value a, value b, value c)
{
  return FRESH(caml_alloc_3(t, A(a, caml_alloc_3), A(b, caml_alloc_3),
                            A(c, caml_alloc_3)));
}

WRAPPER value caml_fides_w_caml_alloc_4(tag_t t, value a, value b, value c,
                                        value d)
{
  return FRESH(caml_alloc_4(t, A(a, caml_alloc_4), A(b, caml_alloc_4),
                            A(c, caml_alloc_4), A(d, caml_alloc_4)));
}

WRAPPER value caml_fides_w_caml_alloc_5(tag_t t, value a, value b, value c,
                                        value d, value e)
{
  return FRESH(caml_alloc_5(t, A(a, caml_alloc_5), A(b, caml_alloc_5),
                            A(c, caml_alloc_5), A(d, caml_alloc_5),
                            A(e, caml_alloc_5)));
}

WRAPPER value caml_fides_w_caml_alloc_6(tag_t t, value a, value b, value c,
                                        value d, value e, value f)
{
  return FRESH(caml_alloc_6(t, A(a, caml_alloc_6), A(b, caml_alloc_6),
                            A(c, caml_alloc_6), A(d, caml_alloc_6),
                            A(e, caml_alloc_6), A(f, caml_alloc_6)));
}

WRAPPER value caml_fides_w_caml_alloc_7(tag_t t, value a, value b, value c,
                                        value d, value e, value f, value g)
{
  return FRESH(caml_alloc_7(t, A(a, caml_alloc_7), A(b, caml_alloc_7),
                            A(c, caml_alloc_7), A(d, caml_alloc_7),
                            A(e, caml_alloc_7), A(f, caml_alloc_7),
                            A(g, caml_alloc_7)));
}

WRAPPER value caml_fides_w_caml_alloc_8(tag_t t, value a, value b, value c,
                                        value d, value e, value f, value g,
                                        value h)
{
  return FRESH(caml_alloc_8(t, A(a, caml_alloc_8), A(b, caml_alloc_8),
                            A(c, caml_alloc_8), A(d, caml_alloc_8),
                            A(e, caml_alloc_8), A(f, caml_alloc_8),
                            A(g, caml_alloc_8), A(h, caml_alloc_8)));
}

WRAPPER value caml_fides_w_caml_alloc_9(tag_t t, value a, value b, value c,
                                        value d, value e, value f, value g,
                                        value h, value i)
{
  return FRESH(caml_alloc_9(t, A(a, caml_alloc_9), A(b, caml_alloc_9),
                            A(c, caml_alloc_9), A(d, caml_alloc_9),
                            A(e, caml_alloc_9), A(f, caml_alloc_9),
                            A(g, caml_alloc_9), A(h, caml_alloc_9),
                            A(i, caml_alloc_9)));
}

WRAPPER value caml_fides_w_caml_alloc_some(value a)
{ return FRESH(caml_alloc_some(A(a, caml_alloc_some))); }

WRAPPER value caml_fides_w_caml_copy_string(char const *s)
{ return FRESH(caml_copy_string(PTR(s, caml_copy_string))); }

WRAPPER value caml_fides_w_caml_copy_double(double d)
{ return FRESH(caml_copy_double(d)); }

WRAPPER value caml_fides_w_caml_copy_int32(int32_t i)
{ return FRESH(caml_copy_int32(i)); }

WRAPPER value caml_fides_w_caml_copy_int64(int64_t i)
{ return FRESH(caml_copy_int64(i)); }

WRAPPER value caml_fides_w_caml_copy_nativeint(intnat i)
{ return FRESH(caml_copy_nativeint(i)); }

/* The runtime keeps the operations' address in the block (its method
   suite, which C may not overwrite: ocamlMethodSuite), so it gets the
   decoded address. */
WRAPPER value caml_fides_w_caml_alloc_custom(const struct custom_operations *ops,
                                             uintnat size, mlsize_t mem,
                                             mlsize_t max)
{
  return FRESH(caml_alloc_custom(PTR(ops, caml_alloc_custom), size, mem, max));
}

WRAPPER value caml_fides_w_caml_alloc_custom_mem(
    const struct custom_operations *ops, uintnat size, mlsize_t mem)
{
  return FRESH(caml_alloc_custom_mem(PTR(ops, caml_alloc_custom_mem), size,
                                     mem));
}

/* Arrays of C strings (caml_copy_string_array, caml_alloc_array). The real
   functions cannot be called: they would read the array and the strings
   through tagged pointers, and store whatever the converter returns
   (tagged, if the converter is sanitized C) into the new block. So the loop
   is redone here, after alloc.c: each element pointer is read through the
   load check, the converter is called the way the pass would call it, and
   its result is checked and stored bare.

   [funct] is what sanitized C passed: a wrapper (when it named a listed C API
   function, e.g. caml_copy_string), sanitized C, or other code. */
static void *real_of_wrapper(void *fn)
{
  for (size_t k = 0; k < caml_fides_api_count; k++)
    if (caml_fides_api_table[k].wrapper == fn) return caml_fides_api_table[k].real;
  return NULL;
}

static value alloc_array(value (*funct)(char const *),
                         char const *const *arr, const char *action)
{
  CAMLparam0();
  CAMLlocal2(v, result);
  mlsize_t n = 0;
  while (*(char const *const *)caml_fides_load_arg(&arr[n], action) != NULL) n++;
  result = caml_alloc(n, 0);
  value (*real)(char const *) = (value (*)(char const *))real_of_wrapper((void *)funct);
  int sanitized = caml_fides_in_sanitized_c((void *)funct);
  for (mlsize_t i = 0; i < n; i++) {
    char const *elem = *(char const *const *)caml_fides_load_arg(&arr[i], action);
    if (real != NULL) v = real(caml_fides_load_arg(elem, action));
    else if (sanitized) v = funct(elem);       /* sanitized C takes tagged */
    else v = funct(caml_fides_load_arg(elem, action));
    v = caml_fides_demote(v, action);
    caml_modify(&Field(result, i), v);
  }
  CAMLreturn(FRESH(result));
}

WRAPPER value caml_fides_w_caml_copy_string_array(char const *const *arr)
{
  return alloc_array(caml_copy_string, arr,
                     "pass a string array to caml_copy_string_array");
}

WRAPPER value caml_fides_w_caml_alloc_array(value (*funct)(char const *),
                                            char const *const *arr)
{
  return alloc_array(funct, arr, "pass an array to caml_alloc_array");
}

/* The pass decodes variadic pointer arguments (they would reach libc's
   formatter unchecked otherwise), so only the format is checked here. %n,
   which writes through its argument, is the libc gap of section 4. */
WRAPPER value caml_fides_w_caml_alloc_sprintf(const char *format, ...)
{
  const char *f = PTR(format, caml_alloc_sprintf);
  va_list ap, ap2;
  va_start(ap, format);
  va_copy(ap2, ap);
  int n = vsnprintf(NULL, 0, f, ap);
  va_end(ap);
  if (n < 0) n = 0;
  value res = caml_alloc_string(n);   /* OCaml strings keep a byte after n */
  vsnprintf((char *)Bytes_val(res), (size_t)n + 1, f, ap2);
  va_end(ap2);
  return FRESH(res);
}

/* ---------------------------------------------------------------------- */
/* Primitives that write into a block C names (D17)                       */

/* The model's runtime-service contract: the service changes only memory C
   already had authority over (TrustedRuntimeCall.writes). These primitives
   write into the block their first value argument names, so C must hold
   that block: a tagged word naming a live OCaml block (a bare word
   authorises nothing, D3), never static data (D10), and, for the byte
   primitives, a block C may write bytes into (no-scan, D43).

   Primitives that check their own index (caml_bytes_set, caml_array_set...)
   keep doing so, so an index out of range still raises Invalid_argument as
   in OCaml: the wrapper checks C's authority over the whole block, which
   bounds the write. Primitives that do not check (caml_fill_bytes,
   caml_blit_*, the unsafe setters) get the exact range checked here. */

/* C holds the whole block [b] and may write it with plain stores (D43).
   Returns the bare block. */
static value writable_block(value b, const char *action)
{
  uintptr_t a;
  int cause;
  if (Is_long(b) || Fides_index((uintptr_t)b) == 0) {
    cause = FIDES_ACCESS_BOUNDS;
  } else {
    const struct fides_entry *e = caml_fides_entry(Fides_index((uintptr_t)b));
    cause = caml_fides_store_cause((uintptr_t)b, e->size, &a);
  }
  if (cause >= 0) caml_fides_trap((enum fides_cause)cause, action, (uintptr_t)b, 0, NULL);
  return caml_fides_demote(b, action);
}

/* May C write [n] bytes at byte offset [ofs] of block [b]? The range is
   checked against b's own entry by subtraction. Adding [ofs] to the tagged
   word instead would let a large offset carry into the cookie or index bits
   and check a different entry from the block the real primitive writes
   (docs: Known bugs 13). [rules]: also apply the write restriction (D43) and
   D10, as for a store C makes itself; without it, only D10 (the caml_modify
   rule, D15). */
static int range_cause(value b, uintnat ofs, uintnat n, int rules)
{
  uint32_t i = Fides_index((uintptr_t)b);
  if (Is_long(b) || i == 0) return FIDES_ACCESS_BOUNDS;
  const struct fides_entry *e = caml_fides_entry(i);
  if (e->cookie == 0) return FIDES_ACCESS_BOUNDS;
  if (e->cookie != Fides_cookie((uintptr_t)b)) return FIDES_ACCESS_COOKIE;
  uintptr_t start = __fides_decode((uintptr_t)b);
  if (start < e->base) return FIDES_ACCESS_BOUNDS;
  uintptr_t so = start - e->base;
  if (so > e->size || ofs > e->size - so || n > e->size - so - ofs)
    return FIDES_ACCESS_BOUNDS;
  if (e->kind == FIDES_KIND_OCAML_STATIC) return FIDES_OCAML_STATIC_WRITE;
  if (rules && e->kind == FIDES_KIND_OCAML) {
    uint8_t tag = Fides_block_tag(e->base);
    if (tag < FIDES_NO_SCAN_TAG) return FIDES_OCAML_SCANNABLE_WRITE;
    if (tag == FIDES_CUSTOM_TAG && so + ofs == 0) return FIDES_OCAML_METHOD_SUITE;
  }
  return -1;
}

/* C may store [n] bytes at [ofs] into block [b] (the full store check). */
static value writable_range(value b, intnat ofs, intnat n, const char *action)
{
  if (n <= 0) return caml_fides_demote(b, action);
  int cause = ofs < 0 ? FIDES_ACCESS_BOUNDS
                      : range_cause(b, (uintnat)ofs, (uintnat)n, 1);
  if (cause >= 0) caml_fides_trap((enum fides_cause)cause, action, (uintptr_t)b, (size_t)n, NULL);
  return caml_fides_demote(b, action);
}

/* An element of an array C holds: for a float array, as writable_*; for an
   array of values, the caml_modify rule (D15): C holds the block, never
   static data, and the stored value is checked and demoted. */
static value array_holder(value a, const char *action)
{
  if (!Is_long(a) && Fides_index((uintptr_t)a) != 0) {
    const struct fides_entry *e = caml_fides_entry(Fides_index((uintptr_t)a));
    if (e->cookie != 0 && e->kind == FIDES_KIND_OCAML
        && Fides_block_tag(e->base) < FIDES_NO_SCAN_TAG) {
      uintptr_t ad;
      int cause = caml_fides_access_cause((uintptr_t)a, e->size, &ad);
      if (cause >= 0) caml_fides_trap((enum fides_cause)cause, action, (uintptr_t)a, 0, NULL);
      return caml_fides_demote(a, action);
    }
  }
  return writable_block(a, action);     /* float arrays, static data, bare */
}

#define WB(b, fn) writable_block((b), "write into a block with " #fn)

WRAPPER value caml_fides_w_caml_bytes_set(value s, value i, value c)
{ return caml_bytes_set(WB(s, caml_bytes_set), i, c); }

WRAPPER value caml_fides_w_caml_string_set(value s, value i, value c)
{ return caml_string_set(WB(s, caml_string_set), i, c); }

WRAPPER value caml_fides_w_caml_bytes_set16(value s, value i, value c)
{ return caml_bytes_set16(WB(s, caml_bytes_set16), i, c); }

WRAPPER value caml_fides_w_caml_bytes_set32(value s, value i, value c)
{ return caml_bytes_set32(WB(s, caml_bytes_set32), i, VAL(c, caml_bytes_set32)); }

WRAPPER value caml_fides_w_caml_bytes_set64(value s, value i, value c)
{ return caml_bytes_set64(WB(s, caml_bytes_set64), i, VAL(c, caml_bytes_set64)); }

WRAPPER value caml_fides_w_caml_fill_bytes(value s, value ofs, value len, value c)
{
  return caml_fill_bytes(writable_range(s, Long_val(ofs), Long_val(len),
                                        "write into a block with caml_fill_bytes"),
                         ofs, len, c);
}

WRAPPER value caml_fides_w_caml_blit_bytes(value s1, value o1, value s2, value o2,
                                           value n)
{
  value src = VAL(s1, caml_blit_bytes);
  value dst = writable_range(s2, Long_val(o2), Long_val(n),
                             "write into a block with caml_blit_bytes");
  return caml_blit_bytes(src, o1, dst, o2, n);
}

WRAPPER value caml_fides_w_caml_blit_string(value s1, value o1, value s2, value o2,
                                            value n)
{
  value src = VAL(s1, caml_blit_string);
  value dst = writable_range(s2, Long_val(o2), Long_val(n),
                             "write into a block with caml_blit_string");
  return caml_blit_string(src, o1, dst, o2, n);
}

WRAPPER value caml_fides_w_caml_array_set(value a, value i, value v)
{
  value arr = array_holder(a, "write into a block with caml_array_set");
  return caml_array_set(arr, i, VAL(v, caml_array_set));
}

WRAPPER value caml_fides_w_caml_floatarray_set(value a, value i, value v)
{
  return caml_floatarray_set(WB(a, caml_floatarray_set), i, VAL(v, caml_floatarray_set));
}

/* The unsafe setters do not check the index: the element itself must lie
   in the block C holds. */
WRAPPER value caml_fides_w_caml_array_unsafe_set(value a, value i, value v)
{
  const char *act = "write into a block with caml_array_unsafe_set";
  value arr = array_holder(a, act);
  intnat idx = Long_val(i);
  int cause = (idx < 0 || (uintnat)idx > SIZE_MAX / sizeof(value))
              ? FIDES_ACCESS_BOUNDS
              : range_cause(a, (uintnat)idx * sizeof(value), sizeof(value), 0);
  if (cause >= 0)
    caml_fides_trap((enum fides_cause)cause, act, (uintptr_t)a, sizeof(value), NULL);
  return caml_array_unsafe_set(arr, i, VAL(v, caml_array_unsafe_set));
}

WRAPPER value caml_fides_w_caml_floatarray_unsafe_set(value a, value i, value v)
{
  intnat idx = Long_val(i);
  const char *act = "write into a block with caml_floatarray_unsafe_set";
  if (idx < 0 || (uintnat)idx > SIZE_MAX / sizeof(double))
    caml_fides_trap(FIDES_ACCESS_BOUNDS, act, (uintptr_t)a, sizeof(double), NULL);
  value arr = writable_range(a, idx * (intnat)sizeof(double), sizeof(double), act);
  return caml_floatarray_unsafe_set(arr, i, VAL(v, caml_floatarray_unsafe_set));
}

/* ---------------------------------------------------------------------- */
/* Raising                                                                */

CAMLnoret WRAPPER void caml_fides_w_caml_raise(value e)
{ caml_raise(VAL(e, caml_raise)); }

CAMLnoret WRAPPER void caml_fides_w_caml_raise_constant(value tag)
{ caml_raise_constant(VAL(tag, caml_raise_constant)); }

CAMLnoret WRAPPER void caml_fides_w_caml_raise_with_arg(value tag, value arg)
{
  caml_raise_with_arg(VAL(tag, caml_raise_with_arg),
                      VAL(arg, caml_raise_with_arg));
}

CAMLnoret WRAPPER void caml_fides_w_caml_raise_with_args(value tag, int n,
                                                        value args[])
{
  value buf[n > 0 ? n : 1];
  vals(buf, args, n, "pass a value to caml_raise_with_args");
  caml_raise_with_args(VAL(tag, caml_raise_with_args), n, buf);
}

CAMLnoret WRAPPER void caml_fides_w_caml_raise_with_string(value tag,
                                                          char const *msg)
{
  caml_raise_with_string(VAL(tag, caml_raise_with_string),
                         PTR(msg, caml_raise_with_string));
}

CAMLnoret WRAPPER void caml_fides_w_caml_failwith_value(value msg)
{ caml_failwith_value(VAL(msg, caml_failwith_value)); }

CAMLnoret WRAPPER void caml_fides_w_caml_invalid_argument_value(value msg)
{ caml_invalid_argument_value(VAL(msg, caml_invalid_argument_value)); }

CAMLnoret WRAPPER void caml_fides_w_caml_raise_sys_error(value msg)
{ caml_raise_sys_error(VAL(msg, caml_raise_sys_error)); }

/* ---------------------------------------------------------------------- */
/* The table: each wrapper's type is checked against the real function's,
   and the pair is recorded for the indirect-call lookup (Stage 4,
   increment 6). */

#define FIDES_WRAP(name)                                                 \
  _Static_assert(__builtin_types_compatible_p(__typeof__(name),          \
                                              __typeof__(caml_fides_w_##name)), \
                 "the wrapper of " #name " has a different type");
#include "caml/fides_api.def"

#define FIDES_WRAP(name) { (void *)&name, (void *)&caml_fides_w_##name, #name },
const struct caml_fides_api_entry caml_fides_api_table[] = {
#include "caml/fides_api.def"
};
const size_t caml_fides_api_count =
  sizeof caml_fides_api_table / sizeof caml_fides_api_table[0];
