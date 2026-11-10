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
#include "caml/fides_ffi.h"
#include "caml/fides.h"

/* Primitives that stubs call directly but that no public header declares. */
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
   this trusted frame: the real function roots it (CAMLxparamN). */

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
