/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*   FIDES software sanitizer: metadata table, fat pointers, checks.      */
/*   Rules follow Resources/model.pdf; see Implementation/DECISIONS.md.   */
/*                                                                        */
/**************************************************************************/

#ifndef CAML_FIDES_H
#define CAML_FIDES_H

#include <stddef.h>
#include <stdint.h>

/* A fat pointer is one word: Index 16 | Cookie 8 | low 40 address bits
   (DECISIONS.md D2). The top address bits come from the entry's Base.
   A raw x86-64 user pointer has bits 48-63 clear, so it decodes as index 0,
   which is never issued and authorises nothing (model §D.4.1). */
#define FIDES_ADDR_BITS    40
#define FIDES_ADDR_MASK    ((UINT64_C(1) << FIDES_ADDR_BITS) - 1)
#define FIDES_COOKIE_SHIFT 40
#define FIDES_INDEX_SHIFT  48
#define FIDES_TABLE_SIZE   65536

#define Fides_index(w)  ((uint32_t)((uint64_t)(w) >> FIDES_INDEX_SHIFT))
#define Fides_cookie(w) ((uint8_t)((uint64_t)(w) >> FIDES_COOKIE_SHIFT))
#define Fides_low(w)    ((uint64_t)(w) & FIDES_ADDR_MASK)
#define Fides_pack(i, k, a)                                    \
  (((uint64_t)(i) << FIDES_INDEX_SHIFT)                        \
   | ((uint64_t)(uint8_t)(k) << FIDES_COOKIE_SHIFT)            \
   | ((uint64_t)(a) & FIDES_ADDR_MASK))

/* Exit status of a program stopped by a FIDES trap (every trap is fatal,
   model §D.8). */
#define FIDES_EXIT 86

/* Trap causes. Names are those of model §C.5. */
enum fides_cause {
  FIDES_ACCESS_BOUNDS,
  FIDES_ACCESS_COOKIE,
  FIDES_FREE_BOUNDS,
  FIDES_FREE_COOKIE,
  FIDES_FREE_NOT_BASE,
  FIDES_FREE_OCAML_HEAP,
  FIDES_META_TABLE_FULL,
  FIDES_CALLBACK_NOT_OCAML_HEAP,
  /* D43, the write restriction (model §D.6.2 p.33): untrusted C may not
     write a scannable OCaml block, nor a custom block's method suite. */
  FIDES_OCAML_SCANNABLE_WRITE,
  FIDES_OCAML_METHOD_SUITE,
  /* D10: OCaml's static data is readable by C but never writable. The Lean
     has no cause for this, because it has no static data. */
  FIDES_OCAML_STATIC_WRITE
};

/* OCaml's own header constants, repeated here so this file builds without the
   OCaml headers (the unit tests compile the runtime library on its own).
   A block's header sits one word below it: wosize | colour | tag. */
#define FIDES_NO_SCAN_TAG 251
#define FIDES_CUSTOM_TAG  255
#define Fides_block_tag(base) ((uint8_t)(((const uintptr_t *)(base))[-1]))

/* What minted an entry. Only FIDES_KIND_OCAML matters to the rules
   (inOCamlHeap(Base), DECISIONS.md D8); the rest is for reports and for
   deciding which deallocator owns the memory. */
enum fides_kind {
  FIDES_KIND_DEAD = 0,
  FIDES_KIND_C_HEAP,      /* halloc: __fides_malloc and friends */
  FIDES_KIND_C_STACK,     /* salloc: address-taken C stack object */
  FIDES_KIND_C_GLOBAL,    /* a C global, or errno */
  FIDES_KIND_OCAML,       /* an OCaml heap block promoted at Extcall */
  FIDES_KIND_OCAML_STATIC /* D10: an OCaml block in the executable's data */
};

struct fides_entry {
  uintptr_t base;
  uintptr_t size;
  uint8_t cookie;         /* 0 means dead */
  uint8_t prev_cookie;    /* cookie of the previous owner, never re-issued */
  uint8_t kind;
};

#ifdef __GNUC__
#define CAMLfides_noreturn __attribute__((noreturn))
#else
#define CAMLfides_noreturn
#endif

/* Every function below is hidden: it links statically into the executable but
   is not exported (OCaml executables are linked with -Wl,-E), so C cannot
   reach it with dlsym. The pass rejects C that names it. */
#pragma GCC visibility push(hidden)

/* Decoding: the address a fat pointer denotes. Index 0 words are raw
   addresses and pass through unchanged. */
uintptr_t __fides_decode(uintptr_t w);
void *__fides_decode_ptr(void *p);

/* The access check on a store of [n] bytes through [p] (model accessCheck:
   accessBounds, then accessCookie). Returns the address to store to;
   traps otherwise. [site] is a "file:line:function" string or NULL. */
void *__fides_check_store(void *p, size_t n, const char *site);

/* halloc / hfree (model §D.4.2) for C heap objects. */
void *__fides_malloc(size_t n);
void *__fides_calloc(size_t nmemb, size_t size);
void *__fides_realloc(void *p, size_t n);
void __fides_free(void *p);

/* salloc / sfree for address-taken C stack objects (model D85). */
void *__fides_salloc(void *addr, size_t n);
void __fides_sfree(void *p);

/* Entries for C globals, live for the whole run (model §I.4). */
void *__fides_global(void *addr, size_t n);

/* errno, as a tagged pointer to a permanent entry (DECISIONS.md D3). */
int *__fides_errno_location(void);

/* Mint an entry; used by the runtime for promotion. Traps metaTableFull. */
uintptr_t caml_fides_mint(uintptr_t base, uintptr_t size, enum fides_kind kind);
/* Zero the entry a word names, if that word still validates against it. */
void caml_fides_release(uintptr_t w);
/* Zero an entry by index. The caller is trusted runtime code. */
void caml_fides_release_index(uint32_t index);
/* Read-only view of an entry, for tests and reports. */
const struct fides_entry *caml_fides_entry(uint32_t index);

/* Does [w] name a live entry whose cookie it carries? A bare word (index 0)
   is not valid: it authorises nothing (model §D.4.1). */
int caml_fides_valid(uintptr_t w);


/* Report a trap and stop the program; every trap is fatal (model §D.8).
   [action] is a short phrase such as "store"; [n] may be 0; [site] may be
   NULL. */
CAMLfides_noreturn
void caml_fides_trap(enum fides_cause cause, const char *action, uintptr_t w,
                     size_t n, const char *site);

#pragma GCC visibility pop

#endif /* CAML_FIDES_H */
