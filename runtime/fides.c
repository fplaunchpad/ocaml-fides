/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*   FIDES software sanitizer: metadata table, fat pointers, checks.      */
/*   Rules follow Resources/model.pdf; see Implementation/DECISIONS.md.   */
/*                                                                        */
/**************************************************************************/

/* The security monitor of the FIDES design, as trusted runtime code.
   This file is part of the trusted side (D30): it is never instrumented,
   and the table below is covered by no entry, so a checked store cannot
   reach it (model §D.4.1, no_access_touches_the_table).

   Single-threaded only (model §I.1). */

#define _GNU_SOURCE
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#ifdef __linux__
#include <sys/random.h>
#endif

#include "caml/fides.h"

/* The metadata table T. Index 0 is never issued and stays zeroed, so a
   word with index 0 (any raw address) authorises nothing. */
static struct fides_entry table[FIDES_TABLE_SIZE];

/* Dead indices, oldest first (DECISIONS.md D7): a freed index goes to the
   back, so it is re-issued as late as possible. */
static uint16_t free_queue[FIDES_TABLE_SIZE];
static uint32_t queue_head, queue_count;

static uint64_t prng_state;
static int ready;

static void init(void)
{
  if (ready) return;
  for (uint32_t i = 1; i < FIDES_TABLE_SIZE; i++) free_queue[i - 1] = i;
  queue_head = 0;
  queue_count = FIDES_TABLE_SIZE - 1;
#ifdef __linux__
  if (getrandom(&prng_state, sizeof prng_state, 0) != sizeof prng_state)
#endif
    prng_state = (uint64_t)time(NULL) ^ ((uint64_t)getpid() << 32)
                 ^ (uint64_t)(uintptr_t)&prng_state;
  ready = 1;
}

/* splitmix64 */
static uint64_t next_random(void)
{
  uint64_t z = (prng_state += UINT64_C(0x9E3779B97F4A7C15));
  z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
  z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
  return z ^ (z >> 31);
}

/* A cookie is never 0 (0 marks a dead entry) and never the cookie the
   index had before, so the previous owner's pointers always fail. */
static uint8_t fresh_cookie(uint8_t previous)
{
  uint8_t c;
  do c = (uint8_t)next_random(); while (c == 0 || c == previous);
  return c;
}

/* ---------------------------------------------------------------------- */
/* Reports. Every trap is fatal (model §D.8).                             */

static const char *const cause_names[] = {
  "accessBounds", "accessCookie", "freeBounds", "freeCookie",
  "freeNotBase", "freeOCamlHeap", "metaTableFull", "callbackNotOCamlHeap",
  "ocamlScannableWrite", "ocamlMethodSuite", "ocamlStaticWrite"
};

static const char *const kind_names[] = {
  "dead", "C heap", "C stack", "C global", "OCaml block", "OCaml static data"
};

static void report_entry(char *buf, size_t size, int *len, uint32_t i)
{
  const struct fides_entry *e = &table[i];
  if (i == 0)
    *len += snprintf(buf + *len, size - *len,
                     "  entry:   none (index 0: a bare address authorises "
                     "nothing)\n");
  else if (e->cookie == 0)
    *len += snprintf(buf + *len, size - *len,
                     "  entry:   %u is dead (freed or never issued)\n", i);
  else
    *len += snprintf(buf + *len, size - *len,
                     "  entry:   %u: base 0x%012lx, size %lu, cookie 0x%02x, "
                     "%s\n", i, (unsigned long)e->base,
                     (unsigned long)e->size, e->cookie, kind_names[e->kind]);
}

void caml_fides_trap(enum fides_cause cause, const char *action,
                     uintptr_t w, size_t n, const char *site)
{
  char buf[1024];
  int len = 0;
  uint32_t i = Fides_index(w);
  len += snprintf(buf + len, sizeof buf - len, "FIDES trap: %s\n",
                  cause_names[cause]);
  if (site != NULL)
    len += snprintf(buf + len, sizeof buf - len, "  site:    %s\n", site);
  if (n > 0)
    len += snprintf(buf + len, sizeof buf - len, "  action:  %s of %lu bytes\n",
                    action, (unsigned long)n);
  else
    len += snprintf(buf + len, sizeof buf - len, "  action:  %s\n", action);
  if (i == 0)
    len += snprintf(buf + len, sizeof buf - len,
                    "  pointer: 0x%016lx (bare)\n", (unsigned long)w);
  else
    len += snprintf(buf + len, sizeof buf - len,
                    "  pointer: 0x%016lx (index %u, cookie 0x%02x, low "
                    "address 0x%010lx)\n", (unsigned long)w, i,
                    Fides_cookie(w), (unsigned long)Fides_low(w));
  report_entry(buf, sizeof buf, &len, i);
  if (len > (int)sizeof buf) len = sizeof buf;
  (void)!write(STDERR_FILENO, buf, len);
  _exit(FIDES_EXIT);
}

static void internal_error(const char *msg, uintptr_t base, uintptr_t size)
  __attribute__((noreturn));

static void internal_error(const char *msg, uintptr_t base, uintptr_t size)
{
  char buf[256];
  int len = snprintf(buf, sizeof buf,
                     "FIDES internal error: %s (base 0x%012lx, size %lu)\n",
                     msg, (unsigned long)base, (unsigned long)size);
  if (len > (int)sizeof buf) len = sizeof buf;
  (void)!write(STDERR_FILENO, buf, len);
  _exit(FIDES_EXIT);
}

/* ---------------------------------------------------------------------- */
/* Entries                                                                */

/* The pointer keeps only the low 40 address bits; the rest come from the
   entry's Base. So no object may cross a 2^40 boundary (D2). */
static int straddles(uintptr_t base, uintptr_t size)
{
  return size > 0 && (base >> FIDES_ADDR_BITS)
                     != ((base + size - 1) >> FIDES_ADDR_BITS);
}

uintptr_t caml_fides_mint(uintptr_t base, uintptr_t size,
                          enum fides_kind kind)
{
  init();
  if (queue_count == 0)
    caml_fides_trap(FIDES_META_TABLE_FULL, "allocate a metadata entry",
                    base, size, NULL);
  if (straddles(base, size))
    internal_error("object crosses a 2^40 boundary", base, size);
  uint32_t i = free_queue[queue_head];
  queue_head = (queue_head + 1) % FIDES_TABLE_SIZE;
  queue_count--;
  struct fides_entry *e = &table[i];
  e->base = base;
  e->size = size;
  e->kind = kind;
  e->cookie = fresh_cookie(e->prev_cookie);
  return Fides_pack(i, e->cookie, base);
}

static void release_index(uint32_t i)
{
  struct fides_entry *e = &table[i];
  e->prev_cookie = e->cookie;
  e->cookie = 0;
  e->base = 0;
  e->size = 0;
  e->kind = FIDES_KIND_DEAD;
  free_queue[(queue_head + queue_count) % FIDES_TABLE_SIZE] = (uint16_t)i;
  queue_count++;
}

void caml_fides_release(uintptr_t w)
{
  if (caml_fides_valid(w))
    release_index(Fides_index(w));
}

void caml_fides_release_index(uint32_t index)
{
  if (index != 0 && index < FIDES_TABLE_SIZE && table[index].cookie != 0)
    release_index(index);
}

int caml_fides_valid(uintptr_t w)
{
  uint32_t i = Fides_index(w);
  return i != 0 && table[i].cookie != 0 && table[i].cookie == Fides_cookie(w);
}

const struct fides_entry *caml_fides_entry(uint32_t index)
{
  return index < FIDES_TABLE_SIZE ? &table[index] : NULL;
}

/* ---------------------------------------------------------------------- */
/* Decoding and the access check                                          */

uintptr_t __fides_decode(uintptr_t w)
{
  uint32_t i = Fides_index(w);
  if (i == 0) return w;
  return (table[i].base & ~FIDES_ADDR_MASK) | Fides_low(w);
}

void *__fides_decode_ptr(void *p)
{
  return (void *)__fides_decode((uintptr_t)p);
}

/* The write restriction (D43, model §D.6.2 p.33), and D10 for static data.
   It runs only after the access check has passed, so the pointer is live, in
   bounds and correctly cookied; what it answers is whether untrusted code may
   write *this* OCaml block at all. The tag comes from the block's header, one
   word below its base. */
static void ocaml_write_check(const struct fides_entry *e, uintptr_t a,
                              uintptr_t w, size_t n, const char *site)
{
  uint8_t tag;
  if (e->kind == FIDES_KIND_OCAML_STATIC)
    caml_fides_trap(FIDES_OCAML_STATIC_WRITE, "store", w, n, site);
  tag = Fides_block_tag(e->base);
  if (tag < FIDES_NO_SCAN_TAG)
    caml_fides_trap(FIDES_OCAML_SCANNABLE_WRITE, "store", w, n, site);
  if (tag == FIDES_CUSTOM_TAG && a == e->base)
    caml_fides_trap(FIDES_OCAML_METHOD_SUITE, "store", w, n, site);
}

/* accessCheck (model §D.4): the whole access [a, a+n) must lie in the
   entry the pointer's own index names, and the cookies must match. A
   zero-width access touches no byte and is not checked. */
void *__fides_check_store(void *p, size_t n, const char *site)
{
  uintptr_t w = (uintptr_t)p;
  uint32_t i = Fides_index(w);
  const struct fides_entry *e = &table[i];
  uintptr_t a = (i == 0) ? w : ((e->base & ~FIDES_ADDR_MASK) | Fides_low(w));
  if (n == 0) return (void *)a;
  if (!(a >= e->base && n <= e->size && a - e->base <= e->size - n))
    caml_fides_trap(FIDES_ACCESS_BOUNDS, "store", w, n, site);
  if (e->cookie != Fides_cookie(w))
    caml_fides_trap(FIDES_ACCESS_COOKIE, "store", w, n, site);
  if (e->kind == FIDES_KIND_OCAML || e->kind == FIDES_KIND_OCAML_STATIC)
    ocaml_write_check(e, a, w, n, site);
  return (void *)a;
}

/* ---------------------------------------------------------------------- */
/* halloc / hfree (model §D.4.2)                                          */

/* malloc, retrying until the block does not cross a 2^40 boundary. A
   rejected block is kept (never freed), so the retry gets another one. */
static void *heap_alloc(size_t n, int zero)
{
  void *p = zero ? calloc(1, n ? n : 1) : malloc(n ? n : 1);
  for (int tries = 0; p != NULL && straddles((uintptr_t)p, n); tries++) {
    if (tries == 8) internal_error("cannot place an allocation",
                                   (uintptr_t)p, n);
    p = zero ? calloc(1, n) : malloc(n);
  }
  return p;
}

void *__fides_malloc(size_t n)
{
  void *p = heap_alloc(n, 0);
  if (p == NULL) return NULL;
  return (void *)caml_fides_mint((uintptr_t)p, n, FIDES_KIND_C_HEAP);
}

void *__fides_calloc(size_t nmemb, size_t size)
{
  if (size != 0 && nmemb > SIZE_MAX / size) {
    errno = ENOMEM;
    return NULL;
  }
  void *p = heap_alloc(nmemb * size, 1);
  if (p == NULL) return NULL;
  return (void *)caml_fides_mint((uintptr_t)p, nmemb * size,
                                 FIDES_KIND_C_HEAP);
}

/* freeCheck (model §D.4.2): freeBounds, freeCookie, freeNotBase,
   freeOCamlHeap, in that order. */
static struct fides_entry *free_check(uintptr_t w, const char *action)
{
  uint32_t i = Fides_index(w);
  struct fides_entry *e = &table[i];
  uintptr_t a = (i == 0) ? w : ((e->base & ~FIDES_ADDR_MASK) | Fides_low(w));
  if (!(a >= e->base && a - e->base < e->size))
    caml_fides_trap(FIDES_FREE_BOUNDS, action, w, 0, NULL);
  if (e->cookie != Fides_cookie(w))
    caml_fides_trap(FIDES_FREE_COOKIE, action, w, 0, NULL);
  if (a != e->base)
    caml_fides_trap(FIDES_FREE_NOT_BASE, action, w, 0, NULL);
  if (e->kind == FIDES_KIND_OCAML || e->kind == FIDES_KIND_OCAML_STATIC)
    caml_fides_trap(FIDES_FREE_OCAML_HEAP, action, w, 0, NULL);
  return e;
}

void __fides_free(void *p)
{
  if (p == NULL) return;              /* free(NULL) frees nothing (D5) */
  uintptr_t w = (uintptr_t)p;
  struct fides_entry *e = free_check(w, "free");
  void *base = (void *)e->base;
  int heap = e->kind == FIDES_KIND_C_HEAP;
  release_index(Fides_index(w));
  /* The model's hfree only zeroes the entry. Only C heap objects also go
     back to the C allocator; a stack or global object has no chunk. */
  if (heap) free(base);
}

void *__fides_realloc(void *p, size_t n)
{
  if (p == NULL) return __fides_malloc(n);
  uintptr_t w = (uintptr_t)p;
  struct fides_entry *e = free_check(w, "realloc");
  if (n == 0) {                       /* glibc: frees and returns NULL */
    __fides_free(p);
    return NULL;
  }
  void *old = (void *)e->base;
  size_t old_size = e->size;
  void *q;
  if (e->kind == FIDES_KIND_C_HEAP) {
    q = realloc(old, n);
    if (q == NULL) return NULL;       /* the old object is unchanged */
    if (straddles((uintptr_t)q, n)) {
      void *r = heap_alloc(n, 0);
      if (r == NULL) internal_error("cannot place a reallocation",
                                    (uintptr_t)q, n);
      memcpy(r, q, n);
      free(q);
      q = r;
    }
  } else {
    q = heap_alloc(n, 0);
    if (q == NULL) return NULL;
    memcpy(q, old, old_size < n ? old_size : n);
  }
  /* The old entry dies even if the block did not move, so stale copies of
     the old pointer fail. */
  release_index(Fides_index(w));
  return (void *)caml_fides_mint((uintptr_t)q, n, FIDES_KIND_C_HEAP);
}

/* ---------------------------------------------------------------------- */
/* Stack objects, globals, errno                                          */

void *__fides_salloc(void *addr, size_t n)
{
  return (void *)caml_fides_mint((uintptr_t)addr, n, FIDES_KIND_C_STACK);
}

/* Inserted by the pass at every exit of the owning frame. The object may
   already have been released by a free, so a word that no longer
   validates is ignored. */
void __fides_sfree(void *p)
{
  caml_fides_release((uintptr_t)p);
}

void *__fides_global(void *addr, size_t n)
{
  return (void *)caml_fides_mint((uintptr_t)addr, n, FIDES_KIND_C_GLOBAL);
}

int *__fides_errno_location(void)
{
  static uintptr_t w;
  if (w == 0)
    w = caml_fides_mint((uintptr_t)&errno, sizeof(int), FIDES_KIND_C_GLOBAL);
  return (int *)w;
}
