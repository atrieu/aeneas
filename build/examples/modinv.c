#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

typedef uint8_t unit_t;
typedef unsigned __int128 u128_t;
typedef __int128 i128_t;
#define AENEAS_I128_MIN (-(i128_t)(((u128_t)1 << 127) - 1) - 1)

enum aeneas_error {
  AENEAS_OK = 0,
  AENEAS_ASSERTION_FAILURE,
  AENEAS_INTEGER_OVERFLOW,
  AENEAS_DIVISION_BY_ZERO,
  AENEAS_ARRAY_OUT_OF_BOUNDS,
  AENEAS_MAXIMUM_SIZE_EXCEEDED,
  AENEAS_PANIC,
  AENEAS_UNDEF
};

/* Types */
typedef struct tup3_u64_u64_u64 tup3_u64_u64_u64;
struct tup3_u64_u64_u64 { uint64_t f0; uint64_t f1; uint64_t f2; };
typedef struct cf_tup3_u64_u64_u64_u64 cf_tup3_u64_u64_u64_u64;
struct cf_tup3_u64_u64_u64_u64 { uint32_t tag; union { tup3_u64_u64_u64 cont; uint64_t done; } u; };

/* Prototypes */
uint64_t P(void);
int pow_mod(uint64_t p0, uint64_t p1, uint64_t *out);
int pow_mod_loop(uint64_t p0, uint64_t p1, uint64_t p2, uint64_t *out);
int mul_mod(uint64_t p0, uint64_t p1, uint64_t *out);
int pow_mod_loop_body(uint64_t p0, uint64_t p1, uint64_t p2, cf_tup3_u64_u64_u64_u64 *out);
int inv_mod(uint64_t p0, uint64_t *out);

/* Functions */
uint64_t P(void) {
  return UINT64_C(4294967291);
}

int inv_mod(uint64_t p0, uint64_t *out) {
  uint64_t t0;
  uint64_t a1 = P();
  uint64_t a2 = UINT64_C(2);
  uint64_t r3; if (__builtin_sub_overflow(a1, a2, &r3)) return AENEAS_INTEGER_OVERFLOW;
  t0 = r3;
  uint64_t x4 = t0;
  uint64_t t6;
  int rc5 = pow_mod(p0, x4, &t6);
  if (rc5) return rc5;
  *out = t6;
  return AENEAS_OK;
}

int mul_mod(uint64_t p0, uint64_t p1, uint64_t *out) {
  uint64_t t0;
  uint64_t r1; if (__builtin_mul_overflow(p0, p1, &r1)) return AENEAS_INTEGER_OVERFLOW;
  t0 = r1;
  uint64_t x2 = t0;
  uint64_t a3 = P();
  if (a3 == 0) return AENEAS_DIVISION_BY_ZERO;
  uint64_t r4 = x2 % a3;
  *out = r4;
  return AENEAS_OK;
}

int pow_mod(uint64_t p0, uint64_t p1, uint64_t *out) {
  uint64_t t0;
  uint64_t a1 = P();
  if (a1 == 0) return AENEAS_DIVISION_BY_ZERO;
  uint64_t r2 = p0 % a1;
  t0 = r2;
  uint64_t x3 = t0;
  uint64_t t5;
  int rc4 = pow_mod_loop(p1, UINT64_C(1), x3, &t5);
  if (rc4) return rc4;
  *out = t5;
  return AENEAS_OK;
}

int pow_mod_loop_body(uint64_t p0, uint64_t p1, uint64_t p2, cf_tup3_u64_u64_u64_u64 *out) {
  if ((p0 > UINT64_C(0))) {
    uint64_t t0;
    t0 = ((uint64_t)(p0 & UINT64_C(1)));
    uint64_t x1 = t0;
    uint64_t t2;
    if ((x1 == UINT64_C(1))) {
      uint64_t t4;
      int rc3 = mul_mod(p1, p2, &t4);
      if (rc3) return rc3;
      t2 = t4;
    } else {
      t2 = p1;
    }
    uint64_t x5 = t2;
    uint64_t t6;
    uint64_t t8;
    int rc7 = mul_mod(p2, p2, &t8);
    if (rc7) return rc7;
    t6 = t8;
    uint64_t x9 = t6;
    uint64_t t10;
    int32_t a11 = ((int32_t)1);
    if (a11 < 0) return AENEAS_INTEGER_OVERFLOW;
    if (a11 >= 64) return AENEAS_INTEGER_OVERFLOW;
    uint64_t r12 = p0 >> a11;
    t10 = r12;
    uint64_t x13 = t10;
    *out = ((cf_tup3_u64_u64_u64_u64){ .tag = 0, .u.cont = ((tup3_u64_u64_u64){ x13, x5, x9 }) });
    return AENEAS_OK;
  } else {
    *out = ((cf_tup3_u64_u64_u64_u64){ .tag = 1, .u.done = p1 });
    return AENEAS_OK;
  }
}

int pow_mod_loop(uint64_t p0, uint64_t p1, uint64_t p2, uint64_t *out) {
  tup3_u64_u64_u64 st0 = ((tup3_u64_u64_u64){ p0, p1, p2 });
  for (;;) {
    uint64_t x1 = st0.f0;
    uint64_t x2 = st0.f1;
    uint64_t x3 = st0.f2;
    cf_tup3_u64_u64_u64_u64 cf4;
    cf_tup3_u64_u64_u64_u64 t6;
    int rc5 = pow_mod_loop_body(x1, x2, x3, &t6);
    if (rc5) return rc5;
    cf4 = t6;
    if (cf4.tag == 0) { st0 = cf4.u.cont; } else {
      *out = cf4.u.done;
      return AENEAS_OK;
      break;
    }
  }
}
