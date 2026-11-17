/* The modular inversion example, in C: `modinv.c` is printed by `#deep_c` from the deep
   terms of `tests/src/modinv.rs` (see Modinv/GenC.lean and run.sh). The expected values
   are the ones Lean computes in Modinv/Example.lean. */
#include <stdio.h>
#include "modinv.c"

static int failures = 0;
#define CHECK(cond, name) \
  do { if (cond) printf("ok   %s\n", name); else { printf("FAIL %s\n", name); failures++; } } while (0)

int main(void) {
  uint64_t r; int rc;
  CHECK(P() == UINT64_C(4294967291), "P = 4294967291");
  rc = inv_mod(3, &r);                      CHECK(rc == 0 && r == UINT64_C(1431655764), "inv_mod 3 = 1431655764");
  rc = mul_mod(3, UINT64_C(1431655764), &r); CHECK(rc == 0 && r == 1, "3 * inv_mod 3 = 1 (mod P)");
  rc = inv_mod(2, &r);                      CHECK(rc == 0 && r == UINT64_C(2147483646), "inv_mod 2 = 2147483646");
  rc = inv_mod(UINT64_C(123456789), &r);    CHECK(rc == 0 && r == UINT64_C(2196879611), "inv_mod 123456789 = 2196879611");
  rc = mul_mod(UINT64_C(123456789), UINT64_C(2196879611), &r); CHECK(rc == 0 && r == 1, "123456789 * its inverse = 1 (mod P)");
  rc = pow_mod(2, 10, &r);                  CHECK(rc == 0 && r == 1024, "pow_mod 2 10 = 1024");
  rc = inv_mod(0, &r);                      CHECK(rc == 0 && r == 0, "inv_mod 0 = 0 (no inverse: 0^(P-2))");
  rc = mul_mod(UINT64_C(1) << 40, UINT64_C(1) << 40, &r);
  CHECK(rc == AENEAS_INTEGER_OVERFLOW, "mul_mod on operands above P overflows, as in the model");
  printf("%d failure(s)\n", failures);
  return failures;
}
