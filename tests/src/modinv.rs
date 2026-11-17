//@ [!lean] skip
//@ [lean] subdir=Modinv
//@ [lean] aeneas-args=-deep
//! A small cryptographic example for the verified compiler to C: modular inversion
//! in the prime field `GF(P)` by Fermat's little theorem, `a⁻¹ = a^(P-2) mod P`, with a
//! square-and-multiply exponentiation. `P` is the largest prime below 2^32, so that the
//! products of two residues fit in a `u64` and every operation is first-order checked
//! arithmetic.

/// The largest prime below 2^32
pub const P: u64 = 4294967291;

/// The product of two residues modulo `P` (the operands are below `P`, so the product
/// does not overflow)
pub fn mul_mod(a: u64, b: u64) -> u64 {
    (a * b) % P
}

/// `base^exp mod P` by square-and-multiply
pub fn pow_mod(base: u64, mut exp: u64) -> u64 {
    let mut result = 1;
    let mut b = base % P;
    while exp > 0 {
        if exp & 1 == 1 {
            result = mul_mod(result, b);
        }
        b = mul_mod(b, b);
        exp >>= 1;
    }
    result
}

/// The inverse of a non-zero residue: `a^(P-2) mod P`
pub fn inv_mod(a: u64) -> u64 {
    pow_mod(a, P - 2)
}
