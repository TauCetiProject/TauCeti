/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Multiplicity

/-!
# Exact `p`-adic valuations of differences of powers

Let `p` be a prime not dividing `a * b` and let `d` be the order of `a / b` modulo `p`, so that
`p ∣ a ^ k - b ^ k` exactly when `d ∣ k`. This file computes the exact power of `p` dividing
`a ^ k - b ^ k` for every positive multiple `k` of `d`, in terms of `a ^ d - b ^ d` and `k`.
The valuation of `n` at `p` is Mathlib's `multiplicity p n` on `ℕ`.

* For an odd prime `p` with `p ∤ d`, `v_p(a ^ k - b ^ k) = v_p(a ^ d - b ^ d) + v_p(k)`.
* For `p = 2` the bases are odd and `d = 1`: `v₂(a ^ k - b ^ k) = v₂(a - b)` for odd `k`, and
  `v₂(a ^ k - b ^ k) + 1 = v₂(a ^ 2 - b ^ 2) + v₂(k)` for even `k ≠ 0`.

The order `d` enters only through `p ∣ a ^ d - b ^ d` and `p ∤ d`, so the statements are phrased
with an arbitrary `d` subject to these hypotheses. They are the lifting-the-exponent input for the
valuation of two-variable cyclotomic values and for the nonprimitive prime divisors of
`a ^ n - b ^ n` in the Bang–Zsigmondy theorem.

All statements reduce to Mathlib's lifting-the-exponent lemmas
`emultiplicity_pow_sub_pow_of_prime`, `Nat.multiplicity_pow_sub_pow` and
`Nat.multiplicity_pow_two_sub_pow` in `Mathlib/NumberTheory/Multiplicity.lean`.

## Main results

* `Nat.multiplicity_pow_sub_pow_of_not_dvd`: for any prime `p` with `p ∣ x - y`, `p ∤ x` and
  `p ∤ n`, the valuations of `x ^ n - y ^ n` and `x - y` at `p` agree.
* `Nat.multiplicity_pow_sub_pow_of_dvd_pow_sub_pow`: for an odd prime `p` with
  `p ∣ x ^ d - y ^ d`, `p ∤ x`, `p ∤ d` and `d ∣ n ≠ 0`,
  `v_p(x ^ n - y ^ n) = v_p(x ^ d - y ^ d) + v_p(n)`.
* `Nat.multiplicity_two_pow_sub_pow_of_odd`: for odd `x`, `y` and odd `n`,
  `v₂(x ^ n - y ^ n) = v₂(x - y)`.
* `Nat.multiplicity_two_pow_sub_pow_of_even`: for odd `y < x` and even `n ≠ 0`,
  `v₂(x ^ n - y ^ n) + 1 = v₂(x ^ 2 - y ^ 2) + v₂(n)`.

## References

* G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of `a ^ n - b ^ n`*, Ann. of
  Math. (2) 5 (1904), 173–180, Theorem III, p. 175.
* Ö. Avcı, *Large Zsigmondy primes*, arXiv:2011.06136v2 (2023), Lemma 2.2.
-/

public section

namespace Nat

variable {p : ℕ} [hp : Fact p.Prime]

/-- For any prime `p`, including `p = 2`, with `p ∣ x - y` and `p ∤ x`, raising to an exponent
`n` prime to `p` does not change the valuation at `p`: `v_p(x ^ n - y ^ n) = v_p(x - y)`. No
ordering of `x` and `y` is needed, since both sides vanish when `x ≤ y`. -/
theorem multiplicity_pow_sub_pow_of_not_dvd {x y n : ℕ} (hxy : p ∣ x - y) (hx : ¬p ∣ x)
    (hn : ¬p ∣ n) : multiplicity p (x ^ n - y ^ n) = multiplicity p (x - y) := by
  obtain hyx | hxy' := le_total y x
  · apply multiplicity_eq_of_emultiplicity_eq
    rw [← Int.natCast_emultiplicity, ← Int.natCast_emultiplicity,
      Nat.cast_sub (Nat.pow_le_pow_left hyx n), Nat.cast_sub hyx]
    rw [← Int.natCast_dvd_natCast, Nat.cast_sub hyx] at hxy
    push_cast
    exact emultiplicity_pow_sub_pow_of_prime (Nat.prime_iff_prime_int.mp hp.out) hxy
      (by exact_mod_cast hx) (by exact_mod_cast hn)
  · rw [Nat.sub_eq_zero_of_le hxy', Nat.sub_eq_zero_of_le (Nat.pow_le_pow_left hxy' n)]

/-- **Lifting the exponent** from an intermediate exponent `d`: for an odd prime `p` with
`p ∣ x ^ d - y ^ d`, `p ∤ x` and `p ∤ d`, every nonzero multiple `n` of `d` satisfies
`v_p(x ^ n - y ^ n) = v_p(x ^ d - y ^ d) + v_p(n)`. Taking for `d` the order of `x / y` modulo
`p` gives the valuation of `x ^ n - y ^ n` at every exponent `n` it divides. -/
theorem multiplicity_pow_sub_pow_of_dvd_pow_sub_pow (hp1 : Odd p) {x y d n : ℕ} (hyx : y < x)
    (hxy : p ∣ x ^ d - y ^ d) (hx : ¬p ∣ x) (hd : ¬p ∣ d) (hdn : d ∣ n) (hn : n ≠ 0) :
    multiplicity p (x ^ n - y ^ n) = multiplicity p (x ^ d - y ^ d) + multiplicity p n := by
  obtain ⟨m, rfl⟩ := hdn
  have hd0 : d ≠ 0 := left_ne_zero_of_mul hn
  have hm0 : m ≠ 0 := right_ne_zero_of_mul hn
  rw [pow_mul, pow_mul, multiplicity_pow_sub_pow hp1 (Nat.pow_lt_pow_left hyx hd0) hxy
      (fun h => hx (hp.out.dvd_of_dvd_pow h)) hm0, multiplicity_mul hd0 hm0,
    multiplicity_eq_zero_of_not_dvd hd, zero_add]

/-- For odd `x` and `y` and an odd exponent `n`, `v₂(x ^ n - y ^ n) = v₂(x - y)`. -/
theorem multiplicity_two_pow_sub_pow_of_odd {x y n : ℕ} (hx : Odd x) (hy : Odd y)
    (hn : Odd n) : multiplicity 2 (x ^ n - y ^ n) = multiplicity 2 (x - y) :=
  multiplicity_pow_sub_pow_of_not_dvd (even_iff_two_dvd.mp (Nat.Odd.sub_odd hx hy))
    hx.not_two_dvd_nat hn.not_two_dvd_nat

/-- **Lifting the exponent** at `p = 2` for an even exponent: for odd `y < x` and even `n ≠ 0`,
`v₂(x ^ n - y ^ n) + 1 = v₂(x ^ 2 - y ^ 2) + v₂(n)`. The odd-prime formula of
`Nat.multiplicity_pow_sub_pow_of_dvd_pow_sub_pow` fails here: at `(x, y, n) = (3, 1, 2)` it would
give `v₂(8) = v₂(2) + v₂(2) = 2`, not `3`. -/
theorem multiplicity_two_pow_sub_pow_of_even {x y n : ℕ} (hyx : y < x) (hx : Odd x)
    (hy : Odd y) (hn : Even n) (hn0 : n ≠ 0) :
    multiplicity 2 (x ^ n - y ^ n) + 1 = multiplicity 2 (x ^ 2 - y ^ 2) + multiplicity 2 n := by
  rw [Nat.sq_sub_sq, multiplicity_mul (by omega) (by omega),
    multiplicity_pow_two_sub_pow hyx (even_iff_two_dvd.mp (Nat.Odd.sub_odd hx hy))
      hx.not_two_dvd_nat hn0 hn]

end Nat
