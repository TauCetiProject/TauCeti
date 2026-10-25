/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Classification

/-!
# Symmetric 2-cocycles over rings with `2 = 0`

Let `R` be a commutative ring in which `2 = 0`, with no further hypothesis: `R` may be the zero
ring or have nilpotents. This file specializes the symmetric 2-cocycle lemma
(`TauCeti.exists_eq_smul_lazardCocycle`) to `R` and adds the *diagonal* condition `f(X, X) = 0`,
which is the obstruction lemma behind the degree-by-degree construction of a strict logarithm for
a commutative formal group law `F` with `[2]_F = 0`. There the first nonvanishing homogeneous
part `f` of the error `g(F(X, Y)) - g(X) - g(Y)` of a truncated logarithm `g` is a homogeneous
symmetric additive 2-cocycle, and `F(X, X) = 0` forces `f(X, X) = 0`.

The answer depends on whether the degree `n` is a power of two, through the parity of the
greatest common divisor `d_n` of the binomial coefficients `n.choose i`, `0 < i < n`.

* If `n ≠ 0` is not a power of two, then `d_n` is odd (`TauCeti.prime_dvd_lazardGcd_iff`), hence
  equal to `1` in `R`, so the Lazard cocycle `C_n` *is* `(X + Y)ⁿ - Xⁿ - Yⁿ` and every homogeneous
  symmetric additive 2-cocycle of degree `n` is a unique multiple of it. Its diagonal
  `(2X)ⁿ - 2Xⁿ` vanishes, so the diagonal condition holds automatically and is not assumed.
* If `n = 2ᵏ` with `k ≥ 1`, then `d_n = 2`, the polynomial `(X + Y)ⁿ - Xⁿ - Yⁿ` vanishes in `R`,
  and the integral cocycle `C_n = ((X + Y)ⁿ - Xⁿ - Yⁿ) / 2` reduced mod `2` has diagonal
  `C_n(X, X) = (2ⁿ⁻¹ - 1) • Xⁿ = Xⁿ`, as `2ⁿ⁻¹ - 1` is odd. Hence the diagonal of `r • C_n` is
  `r • Xⁿ`, whose coefficient of `Xⁿ` is `r`, so its vanishing forces `r = 0` (also over the zero
  ring), and a homogeneous symmetric additive 2-cocycle of degree `n` with zero diagonal is `0`.

No coefficient field and no division by two is used: everything is deduced from the
classification over an arbitrary commutative ring and binomial-coefficient arithmetic.

## Main results

* `TauCeti.lazardCocycle_eq_add_pow_sub_pow_sub_pow_of_two_eq_zero`: if `2 = 0` in `R` and
  `n ≠ 0` is not a power of two, then `C_n = (X + Y)ⁿ - Xⁿ - Yⁿ`.
* `TauCeti.aeval_diag_lazardCocycle_two_pow`: if `2 = 0` in `R` and `k ≠ 0`, then
  `C_{2ᵏ}(a, a) = a^{2ᵏ}` for every element `a` of an `R`-algebra.
* `TauCeti.existsUnique_eq_smul_add_pow_sub_pow_sub_pow_of_two_eq_zero`: if `2 = 0` in `R` and
  `n ≠ 0` is not a power of two, a homogeneous symmetric additive 2-cocycle of degree `n` is
  `r • ((X + Y)ⁿ - Xⁿ - Yⁿ)` for a unique `r : R`.
* `TauCeti.eq_zero_of_two_eq_zero_of_aeval_X_X_eq_zero`: if `2 = 0` in `R`, a homogeneous
  symmetric additive 2-cocycle `f` of degree `2ᵏ` with `f(X, X) = 0` is zero.

## References

* M. Lazard, *Commutative Formal Groups*, Lecture Notes in Mathematics 443 (1975).
* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, Bull. Amer.
  Math. Soc. 75 (1969), for formal group laws with `[2]_F = 0`.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

open MvPolynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- If `2 = 0` in `R` and `n ≠ 0` is not a power of two, the Lazard cocycle `C_n` is
`(X + Y)ⁿ - Xⁿ - Yⁿ`: the greatest common divisor `d_n` of the `n.choose i`, `0 < i < n`, is odd,
so `d_n = 1` in `R`. -/
theorem lazardCocycle_eq_add_pow_sub_pow_sub_pow_of_two_eq_zero (h2 : (2 : R) = 0) {n : ℕ}
    (hn0 : n ≠ 0) (hn : ∀ k, n ≠ 2 ^ k) :
    lazardCocycle n R = (X 0 + X 1) ^ n - X 0 ^ n - X 1 ^ n := by
  have hodd : Odd (lazardGcd n) := by
    refine Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h => ?_)
    obtain ⟨k, hk⟩ := (prime_dvd_lazardGcd_iff Nat.prime_two hn0).1 h
    exact hn k hk
  rw [← lazardGcd_nsmul_lazardCocycle hn0, ← Nat.cast_smul_eq_nsmul R,
    natCast_eq_one_of_odd_of_two_eq_zero hodd h2, one_smul]

/-- If `2 = 0` in `R` and `k ≠ 0`, the diagonal of the Lazard cocycle of degree `2ᵏ` is
`C_{2ᵏ}(a, a) = a^{2ᵏ}` for an element `a` of any commutative `R`-algebra: its integral
coefficient `(2^{2ᵏ} - 2) / 2` is odd. -/
-- High priority, so that `simp` tries this before the general `aeval_diag_lazardCocycle`.
@[simp high]
theorem aeval_diag_lazardCocycle_two_pow {A : Type*} [CommRing A] [Algebra R A]
    (h2 : (2 : R) = 0) {k : ℕ} (hk : k ≠ 0) (a : A) :
    aeval ![a, a] (lazardCocycle (2 ^ k) R) = a ^ 2 ^ k := by
  rw [aeval_diag_lazardCocycle, lazardGcd_prime_pow Nat.prime_two hk, ← Nat.cast_smul_eq_nsmul R,
    natCast_eq_one_of_odd_of_two_eq_zero _ h2, one_smul]
  -- Write `2 ^ 2 ^ k = 4 * m` with `m ≥ 1`; then `(4 * m - 2) / 2 = 2 * m - 1` is odd.
  obtain ⟨m, hm, hm'⟩ : ∃ m, 1 ≤ m ∧ 2 ^ 2 ^ k = 4 * m := by
    refine ⟨2 ^ (2 ^ k - 2), Nat.one_le_two_pow, ?_⟩
    have : 2 ≤ 2 ^ k := Nat.le_self_pow hk 2
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4, ← pow_add, Nat.add_sub_cancel' this]
  rw [hm']
  exact ⟨m - 1, by omega⟩

/-- **The symmetric 2-cocycle lemma when `2 = 0`, away from powers of two.** If `2 = 0` in `R`
and `n ≠ 0` is not a power of two, a homogeneous symmetric additive 2-cocycle of degree `n` over
`R` is `r • ((X + Y)ⁿ - Xⁿ - Yⁿ)` for a unique `r : R`. -/
theorem existsUnique_eq_smul_add_pow_sub_pow_sub_pow_of_two_eq_zero (h2 : (2 : R) = 0) {n : ℕ}
    (hn0 : n ≠ 0) (hn : ∀ k, n ≠ 2 ^ k) {f : MvPolynomial (Fin 2) R} (hh : f.IsHomogeneous n)
    (hs : f.IsSymmetric) (hf : f.IsAddCocycle₂) :
    ∃! r : R, f = r • ((X 0 + X 1) ^ n - X 0 ^ n - X 1 ^ n) := by
  have hn2 : 2 ≤ n := by
    have := hn 0
    omega
  rw [← lazardCocycle_eq_add_pow_sub_pow_sub_pow_of_two_eq_zero h2 hn0 hn]
  exact existsUnique_eq_smul_lazardCocycle hn2 hh hs hf

/-- **The symmetric 2-cocycle lemma when `2 = 0`, at powers of two.** If `2 = 0` in `R`, a
homogeneous symmetric additive 2-cocycle `f` of degree `2ᵏ` over `R` with zero diagonal
`f(X, X) = 0` is zero. -/
theorem eq_zero_of_two_eq_zero_of_aeval_X_X_eq_zero (h2 : (2 : R) = 0) {k : ℕ}
    {f : MvPolynomial (Fin 2) R} (hh : f.IsHomogeneous (2 ^ k)) (hs : f.IsSymmetric)
    (hf : f.IsAddCocycle₂) (hd : aeval ![(Polynomial.X : Polynomial R), Polynomial.X] f = 0) :
    f = 0 := by
  obtain ⟨r, rfl⟩ := exists_eq_smul_lazardCocycle (pow_ne_zero k two_ne_zero) hh hs hf
  rcases eq_or_ne k 0 with rfl | hk
  · rw [lazardCocycle_eq_zero_of_lt_two (by norm_num), smul_zero]
  · -- The diagonal of `r • C_{2ᵏ}` is `r • X^{2ᵏ}`, whose coefficient of `X^{2ᵏ}` is `r`.
    rw [map_smul, aeval_diag_lazardCocycle_two_pow h2 hk] at hd
    have hr : r = 0 := by simpa using congrArg (Polynomial.coeff · (2 ^ k)) hd
    rw [hr, zero_smul]

end TauCeti
