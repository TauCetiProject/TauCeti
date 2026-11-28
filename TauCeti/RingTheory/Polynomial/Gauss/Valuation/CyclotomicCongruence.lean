/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import TauCeti.RingTheory.Polynomial.Gauss.Valuation.ResidueField
import TauCeti.RingTheory.Valuation.PowSubPow

/-!
# Gauss valuations under cyclotomic congruences

A congruence modulo `(1 + X) ^ (p ^ n) - 1`, up to multiplication by a power of `1 + X`,
transfers a sufficiently large Gauss value to an evaluation on the disc. For a product of an
initial polynomial and cleared Euler factors, a lower bound uses only the constant term of the
initial polynomial and the leading coefficient of the product of Euler factors.

This is the polynomial estimate used in
`New.Selmer.StickelbergerSystem.exists_point_ellVal_universalChar_le` in
`grh/src/New/Congruences/Selmer/StickelbergerLine.lean` of [lsernau/grh-lean][short-proof].
Valuations here are multiplicative, so small errors have small values.

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Congruences/Selmer/StickelbergerLine.lean
-/

public section

namespace Polynomial

/-- A congruence modulo `(1 + X)^(p^n) - 1` preserves the Gauss valuation of `Q` if the
quotient has Gauss valuation at most one and `r^(n+1)`, an upper bound for the value of the
modulus at radius `v p ≤ r ≤ 1`, is strictly smaller than the value of `Q`. The factor
`(1 + X)^k` does not affect the value on the unit disc. -/
theorem gaussValuation_eq_of_cyclotomic_congruence {R Γ₀ : Type*} [CommRing R]
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) {p : ℕ}
    {r : Γ₀} (hrp : v (p : R) ≤ r) (hr : r ≤ 1) {n k : ℕ} {P Q H : R[X]}
    (hcong : P - (1 + X) ^ k * Q = ((1 + X) ^ p ^ n - 1) * H)
    (hH : H.gaussValuation v r ≤ 1) (hQ : r ^ (n + 1) < Q.gaussValuation v r) :
    P.gaussValuation v r = Q.gaussValuation v r := by
  have hunit : (1 + X : R[X]).gaussValuation v r = 1 := by
    have he : (1 + X : R[X]) = X - C (-1) := by simp [add_comm]
    simp only [he, gaussValuation_X_sub_C, v.map_neg, map_one, max_eq_right hr]
  have hscaled : ((1 + X) ^ k * Q).gaussValuation v r = Q.gaussValuation v r := by
    simp [gaussValuation_pow, hunit]
  have hmod := (v.gauss r).map_one_add_pow_pow_sub_one_le (x := X) (by simpa using hr) p n
  simp only [Valuation.gauss_apply, ← C_eq_natCast, gaussValuation_C, gaussValuation_X] at hmod
  have hsmall : (P - (1 + X) ^ k * Q).gaussValuation v r < Q.gaussValuation v r := by
    rw [hcong, gaussValuation_mul]
    refine (mul_le_of_le_one_right' hH).trans_lt (hmod.trans_lt ?_)
    rw [max_eq_right (by simpa using hrp), ← pow_succ']
    exact hQ
  have h := (v.gauss r).map_add_eq_of_lt_right (x := P - (1 + X) ^ k * Q)
    (y := (1 + X) ^ k * Q) (by simpa only [Valuation.gauss_apply, hscaled] using hsmall)
  simpa only [sub_add_cancel, Valuation.gauss_apply, hscaled] using h

/-- A congruence with `A * B`, up to a power of `1 + X`, gives a point of radius `v c` where
`P` has value at least the value of the constant coefficient of `A` times the weighted value
of the leading coefficient of `B`, provided this lower bound strictly dominates the modulus. -/
theorem exists_valuation_eval_ge_of_cyclotomic_congruence {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)] {p : ℕ}
    (c : K) (hcp : v (p : K) ≤ v c) (hc : v c ≤ 1) {n k : ℕ} {P A B H : K[X]}
    (hcong : P - (1 + X) ^ k * (A * B) = ((1 + X) ^ p ^ n - 1) * H)
    (hH : H.gaussValuation v (v c) ≤ 1)
    (hsep : v c ^ (n + 1) < v (A.coeff 0) * (v B.leadingCoeff * v c ^ B.natDegree)) :
    ∃ x : K, v x = v c ∧ v (A.coeff 0) * (v B.leadingCoeff * v c ^ B.natDegree) ≤ v (P.eval x) := by
  have hA : v (A.coeff 0) ≤ A.gaussValuation v (v c) := by
    simpa using le_gaussValuation v (v c) A 0
  have hB := le_gaussValuation v (v c) B B.natDegree
  rw [coeff_natDegree] at hB
  have hprod : v (A.coeff 0) * (v B.leadingCoeff * v c ^ B.natDegree) ≤
      (A * B).gaussValuation v (v c) := by
    rw [gaussValuation_mul]
    exact mul_le_mul' hA hB
  obtain ⟨x, hx, hP⟩ := exists_forall_valuation_eval_eq_gaussValuation v {()} (fun _ ↦ P) c
  refine ⟨x, hx, ?_⟩
  rw [hP () (by simp), gaussValuation_eq_of_cyclotomic_congruence v hcp hc hcong hH
    (hsep.trans_le hprod)]
  exact hprod

end Polynomial
