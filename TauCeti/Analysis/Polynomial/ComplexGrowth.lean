/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, OpenAI Codex
-/
module

public import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Real-part growth of a complex polynomial on large circles

A nonconstant complex polynomial attains a real part at least half the modulus of its leading
monomial on every sufficiently large circle. The radius is prescribed. This quantitative
obstruction is used in finite-order Hadamard factorization.

The proof is adapted from Matteo Cipollina's `ExpPoly/Growth.lean` in
[PrimeNumberTheoremAnd](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/e1ed50ef52b80922d0cf26293cdc74b84039b5d6/PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/ExpPoly/Growth.lean).
-/

public section

namespace Polynomial

/-- On every sufficiently large circle, the real part of a nonconstant complex polynomial
is at least half the modulus of its leading monomial at some point of that circle. -/
theorem exists_norm_eq_re_eval_ge (P : Polynomial ℂ) (hn : 0 < P.natDegree) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ R : ℝ, R0 ≤ R → ∃ z : ℂ, ‖z‖ = R ∧
      (‖P.leadingCoeff‖ / 2) * R ^ P.natDegree ≤ (P.eval z).re := by
  have ha : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr fun h ↦ by simp [h] at hn
  let wtarget : ℂ := (starRingEnd ℂ) P.leadingCoeff / (‖P.leadingCoeff‖ : ℂ)
  let w : ℂ := wtarget ^ (P.natDegree⁻¹ : ℂ)
  have hw : w ^ P.natDegree = wtarget := Complex.cpow_nat_inv_pow wtarget hn.ne'
  have hw_norm : ‖w‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg w) hn.ne').mp
    simpa [wtarget, ha] using congrArg norm hw
  have hleadw : P.leadingCoeff * w ^ P.natDegree = (‖P.leadingCoeff‖ : ℂ) := by
    rw [hw]
    dsimp only [wtarget]
    rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)]
  obtain ⟨B, _, hB⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp
    ((isEquivalent_cobounded_leading_monomial (P := P)).isLittleO.bound
      (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨max B 1, zero_lt_one.trans_le (le_max_right _ _), fun R hR ↦ ?_⟩
  have hR0 : 0 ≤ R := zero_le_one.trans ((le_max_right _ _).trans hR)
  let z : ℂ := (R : ℂ) * w
  have hz : ‖z‖ = R := by simp [z, hw_norm, abs_of_nonneg hR0]
  have hlead : P.leadingCoeff * z ^ P.natDegree =
      ((‖P.leadingCoeff‖ * R ^ P.natDegree : ℝ) : ℂ) := by
    calc
      _ = (R : ℂ) ^ P.natDegree * (P.leadingCoeff * w ^ P.natDegree) := by
        simp only [z, mul_pow]; ring
      _ = _ := by rw [hleadw]; push_cast; ring
  have hzB : B ≤ ‖z‖ := by rw [hz]; exact (le_max_left _ _).trans hR
  have herror := hB hzB
  -- The asymptotic estimate uses subtraction of functions. Evaluate it at z by unfolding
  -- pointwise subtraction and function application.
  change ‖P.eval z - P.leadingCoeff * z ^ P.natDegree‖ ≤
    (1 / 2 : ℝ) * ‖P.leadingCoeff * z ^ P.natDegree‖ at herror
  have hreal := neg_le_of_abs_le (Complex.abs_re_le_norm
    (P.eval z - P.leadingCoeff * z ^ P.natDegree))
  rw [hlead] at herror hreal
  simp only [Complex.sub_re, Complex.ofReal_re] at hreal
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hR0 _))] at herror
  exact ⟨z, hz, by nlinarith⟩

end Polynomial
