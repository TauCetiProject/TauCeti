/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Stable.PDF
import TauCeti.Analysis.Bochner.CharFun.Smooth
import TauCeti.MeasureTheory.Integral.Gamma

/-!
# Smooth densities of scalar stable laws

The modulus of a positive-scale stable characteristic function is `exp (-|s t| ^ α)`.
Every natural polynomial weight remains integrable, so Fourier differentiation makes the
existing inversion density `stablePDFReal` smooth. This holds at shape one and at full
skewness, where formulas for the characteristic exponent require separate branches.

The smoothness statement also covers invalid parameters and zero scale: the chosen density
vanishes there. At valid shape and zero scale the law is Dirac, and this zero function is
not a density of that law.

The weighted integrability proof uses the two-sided Gamma integrability criterion, and the
smoothness proof uses `MeasureTheory.Measure.contDiff_charFunDensity`.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, section 3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ContDiff

namespace TauCeti.Probability

/-- Every natural polynomial weight of a positive-scale stable characteristic function is
integrable. Invalid shapes give the zero characteristic function. -/
theorem integrable_norm_pow_mul_norm_charFun_stableMeasure (α β : ℝ) {s : ℝ≥0}
    (hs : 0 < s) (m : ℝ) (n : ℕ) :
    Integrable (fun t : ℝ ↦ ‖t‖ ^ n * ‖charFun (stableMeasure α β s m) t‖) := by
  by_cases h : α ∈ Ioc 0 2 ∧ |β| ≤ 1
  · have hs' : (s : ℝ) ≠ 0 := (NNReal.coe_pos.2 hs).ne'
    have hint := (integrable_abs_rpow_mul_exp_neg_abs_rpow_iff h.1.1
      (q := (n : ℝ))).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hscaled := (hint.comp_mul_left' hs').const_mul ((s : ℝ) ^ n)⁻¹
    refine hscaled.congr (Filter.Eventually.of_forall fun t ↦ ?_)
    dsimp only
    rw [norm_charFun_stableMeasure h.1 h.2]
    simp only [Real.rpow_natCast, abs_mul, abs_of_nonneg s.coe_nonneg, mul_pow,
      Real.norm_eq_abs]
    field_simp [hs']
  · have hi : α ≤ 0 ∨ 2 < α ∨ 1 < |β| := by
      simpa only [mem_Ioc, not_and_or, not_lt, not_le, or_assoc] using h
    simp_rw [stableMeasure_of_invalid hi, charFun_zero_measure, norm_zero, mul_zero]
    exact integrable_zero _ _ _

/-- The chosen stable density is smooth in its sample point for every parameter value.
For positive scale it is a density of the stable law; for zero scale it is identically zero. -/
@[fun_prop]
theorem contDiff_stablePDFReal (α β : ℝ) (s : ℝ≥0) (m : ℝ) :
    ContDiff ℝ ∞ (stablePDFReal α β s m) := by
  by_cases hs : s = 0
  · subst s
    simpa only [funext (stablePDFReal_zero_scale α β m)] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ (0 : ℝ)))
  · rw [funext (stablePDFReal_def α β s m)]
    exact Measure.contDiff_charFunDensity fun n _ ↦
      integrable_norm_pow_mul_norm_charFun_stableMeasure α β (pos_iff_ne_zero.2 hs) m n

end TauCeti.Probability
