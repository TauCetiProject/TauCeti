/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Squared triangle inequality for lower square energies

The lower Lebesgue integral of `‖f - g‖ₑ ^ 2` is at most twice the sum of the lower integrals of
`‖f - h‖ₑ ^ 2` and `‖g - h‖ₑ ^ 2`. Only the first of the two summands needs to be almost
everywhere measurable, and the integrals may be infinite.

## Main statements

* `TauCeti.lintegral_enorm_sub_sq_le_two_mul`: the squared triangle inequality through an
  intermediate function, integrated against an arbitrary measure.
* `TauCeti.lintegral_enorm_add_sq_le_two_mul`: the squared triangle inequality for addition,
  integrated against an arbitrary measure.
* `TauCeti.ae_eq_iff_lintegral_enorm_sub_sq_eq_zero`: characterization of almost-everywhere
  equality by vanishing lower square energy.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [SeminormedAddCommGroup E]

/-- **Squared triangle inequality for lower square energies.** The lower square energy of
`f - g` is at most twice the sum of those of `f - h` and `g - h`. -/
theorem lintegral_enorm_sub_sq_le_two_mul {f g h : α → E}
    (hfh : AEMeasurable (fun x ↦ ‖f x - h x‖ₑ ^ 2) μ) :
    ∫⁻ x, ‖f x - g x‖ₑ ^ 2 ∂μ ≤
      2 * ((∫⁻ x, ‖f x - h x‖ₑ ^ 2 ∂μ) + ∫⁻ x, ‖g x - h x‖ₑ ^ 2 ∂μ) := by
  rw [← lintegral_add_left' hfh, ← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_mono fun x ↦ ?_
  have hx := ENNReal.ofReal_le_ofReal (norm_sub_sq_le_two_mul (f x) (g x) (h x))
  simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, ENNReal.ofReal_ofNat] using hx

/-- **Squared triangle inequality for lower square energies (addition).** The lower square energy
of `f + g` is at most twice the sum of those of `f` and `g`. -/
theorem lintegral_enorm_add_sq_le_two_mul {f g : α → E}
    (hf : AEMeasurable (fun x ↦ ‖f x‖ₑ ^ 2) μ) :
    ∫⁻ x, ‖f x + g x‖ₑ ^ 2 ∂μ ≤
      2 * ((∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) + ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) := by
  simpa only [Pi.zero_apply, Pi.neg_apply, sub_neg_eq_add, sub_zero, eNorm_neg] using
    lintegral_enorm_sub_sq_le_two_mul (μ := μ) (f := f) (g := -g) (h := 0)
      (by simpa only [Pi.zero_apply, sub_zero] using hf)

/-- Two functions agree almost everywhere on an arbitrary measure space if and only if the lower
integral of their squared extended norm difference vanishes. -/
theorem ae_eq_iff_lintegral_enorm_sub_sq_eq_zero {E : Type*} [NormedAddCommGroup E]
    {f g : α → E} (hfg : AEMeasurable (fun x ↦ ‖f x - g x‖ₑ ^ 2) μ) :
    f =ᵐ[μ] g ↔ ∫⁻ x, ‖f x - g x‖ₑ ^ 2 ∂μ = 0 := by
  rw [lintegral_eq_zero_iff' hfg]
  simp only [Filter.EventuallyEq, Pi.zero_apply,
    pow_eq_zero_iff (by norm_num : 2 ≠ 0), eNorm_eq_zero, sub_eq_zero]

end TauCeti
