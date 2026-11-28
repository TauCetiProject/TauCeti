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

end TauCeti
