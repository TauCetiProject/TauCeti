/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral

/-!
# Lower Lebesgue integrals of norms

For an a.e.-strongly measurable `f`, the lower Lebesgue integral of `‖g‖ₑ` is at most the sum of
those of `‖g - f‖ₑ` and `‖f‖ₑ`
(`TauCeti.MeasureTheory.lintegral_enorm_le_lintegral_enorm_sub_add`). This is the pointwise
triangle inequality integrated with `MeasureTheory.lintegral_eNorm_add_right`; applied to a
restricted measure it gives the corresponding estimate for set integrals.

A function with finite integral for the infinite multiple `∞ • μ` vanishes `μ`-almost everywhere
(`TauCeti.MeasureTheory.ae_eq_zero_of_hasFiniteIntegral_top_smul`).
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti.MeasureTheory

/-- The lower Lebesgue integral of `‖g‖ₑ` is at most the sum of the lower Lebesgue integrals of
`‖g - f‖ₑ` and `‖f‖ₑ`, provided `f` is a.e.-strongly measurable. -/
theorem lintegral_enorm_le_lintegral_enorm_sub_add {α E : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [SeminormedAddGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ)
    (g : α → E) :
    ∫⁻ x, ‖g x‖ₑ ∂μ ≤ ∫⁻ x, ‖g x - f x‖ₑ ∂μ + ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rw [← lintegral_eNorm_add_right _ hf]
  refine lintegral_mono fun x ↦ ?_
  simpa only [sub_add_cancel] using eNorm_add_le (g x - f x) (f x)

/-- An a.e.-strongly measurable function with finite integral for `∞ • μ` vanishes `μ`-almost
everywhere. -/
theorem ae_eq_zero_of_hasFiniteIntegral_top_smul {α E : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ)
    (h_fin : HasFiniteIntegral f (∞ • μ)) : f =ᵐ[μ] 0 := by
  have h_lt : ∞ * ∫⁻ x, ‖f x‖ₑ ∂μ < ∞ := by
    simpa [HasFiniteIntegral] using h_fin
  have h_norm : ∫⁻ x, ‖f x‖ₑ ∂μ = 0 := by simpa [ENNReal.mul_lt_top_iff] using h_lt
  filter_upwards [(lintegral_eq_zero_iff' hf.eNorm).1 h_norm] with x hx using by simpa using hx

end TauCeti.MeasureTheory
