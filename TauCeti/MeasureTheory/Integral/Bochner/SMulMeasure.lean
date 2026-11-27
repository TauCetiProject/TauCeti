/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Function.L1Space.HasFiniteIntegral

/-!
# Integrals for a multiple of a measure

For `c ∈ (0, ∞]`, an integral formula for `c • q` gives one for `q`: there is a real `a ≠ 0`
such that `∫ F ∂(c • q) = V • I` implies `∫ F ∂q = a • I`, together with integrability for `q`
(`MeasureTheory.exists_integral_eq_mul_of_smul_measure`). The constant `a` depends only on `c`
and `V`. For `c = ∞` the function vanishes almost everywhere, by
`TauCeti.MeasureTheory.ae_eq_zero_of_hasFiniteIntegral_top_smul`.

## References

The statement and proof are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/IwasawaUnfolding.lean`
(`New.exists_integral_eq_mul_of_smul_measure`).
-/

public section

open MeasureTheory Measure

open scoped ENNReal

namespace MeasureTheory

/-- **Dividing an integral formula by a factor of the measure.** For `c ∈ (0, ∞]` and finite
nonzero `V` there is a real `a ≠ 0` such that whenever `F` is integrable for `c • q` with
`∫ F ∂(c • q) = V • I`, then `F` is integrable for `q` with `∫ F ∂q = a • I`. For `c = ∞` this
uses that a function integrable for `∞ • q` vanishes `q`-almost everywhere. -/
theorem exists_integral_eq_mul_of_smul_measure {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (q : Measure X) {c V : ℝ≥0∞} (hc : c ≠ 0)
    (hV_zero : V ≠ 0) (hV_top : V ≠ ∞) :
    ∃ a ≠ (0 : ℝ), ∀ (F : X → E) (I : E), Integrable F (c • q) →
      ∫ x, F x ∂(c • q) = V.toReal • I → Integrable F q ∧ ∫ x, F x ∂q = a • I := by
  have hV : V.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hV_zero, hV_top⟩
  rcases eq_or_ne c ∞ with rfl | hc_top
  · -- for `c = ∞` integrability forces `F = 0` almost everywhere
    refine ⟨1, one_ne_zero, fun F I h_int h_eq ↦ ?_⟩
    have hF_zero : F =ᵐ[q] 0 := TauCeti.MeasureTheory.ae_eq_zero_of_hasFiniteIntegral_top_smul
      (h_int.aestronglyMeasurable.mono_ac (absolutelyContinuous_smul ENNReal.top_ne_zero))
      h_int.hasFiniteIntegral
    obtain rfl : I = 0 := by
      rw [integral_smul_measure, ENNReal.toReal_top, zero_smul, eq_comm, smul_eq_zero] at h_eq
      exact h_eq.resolve_left hV
    exact ⟨(integrable_zero X E q).congr hF_zero.symm, by simp [integral_eq_zero_of_ae hF_zero]⟩
  · have hc_real : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hc, hc_top⟩
    refine ⟨V.toReal / c.toReal, div_ne_zero hV hc_real,
      fun F I h_int h_eq ↦ ⟨(integrable_smul_measure hc hc_top).1 h_int, ?_⟩⟩
    rw [integral_smul_measure] at h_eq
    rw [div_eq_inv_mul, mul_smul, ← h_eq, smul_smul, inv_mul_cancel₀ hc_real, one_smul]

end MeasureTheory
