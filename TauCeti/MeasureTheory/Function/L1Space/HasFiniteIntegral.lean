/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral

/-!
# Lower bounds for lower Lebesgue integrals of norms of differences

If the lower Lebesgue integral of `‖g‖ₑ` exceeds `ε` while that of `‖f‖ₑ` is at most `ε / 2`,
then the lower Lebesgue integral of `‖g - f‖ₑ` exceeds `ε / 2`
(`TauCeti.MeasureTheory.half_lt_lintegral_enorm_sub`). This is the triangle inequality
`MeasureTheory.lintegral_edist_triangle` combined with `ENNReal.add_halves`; applied to a
restricted measure it gives the corresponding estimate for set integrals.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.MeasureTheory

/-- If `‖g‖ₑ` has lower Lebesgue integral more than `ε` and `‖f‖ₑ` has lower Lebesgue integral at
most `ε / 2`, then `‖g - f‖ₑ` has lower Lebesgue integral more than `ε / 2`. -/
theorem half_lt_lintegral_enorm_sub {α E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup E] {f g : α → E} (hf : AEStronglyMeasurable f μ) {ε : ℝ≥0∞}
    (hg : ε < ∫⁻ x, ‖g x‖ₑ ∂μ) (hfε : ∫⁻ x, ‖f x‖ₑ ∂μ ≤ ε / 2) :
    ε / 2 < ∫⁻ x, ‖g x - f x‖ₑ ∂μ := by
  by_contra! hle
  have hsplit := lintegral_edist_triangle (μ := μ) (f := fun _ : α ↦ (0 : E)) (g := g)
    (h := f) aestronglyMeasurable_zero hf
  simp only [edist_eq_enorm_sub, zero_sub, enorm_neg] at hsplit
  have := hg.trans_le (hsplit.trans (add_le_add hfε hle))
  rw [ENNReal.add_halves] at this
  exact lt_irrefl _ this

end TauCeti.MeasureTheory
