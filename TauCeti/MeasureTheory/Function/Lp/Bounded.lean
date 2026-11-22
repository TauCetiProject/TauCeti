/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Almost-sure difference bounds and `Lᵖ` membership of bounded squared differences

Two functions almost surely bounded in norm have an almost surely bounded difference
(`MeasureTheory.ae_norm_sub_le`), yielding an almost-sure bound on squared differences of real
functions (`MeasureTheory.ae_sq_sub_le`) and `Lᵖ` membership on finite measure spaces
(`MeasureTheory.memLp_sub_sq_of_bound`).
-/

public section

open scoped ENNReal

namespace MeasureTheory

/-- If two functions are almost surely bounded in norm by `R₁` and `R₂`, then their difference is
almost surely bounded in norm by `R₁ + R₂`. -/
theorem ae_norm_sub_le {Ω E : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [SeminormedAddCommGroup E] {f g : Ω → E} {R₁ R₂ : ℝ}
    (hf : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ R₁) (hg : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ R₂) :
    ∀ᵐ ω ∂μ, ‖f ω - g ω‖ ≤ R₁ + R₂ :=
  hf.mp <| hg.mono fun _ h2 h1 ↦ (norm_sub_le _ _).trans (add_le_add h1 h2)

/-- If two real functions are almost surely bounded in absolute value by `R`, then their squared
difference is almost surely bounded by `(2 * R) ^ 2`. -/
theorem ae_sq_sub_le {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} {R : ℝ} (hf : ∀ᵐ ω ∂μ, |f ω| ≤ R) (hg : ∀ᵐ ω ∂μ, |g ω| ≤ R) :
    ∀ᵐ ω ∂μ, (f ω - g ω) ^ 2 ≤ (2 * R) ^ 2 :=
  (ae_norm_sub_le (f := f) (g := g) (R₁ := R) (R₂ := R)
      (hf.mono fun _ h ↦ by rwa [Real.norm_eq_abs])
      (hg.mono fun _ h ↦ by rwa [Real.norm_eq_abs])).mono fun _ hω ↦ by
    rw [Real.norm_eq_abs, ← two_mul] at hω
    rw [← sq_abs]
    gcongr

/-- Under a finite measure, the squared difference of two almost-surely bounded measurable real
functions lies in `Lᵖ` for every `p`. -/
theorem memLp_sub_sq_of_bound {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f g : Ω → ℝ} {R : ℝ} (p : ℝ≥0∞)
    (hf_m : AEStronglyMeasurable f μ) (hg_m : AEStronglyMeasurable g μ)
    (hf_bd : ∀ᵐ ω ∂μ, |f ω| ≤ R) (hg_bd : ∀ᵐ ω ∂μ, |g ω| ≤ R) :
    MemLp (fun ω ↦ (f ω - g ω) ^ 2) p μ :=
  MemLp.of_bound ((hf_m.sub hg_m).pow 2) ((2 * R) ^ 2)
    ((ae_sq_sub_le hf_bd hg_bd).mono fun _ hω ↦ by
      rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])

end MeasureTheory
