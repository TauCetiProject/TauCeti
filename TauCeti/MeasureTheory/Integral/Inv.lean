/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrals of reciprocals of functions bounded away from zero

If `λ ≤ f` almost everywhere with `λ > 0`, then `‖1 / f‖ ≤ 1 / λ` almost everywhere, so `1 / f`
is integrable for a finite measure and its integral is positive for a nonzero finite measure. If
moreover `f ≤ M`, the integral of `1 / f` is at least `μ(univ) / M`. These are the estimates on
`∫ 1 / a` that control the explicit solution of a one-dimensional divergence-form equation with
coefficient `a`.

## Main results

* `MeasureTheory.ae_norm_inv_le_inv_of_le`: `‖1 / f‖ ≤ 1 / λ` almost everywhere.
* `MeasureTheory.integrable_inv_of_le`: `1 / f` is integrable for a finite measure.
* `MeasureTheory.integral_inv_pos_of_le`: `∫ 1 / f > 0` for a nonzero finite measure.
* `MeasureTheory.measureReal_univ_div_le_integral_inv`: `μ(univ) / M ≤ ∫ 1 / f` when
  `0 < f ≤ M` almost everywhere.
-/

public section

open Filter

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {lam M : ℝ}

/-- If `λ ≤ f` almost everywhere with `λ > 0`, then `‖1 / f‖ ≤ 1 / λ` almost everywhere. -/
theorem ae_norm_inv_le_inv_of_le (hlam : 0 < lam) (hf : ∀ᵐ x ∂μ, lam ≤ f x) :
    ∀ᵐ x ∂μ, ‖(f x)⁻¹‖ ≤ lam⁻¹ :=
  hf.mono fun x hx => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hlam.trans_le hx)]
    exact inv_anti₀ hlam hx

/-- For a finite measure, the reciprocal of a function bounded below by `λ > 0` is integrable. -/
theorem integrable_inv_of_le [IsFiniteMeasure μ] (hlam : 0 < lam)
    (hm : AEStronglyMeasurable f μ) (hf : ∀ᵐ x ∂μ, lam ≤ f x) :
    Integrable (fun x => (f x)⁻¹) μ :=
  Integrable.of_bound hm.aemeasurable.inv.aestronglyMeasurable _
    (ae_norm_inv_le_inv_of_le hlam hf)

/-- For a nonzero finite measure, the reciprocal of a function bounded below by `λ > 0` has
positive integral. -/
theorem integral_inv_pos_of_le [IsFiniteMeasure μ] [NeZero μ] (hlam : 0 < lam)
    (hm : AEStronglyMeasurable f μ) (hf : ∀ᵐ x ∂μ, lam ≤ f x) :
    0 < ∫ x, (f x)⁻¹ ∂μ := by
  have hpos : ∀ᵐ x ∂μ, 0 < (f x)⁻¹ := hf.mono fun x hx => inv_pos.2 (hlam.trans_le hx)
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun x hx => hx.le)
    (integrable_inv_of_le hlam hm hf)]
  exact (Measure.measure_univ_pos.2 (NeZero.ne μ)).trans_le
    (measure_mono_ae (hpos.mono fun x hx _ => hx.ne'))

/-- If `0 < f ≤ M` almost everywhere and `1 / f` is integrable, then `μ(univ) / M ≤ ∫ 1 / f`. -/
theorem measureReal_univ_div_le_integral_inv [IsFiniteMeasure μ]
    (hi : Integrable (fun x => (f x)⁻¹) μ) (hf : ∀ᵐ x ∂μ, 0 < f x ∧ f x ≤ M) :
    μ.real Set.univ / M ≤ ∫ x, (f x)⁻¹ ∂μ := by
  have h := integral_mono_ae (integrable_const M⁻¹) hi (hf.mono fun x hx => inv_anti₀ hx.1 hx.2)
  rwa [integral_const, smul_eq_mul, ← div_eq_mul_inv] at h

end MeasureTheory
