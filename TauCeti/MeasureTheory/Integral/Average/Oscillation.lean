/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average

/-!
# The `L¹` and `L^γ` mean oscillation about the average

On a set `s` of finite measure, the `L¹` deviation of an integrable `f` from its average
`f_s = ⨍_s f` is at most twice its deviation from any constant `c`:

`∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`,

and for `1 ≤ γ` the `γ`-th powers satisfy `∫_s ‖f - f_s‖^γ ≤ 2^γ ∫_s ‖f - c‖^γ`.

These are the Bochner-integral forms of the `Lᵖ` comparison `TauCeti.eLpNorm_sub_setAverage_le`;
the `L²` analogue, with factor `4`, is `TauCeti.setIntegral_norm_sub_setAverage_sq_le`.

## Main results

* `TauCeti.setIntegral_norm_sub_setAverage_le_two_mul`: `∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.
* `TauCeti.setIntegral_norm_sub_setAverage_rpow_le_two_rpow_mul`:
  `∫_s ‖f - f_s‖^γ ≤ 2^γ ∫_s ‖f - c‖^γ` for `1 ≤ γ`.
-/

public section

namespace TauCeti

open MeasureTheory

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {f : X → F} {s : Set X}

/-- **The `L¹` mean oscillation about the average.** On a set `s` of finite measure,
`∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖` for every constant `c`, where `f_s` is the average of `f` over
`s`. -/
theorem setIntegral_norm_sub_setAverage_le_two_mul (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ)
    (c : F) : ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ∂μ ≤ 2 * ∫ x in s, ‖f x - c‖ ∂μ := by
  have h := eLpNorm_sub_setAverage_le (μ := μ) (f := f) hs le_rfl c
  have hia : IntegrableOn (fun x ↦ f x - ⨍ y in s, f y ∂μ) s μ := hf.sub (integrableOn_const hs)
  have hic : IntegrableOn (fun x ↦ f x - c) s μ := hf.sub (integrableOn_const hs)
  rw [eLpNorm_one_eq_lintegral_eNorm hia.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_eNorm hic.aestronglyMeasurable] at h
  rw [integral_norm_eq_lintegral_eNorm hia.aestronglyMeasurable,
    integral_norm_eq_lintegral_eNorm hic.aestronglyMeasurable, ← ENNReal.toReal_ofNat,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hic.2.ne) h

/-- **The `L^γ` mean oscillation about the average.** On a set `s` of finite measure, for
`1 ≤ γ`, `∫_s ‖f - f_s‖^γ ≤ 2^γ ∫_s ‖f - c‖^γ` for every constant `c` with `‖f - c‖^γ` integrable
on `s`, where `f_s` is the average of `f` over `s`. -/
theorem setIntegral_norm_sub_setAverage_rpow_le_two_rpow_mul (hs : μ s ≠ ⊤) {γ : ℝ} (hγ : 1 ≤ γ)
    (hf : AEStronglyMeasurable f (μ.restrict s)) (c : F)
    (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ γ) s μ) :
    ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ ≤ 2 ^ γ * ∫ x in s, ‖f x - c‖ ^ γ ∂μ := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hp0 : ENNReal.ofReal γ ≠ 0 := by simpa using hγ0
  have hma : AEStronglyMeasurable (fun x ↦ f x - ⨍ y in s, f y ∂μ) (μ.restrict s) :=
    hf.sub aestronglyMeasurable_const
  have hmc : AEStronglyMeasurable (fun x ↦ f x - c) (μ.restrict s) :=
    hf.sub aestronglyMeasurable_const
  -- The `Lᵖ` comparison at `p = γ`, raised to the power `γ`.
  have h := eLpNorm_sub_setAverage_le (μ := μ) (f := f) hs
    (p := ENNReal.ofReal γ) (by simpa using ENNReal.ofReal_le_ofReal hγ) c
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 ENNReal.ofReal_ne_top hma,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 ENNReal.ofReal_ne_top hmc,
    ENNReal.toReal_ofReal hγ0.le] at h
  have h' := ENNReal.rpow_le_rpow h hγ0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hγ0.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ hγ0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hγ0.ne',
    ENNReal.rpow_one] at h'
  -- The right-hand lower integral is finite, since `‖f - c‖^γ` is integrable on `s`.
  have hfin : ∫⁻ x in s, ‖f x - c‖ₑ ^ γ ∂μ ≠ ⊤ := by
    refine ne_of_lt (lt_of_eq_of_lt (lintegral_congr fun x => ?_) hfc.lintegral_lt_top)
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hγ0.le, ofReal_norm]
  -- Both sides are the real parts of the corresponding lower integrals.
  have hconv : ∀ g : X → F, AEStronglyMeasurable g (μ.restrict s) →
      ∫ x in s, ‖g x‖ ^ γ ∂μ = (∫⁻ x in s, ‖g x‖ₑ ^ γ ∂μ).toReal := fun g hg => by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => by positivity)
      (hg.norm.aemeasurable.pow_const γ).aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hγ0.le, ofReal_norm]
  rw [hconv _ hma, hconv _ hmc]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) h').trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  simp

end TauCeti
