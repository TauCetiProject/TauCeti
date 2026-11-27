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

and for `1 ≤ γ` the `γ`-th powers satisfy `∫_s ‖f - f_s‖^γ ≤ 2^γ ∫_s ‖f - c‖^γ`; the former is
the case `γ = 1` of the latter.

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

/-- **The `L^γ` mean oscillation about the average.** On a set `s` of finite measure, for
`1 ≤ γ`, `∫_s ‖f - f_s‖^γ ≤ 2^γ ∫_s ‖f - c‖^γ` for every constant `c` with `‖f - c‖^γ` integrable
on `s`, where `f_s` is the average of `f` over `s`. -/
theorem setIntegral_norm_sub_setAverage_rpow_le_two_rpow_mul (hs : μ s ≠ ⊤) {γ : ℝ} (hγ : 1 ≤ γ)
    (hf : AEStronglyMeasurable f (μ.restrict s)) (c : F)
    (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ γ) s μ) :
    ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ ≤ 2 ^ γ * ∫ x in s, ‖f x - c‖ ^ γ ∂μ := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  -- `∫_s ‖g‖^γ` is the real part of `‖g‖_{L^γ(s)}^γ`, the `L¹` norm of `‖g‖^γ`.
  have hconv : ∀ g : X → F, AEStronglyMeasurable g (μ.restrict s) →
      eLpNorm (fun x ↦ ‖g x‖ ^ γ) 1 (μ.restrict s) =
          eLpNorm g (ENNReal.ofReal γ) (μ.restrict s) ^ γ ∧
        ∫ x in s, ‖g x‖ ^ γ ∂μ = (eLpNorm g (ENNReal.ofReal γ) (μ.restrict s) ^ γ).toReal :=
    fun g hg ↦ by
      have h := eLpNorm_norm_rpow (p := 1) g hg hγ0
      rw [one_mul] at h
      refine ⟨h, ?_⟩
      have hm := (hg.norm.aemeasurable.pow_const γ).aestronglyMeasurable
      rw [← h, eLpNorm_one_eq_lintegral_eNorm hm, ← integral_norm_eq_lintegral_eNorm hm]
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) γ)]
  have ha := hconv (fun x ↦ f x - ⨍ y in s, f y ∂μ) (hf.sub aestronglyMeasurable_const)
  have hc := hconv (fun x ↦ f x - c) (hf.sub aestronglyMeasurable_const)
  -- The `Lᵖ` comparison at `p = γ`, raised to the power `γ`.
  have h := ENNReal.rpow_le_rpow (eLpNorm_sub_setAverage_le (μ := μ) (f := f) hs
    (p := ENNReal.ofReal γ) (by simpa using ENNReal.ofReal_le_ofReal hγ) c) hγ0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hγ0.le] at h
  have hfin : eLpNorm (fun x ↦ f x - c) (ENNReal.ofReal γ) (μ.restrict s) ^ γ ≠ ⊤ := by
    rw [← hc.1]
    exact (memLp_one_iff_integrable.2 hfc).eLpNorm_ne_top
  rw [ha.2, hc.2]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) h).trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  simp

/-- **The `L¹` mean oscillation about the average.** On a set `s` of finite measure,
`∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖` for every constant `c`, where `f_s` is the average of `f` over
`s`. -/
theorem setIntegral_norm_sub_setAverage_le_two_mul (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ)
    (c : F) : ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ∂μ ≤ 2 * ∫ x in s, ‖f x - c‖ ∂μ := by
  simpa using setIntegral_norm_sub_setAverage_rpow_le_two_rpow_mul hs le_rfl hf.aestronglyMeasurable
    c (by simp_rw [Real.rpow_one]; exact (hf.sub (integrableOn_const hs)).norm)

end TauCeti
