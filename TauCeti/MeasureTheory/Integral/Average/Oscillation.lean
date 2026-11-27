/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average

/-!
# The `L¹` mean oscillation about the average

On a set `s` of finite measure, the `L¹` deviation of an integrable `f` from its average
`f_s = ⨍_s f` is at most twice its deviation from any constant `c`:

`∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.

This is the Bochner-integral form, at `p = 1`, of the `Lᵖ` comparison
`TauCeti.eLpNorm_sub_setAverage_le`; its `L²` analogue, with factor `4`, is
`TauCeti.setIntegral_norm_sub_setAverage_sq_le`.

The mean oscillation is subadditive, and the oscillation of a perturbation `g` is at most twice
its average size, so `⨍_s ‖(f + g) - (f + g)_s‖ ≤ ⨍_s ‖f - f_s‖ + 2 ⨍_s ‖g‖`. This compares the
mean oscillation of a function with that of a nearby one, such as a solution of a frozen equation.

## Main results

* `TauCeti.setIntegral_norm_sub_setAverage_le_two_mul`: `∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖`.
* `TauCeti.setAverage_norm_add_sub_setAverage_le`:
  `⨍_s ‖(f + g) - (f + g)_s‖ ≤ ⨍_s ‖f - f_s‖ + 2 ⨍_s ‖g‖`.
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

/-- **Mean oscillation of a perturbation.** For `f` and `g` integrable on `s`,
`⨍_s ‖(f + g) - (f + g)_s‖ ≤ ⨍_s ‖f - f_s‖ + 2 ⨍_s ‖g‖`. On a set of infinite measure every
average vanishes. -/
theorem setAverage_norm_add_sub_setAverage_le {g : X → F} (hf : IntegrableOn f s μ)
    (hg : IntegrableOn g s μ) :
    ⨍ x in s, ‖f x + g x - ⨍ y in s, (f y + g y) ∂μ‖ ∂μ ≤
      ⨍ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ∂μ + 2 * ⨍ x in s, ‖g x‖ ∂μ := by
  rcases eq_or_ne (μ s) ⊤ with hs | hs
  · simp [setAverage_eq, Measure.real, hs]
  have hif : IntegrableOn (fun x => ‖f x - ⨍ y in s, f y ∂μ‖) s μ :=
    (hf.sub (integrableOn_const hs)).norm
  have hig : IntegrableOn (fun x => ‖g x - ⨍ y in s, g y ∂μ‖) s μ :=
    (hg.sub (integrableOn_const hs)).norm
  have hsplit : ∫ x in s, ‖f x + g x - ⨍ y in s, (f y + g y) ∂μ‖ ∂μ ≤
      ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ∂μ + ∫ x in s, ‖g x - ⨍ y in s, g y ∂μ‖ ∂μ := by
    rw [← integral_add hif hig]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hif.add hig)
      (ae_of_all _ fun x => ?_)
    have havg : ⨍ y in s, (f y + g y) ∂μ = (⨍ y in s, f y ∂μ) + ⨍ y in s, g y ∂μ :=
      average_add hf hg
    dsimp only
    rw [havg, add_sub_add_comm]
    exact norm_add_le _ _
  have hg2 := setIntegral_norm_sub_setAverage_le_two_mul hs hg 0
  simp only [sub_zero] at hg2
  set m := ⨍ y in s, (f y + g y) ∂μ
  set mf := ⨍ y in s, f y ∂μ
  simp only [setAverage_eq, smul_eq_mul]
  have hinv : 0 ≤ (μ.real s)⁻¹ := inv_nonneg.2 measureReal_nonneg
  calc (μ.real s)⁻¹ * ∫ x in s, ‖f x + g x - ⨍ y in s, (f y + g y) ∂μ‖ ∂μ
      ≤ (μ.real s)⁻¹ * (∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ∂μ + 2 * ∫ x in s, ‖g x‖ ∂μ) :=
        mul_le_mul_of_nonneg_left (hsplit.trans (add_le_add_right hg2 _)) hinv
    _ = _ := by ring

end TauCeti
