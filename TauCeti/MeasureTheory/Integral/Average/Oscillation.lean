/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Integral.MeanInequalities
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Mean oscillation about the average in `L^γ`

On a set `s` of finite measure, the deviation of an integrable `f` from its average
`f_s = ⨍_s f`, measured in any power `γ ≥ 1`, is at most `2^γ` times its deviation from any
constant `c`:

`∫_s ‖f - f_s‖^γ ≤ 2^γ ∫_s ‖f - c‖^γ`.

This is the Bochner-integral form of the `Lᵖ` comparison `TauCeti.eLpNorm_sub_setAverage_le`. Its
cases `γ = 1` and `γ = 2` give `∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖` and
`∫_s ‖f - f_s‖² ≤ 4 ∫_s ‖f - c‖²`.

On concentric balls `B_ρ ⊆ B_{κρ}` for an additive Haar measure, the comparison splits the `L^γ`
mean oscillation of a sum `g = v + w` into that of `v` on `B_ρ` and the `L^γ` average of `w` on
`B_{κρ}`, with the volume factor `κⁿ`.

## Main results

* `TauCeti.setIntegral_norm_sub_setAverage_rpow_le`: `∫_s ‖f - f_s‖^γ ≤ 2^γ ∫_s ‖f - c‖^γ` for
  `γ ≥ 1`.
* `TauCeti.setIntegral_norm_sub_setAverage_le_two_mul` and
  `TauCeti.setIntegral_norm_sub_setAverage_sq_le`: its cases `γ = 1` and `γ = 2`.
* `TauCeti.integrableOn_norm_rpow_of_memLp` and `TauCeti.integrableOn_norm_sub_const_rpow`: the
  integrability of `‖g‖^γ` for `g ∈ L^γ(s)`, and of `‖g - c‖^γ` along with `‖g‖^γ` on a set of
  finite measure.
* `TauCeti.setAverage_norm_sub_setAverage_rpow_le_add`: the `L^γ` mean oscillation of `v + w` on a
  ball, through that of `v` and the `L^γ` average of `w` on a larger concentric ball.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module
open scoped ENNReal

section Integrability

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F] {s : Set X}

/-- A function in `L^γ(s)`, `0 < γ`, has `‖g‖^γ` integrable on `s`. -/
theorem integrableOn_norm_rpow_of_memLp {g : X → F} {γ : ℝ} (hγ0 : 0 < γ)
    (hg : MemLp g (ENNReal.ofReal γ) (μ.restrict s)) :
    IntegrableOn (fun x ↦ ‖g x‖ ^ γ) s μ := by
  have h := hg.integrable_norm_rpow (by simpa using hγ0) ENNReal.ofReal_ne_top
  rwa [ENNReal.toReal_ofReal hγ0.le] at h

/-- On a set of finite measure, `‖g - c‖^γ` is integrable along with `‖g‖^γ`, for `γ ≥ 1` and every
constant `c`. -/
theorem integrableOn_norm_sub_const_rpow {g : X → F} (hs : μ s ≠ ⊤) {γ : ℝ} (hγ : 1 ≤ γ)
    (hgm : AEStronglyMeasurable g (μ.restrict s)) (hg : IntegrableOn (fun x ↦ ‖g x‖ ^ γ) s μ)
    (c : F) : IntegrableOn (fun x ↦ ‖g x - c‖ ^ γ) s μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hm : MemLp g (ENNReal.ofReal γ) (μ.restrict s) :=
    (integrable_norm_rpow_iff hgm (by simpa using hγ0) ENNReal.ofReal_ne_top).1
      (by rwa [ENNReal.toReal_ofReal hγ0.le])
  exact integrableOn_norm_rpow_of_memLp hγ0 (hm.sub (memLp_const c))

end Integrability

section Comparison

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {f : X → F} {s : Set X}

/-- **The `Lᵖ` mean oscillation about the average, in integral form.** On a set `s` of finite
measure, for `γ ≥ 1` and every constant `c` with `‖f - c‖^γ` integrable on `s`,
`∫_s ‖f - f_s‖^γ ≤ 2^γ ∫_s ‖f - c‖^γ`, where `f_s` is the average of `f` over `s`. -/
theorem setIntegral_norm_sub_setAverage_rpow_le (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ)
    {γ : ℝ} (hγ : 1 ≤ γ) {c : F} (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ γ) s μ) :
    ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ ≤ 2 ^ γ * ∫ x in s, ‖f x - c‖ ^ γ ∂μ := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  set p : ℝ≥0∞ := ENNReal.ofReal γ
  have hp0 : p ≠ 0 := by simpa [p] using hγ0
  have hpt : p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpγ : p.toReal = γ := ENNReal.toReal_ofReal hγ0.le
  have hmc : MemLp (fun x ↦ f x - c) p (μ.restrict s) :=
    (integrable_norm_rpow_iff (hf.sub (integrableOn_const hs)).aestronglyMeasurable hp0 hpt).1
      (by rwa [hpγ])
  have hma : MemLp (fun x ↦ f x - ⨍ y in s, f y ∂μ) p (μ.restrict s) :=
    (hmc.add (memLp_const (c - ⨍ y in s, f y ∂μ))).ae_eq (ae_of_all _ fun x ↦ by
      simp only [Pi.add_apply]
      abel)
  have h := eLpNorm_sub_setAverage_le (μ := μ) (f := f) hs (ENNReal.one_le_ofReal.2 hγ) c
  rw [hma.eLpNorm_eq_integral_rpow_norm hp0 hpt, hmc.eLpNorm_eq_integral_rpow_norm hp0 hpt, hpγ,
    ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul zero_le_two,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have hI₁ : 0 ≤ ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ :=
    integral_nonneg fun _ ↦ by positivity
  have hI₂ : 0 ≤ ∫ x in s, ‖f x - c‖ ^ γ ∂μ := integral_nonneg fun _ ↦ by positivity
  calc ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ
      = ((∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ γ ∂μ) ^ γ⁻¹) ^ γ := by
        rw [← Real.rpow_mul hI₁, inv_mul_cancel₀ hγ0.ne', Real.rpow_one]
    _ ≤ (2 * (∫ x in s, ‖f x - c‖ ^ γ ∂μ) ^ γ⁻¹) ^ γ := by gcongr
    _ = 2 ^ γ * ∫ x in s, ‖f x - c‖ ^ γ ∂μ := by
        rw [Real.mul_rpow zero_le_two (by positivity), ← Real.rpow_mul hI₂,
          inv_mul_cancel₀ hγ0.ne', Real.rpow_one]

/-- **The `L¹` mean oscillation about the average.** On a set `s` of finite measure,
`∫_s ‖f - f_s‖ ≤ 2 ∫_s ‖f - c‖` for every constant `c`, where `f_s` is the average of `f` over
`s`. -/
theorem setIntegral_norm_sub_setAverage_le_two_mul (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ)
    (c : F) : ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ∂μ ≤ 2 * ∫ x in s, ‖f x - c‖ ∂μ := by
  have hfc : IntegrableOn (fun x ↦ f x - c) s μ := hf.sub (integrableOn_const hs)
  simpa only [Real.rpow_one] using setIntegral_norm_sub_setAverage_rpow_le hs hf le_rfl
    (by simp only [Real.rpow_one]; exact hfc.norm)

/-- The square mean oscillation of `f` on a set `s` of finite measure about its own average is at
most four times its square mean oscillation about any constant `c`:
`∫_s ‖f - f_s‖² ≤ 4 ∫_s ‖f - c‖²`. -/
theorem setIntegral_norm_sub_setAverage_sq_le (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ) {c : F}
    (hfc : IntegrableOn (fun x ↦ ‖f x - c‖ ^ 2) s μ) :
    ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ ≤ 4 * ∫ x in s, ‖f x - c‖ ^ 2 ∂μ := by
  have h := setIntegral_norm_sub_setAverage_rpow_le hs hf one_le_two
    (by simpa only [Real.rpow_two] using hfc)
  rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at h
  simpa only [Real.rpow_two] using h

end Comparison

section Ball

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-- **Splitting the mean oscillation on a ball.** Let `g = v + w` on `B_{κρ} = ball c (κ ρ)`,
`κ ≥ 1`, for an additive Haar measure on a space of dimension `n`. Then the `L^γ` mean oscillation
of `g` on `B_ρ`, `γ ≥ 1`, is at most `2^(2γ - 1)` times the sum of that of `v` and of `κⁿ` times
the `L^γ` average of `w` over `B_{κρ}`. -/
theorem setAverage_norm_sub_setAverage_rpow_le_add {g v w : E → F} {c : E} {ρ κ γ : ℝ}
    (hρ : 0 < ρ) (hκ : 1 ≤ κ) (hγ : 1 ≤ γ)
    (hgvw : ∀ᵐ x ∂μ.restrict (ball c (κ * ρ)), g x = v x + w x)
    (hg : IntegrableOn g (ball c (κ * ρ)) μ) (hv : IntegrableOn v (ball c (κ * ρ)) μ)
    (hgγ : IntegrableOn (fun x ↦ ‖g x‖ ^ γ) (ball c (κ * ρ)) μ)
    (hvγ : IntegrableOn (fun x ↦ ‖v x‖ ^ γ) (ball c (κ * ρ)) μ)
    (hwγ : IntegrableOn (fun x ↦ ‖w x‖ ^ γ) (ball c (κ * ρ)) μ) :
    ⨍ x in ball c ρ, ‖g x - ⨍ y in ball c ρ, g y ∂μ‖ ^ γ ∂μ ≤ 2 ^ (2 * γ - 1) *
      ((⨍ x in ball c ρ, ‖v x - ⨍ y in ball c ρ, v y ∂μ‖ ^ γ ∂μ) +
        κ ^ finrank ℝ E * ⨍ x in ball c (κ * ρ), ‖w x‖ ^ γ ∂μ) := by
  have hr : 0 < κ * ρ := mul_pos (zero_lt_one.trans_le hκ) hρ
  have hsub : ball c ρ ⊆ ball c (κ * ρ) := ball_subset_ball (le_mul_of_one_le_left hρ.le hκ)
  have hsρ : μ (ball c ρ) ≠ ⊤ := measure_ball_lt_top.ne
  set P := ⨍ y in ball c ρ, v y ∂μ
  -- Comparison with the constant `P = v_ρ`, then `‖g - P‖ ≤ ‖v - P‖ + ‖w‖` on `B_ρ`.
  have hgP := setIntegral_norm_sub_setAverage_rpow_le hsρ (hg.mono_set hsub) hγ
    (integrableOn_norm_sub_const_rpow hsρ hγ (hg.mono_set hsub).aestronglyMeasurable
      (hgγ.mono_set hsub) P)
  have hsplit := setIntegral_norm_rpow_le_of_ae_norm_le (φ := fun x ↦ g x - P)
    (ψ := fun x ↦ v x - P) hγ ((ae_restrict_of_ae_restrict_of_subset hsub hgvw).mono
      fun x hx ↦ by rw [hx, add_sub_right_comm]; exact norm_add_le _ _)
    (integrableOn_norm_sub_const_rpow hsρ hγ (hv.mono_set hsub).aestronglyMeasurable
      (hvγ.mono_set hsub) P) (hwγ.mono_set hsub)
  have hwρr : ∫ x in ball c ρ, ‖w x‖ ^ γ ∂μ ≤ ∫ x in ball c (κ * ρ), ‖w x‖ ^ γ ∂μ :=
    setIntegral_mono_set hwγ (ae_of_all _ fun _ ↦ by positivity) hsub.eventuallySubset
  have h2 : (2 : ℝ) ^ γ * 2 ^ (γ - 1) = 2 ^ (2 * γ - 1) := by
    rw [← Real.rpow_add two_pos]; ring_nf
  -- Pass to averages, with `|B_{κρ}| = κⁿ |B_ρ|`.
  have hVρ : 0 < μ.real (ball c ρ) := measureReal_ball_pos μ c hρ
  have hVr : μ.real (ball c (κ * ρ)) = κ ^ finrank ℝ E * μ.real (ball c ρ) := by
    rw [μ.addHaar_real_ball_of_pos c hr, μ.addHaar_real_ball_of_pos c hρ, mul_pow]
    ring
  rw [setAverage_eq (f := fun x ↦ ‖g x - ⨍ y in ball c ρ, g y ∂μ‖ ^ γ),
    setAverage_eq (f := fun x ↦ ‖v x - P‖ ^ γ),
    setAverage_eq (f := fun x ↦ ‖w x‖ ^ γ), hVr, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  calc _ ≤ (μ.real (ball c ρ))⁻¹ * (2 ^ (2 * γ - 1) *
          ((∫ x in ball c ρ, ‖v x - P‖ ^ γ ∂μ) + ∫ x in ball c (κ * ρ), ‖w x‖ ^ γ ∂μ)) := by
        gcongr
        calc _ ≤ 2 ^ γ * ∫ x in ball c ρ, ‖g x - P‖ ^ γ ∂μ := hgP
          _ ≤ 2 ^ γ * (2 ^ (γ - 1) * ((∫ x in ball c ρ, ‖v x - P‖ ^ γ ∂μ) +
                ∫ x in ball c (κ * ρ), ‖w x‖ ^ γ ∂μ)) := by
              gcongr
              exact hsplit.trans (by gcongr)
          _ = _ := by rw [← h2, mul_assoc]
    _ = _ := by field_simp

end Ball

end TauCeti
