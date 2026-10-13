/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Hölder's inequality for a function supported in a set

Let `w` vanish almost everywhere off a set `A` of finite measure. For exponents `r, s > 0` with
`1/r + 1/s ≤ 1`, Hölder's inequality with the three exponents `r`, `s` and
`(1 - 1/r - 1/s)⁻¹`, the last applied to the indicator of `A`, gives

`|∫ f w| ≤ ‖f‖_{Lʳ} ‖w‖_{Lˢ} μ(A) ^ (1 - 1/r - 1/s)`.

The factor `μ(A) ^ (1 - 1/r - 1/s)` is what makes the inequality useful when `A` is small. In
Stampacchia's and De Giorgi's methods, `w` is a truncation `(u - k)⁺`, `A` is the superlevel set
`{u > k}`, and the power of its measure is the source of the superlinear gain that drives the
iteration.

## Main declarations

* `TauCeti.MeasureTheory.abs_integral_mul_le_eLpNorm_mul_eLpNorm_mul_measureReal_rpow`: the
  inequality.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace TauCeti

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Hölder's inequality for a function vanishing off a set.** Let `0 < r`, `0 < s` with
`1/r + 1/s ≤ 1`, let `f ∈ Lʳ` and `w ∈ Lˢ`, and suppose that `w` vanishes almost everywhere off a
measurable set `A` of finite measure. Then

`|∫ f w| ≤ ‖f‖_{Lʳ} ‖w‖_{Lˢ} μ(A) ^ (1 - 1/r - 1/s)`. -/
theorem abs_integral_mul_le_eLpNorm_mul_eLpNorm_mul_measureReal_rpow {f w : Ω → ℝ} {r s : ℝ≥0}
    (hr : 0 < r) (hs : 0 < s) (hrs : (r : ℝ)⁻¹ + (s : ℝ)⁻¹ ≤ 1)
    (hf : MemLp f r μ) (hw : MemLp w s μ) {A : Set Ω} (hA : MeasurableSet A) (hAfin : μ A ≠ ∞)
    (hwA : ∀ᵐ x ∂μ, x ∉ A → w x = 0) :
    |∫ x, f x * w x ∂μ| ≤
      (eLpNorm f r μ).toReal * (eLpNorm w s μ).toReal *
        μ.real A ^ (1 - (r : ℝ)⁻¹ - (s : ℝ)⁻¹) := by
  have hr0 : (0 : ℝ) < r := hr
  have hs0 : (0 : ℝ) < s := hs
  -- The exponent `t` conjugate to `s`, with `1/t = 1 - 1/s ≥ 1/r`.
  set τ : ℝ := 1 - (s : ℝ)⁻¹
  have hτ : (r : ℝ)⁻¹ ≤ τ := by simp only [τ]; linarith
  have hτ0 : 0 < τ := (inv_pos.2 hr0).trans_le hτ
  set t : ℝ≥0∞ := ENNReal.ofReal τ⁻¹
  have ht : t.toReal = τ⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.2 hτ0.le)
  have hcoe : ∀ x : ℝ≥0, (x : ℝ≥0∞) = ENNReal.ofReal x := fun x => ENNReal.ofReal_coe_nnreal.symm
  have : ENNReal.HolderTriple t s 1 := by
    refine ⟨?_⟩
    simp only [t]
    rw [inv_one, ENNReal.ofReal_inv_of_pos hτ0, inv_inv, hcoe, ← ENNReal.ofReal_inv_of_pos hs0,
      ← ENNReal.ofReal_add hτ0.le (inv_nonneg.2 hs0.le)]
    simp [τ]
  have htr : t ≤ r := by
    rw [hcoe]
    exact ENNReal.ofReal_le_ofReal ((inv_le_comm₀ hτ0 hr0).2 hτ)
  -- Put the indicator of `A` on `f`, where it costs a power of `μ(A)`.
  have hind : (fun x => f x * w x) =ᵐ[μ] (A.indicator f) • w := by
    filter_upwards [hwA] with x hx
    by_cases hxA : x ∈ A
    · simp [hxA]
    · simp [hxA, hx hxA]
  have hholder : eLpNorm ((A.indicator f) • w) 1 μ ≤
      eLpNorm f r μ * μ A ^ (τ - (r : ℝ)⁻¹) * eLpNorm w s μ := by
    refine (eLpNorm_smul_le_mul_eLpNorm (p := t) (q := s)
      (hf.aestronglyMeasurable.indicator hA) hw.aestronglyMeasurable).trans ?_
    gcongr
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hA.nullMeasurableSet]
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ htr
      hf.aestronglyMeasurable.restrict).trans ?_
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, ht, one_div, inv_inv,
      ENNReal.coe_toReal, one_div]
    gcongr
    exact Measure.restrict_le_self
  have hfin : eLpNorm f r μ * μ A ^ (τ - (r : ℝ)⁻¹) * eLpNorm w s μ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hf.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hτ) hAfin)) hw.eLpNorm_ne_top
  have hmeas : AEStronglyMeasurable ((A.indicator f) • w) μ :=
    (hf.aestronglyMeasurable.indicator hA).smul hw.aestronglyMeasurable
  calc |∫ x, f x * w x ∂μ|
      = ‖∫ x, ((A.indicator f) • w) x ∂μ‖ := by
        rw [integral_congr_ae hind, Real.norm_eq_abs]
    _ ≤ (eLpNorm ((A.indicator f) • w) 1 μ).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm hmeas]
        exact (norm_integral_le_lintegral_norm _).trans_eq (by simp_rw [ofReal_norm])
    _ ≤ _ := by
        refine (ENNReal.toReal_mono hfin hholder).trans_eq ?_
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← measureReal_def]
        simp only [τ]
        ring_nf

end MeasureTheory

end TauCeti
