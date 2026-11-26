/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Minkowski's inequality for square sums

For `2 ≤ p` and a countable family of functions `fᵢ` with values in `[0, ∞]`, the `Lᵖ` seminorm of
the pointwise `ℓ²` norm is at most the `ℓ²` norm of the `Lᵖ` seminorms:

`‖(∑ᵢ fᵢ²)^{1/2}‖_p ≤ (∑ᵢ ‖fᵢ‖_p²)^{1/2}`

(`MeasureTheory.eLpNorm_tsum_sq_rpow_le`). This is Minkowski's inequality for series
(`MeasureTheory.eLpNorm_tsum_le`) in `L^{p/2}`, applied to the squares `fᵢ²`, since
`‖g^{1/2}‖_p = ‖g‖_{p/2}^{1/2}` and `‖fᵢ²‖_{p/2} = ‖fᵢ‖_p²`. The restriction `2 ≤ p` is what
makes `p/2 ≥ 1`, so that the triangle inequality holds in `L^{p/2}`.

The inequality interchanges a square sum with an `Lᵖ` norm. It is how square function estimates,
such as the Littlewood–Paley inequality, combine with estimates for the individual pieces.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Minkowski's inequality for square sums.** For `2 ≤ p`, the `Lᵖ` seminorm of the pointwise
`ℓ²` norm `(∑ᵢ fᵢ²)^{1/2}` of a countable family of almost everywhere measurable functions with
values in `[0, ∞]` is at most the `ℓ²` norm of their `Lᵖ` seminorms. -/
theorem eLpNorm_tsum_sq_rpow_le {ι : Type*} [Countable ι] {f : ι → α → ℝ≥0∞}
    (hf : ∀ i, AEMeasurable (f i) μ) {p : ℝ≥0∞} (hp : 2 ≤ p) :
    eLpNorm (fun x ↦ (∑' i, f i x ^ 2) ^ (2⁻¹ : ℝ)) p μ ≤
      (∑' i, eLpNorm (f i) p μ ^ 2) ^ (2⁻¹ : ℝ) := by
  have hf2 (i : ι) : AEMeasurable (fun x ↦ f i x ^ 2) μ := (hf i).pow_const 2
  have hp2 : 1 ≤ p / 2 := by
    rwa [ENNReal.le_div_iff_mul_le (by simp) (by simp), one_mul]
  -- `‖g ^ (1/2)‖_p = ‖g‖_{p/2} ^ (1/2)` and `‖fᵢ ^ 2‖_{p/2} = ‖fᵢ‖_p ^ 2`.
  have hhalf : eLpNorm (fun x ↦ (∑' i, f i x ^ 2) ^ (2⁻¹ : ℝ)) p μ =
      eLpNorm (fun x ↦ ∑' i, f i x ^ 2) (p / 2) μ ^ (2⁻¹ : ℝ) := by
    have h := eLpNorm_eNorm_rpow (fun x ↦ ∑' i, f i x ^ 2) (p := p)
      (AEMeasurable.tsum hf2).aestronglyMeasurable (by norm_num : (0 : ℝ) < 2⁻¹)
    simp only [eNorm_eq_self] at h
    rw [h, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat, ← div_eq_mul_inv]
  have hsq (i : ι) : eLpNorm (fun x ↦ f i x ^ 2) (p / 2) μ = eLpNorm (f i) p μ ^ 2 := by
    have h := eLpNorm_eNorm_rpow (f i) (p := p / 2) (hf i).aestronglyMeasurable two_pos
    simp only [eNorm_eq_self, ENNReal.rpow_two] at h
    rw [h, ENNReal.ofReal_ofNat, ENNReal.div_mul_cancel (by simp) (by simp)]
  rw [hhalf]
  gcongr
  calc eLpNorm (fun x ↦ ∑' i, f i x ^ 2) (p / 2) μ
      ≤ ∑' i, eLpNorm (fun x ↦ f i x ^ 2) (p / 2) μ := eLpNorm_tsum_le hf2 hp2
    _ = ∑' i, eLpNorm (f i) p μ ^ 2 := by simp_rw [hsq]

end MeasureTheory
