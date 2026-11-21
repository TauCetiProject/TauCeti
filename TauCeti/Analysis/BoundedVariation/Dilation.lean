/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.Distribution.TestFunction.Dilation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.BoundedVariation.Translation

/-!
# Dilation of distributional variation and perimeter

Pulling a function and its open domain back by a dilation of ratio `r` multiplies its variation
by `|r| / |r| ^ n`, where `n` is the dimension. Equivalently, for a nonzero ratio `r`, dilating a
set and its ambient open domain multiplies its perimeter by `|r| ^ (n - 1)`, with truncated
subtraction, hence by `1` in dimension zero.

The quantities are extended nonnegative reals, so the statements apply to infinite perimeter
and do not require finite volume. The pullback coefficient written as a quotient also covers
dimension zero and the degenerate dilation `r = 0`, where both sides vanish. A one-sided domain
inclusion gives the corresponding localization inequality.

Combined with translation invariance, the perimeter in `ball 0 R` of the blow-up
`(fun y => x + r • y) ⁻¹' s` is `|r| / |r| ^ n` times the perimeter of `s` in `ball x (|r| * R)`
(`TauCeti.perimeter_ball_zero_preimage_add_smul`), that is, the perimeter of `s` in
`ball x (|r| * R)` divided by `|r| ^ (n - 1)`
(`TauCeti.perimeter_ball_zero_preimage_add_smul_eq_div`).

The proof uses the divergence of a dilated test vector field and change of variables for an
additive Haar measure; it does not require a derivative measure or boundary regularity.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TestFunction TopologicalSpace
open scoped Distributions ENNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω V : Opens E} {r : ℝ} {u : E → ℝ} {s : Set E}

/-- Pullback by a dilation scales variation by at most its inverse surface factor when the dilated
domain lies in the original domain. -/
theorem totalVariationOn_comp_smul_le (hVO : MapsTo (fun x : E => r • x) V Ω) :
    totalVariationOn μ V (fun x => u (r • x)) ≤
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * totalVariationOn μ Ω u := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [totalVariationOn_const (μ := μ) (Ω := V) (u 0)]
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  let ψ := dilateTestFunction hr hVO φ
  have hpair : (∫ y, divergenceCLM ψ y * u y ∂μ) =
      (|r| ^ Module.finrank ℝ E / r) * ∫ x, divergenceCLM φ x * u (r • x) ∂μ := by
    calc
      (∫ y, divergenceCLM ψ y * u y ∂μ) =
          r⁻¹ * ∫ y, divergenceCLM φ (r⁻¹ • y) * u y ∂μ := by
        simp only [ψ, divergenceCLM_dilateTestFunction, IsSMulApply.smul_apply,
          dilateTestFunction_apply, smul_eq_mul, mul_assoc, integral_const_mul]
      _ = r⁻¹ * (|r| ^ Module.finrank ℝ E * ∫ x, divergenceCLM φ x * u (r • x) ∂μ) := by
        congr 1
        simpa only [smul_inv_smul₀ hr, smul_eq_mul, abs_pow] using
          μ.integral_comp_inv_smul (fun x => divergenceCLM φ x * u (r • x)) r
      _ = _ := by ring
  have hinv : (∫ x, divergenceCLM φ x * u (r • x) ∂μ) =
      (r / |r| ^ Module.finrank ℝ E) * ∫ y, divergenceCLM ψ y * u y ∂μ := by
    rw [hpair]
    field_simp
  calc
    ENNReal.ofReal (∫ x, divergenceCLM φ x * u (r • x) ∂μ) ≤
        ENNReal.ofReal |∫ x, divergenceCLM φ x * u (r • x) ∂μ| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) *
        ENNReal.ofReal |∫ y, divergenceCLM ψ y * u y ∂μ| := by
      rw [hinv, abs_mul, abs_div, abs_pow, abs_abs, ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := mul_le_mul_right (ofReal_abs_integral_le_totalVariationOn ψ fun y => by
      simpa only [ψ, dilateTestFunction_apply] using hφ (r⁻¹ • y)) _

/-- Pulling a function and its open domain back by a dilation gives the exact inverse surface
scaling of its distributional variation. The quotient coefficient includes dimension zero and the
degenerate dilation `r = 0`, where both sides vanish. -/
theorem totalVariationOn_comp_smul (hVO : MapsTo (fun x : E => r • x) V Ω)
    (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) :
    totalVariationOn μ V (fun x => u (r • x)) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * totalVariationOn μ Ω u := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [totalVariationOn_const (μ := μ) (Ω := V) (u 0)]
  refine le_antisymm (totalVariationOn_comp_smul_le hVO) ?_
  have hle := totalVariationOn_comp_smul_le (μ := μ) hOV (u := fun x => u (r • x))
  simp only [smul_inv_smul₀ hr] at hle
  have hcancel : ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) *
      ENNReal.ofReal (|r⁻¹| / |r⁻¹| ^ Module.finrank ℝ E) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have habs : |r| ≠ 0 := abs_ne_zero.mpr hr
    have hreal : (|r| / |r| ^ Module.finrank ℝ E) *
        (|r⁻¹| / |r⁻¹| ^ Module.finrank ℝ E) = 1 := by
      simp only [abs_inv, inv_pow, div_eq_mul_inv, inv_inv]
      field_simp
    rw [hreal, ENNReal.ofReal_one]
  calc
    ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * totalVariationOn μ Ω u ≤
        ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) *
          (ENNReal.ofReal (|r⁻¹| / |r⁻¹| ^ Module.finrank ℝ E) *
            totalVariationOn μ V (fun x => u (r • x))) := mul_le_mul_right hle _
    _ = _ := by rw [← mul_assoc, hcancel, one_mul]

/-- Canonical preimage-domain form of the variation scaling law. -/
theorem totalVariationOn_comap_smul :
    totalVariationOn μ (Opens.comap ⟨(r • ·), by fun_prop⟩ Ω) (fun x => u (r • x)) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * totalVariationOn μ Ω u := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [totalVariationOn_const (μ := μ) (u 0)]
  apply totalVariationOn_comp_smul
  · intro x hx
    exact Opens.mem_comap.mp hx
  · intro y hy
    apply Opens.mem_comap.mpr
    simpa [smul_inv_smul₀ hr] using hy

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem perimeter_preimage_smul_eq_totalVariationOn :
    perimeter μ V ((r • ·) ⁻¹' s) = totalVariationOn μ V (fun x => s.indicator 1 (r • x)) := by
  simp only [perimeter_def, ← Set.indicator_comp_right, Function.comp_def, Pi.one_def]

/-- Pulling a set back by a dilation bounds perimeter by its inverse surface factor when the
dilated domain is contained in the original domain. -/
theorem perimeter_preimage_smul_le (hVO : MapsTo (fun x : E => r • x) V Ω) :
    perimeter μ V ((r • ·) ⁻¹' s) ≤
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * perimeter μ Ω s := by
  rw [perimeter_preimage_smul_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comp_smul_le hVO

/-- Pulling back a set and its open domain by a dilation scales perimeter by the inverse surface
factor. No finite-volume assumption is needed. -/
theorem perimeter_preimage_smul (hVO : MapsTo (fun x : E => r • x) V Ω)
    (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) :
    perimeter μ V ((r • ·) ⁻¹' s) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * perimeter μ Ω s := by
  rw [perimeter_preimage_smul_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comp_smul hVO hOV

/-- Perimeter scaling with the preimage domain written canonically. -/
theorem perimeter_comap_smul :
    perimeter μ (Opens.comap ⟨(r • ·), by fun_prop⟩ Ω) ((r • ·) ⁻¹' s) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * perimeter μ Ω s := by
  rw [perimeter_preimage_smul_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comap_smul

/-- Dilating a set and its ambient open domain by a nonzero ratio `r` scales perimeter by
`|r| ^ (n - 1)`, with truncated subtraction, so the factor is `1` in dimension zero. This includes
sets of infinite volume or perimeter. -/
theorem perimeter_smul (hr : r ≠ 0)
    (hVO : MapsTo (fun x : E => r • x) V Ω) (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) :
    perimeter μ Ω (r • s) =
      ENNReal.ofReal (|r| ^ (Module.finrank ℝ E - 1)) * perimeter μ V s := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp
  have h := perimeter_preimage_smul (μ := μ) (s := s) hOV (by simpa only [inv_inv] using hVO)
  rw [preimage_smul_inv₀ hr] at h
  have hfactor : |r⁻¹| / |r⁻¹| ^ Module.finrank ℝ E = |r| ^ (Module.finrank ℝ E - 1) := by
    rw [abs_inv, inv_pow, div_inv_eq_mul,
      pow_sub₀ |r| (abs_ne_zero.mpr hr) (Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos.ne'))]
    simp [mul_comm]
  rwa [hfactor] at h

/-- **The perimeter of a blow-up in a ball.** Against an additive Haar measure, the perimeter in
`ball 0 R` of the blow-up `(fun y => x + r • y) ⁻¹' s` is `|r| / |r| ^ n` times the perimeter of
`s` in `ball x (|r| * R)`, where `n = dim E`. For `r = 0` both sides vanish. -/
theorem perimeter_ball_zero_preimage_add_smul {x : E} (R : ℝ) :
    perimeter μ ⟨Metric.ball 0 R, Metric.isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) *
        perimeter μ ⟨Metric.ball x (|r| * R), Metric.isOpen_ball⟩ s := by
  rcases eq_or_ne r 0 with rfl | hr
  · by_cases hx : x ∈ s <;> simp [hx]
  have hr' : 0 < |r| := abs_pos.mpr hr
  have h : (fun y => x + r • y) ⁻¹' s = (r • ·) ⁻¹' ((· + x) ⁻¹' s) := by
    ext y
    simp [add_comm]
  rw [h, perimeter_preimage_smul (Ω := ⟨Metric.ball 0 (|r| * R), Metric.isOpen_ball⟩) ?_ ?_,
    perimeter_preimage_add_right (Ω := ⟨Metric.ball x (|r| * R), Metric.isOpen_ball⟩) ?_ ?_]
  · intro y hy
    simpa using hy
  · intro y hy
    simpa [dist_eq_norm] using hy
  · intro y hy
    simpa [norm_smul, mul_lt_mul_iff_right₀ hr'] using hy
  · intro y hy
    simpa [norm_smul, inv_mul_lt_iff₀ hr'] using hy

/-- **The perimeter of a blow-up in a ball, normalized.** Against an additive Haar measure on a
space of dimension `n`, the perimeter in `ball 0 R` of the blow-up `(fun y => x + r • y) ⁻¹' s` is
the perimeter of `s` in `ball x (|r| * R)` divided by `|r| ^ (n - 1)`. For `r = 0` both sides
vanish: the blow-up is `∅` or the whole space, and `ball x 0` is empty. -/
theorem perimeter_ball_zero_preimage_add_smul_eq_div {x : E} (R : ℝ) :
    perimeter μ ⟨Metric.ball 0 R, Metric.isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s) =
      perimeter μ ⟨Metric.ball x (|r| * R), Metric.isOpen_ball⟩ s /
        ENNReal.ofReal (|r| ^ (Module.finrank ℝ E - 1)) := by
  rw [perimeter_ball_zero_preimage_add_smul]
  rcases eq_or_ne r 0 with rfl | hr
  · rw [perimeter_congr_of_inter_eq (t := ∅) (by simp)]
    simp
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank ℝ E = m + 1 :=
    ⟨_, (Nat.sub_add_cancel Module.finrank_pos).symm⟩
  rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 2
  rw [hm, Nat.add_sub_cancel, pow_succ]
  field_simp

end TauCeti
