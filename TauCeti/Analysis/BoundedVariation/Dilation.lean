/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.Distribution.TestFunction.Dilation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dilation of distributional variation and perimeter

Pulling a function and its open domain back by a positive dilation of ratio `r` multiplies its
variation by `r / r ^ n`, where `n` is the dimension. Equivalently, dilating a set and its
ambient open domain multiplies its perimeter by `r ^ (n - 1)` in positive dimension.

The quantities are extended nonnegative reals, so the statements apply to infinite perimeter
and do not require finite volume. The coefficient written as a quotient also covers dimension
zero. A one-sided domain inclusion gives the corresponding localization inequality.

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

/-- Pullback by a positive dilation scales variation by at most its inverse surface factor
when the dilated domain lies in the original domain. -/
theorem totalVariationOn_comp_smul_le (hr : 0 < r) (hVO : MapsTo (fun x : E => r • x) V Ω) :
    totalVariationOn μ V (fun x => u (r • x)) ≤
      ENNReal.ofReal (r / r ^ Module.finrank ℝ E) * totalVariationOn μ Ω u := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  let ψ := dilateTestFunction hr.ne' hVO φ
  have hpair : (∫ y, divergenceCLM ψ y * u y ∂μ) =
      (r ^ Module.finrank ℝ E / r) * ∫ x, divergenceCLM φ x * u (r • x) ∂μ := by
    calc
      (∫ y, divergenceCLM ψ y * u y ∂μ) =
          r⁻¹ * ∫ y, divergenceCLM φ (r⁻¹ • y) * u y ∂μ := by
        simp only [ψ, divergenceCLM_dilateTestFunction, IsSMulApply.smul_apply,
          dilateTestFunction_apply, smul_eq_mul, mul_assoc, integral_const_mul]
      _ = r⁻¹ * (r ^ Module.finrank ℝ E * ∫ x, divergenceCLM φ x * u (r • x) ∂μ) := by
        congr 1
        simpa only [smul_inv_smul₀ hr.ne', smul_eq_mul] using
          μ.integral_comp_inv_smul_of_nonneg
            (fun x => divergenceCLM φ x * u (r • x)) hr.le
      _ = _ := by ring
  have hinv : (∫ x, divergenceCLM φ x * u (r • x) ∂μ) =
      (r / r ^ Module.finrank ℝ E) * ∫ y, divergenceCLM ψ y * u y ∂μ := by
    rw [hpair]
    field_simp
  rw [hinv, ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul_right (ofReal_integral_le_totalVariationOn ψ fun y => by
    simpa only [ψ, dilateTestFunction_apply] using hφ (r⁻¹ • y)) _

/-- Pulling a function and its open domain back by a positive dilation gives the exact
inverse surface scaling of its distributional variation. The quotient coefficient includes
dimension zero. -/
theorem totalVariationOn_comp_smul (hr : 0 < r) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) :
    totalVariationOn μ V (fun x => u (r • x)) =
      ENNReal.ofReal (r / r ^ Module.finrank ℝ E) * totalVariationOn μ Ω u := by
  refine le_antisymm (totalVariationOn_comp_smul_le hr hVO) ?_
  have hle := totalVariationOn_comp_smul_le (μ := μ) (inv_pos.mpr hr) hOV
    (u := fun x => u (r • x))
  simp only [smul_inv_smul₀ hr.ne'] at hle
  have hcancel : ENNReal.ofReal (r / r ^ Module.finrank ℝ E) *
      ENNReal.ofReal (r⁻¹ / (r⁻¹) ^ Module.finrank ℝ E) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have hreal : (r / r ^ Module.finrank ℝ E) *
        (r⁻¹ / (r⁻¹) ^ Module.finrank ℝ E) = 1 := by
      simp only [inv_pow, div_eq_mul_inv, inv_inv]
      field_simp
    rw [hreal, ENNReal.ofReal_one]
  calc
    ENNReal.ofReal (r / r ^ Module.finrank ℝ E) * totalVariationOn μ Ω u ≤
        ENNReal.ofReal (r / r ^ Module.finrank ℝ E) *
          (ENNReal.ofReal (r⁻¹ / (r⁻¹) ^ Module.finrank ℝ E) *
            totalVariationOn μ V (fun x => u (r • x))) := mul_le_mul_right hle _
    _ = _ := by rw [← mul_assoc, hcancel, one_mul]

/-- Canonical preimage-domain form of the variation scaling law. -/
theorem totalVariationOn_comap_smul (hr : 0 < r) :
    totalVariationOn μ (Opens.comap ⟨(r • ·), by fun_prop⟩ Ω) (fun x => u (r • x)) =
      ENNReal.ofReal (r / r ^ Module.finrank ℝ E) * totalVariationOn μ Ω u := by
  apply totalVariationOn_comp_smul hr
  · intro x hx
    exact Opens.mem_comap.mp hx
  · intro y hy
    apply Opens.mem_comap.mpr
    simpa [smul_inv_smul₀ hr.ne'] using hy

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem perimeter_preimage_smul_eq_totalVariationOn :
    perimeter μ V ((r • ·) ⁻¹' s) = totalVariationOn μ V (fun x => s.indicator 1 (r • x)) := by
  simp only [perimeter_def, ← Set.indicator_comp_right, Function.comp_def, Pi.one_def]

/-- Pulling a set back by a positive dilation bounds perimeter by its inverse surface factor
when the dilated domain is contained in the original domain. -/
theorem perimeter_preimage_smul_le (hr : 0 < r)
    (hVO : MapsTo (fun x : E => r • x) V Ω) :
    perimeter μ V ((r • ·) ⁻¹' s) ≤
      ENNReal.ofReal (r / r ^ Module.finrank ℝ E) * perimeter μ Ω s := by
  rw [perimeter_preimage_smul_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comp_smul_le hr hVO

/-- Pulling back a set and its open domain by a positive dilation scales perimeter by the
inverse surface factor. No finite-volume assumption is needed. -/
theorem perimeter_preimage_smul (hr : 0 < r) (hVO : MapsTo (fun x : E => r • x) V Ω)
    (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) :
    perimeter μ V ((r • ·) ⁻¹' s) =
      ENNReal.ofReal (r / r ^ Module.finrank ℝ E) * perimeter μ Ω s := by
  rw [perimeter_preimage_smul_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comp_smul hr hVO hOV

/-- Perimeter scaling with the preimage domain written canonically. -/
theorem perimeter_comap_smul (hr : 0 < r) :
    perimeter μ (Opens.comap ⟨(r • ·), by fun_prop⟩ Ω) ((r • ·) ⁻¹' s) =
      ENNReal.ofReal (r / r ^ Module.finrank ℝ E) * perimeter μ Ω s := by
  rw [perimeter_preimage_smul_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comap_smul hr

/-- Dilating a set and its ambient open domain by a positive ratio scales perimeter by
`r ^ (n - 1)` in positive dimension. This includes sets of infinite volume or perimeter. -/
theorem perimeter_smul [Nontrivial E] (hr : 0 < r)
    (hVO : MapsTo (fun x : E => r • x) V Ω) (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) :
    perimeter μ Ω (r • s) =
      ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * perimeter μ V s := by
  have h := perimeter_preimage_smul (μ := μ) (s := s) (inv_pos.mpr hr) hOV
    (by simpa only [inv_inv] using hVO)
  rw [preimage_smul_inv₀ hr.ne'] at h
  have hfactor : r⁻¹ / (r⁻¹) ^ Module.finrank ℝ E = r ^ (Module.finrank ℝ E - 1) := by
    rw [inv_pow, div_inv_eq_mul,
      pow_sub₀ r hr.ne' (Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos.ne'))]
    simp [mul_comm]
  rwa [hfactor] at h

end TauCeti
