/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Laplacian
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.MeasureTheory.Integral.NormRpow
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Worked examples for divergence-form Laplace regularity

Divergence-form Laplace regularity solves `Δξ = ∂ₛf + ∂ₜg` for real data `f, g` through the
Cauchy transform: with `h = f + i g`, the candidate solution is `ξ₀ = ½ Re (T h)`. This file
checks the two pieces of bookkeeping in that argument on explicit data.

* **The solution formula.** For compactly supported `C²` data, `Δ (T h) = 4 ∂h`
  (`HasCompactSupport.laplacian_cauchyTransform`). Taking real parts,
  `Δ (½ Re T h) = ∂ₛf + ∂ₜg`, whereas the plausible variant `Re T h` has Laplacian
  `2 (∂ₛf + ∂ₜg)`, which differs for some data.
* **Exponent bookkeeping on `log ‖z‖`.** Its weak gradient is `z / ‖z‖²`
  (`hasWeakFDerivOn_log_norm`), and `Δ log ‖z‖ = ∂ₛf + ∂ₜg` weakly
  (`integral_log_norm_mul_laplacian`). The data `f = s / ‖z‖²` and `g = t / ‖z‖²` are locally
  `Lʳ` near the origin exactly for `r < 2`, and `log ‖z‖` is locally `W^{1,r}` there exactly for
  `r < 2`.

## Main results

* `laplacian_half_re_cauchyTransform`: the divergence-form solution formula.
* `exists_laplacian_re_cauchyTransform_ne`: the factor `½` cannot be dropped.
* `memLpLoc_norm_inv_iff`, `memLpLoc_re_div_and_im_div_iff`, `memWkpLoc_one_log_norm_iff`: the
  exponent bookkeeping.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4.
-/

public noncomputable section

open Complex MeasureTheory Metric Set TopologicalSpace InnerProductSpace Laplacian Filter
open scoped ENNReal Distributions Gradient Topology

namespace TauCeti

/-! ### The classical solution formula -/

section RealData

variable {f g : ℂ → ℝ}

/-- The derivative of `f + i g` for real `f, g`, in each direction. -/
private lemma fderiv_ofReal_add_ofReal_mul_I_apply {w : ℂ} (hf : DifferentiableAt ℝ f w)
    (hg : DifferentiableAt ℝ g w) (v : ℂ) :
    fderiv ℝ (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w v =
      (fderiv ℝ f w v : ℂ) + (fderiv ℝ g w v : ℂ) * I := by
  have hF : HasFDerivAt (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) _ w :=
    (ofRealCLM.hasFDerivAt.comp w hf.hasFDerivAt).add
    ((ofRealCLM.hasFDerivAt.comp w hg.hasFDerivAt).mul_const I)
  rw [hF.fderiv]
  simp [mul_comm]

private lemma contDiff_ofReal_add_ofReal_mul_I {n : ℕ∞} (hf : ContDiff ℝ n f)
    (hg : ContDiff ℝ n g) : ContDiff ℝ n fun z ↦ (f z : ℂ) + (g z : ℂ) * I :=
  (ofRealCLM.contDiff.comp hf).add ((ofRealCLM.contDiff.comp hg).mul contDiff_const)

private lemma hasCompactSupport_ofReal_add_ofReal_mul_I (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) : HasCompactSupport fun z ↦ (f z : ℂ) + (g z : ℂ) * I :=
  (hf.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero).add
    ((hg.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero).mul_right)

private lemma contDiff_re_cauchyTransform {n : ℕ∞} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ContDiff ℝ n fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re :=
  reCLM.contDiff.comp <|
    (hasCompactSupport_ofReal_add_ofReal_mul_I hfc hgc).contDiff_cauchyTransform
      (contDiff_ofReal_add_ofReal_mul_I hf hg)

/-- The real part of the Cauchy transform of `f + i g` has Laplacian `2 (∂ₛf + ∂ₜg)`, twice the
divergence-form right-hand side. -/
theorem laplacian_re_cauchyTransform (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (w : ℂ) :
    Δ (fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re) w =
      2 * (fderiv ℝ f w 1 + fderiv ℝ g w I) := by
  set h : ℂ → ℂ := fun z ↦ (f z : ℂ) + (g z : ℂ) * I
  have hh : ContDiff ℝ 2 h := contDiff_ofReal_add_ofReal_mul_I hf hg
  have hhc : HasCompactSupport h := hasCompactSupport_ofReal_add_ofReal_mul_I hfc hgc
  have hu : ContDiff ℝ 2 (cauchyTransform h) := hhc.contDiff_cauchyTransform hh
  have hre : (fun w ↦ (cauchyTransform h w).re) = reCLM ∘ cauchyTransform h := rfl
  rw [hre, hu.contDiffAt.laplacian_CLM_comp_left, Function.comp_apply,
    hhc.laplacian_cauchyTransform hh w,
    fderiv_ofReal_add_ofReal_mul_I_apply ((hf.differentiable two_ne_zero) w)
      ((hg.differentiable two_ne_zero) w),
    fderiv_ofReal_add_ofReal_mul_I_apply ((hf.differentiable two_ne_zero) w)
      ((hg.differentiable two_ne_zero) w)]
  simp only [reCLM_apply, smul_eq_mul, mul_re, sub_re, add_re, ofReal_re, ofReal_im, I_re, I_im,
    mul_im, add_im, sub_im, re_ofNat, im_ofNat]
  ring

/-- **The divergence-form solution formula.** For real compactly supported `C²` data `f, g` and
`h = f + i g`, the function `ξ₀ = ½ Re (T h)` solves `Δξ₀ = ∂ₛf + ∂ₜg` at every point. -/
theorem laplacian_half_re_cauchyTransform (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (w : ℂ) :
    Δ (fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re / 2) w =
      fderiv ℝ f w 1 + fderiv ℝ g w I := by
  set u := fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re
  have hu : ContDiff ℝ 2 u := contDiff_re_cauchyTransform hf hg hfc hgc
  -- `laplacian_smul` is stated for a scalar multiple `c • u`, so write `u / 2` as `2⁻¹ • u`.
  have hhalf : (fun w ↦ u w / 2) = (2⁻¹ : ℝ) • u :=
    funext fun w ↦ by rw [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  rw [hhalf, laplacian_smul _ hu.contDiffAt, laplacian_re_cauchyTransform hf hg hfc hgc w,
    smul_eq_mul]
  ring

/-- The smoothness half of the solution formula: for `Cⁿ` data, `½ Re (T h)` is `Cⁿ`. -/
theorem contDiff_half_re_cauchyTransform {n : ℕ∞} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ContDiff ℝ n fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re / 2 :=
  (contDiff_re_cauchyTransform hf hg hfc hgc).div_const 2

/-- A compactly supported `C¹` function whose horizontal derivative vanishes identically is
zero. -/
private lemma eq_zero_of_fderiv_apply_one_eq_zero (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (h0 : ∀ w, fderiv ℝ f w 1 = 0) (z : ℂ) : f z = 0 := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  -- Moving `z` horizontally out of the support does not change `f`.
  have hconst := apply_add_eq_of_fderiv_apply_eq_zero (𝕂 := ℝ) (z := z)
    (v := ((|R| + ‖z‖ + 1 : ℝ) : ℂ)) (fun _ _ ↦ (hf.differentiable one_ne_zero) _)
    fun _ _ ↦ by rw [← mul_one ((_ : ℝ) : ℂ), ← real_smul, map_smul, h0, smul_zero]
  rw [← hconst]
  refine image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_
  have hle := mem_closedBall_zero_iff.1 (hR hmem)
  have hlow : ‖((|R| + ‖z‖ + 1 : ℝ) : ℂ)‖ - ‖z‖ ≤ ‖z + ((|R| + ‖z‖ + 1 : ℝ) : ℂ)‖ := by
    have := norm_sub_norm_le ((|R| + ‖z‖ + 1 : ℝ) : ℂ) (-z)
    simpa [sub_neg_eq_add, add_comm] using this
  rw [norm_real, Real.norm_of_nonneg (by positivity)] at hlow
  linarith [le_abs_self R]

/-- **The factor `½` in the solution formula is needed.** There are real compactly supported
`C²` data for which `Re (T h)` does not solve `Δξ = ∂ₛf + ∂ₜg`. -/
theorem exists_laplacian_re_cauchyTransform_ne :
    ∃ f g : ℂ → ℝ, ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧ HasCompactSupport f ∧
      HasCompactSupport g ∧ ∃ w,
        Δ (fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re) w ≠
          fderiv ℝ f w 1 + fderiv ℝ g w I := by
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb : ContDiff ℝ 2 (b : ℂ → ℝ) := b.contDiff
  have hbc : HasCompactSupport (b : ℂ → ℝ) := b.hasCompactSupport
  have hne : ∃ w, fderiv ℝ (b : ℂ → ℝ) w 1 ≠ 0 := by
    by_contra! H
    have h0 := eq_zero_of_fderiv_apply_one_eq_zero (hb.of_le (by norm_num)) hbc H 0
    rw [b.one_of_mem_closedBall (by simp [b])] at h0
    exact one_ne_zero h0
  obtain ⟨w, hw⟩ := hne
  refine ⟨b, 0, hb, contDiff_const, hbc, HasCompactSupport.zero, w, ?_⟩
  rw [laplacian_re_cauchyTransform (g := 0) hb contDiff_const hbc HasCompactSupport.zero w]
  simp only [fderiv_zero, Pi.zero_apply, zero_apply, add_zero]
  intro h
  exact hw (by linarith)

end RealData

/-! ### Exponent bookkeeping on `log ‖z‖` -/

section LogNorm

/-- **`‖z‖⁻¹` is locally `Lʳ` near the origin exactly for `r < 2`.** -/
theorem memLpLoc_norm_inv_iff {U : Set ℂ} (hU : U ∈ 𝓝 0) {r : ℝ≥0∞} (hr : r ≠ 0) :
    MemLpLoc r U (fun z : ℂ ↦ ‖z‖⁻¹) ↔ r < 2 := by
  refine ⟨fun h ↦ ?_, fun h ↦ memLpLoc_iff.2 fun K _ hK ↦
    memLp_norm_inv_restrict hK hr (by simpa [Complex.finrank_real_complex] using h)⟩
  by_contra! hr2
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hε (by simpa [Complex.finrank_real_complex] using hr2)
    (memLpLoc_iff.1 h _ hεU (isCompact_closedBall 0 ε))

/-- **The divergence-form data of `log ‖z‖` are locally `Lʳ` near the origin exactly for
`r < 2`.** These are `f = s / ‖z‖²` and `g = t / ‖z‖²`, the two components of its gradient. -/
theorem memLpLoc_re_div_and_im_div_iff {U : Set ℂ} (hU : U ∈ 𝓝 0) {r : ℝ≥0∞} (hr : r ≠ 0) :
    (MemLpLoc r U (fun z : ℂ ↦ z.re / ‖z‖ ^ 2) ∧ MemLpLoc r U fun z : ℂ ↦ z.im / ‖z‖ ^ 2) ↔
      r < 2 := by
  rw [← memLpLoc_norm_inv_iff hU hr]
  have hdiv (a : ℝ) (z : ℂ) (hz : |a| ≤ ‖z‖) :
      ‖a / ‖z‖ ^ 2‖ ≤ ‖‖z‖⁻¹‖ := by
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    rw [norm_div, norm_pow, norm_norm, Real.norm_eq_abs,
      Real.norm_of_nonneg (inv_nonneg.2 hn.le), div_le_iff₀ (pow_pos hn 2)]
    calc |a| ≤ ‖z‖ := hz
      _ = ‖z‖⁻¹ * ‖z‖ ^ 2 := by field_simp
  constructor
  · rintro ⟨hf, hg⟩
    refine memLpLoc_iff.2 fun K hKU hK ↦ ?_
    refine ((memLpLoc_iff.1 hf K hKU hK).norm.add
      (memLpLoc_iff.1 hg K hKU hK).norm).of_le (by fun_prop) ?_
    filter_upwards with z
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have key : ‖z‖⁻¹ ≤ |z.re| / ‖z‖ ^ 2 + |z.im| / ‖z‖ ^ 2 := by
      rw [← add_div, le_div_iff₀ (pow_pos hn 2)]
      calc ‖z‖⁻¹ * ‖z‖ ^ 2 = ‖z‖ := by field_simp
        _ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    rw [Real.norm_of_nonneg (inv_nonneg.2 hn.le), Pi.add_apply,
      Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    simpa only [Real.norm_eq_abs, abs_div, abs_pow, abs_norm] using key
  · intro h
    exact ⟨memLpLoc_iff.2 fun K hKU hK ↦ (memLpLoc_iff.1 h K hKU hK).of_le
        (by fun_prop : Measurable fun z : ℂ ↦ z.re / ‖z‖ ^ 2).aestronglyMeasurable
        (ae_of_all _ fun z ↦ hdiv _ z (abs_re_le_norm z)),
      memLpLoc_iff.2 fun K hKU hK ↦ (memLpLoc_iff.1 h K hKU hK).of_le
        (by fun_prop : Measurable fun z : ℂ ↦ z.im / ‖z‖ ^ 2).aestronglyMeasurable
        (ae_of_all _ fun z ↦ hdiv _ z (abs_im_le_norm z))⟩

/-- The gradient covector of `log ‖z‖`, `v ↦ ⟪z, v⟫ / ‖z‖²`, set to `0` at the origin. -/
private lemma norm_innerSL_inv_sq_smul (z : ℂ) :
    ‖innerSL ℝ ((‖z‖ ^ 2)⁻¹ • z)‖ = ‖z‖⁻¹ := by
  rw [innerSL_apply_norm, norm_smul, norm_inv, norm_pow, norm_norm]
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  field_simp

/-- **`log ‖z‖` is locally `W^{1,r}` near the origin exactly for `r < 2`.** In particular the
divergence-form regularity statement is consistent at every exponent and claims nothing at
`r = 2`. -/
theorem memWkpLoc_one_log_norm_iff {Ω : Opens ℂ} (h0 : (0 : ℂ) ∈ Ω) {r : ℝ≥0∞} (hr : r ≠ 0) :
    MemWkpLoc r Ω 1 (fun z : ℂ ↦ Real.log ‖z‖) ↔ r < 2 := by
  have hU : (Ω : Set ℂ) ∈ 𝓝 0 := Ω.isOpen.mem_nhds h0
  have hmeas : AEStronglyMeasurable (fun z : ℂ ↦ innerSL ℝ ((‖z‖ ^ 2)⁻¹ • z)) := by
    fun_prop
  simp only [memWkpLoc_succ_iff_of_isOpen, memWkpLoc_zero_iff]
  rw [← memLpLoc_norm_inv_iff hU hr]
  constructor
  · rintro ⟨-, D, hD, hDr⟩
    have hae := hD.ae_eq (hasWeakFDerivOn_log_norm Ω)
    refine memLpLoc_iff.2 fun K hKU hK ↦ ?_
    have := (memLpLoc_iff.1 (hDr.congr_ae hae) K hKU hK).norm
    simpa only [norm_innerSL_inv_sq_smul] using this
  · intro h
    refine ⟨memLpLoc_iff.2 fun K hKU hK ↦ ?_, _, hasWeakFDerivOn_log_norm Ω,
      memLpLoc_iff.2 fun K hKU hK ↦ ?_⟩
    · have hn : MemLp (fun z : ℂ ↦ ‖z‖) r (volume.restrict K) :=
        memLpLoc_iff.1 (continuous_norm.continuousOn.memLpLoc (p := r)) K subset_rfl hK
      refine ((memLpLoc_iff.1 h K hKU hK).add hn).of_le
        (Real.measurable_log.comp measurable_norm).aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
      rw [Pi.add_apply, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
      rcases eq_or_ne z 0 with rfl | hz0
      · simp
      have hn0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
      rw [abs_le]
      constructor
      · have := Real.log_le_sub_one_of_pos (inv_pos.2 hn0)
        rw [Real.log_inv] at this
        linarith
      · linarith [Real.log_le_sub_one_of_pos hn0, inv_pos.2 hn0]
    · exact (memLpLoc_iff.1 h K hKU hK).of_le hmeas.restrict
        (ae_of_all _ fun z ↦ by
          rw [norm_innerSL_inv_sq_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg z))])

end LogNorm

end TauCeti
