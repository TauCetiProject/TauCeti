/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.Analysis.Complex.CauchyKernel
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Gradient
import TauCeti.MeasureTheory.Integral.NormRpow
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Worked examples for divergence-form Laplace regularity

Divergence-form Laplace regularity solves `Δξ = ∂ₛf + ∂ₜg` for real data `f, g` through the
Cauchy transform: with `h = f + i g`, the candidate solution is `ξ₀ = ½ Re (T h)`. This file
checks the two pieces of bookkeeping in that argument on explicit data.

* **The solution formula.** For compactly supported `C²` data, `Δ (T h) = 4 ∂h`, because
  `Δ = 4 ∂ \bar∂` and `\bar∂ T = id`. Taking real parts, `Δ (½ Re T h) = ∂ₛf + ∂ₜg`, whereas the
  plausible variant `Re T h` has Laplacian `2 (∂ₛf + ∂ₜg)`, which differs for some data.
* **Exponent bookkeeping on `log ‖z‖`.** Its weak gradient is `z / ‖z‖²`, the data
  `f = s / ‖z‖²` and `g = t / ‖z‖²` are locally `Lʳ` near the origin exactly for `r < 2`, and
  `log ‖z‖` is locally `W^{1,r}` there exactly for `r < 2`. The weak identity
  `∫ ξ Δφ = -∫ (f ∂ₛφ + g ∂ₜφ)` holds for every test function.

## Main results

* `HasCompactSupport.laplacian_cauchyTransform`: `Δ (T h) = 4 ∂h` for compactly supported `C²`
  data.
* `laplacian_half_re_cauchyTransform`: the divergence-form solution formula.
* `exists_laplacian_re_cauchyTransform_ne`: the factor `½` cannot be dropped.
* `hasWeakFDerivOn_log_norm`, `integral_log_norm_mul_laplacian`: the weak gradient of `log ‖z‖`
  and the weak divergence-form identity.
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

section SolutionFormula

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- The Cauchy transform of a compactly supported `Cⁿ` map is `Cⁿ`. -/
private lemma contDiff_cauchyTransform_of_compact {n : ℕ∞} {h : ℂ → F}
    (hc : HasCompactSupport h) (hh : ContDiff ℝ n h) : ContDiff ℝ n (cauchyTransform h) := by
  rw [cauchyTransform_eq_convolution]
  exact (hc.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_inv hh).const_smul _

omit [CompleteSpace F] in
/-- The directional derivative of the Cauchy transform of compactly supported `C¹` data is the
Cauchy transform of the directional derivative. -/
private lemma fderiv_cauchyTransform_apply_of_compact {h : ℂ → F}
    (hc : HasCompactSupport h) (hh : ContDiff ℝ 1 h) (w v : ℂ) :
    fderiv ℝ (cauchyTransform h) w v = cauchyTransform (fun z ↦ fderiv ℝ h z v) w := by
  have hint : Integrable fun z ↦ (w - z)⁻¹ • fderiv ℝ h z :=
    (locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport
      (hh.continuous_fderiv one_ne_zero) (hc.fderiv ℝ)
  rw [(hc.hasFDerivAt_cauchyTransform hh w).fderiv, cauchyTransform_apply,
    smul_apply, ContinuousLinearMap.integral_apply hint]
  rfl

/-- **`Δ = 4 ∂ \bar∂` on the Cauchy transform.** For compactly supported `C²` data `h`, the
Laplacian of `T h` is `4 ∂h = 2 (∂ₛh - i ∂ₜh)`. -/
theorem _root_.HasCompactSupport.laplacian_cauchyTransform {h : ℂ → F}
    (hc : HasCompactSupport h) (hh : ContDiff ℝ 2 h) (w : ℂ) :
    Δ (cauchyTransform h) w = (2 : ℂ) • (fderiv ℝ h w 1 - I • fderiv ℝ h w I) := by
  set u := cauchyTransform h
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hu : ContDiff ℝ 2 u := contDiff_cauchyTransform_of_compact hc hh
  have hu1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hdu (v : ℂ) : (fun y ↦ fderiv ℝ u y v) = cauchyTransform fun z ↦ fderiv ℝ h z v :=
    funext fun y ↦ fderiv_cauchyTransform_apply_of_compact hc hh1 y v
  -- Each directional derivative of `u` is a Cauchy transform, so `\bar∂` inverts it.
  have hdbar (v : ℂ) :
      fderiv ℝ (fun y ↦ fderiv ℝ u y v) w 1 + I • fderiv ℝ (fun y ↦ fderiv ℝ u y v) w I =
        (2 : ℂ) • fderiv ℝ h w v := by
    have hcv : HasCompactSupport fun z ↦ fderiv ℝ h z v :=
      (hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] F ↦ L v) rfl
    have hv : ContDiff ℝ 1 fun z ↦ fderiv ℝ h z v :=
      (hh.fderiv_right (by norm_num)).clm_apply contDiff_const
    have e := hcv.conjWirtingerDeriv_cauchyTransform hv w
    rw [conjWirtingerDeriv_apply, ← hdu, smul_eq_mul, mul_one] at e
    rw [← e, smul_smul]
    norm_num
  have hsymm := (hu.contDiffAt (x := w)).isSymmSndFDerivAt (by simp) I 1
  have hd2 (a b : ℂ) : fderiv ℝ (fun y ↦ fderiv ℝ u y b) w a = fderiv ℝ (fderiv ℝ u) w a b := by
    rw [fderiv_clm_apply ((hu1.differentiable one_ne_zero) w) (differentiableAt_const _)]
    simp
  have hΔ : Δ u w = fderiv ℝ (fun y ↦ fderiv ℝ u y 1) w 1 +
      fderiv ℝ (fun y ↦ fderiv ℝ u y I) w I := by
    rw [laplacian_eq_sum_fderiv_fderiv_apply Complex.orthonormalBasisOneI
      ((hu1.differentiable one_ne_zero) w), Fin.sum_univ_two]
    simp
  have h1 := hdbar 1
  have hI := hdbar I
  rw [hd2, hd2] at h1 hI
  rw [hd2, hd2] at hΔ
  rw [hΔ]
  linear_combination (norm := match_scalars <;> first | ring1 | linear_combination I_sq)
    h1 - I • hI - I • hsymm

end SolutionFormula

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

private lemma contDiff_re_cauchyTransform (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ContDiff ℝ 2 fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re :=
  reCLM.contDiff.comp <|
    contDiff_cauchyTransform_of_compact (hasCompactSupport_ofReal_add_ofReal_mul_I hfc hgc)
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
  have hu : ContDiff ℝ 2 (cauchyTransform h) := contDiff_cauchyTransform_of_compact hhc hh
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
  have hu := contDiff_re_cauchyTransform hf hg hfc hgc
  simp_rw [div_eq_mul_inv]
  rw [show (fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re * 2⁻¹) =
      (2⁻¹ : ℝ) • fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re from
    funext fun _ ↦ mul_comm _ _, laplacian_smul _ hu.contDiffAt,
    laplacian_re_cauchyTransform hf hg hfc hgc w, smul_eq_mul]
  ring

/-- The smoothness half of the solution formula: `½ Re (T h)` is `C²`. -/
theorem contDiff_half_re_cauchyTransform (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ContDiff ℝ 2 fun w ↦ (cauchyTransform (fun z ↦ (f z : ℂ) + (g z : ℂ) * I) w).re / 2 :=
  (contDiff_re_cauchyTransform hf hg hfc hgc).div_const 2

/-- A compactly supported `C¹` function whose horizontal derivative vanishes identically is
zero. -/
private lemma eq_zero_of_fderiv_apply_one_eq_zero (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (h0 : ∀ w, fderiv ℝ f w 1 = 0) (z : ℂ) : f z = 0 := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hφ (t : ℝ) : HasDerivAt (f ∘ fun t : ℝ ↦ z + (t : ℂ)) 0 t := by
    have hl : HasDerivAt (fun t : ℝ ↦ z + (t : ℂ)) 1 t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_add z
    have := ((hf.differentiable one_ne_zero) (z + t)).hasFDerivAt.comp_hasDerivAt t hl
    simpa [h0] using this
  have hconst := is_const_of_deriv_eq_zero (fun t ↦ (hφ t).differentiableAt)
    (fun t ↦ (hφ t).deriv) (|R| + ‖z‖ + 1) 0
  simp only [Function.comp_apply, ofReal_zero, add_zero] at hconst
  rw [← hconst]
  refine image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_
  have hle := mem_closedBall_zero_iff.1 (hR hmem)
  have hlow : ‖((|R| + ‖z‖ + 1 : ℝ) : ℂ)‖ - ‖z‖ ≤ ‖z + ((|R| + ‖z‖ + 1 : ℝ) : ℂ)‖ := by
    have := norm_sub_norm_le ((|R| + ‖z‖ + 1 : ℝ) : ℂ) (-z)
    simpa [sub_neg_eq_add, add_comm] using this
  rw [norm_real, Real.norm_of_nonneg (by positivity)] at hlow
  linarith [le_abs_self R]

/-- **The factor `½` in the solution formula is needed.** There are real compactly supported
smooth data for which `Re (T h)` does not solve `Δξ = ∂ₛf + ∂ₜg`. -/
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

/-- On a compact set, `‖z‖⁻¹` is `Lʳ` for every positive `r < 2`. -/
private lemma memLp_norm_inv_restrict {K : Set ℂ} (hK : IsCompact K) {r : ℝ≥0∞} (hr0 : r ≠ 0)
    (hr : r < 2) : MemLp (fun z : ℂ ↦ ‖z‖⁻¹) r (volume.restrict K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  have hrtop : r ≠ ∞ := (hr.trans_le le_top).ne
  refine MemLp.mono_measure (Measure.restrict_mono hR le_rfl) ?_
  rw [← integrable_norm_rpow_iff (by fun_prop) hr0 hrtop]
  have heq : (fun z : ℂ ↦ ‖‖z‖⁻¹‖ ^ r.toReal) = fun z ↦ ‖z‖ ^ (-r.toReal) := by
    funext z
    rw [Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg z)), Real.inv_rpow (norm_nonneg z),
      Real.rpow_neg (norm_nonneg z)]
  rw [heq]
  refine integrableOn_norm_rpow_ball (E := ℂ) ?_
  have : r.toReal < 2 := by
    simpa using (ENNReal.toReal_lt_toReal hrtop (by simp)).2 hr
  simp only [Complex.finrank_real_complex, Nat.cast_ofNat]
  linarith

/-- On a closed ball of positive radius about the origin, `‖z‖⁻¹` is not `Lʳ` for `r ≥ 2`. -/
private lemma not_memLp_norm_inv_closedBall {ε : ℝ} (hε : 0 < ε) {r : ℝ≥0∞} (hr : 2 ≤ r) :
    ¬ MemLp (fun z : ℂ ↦ ‖z‖⁻¹) r (volume.restrict (closedBall 0 ε)) := by
  intro h
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) ε)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have h2 := h.mono_exponent hr
  rw [← integrable_norm_rpow_iff (by fun_prop) (by simp) (by simp)] at h2
  have heq : (fun z : ℂ ↦ ‖‖z‖⁻¹‖ ^ (2 : ℝ≥0∞).toReal) = fun z ↦ ‖z‖ ^ (-2 : ℝ) := by
    funext z
    rw [Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg z)), Real.inv_rpow (norm_nonneg z),
      Real.rpow_neg (norm_nonneg z)]
    simp
  rw [heq] at h2
  have h3 : IntegrableOn (fun z : ℂ ↦ ‖z‖ ^ (-2 : ℝ)) (ball 0 ε) :=
    IntegrableOn.mono_set h2 ball_subset_closedBall
  have := (integrableOn_norm_rpow_ball_iff (E := ℂ) (mu := volume) hε).1 h3
  norm_num at this

/-- **`‖z‖⁻¹` is locally `Lʳ` near the origin exactly for `r < 2`.** -/
theorem memLpLoc_norm_inv_iff {U : Set ℂ} (hU : U ∈ 𝓝 0) {r : ℝ≥0∞} (hr : r ≠ 0) :
    MemLpLoc r U (fun z : ℂ ↦ ‖z‖⁻¹) ↔ r < 2 := by
  refine ⟨fun h ↦ ?_, fun h ↦ memLpLoc_iff.2 fun K _ hK ↦ memLp_norm_inv_restrict hK hr h⟩
  by_contra! hr2
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hε hr2 (memLpLoc_iff.1 h _ hεU (isCompact_closedBall 0 ε))

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

/-- **The weak gradient of `log ‖z‖`.** On every open subset of the plane, `log ‖z‖` has weak
derivative `v ↦ ⟪z, v⟫ / ‖z‖²`, that is, weak gradient `z / ‖z‖²`. -/
theorem hasWeakFDerivOn_log_norm (Ω : Opens ℂ) :
    HasWeakFDerivOn volume Ω (fun z : ℂ ↦ Real.log ‖z‖)
      fun z ↦ innerSL ℝ ((‖z‖ ^ 2)⁻¹ • z) := by
  have h := (hasWeakFDerivOn_planarNewtonianKernel Ω).const_smul (-(2 * Real.pi))
  have hu : (-(2 * Real.pi)) • planarNewtonianKernel = fun z : ℂ ↦ Real.log ‖z‖ := by
    funext z
    simp only [Pi.smul_apply, planarNewtonianKernel_def, smul_eq_mul]
    field_simp
  rw [hu] at h
  refine h.congr_ae_deriv ?_
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
  ext v
  simp only [Pi.smul_apply, smul_apply, fderiv_planarNewtonianKernel_apply hz,
    innerSL_apply_apply, real_inner_smul_left, smul_eq_mul]
  field_simp

/-- Expanding a real-linear functional on `ℂ` in the basis `1, I`. -/
private lemma clm_apply_eq_re_mul_add_im_mul (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L I := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [show (z.re : ℂ) = z.re • (1 : ℂ) by simp, show (z.im : ℂ) * I = z.im • I by simp,
    map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **The weak divergence-form identity for `log ‖z‖`.** For every test function `φ` on an open
set `Ω`, `∫ log ‖z‖ Δφ = -∫ (f ∂ₛφ + g ∂ₜφ)` with `f = s / ‖z‖²` and `g = t / ‖z‖²`; that is,
`Δ log ‖z‖ = ∂ₛf + ∂ₜg` weakly, with `(f, g)` the weak gradient of `log ‖z‖`. -/
theorem integral_log_norm_mul_laplacian (Ω : Opens ℂ) (φ : 𝓓(Ω, ℝ)) :
    ∫ z, Real.log ‖z‖ * Δ (φ : ℂ → ℝ) z =
      -∫ z, (z.re / ‖z‖ ^ 2 * fderiv ℝ (φ : ℂ → ℝ) z 1 +
        z.im / ‖z‖ ^ 2 * fderiv ℝ (φ : ℂ → ℝ) z I) := by
  have h := (hasWeakFDerivOn_log_norm Ω).integral_laplacian_smul_eq_neg_integral_inner φ
  simp only [smul_eq_mul] at h
  simp_rw [mul_comm (Real.log _)]
  rw [h]
  congr 2
  funext z
  rw [inner_gradient_left, map_smul, clm_apply_eq_re_mul_add_im_mul, smul_eq_mul]
  ring

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
