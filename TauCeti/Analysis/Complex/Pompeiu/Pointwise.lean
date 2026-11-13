/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Pointwise bounds for the Cauchy transform of supercritical data

For compactly supported `Lᵖ` data with `p > 2`, the Cauchy integral exists at every point,
not just almost everywhere. On an output disc its norm is bounded by the input `Lᵖ` norm
times the `L^q` norm of the reciprocal kernel truncated at the sum of the input and output
radii, where `q` is conjugate to `p`. The latter norm is finite because `q < 2`.
These bounds are useful for Cauchy integral equations with rough zeroth-order coefficients.
The exponent hypotheses are expressed by a Hölder conjugate pair, allowing `p = ∞`, `q = 1`.
For bounded data the transform is moreover continuous on the whole plane
(`TauCeti.continuous_cauchyTransform_of_norm_le`), since moving the pole moves the reciprocal
kernel continuously in `L¹` on the support disc. On supercritical data supported in discs the
transform is subtractive (`TauCeti.cauchyTransform_sub_of_memLp`) and continuous
(`TauCeti.continuous_cauchyTransform_of_memLp`), by uniform approximation with bounded data.

The normalization is `T f = π⁻¹ ∫ (w - z)⁻¹ • f z`, inverting
`bar∂ = (∂ₛ + i ∂ₜ)/2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Cauchy integral equation in the similarity principle).
-/

public noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped ENNReal Convolution BoundedContinuousFunction

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {f : ℂ → F} {c w : ℂ} {r R : ℝ} {p q : ENNReal}

/-- Supercritical compactly supported data have an absolutely convergent Cauchy integral at
every point. The conjugate exponent condition includes the bounded-data endpoint. -/
theorem integrable_sub_inv_smul_of_memLp [p.HolderConjugate q] (hq : q < 2)
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c r) (w : ℂ) :
    Integrable (fun z ↦ (w - z)⁻¹ • f z) volume := by
  have hw : w ∈ closedBall c (dist w c) := mem_closedBall.mpr le_rfl
  have hk := memLp_truncatedCauchyKernel hq (r + dist w c)
  have hi : Integrable (fun z ↦ truncatedCauchyKernel (r + dist w c) z • f (w - z)) := by
    simpa only [ContinuousLinearMap.lsmul_apply] using
      (ConvolutionExists.of_memLp_memLp (ContinuousLinearMap.lsmul ℝ ℂ) hk hf w).integrable
  have hi' := hi.congr (ae_of_all _ (truncatedCauchyKernel_smul_eq hs hw))
  simpa only [sub_sub_cancel] using hi'.comp_sub_left w

/-- The pointwise Cauchy-transform bound on a fixed output disc. Its explicit kernel factor
is finite for `q < 2`; the constant is independent of the data and of the pole in that disc. -/
theorem enorm_cauchyTransform_le [p.HolderConjugate q] (hf : AEStronglyMeasurable f volume)
    (hs : support f ⊆ closedBall c r) (hw : w ∈ closedBall c R) :
    ‖cauchyTransform f w‖ₑ ≤ ENNReal.ofReal Real.pi⁻¹ *
      eLpNorm (truncatedCauchyKernel (r + R)) q volume * eLpNorm f p volume := by
  rw [cauchyTransform_eq_truncatedCauchyKernel_convolution hs hw, eNorm_smul]
  have hπ : ‖(Real.pi : ℂ)⁻¹‖ₑ = ENNReal.ofReal Real.pi⁻¹ := by
    rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hπ]
  calc
    _ ≤ ENNReal.ofReal Real.pi⁻¹ *
        (‖(ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F)‖ₑ *
          eLpNorm (truncatedCauchyKernel (r + R)) q volume * eLpNorm f p volume) := by
      gcongr
      exact eNorm_convolution_le (ContinuousLinearMap.lsmul ℝ ℂ)
        (measurable_truncatedCauchyKernel _).aestronglyMeasurable hf w
    _ ≤ ENNReal.ofReal Real.pi⁻¹ *
        (1 * eLpNorm (truncatedCauchyKernel (r + R)) q volume * eLpNorm f p volume) := by
      gcongr
      exact ContinuousLinearMap.opENorm_lsmul_le
    _ = _ := by rw [one_mul, mul_assoc]

/-- A finite real bound for the Cauchy transform on a fixed output disc, uniform in the pole
and in the data. The constant depends only on the two radii and the conjugate exponent. -/
theorem norm_cauchyTransform_le [p.HolderConjugate q] (hq : q < 2)
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c r) (hw : w ∈ closedBall c R) :
    ‖cauchyTransform f w‖ ≤ Real.pi⁻¹ *
      (eLpNorm (truncatedCauchyKernel (r + R)) q volume).toReal *
        (eLpNorm f p volume).toReal := by
  have hk := memLp_truncatedCauchyKernel hq (r + R)
  have hb := enorm_cauchyTransform_le (p := p) (q := q) hf.aestronglyMeasurable hs hw
  have hfin : ENNReal.ofReal Real.pi⁻¹ *
      eLpNorm (truncatedCauchyKernel (r + R)) q volume * eLpNorm f p volume ≠ ⊤ := by
    finiteness
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr Real.pi_pos.le),
    toReal_eNorm] using ENNReal.toReal_mono hfin hb

/-- The Cauchy transform is subtractive on supercritical data supported in closed discs. -/
theorem cauchyTransform_sub_of_memLp [p.HolderConjugate q] (hq : q < 2) {g : ℂ → F} {c' : ℂ}
    {r' : ℝ} (hf : MemLp f p volume) (hfs : support f ⊆ closedBall c r) (hg : MemLp g p volume)
    (hgs : support g ⊆ closedBall c' r') :
    cauchyTransform (f - g) = cauchyTransform f - cauchyTransform g := by
  funext w
  simp only [cauchyTransform_apply, Pi.sub_apply, smul_sub]
  rw [integral_sub (integrable_sub_inv_smul_of_memLp hq hf hfs w)
    (integrable_sub_inv_smul_of_memLp hq hg hgs w), smul_sub]

/-- The difference of two values of the Cauchy transform of data supported in a closed disc is
the integral over the disc of the difference of the two reciprocal kernels against the data. -/
theorem cauchyTransform_sub_cauchyTransform_eq_setIntegral [p.HolderConjugate q] (hq : q < 2)
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c r) (w w' : ℂ) :
    cauchyTransform f w' - cauchyTransform f w =
      (Real.pi : ℂ)⁻¹ • ∫ z in closedBall c r, ((w' - z)⁻¹ - (w - z)⁻¹) • f z := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
      simp [notMem_support.1 fun h ↦ hz (hs h)],
    cauchyTransform_apply, cauchyTransform_apply, ← smul_sub]
  simp only [sub_smul]
  rw [integral_sub (integrable_sub_inv_smul_of_memLp hq hf hs w')
    (integrable_sub_inv_smul_of_memLp hq hf hs w)]

/-- **Continuity of the Cauchy transform of bounded data.** The Cauchy transform of an essentially
bounded measurable map supported in a closed disc is continuous on the whole plane: moving the
pole moves the reciprocal kernel continuously in `L¹` on the disc. -/
theorem continuous_cauchyTransform_of_norm_le (hf : AEStronglyMeasurable f volume)
    (hs : support f ⊆ closedBall c r) {M : ℝ} (hM : ∀ᵐ z, ‖f z‖ ≤ M) :
    Continuous (cauchyTransform f) := by
  have hfM : MemLp f ∞ volume := memLp_top_of_bound hf M hM
  -- the difference of two values is controlled by the `L¹` distance of the moved kernels
  have hbound (w w' : ℂ) : ‖cauchyTransform f w' - cauchyTransform f w‖ ≤
      Real.pi⁻¹ * (M * ∫ z in closedBall c r, ‖(z - w')⁻¹ - (z - w)⁻¹‖) := by
    have hk : IntegrableOn (fun z ↦ (w' - z)⁻¹ - (w - z)⁻¹) (closedBall c r) :=
      ((Complex.locallyIntegrable_sub_inv w').integrableOn_isCompact
        (isCompact_closedBall c r)).sub
        ((Complex.locallyIntegrable_sub_inv w).integrableOn_isCompact (isCompact_closedBall c r))
    have hnorm (z : ℂ) : ‖(z - w')⁻¹ - (z - w)⁻¹‖ = ‖(w' - z)⁻¹ - (w - z)⁻¹‖ := by
      rw [← neg_sub w' z, ← neg_sub w z, inv_neg, inv_neg, neg_sub_neg, norm_sub_rev]
    calc ‖cauchyTransform f w' - cauchyTransform f w‖
        = Real.pi⁻¹ * ‖∫ z in closedBall c r, ((w' - z)⁻¹ - (w - z)⁻¹) • f z‖ := by
          rw [cauchyTransform_sub_cauchyTransform_eq_setIntegral (p := ∞) (q := 1) (by norm_num)
            hfM hs, norm_smul]
          simp
      _ ≤ Real.pi⁻¹ * ∫ z in closedBall c r, M * ‖(w' - z)⁻¹ - (w - z)⁻¹‖ := by
          gcongr
          refine norm_integral_le_of_norm_le (hk.norm.const_mul M)
            ((ae_restrict_of_ae hM).mono fun z hz ↦ ?_)
          rw [norm_smul, mul_comm]
          exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ = Real.pi⁻¹ * (M * ∫ z in closedBall c r, ‖(z - w')⁻¹ - (z - w)⁻¹‖) := by
          simp only [hnorm, integral_const_mul]
  refine continuous_iff_continuousAt.2 fun w ↦ tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hlim := (tendsto_integral_norm_sub_inv_sub_sub_inv_closedBall
    (tendsto_id (x := 𝓝 w)) c r).const_mul M |>.const_mul Real.pi⁻¹
  simp only [mul_zero] at hlim
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun w' ↦ hbound w w') hlim

/-- **Continuity of the Cauchy transform of supercritical data.** For a Hölder conjugate pair with
`q < 2`, that is `p > 2`, the Cauchy transform of `Lᵖ` data supported in a closed disc is
continuous on the whole plane. For `p < ∞` the data are approximated in `Lᵖ` by bounded data on
the disc, whose transforms are continuous, and the pointwise bound
`TauCeti.norm_cauchyTransform_le` makes the approximation uniform on every disc. -/
theorem continuous_cauchyTransform_of_memLp [p.HolderConjugate q] (hq : q < 2)
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c r) :
    Continuous (cauchyTransform f) := by
  rcases eq_or_ne p ∞ with rfl | hp
  · refine continuous_cauchyTransform_of_norm_le hf.aestronglyMeasurable hs
      (M := (eLpNormEssSup f volume).toReal) ?_
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume)] with z hz
    rw [← toReal_eNorm]
    exact ENNReal.toReal_mono
      (by rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]; exact hf.eLpNorm_ne_top) hz
  -- bounded continuous approximations, cut off to the disc
  have happrox (n : ℕ) : ∃ g : ℂ →ᵇ F,
      eLpNorm (f - ⇑g) p volume ≤ ENNReal.ofReal (1 / (n + 1)) ∧ MemLp g p volume :=
    hf.exists_boundedContinuous_eLpNorm_sub_le hp
      (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)
  choose g hgf hgp using happrox
  set h : ℕ → ℂ → F := fun n ↦ (closedBall c r).indicator (g n)
  have hhs (n : ℕ) : support (h n) ⊆ closedBall c r := support_indicator_subset
  have hhp (n : ℕ) : MemLp (h n) p volume :=
    (hgp n).indicator measurableSet_closedBall.nullMeasurableSet
  have hhc (n : ℕ) : Continuous (cauchyTransform (h n)) :=
    continuous_cauchyTransform_of_norm_le ((hgp n).aestronglyMeasurable.indicator
      measurableSet_closedBall) (hhs n) (ae_of_all volume fun z : ℂ ↦
        (norm_indicator_le_norm_self (g n) z).trans ((g n).norm_coe_le_norm z))
  have hfh (n : ℕ) : eLpNorm (f - h n) p volume ≤ ENNReal.ofReal (1 / (n + 1)) := by
    have : f - h n = (closedBall c r).indicator (f - ⇑(g n)) := by
      ext z
      by_cases hz : z ∈ closedBall c r
      · simp [h, hz]
      · simp [h, hz, notMem_support.1 fun h' ↦ hz (hs h')]
    rw [this]
    exact (eLpNorm_indicator_le _ measurableSet_closedBall.nullMeasurableSet).trans (hgf n)
  -- the approximations converge uniformly on every disc about `c`
  have hunif (R : ℝ) : TendstoUniformlyOn (fun n ↦ cauchyTransform (h n))
      (cauchyTransform f) atTop (closedBall c R) := by
    set K := Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + R)) q volume).toReal
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (K / ε)
    refine eventually_atTop.2 ⟨N, fun n hn w hw ↦ ?_⟩
    have hsub : cauchyTransform f w - cauchyTransform (h n) w = cauchyTransform (f - h n) w := by
      rw [cauchyTransform_sub_of_memLp hq hf hs (hhp n) (hhs n), Pi.sub_apply]
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    rw [dist_eq_norm, hsub]
    calc ‖cauchyTransform (f - h n) w‖
        ≤ K * (eLpNorm (f - h n) p volume).toReal :=
          norm_cauchyTransform_le hq (hf.sub (hhp n))
            ((support_sub _ _).trans (union_subset hs (hhs n))) hw
      _ ≤ K * (1 / (n + 1)) := by
          gcongr
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hfh n)
      _ < ε := by
          rw [mul_one_div, div_lt_iff₀ hn1]
          have : K / ε < n + 1 := hN.trans_le (by exact_mod_cast hn.trans (Nat.le_succ n))
          rwa [div_lt_iff₀ hε, mul_comm] at this
  refine continuous_iff_continuousAt.2 fun w ↦ ?_
  have hw : closedBall c (dist w c + 1) ∈ 𝓝 w :=
    closedBall_mem_nhds_of_mem (by rw [mem_ball]; linarith)
  exact ((hunif _).continuousOn (Frequently.of_forall fun n ↦ (hhc n).continuousOn))
    |>.continuousAt hw

end TauCeti
