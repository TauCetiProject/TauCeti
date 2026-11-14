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
import Mathlib.Topology.UniformSpace.UniformApproximation

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
kernel continuously in `L¹` on the support disc. So it is for supercritical data
(`TauCeti.continuous_cauchyTransform_of_memLp`), as a locally uniform limit of transforms of
bounded data. On supercritical data supported in discs the
transform is subtractive (`TauCeti.cauchyTransform_sub_of_memLp`).

The normalization is `T f = π⁻¹ ∫ (w - z)⁻¹ • f z`, inverting
`bar∂ = (∂ₛ + i ∂ₜ)/2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Cauchy integral equation in the similarity principle).
-/

public noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped ENNReal Convolution

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


/-- **Continuity of the Cauchy transform of supercritical data.** For `p > 2`, expressed by a
conjugate exponent `q < 2`, the Cauchy transform of `Lᵖ` data supported in a closed disc is
continuous on the whole plane. For `p < ∞` the data are approximated in `Lᵖ` by bounded data
supported in the same disc, whose transforms are continuous
(`TauCeti.continuous_cauchyTransform_of_norm_le`), and the pointwise bound
`TauCeti.norm_cauchyTransform_le` makes the approximation locally uniform. -/
theorem continuous_cauchyTransform_of_memLp [p.HolderConjugate q] (hq : q < 2)
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c r) :
    Continuous (cauchyTransform f) := by
  rcases eq_or_ne p ∞ with rfl | hp
  · refine continuous_cauchyTransform_of_norm_le hf.aestronglyMeasurable hs
      (M := (eLpNorm f ∞ volume).toReal) ?_
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := volume)] with z hz
    have hne : eLpNormEssSup f volume ≠ ∞ := by
      rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]
      exact hf.eLpNorm_ne_top
    rw [← toReal_eNorm, eLpNorm_exponent_top hf.aestronglyMeasurable]
    exact ENNReal.toReal_mono hne hz
  refine continuous_of_locally_uniform_approx_of_continuousAt fun w u hu ↦ ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  set R := dist w c + 1
  set A := Real.pi⁻¹ * (eLpNorm (truncatedCauchyKernel (r + R)) q volume).toReal
  have hA : 0 ≤ A := by positivity
  set δ := ε / (2 * (A + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨g, hgc, hfg, hgcont, hgp⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le hp (ε := ENNReal.ofReal δ) (by simpa using hδ)
  -- the bounded approximant, cut off to the support disc
  obtain ⟨M, hM⟩ := hgcont.bounded_above_of_compact_support hgc
  set g' := (closedBall c r).indicator g
  have hg's : support g' ⊆ closedBall c r := support_indicator_subset
  have hg'p : MemLp g' p volume := hgp.indicator measurableSet_closedBall.nullMeasurableSet
  have hfg' : eLpNorm (f - g') p volume ≤ ENNReal.ofReal δ := by
    have h : f - g' = (closedBall c r).indicator (f - g) := by
      funext z
      by_cases hz : z ∈ closedBall c r
      · simp [g', hz]
      · simp [g', hz, notMem_support.1 fun h ↦ hz (hs h)]
    rw [h]
    exact (eLpNorm_indicator_le _ measurableSet_closedBall.nullMeasurableSet).trans hfg
  refine ⟨closedBall c R, closedBall_mem_nhds_of_mem (by simp [R]),
    cauchyTransform g', (continuous_cauchyTransform_of_norm_le
      (hgcont.aestronglyMeasurable.indicator measurableSet_closedBall) hg's
      (ae_of_all _ fun z ↦ (norm_indicator_le_norm_self g z).trans (hM z))).continuousAt,
    fun y hy ↦ hεu ?_⟩
  rw [dist_eq_norm, ← Pi.sub_apply, ← cauchyTransform_sub_of_memLp hq hf hs hg'p hg's]
  calc _ ≤ A * (eLpNorm (f - g') p volume).toReal :=
        norm_cauchyTransform_le hq (hf.sub hg'p)
          ((support_sub _ _).trans (union_subset hs hg's)) hy
    _ ≤ (A + 1) * δ := by
        gcongr
        · linarith
        · exact ENNReal.toReal_le_of_le_ofReal hδ.le hfg'
    _ < ε := by
        rw [show (A + 1) * δ = ε / 2 by simp only [δ]; field_simp]
        linarith

end TauCeti
