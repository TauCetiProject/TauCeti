/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# Pointwise bounds for the Cauchy transform of supercritical data

For compactly supported `Lᵖ` data with `p > 2`, the Cauchy integral exists at every point,
not just almost everywhere. On an output disc its norm is bounded by the input `Lᵖ` norm
times the `L^q` norm of the reciprocal kernel truncated at the sum of the input and output
radii, where `q` is conjugate to `p`. The latter norm is finite because `q < 2`.
These bounds are useful for Cauchy integral equations with rough zeroth-order coefficients.
The exponent hypotheses are expressed by a Hölder conjugate pair, allowing `p = ∞`, `q = 1`.
For all supercritical data (`q < 2`) supported in a closed disc, the transform is continuous on the
whole plane (`TauCeti.continuous_cauchyTransform_of_memLp`, with bounded-data corollary
`TauCeti.continuous_cauchyTransform_of_norm_le`), since moving the pole translates a truncated
reciprocal kernel continuously in `L^q`. On supercritical data supported in discs the
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

private theorem norm_cauchyTransform_sub_le_eLpNorm_sub [p.HolderConjugate q] (hq : q < 2)
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c r) {R : ℝ} {w w' : ℂ}
    (hw : w ∈ closedBall c R) (hw' : w' ∈ closedBall c R) :
    ‖cauchyTransform f w' - cauchyTransform f w‖ ≤
      Real.pi⁻¹ * ((eLpNorm (fun u ↦ truncatedCauchyKernel (r + R) (u + (w' - w)) -
          truncatedCauchyKernel (r + R) u) q volume).toReal *
        (eLpNorm f p volume).toReal) := by
  set k := truncatedCauchyKernel (r + R)
  have hk : MemLp k q volume := memLp_truncatedCauchyKernel hq (r + R)
  have hshift : (∫ z, k z • f (w' - z)) = ∫ u, k (u + (w' - w)) • f (w - u) := by
    have h := integral_add_right_eq_self (μ := volume) (fun z ↦ k z • f (w' - z)) (w' - w)
    simpa only [show ∀ u : ℂ, w' - (u + (w' - w)) = w - u by intro; ring] using h.symm
  have hkm : MemLp (fun u ↦ k (u + (w' - w))) q volume :=
    hk.comp_measurePreserving (measurePreserving_add_right volume (w' - w))
  have hi1 : Integrable (fun u ↦ k (u + (w' - w)) • f (w - u)) := by
    simpa only [ContinuousLinearMap.lsmul_apply] using
      (ConvolutionExists.of_memLp_memLp (ContinuousLinearMap.lsmul ℝ ℂ) hkm hf w).integrable
  have hi2 : Integrable (fun u ↦ k u • f (w - u)) := by
    simpa only [ContinuousLinearMap.lsmul_apply] using
      (ConvolutionExists.of_memLp_memLp (ContinuousLinearMap.lsmul ℝ ℂ) hk hf w).integrable
  have hdiff : cauchyTransform f w' - cauchyTransform f w =
      (Real.pi : ℂ)⁻¹ • (((fun u ↦ k (u + (w' - w)) - k u) ⋆[ContinuousLinearMap.lsmul ℝ ℂ] f)
        w) := by
    rw [cauchyTransform_apply, cauchyTransform_apply,
      integral_sub_inv_smul_eq_truncatedCauchyKernel_smul hs hw',
      integral_sub_inv_smul_eq_truncatedCauchyKernel_smul hs hw, hshift, ← smul_sub,
      ← integral_sub hi1 hi2]
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, sub_smul]
  have hconv : ‖((fun u ↦ k (u + (w' - w)) - k u) ⋆[ContinuousLinearMap.lsmul ℝ ℂ] f) w‖ₑ ≤
      eLpNorm (fun u ↦ k (u + (w' - w)) - k u) q volume * eLpNorm f p volume := by
    calc _ ≤ ‖(ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F)‖ₑ *
          eLpNorm (fun u ↦ k (u + (w' - w)) - k u) q volume * eLpNorm f p volume :=
          eNorm_convolution_le (ContinuousLinearMap.lsmul ℝ ℂ)
            (hkm.sub hk).aestronglyMeasurable hf.aestronglyMeasurable w
      _ ≤ 1 * eLpNorm (fun u ↦ k (u + (w' - w)) - k u) q volume * eLpNorm f p volume := by
          gcongr
          exact ContinuousLinearMap.opENorm_lsmul_le
      _ = _ := by rw [one_mul]
  rw [hdiff, norm_pi_inv_smul]
  gcongr
  have hfin : eLpNorm (fun u ↦ k (u + (w' - w)) - k u) q volume * eLpNorm f p volume ≠ ⊤ :=
    ENNReal.mul_ne_top (hkm.sub hk).eLpNorm_ne_top hf.eLpNorm_ne_top
  simpa only [ENNReal.toReal_mul, toReal_eNorm] using ENNReal.toReal_mono hfin hconv

/-- **Continuity of the Cauchy transform of supercritical data.** For `Lᵖ` data supported in a
closed disc whose conjugate exponent satisfies `q < 2` (that is, `2 < p ≤ ∞`), the Cauchy transform
is continuous on the whole plane: near each pole it is a convolution against a fixed truncated
reciprocal kernel in `L^q`, whose translates vary continuously in `L^q`. -/
theorem continuous_cauchyTransform_of_memLp [p.HolderConjugate q] (hq : q < 2)
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c r) :
    Continuous (cauchyTransform f) := by
  refine continuous_iff_continuousAt.2 fun w ↦ tendsto_iff_norm_sub_tendsto_zero.2 ?_
  set R := dist w c + 1
  set k := truncatedCauchyKernel (r + R)
  have hk : MemLp k q volume := memLp_truncatedCauchyKernel hq (r + R)
  have hw : w ∈ closedBall c R := mem_closedBall.2 (by linarith)
  have hbound : ∀ᶠ w' in 𝓝 w, ‖cauchyTransform f w' - cauchyTransform f w‖ ≤
      Real.pi⁻¹ * ((eLpNorm (fun u ↦ k (u + (w' - w)) - k u) q volume).toReal *
        (eLpNorm f p volume).toReal) := by
    filter_upwards [ball_mem_nhds w zero_lt_one] with w' hw'
    exact norm_cauchyTransform_sub_le_eLpNorm_sub hq hf hs hw <|
      mem_closedBall.2 ((dist_triangle w' w c).trans (by linarith [mem_ball.1 hw']))
  have hlim0 : Tendsto (fun w' : ℂ ↦ (eLpNorm (fun u ↦ k (u + (w' - w)) - k u) q volume).toReal)
      (𝓝 w) (𝓝 0) := by
    have hsub : Tendsto (fun w' : ℂ ↦ w' - w) (𝓝 w) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 w)).sub_const w
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        ((hk.tendsto_eLpNorm_comp_add_sub (ENNReal.HolderConjugate.one_le q p) hq.ne_top).comp hsub)
  have hlim := (hlim0.mul_const (eLpNorm f p volume).toReal).const_mul Real.pi⁻¹
  simp only [zero_mul, mul_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hbound hlim

/-- **Continuity of the Cauchy transform of bounded data.** The Cauchy transform of an essentially
bounded measurable map supported in a closed disc is continuous on the whole plane. -/
theorem continuous_cauchyTransform_of_norm_le (hf : AEStronglyMeasurable f volume)
    (hs : support f ⊆ closedBall c r) {M : ℝ} (hM : ∀ᵐ z, ‖f z‖ ≤ M) :
    Continuous (cauchyTransform f) :=
  continuous_cauchyTransform_of_memLp (p := ∞) (q := 1) (by norm_num) (memLp_top_of_bound hf M hM)
    hs

end TauCeti
