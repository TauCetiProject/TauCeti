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
The transform is moreover continuous on the whole plane
(`TauCeti.continuous_cauchyTransform_of_memLp`, and
`TauCeti.continuous_cauchyTransform_of_norm_le` for bounded data), since moving the pole
translates the truncated reciprocal kernel continuously in `L^q`. On supercritical data supported
in discs the transform is subtractive (`TauCeti.cauchyTransform_sub_of_memLp`).

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

private theorem norm_cauchyTransform_sub_le [p.HolderConjugate q] (hq : q < 2)
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c r) {w w₀ : ℂ}
    (hw : w ∈ closedBall c R) (hw₀ : w₀ ∈ closedBall c R) :
    ‖cauchyTransform f w - cauchyTransform f w₀‖ ≤
      Real.pi⁻¹ *
        (eLpNorm (fun z ↦ truncatedCauchyKernel (r + R) (z + (w - w₀)) -
          truncatedCauchyKernel (r + R) z) q volume).toReal *
          (eLpNorm f p volume).toReal := by
  set K := truncatedCauchyKernel (r + R)
  have hk : MemLp K q volume := memLp_truncatedCauchyKernel hq (r + R)
  have hkw : MemLp (fun z ↦ K (z + (w - w₀))) q volume :=
    hk.comp_measurePreserving (measurePreserving_add_right volume (w - w₀))
  let L := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F)
  have hiw : Integrable (fun z ↦ K (z + (w - w₀)) • f (w₀ - z)) := by
    simpa only [L, ContinuousLinearMap.lsmul_apply] using
      (ConvolutionExists.of_memLp_memLp L hkw hf w₀).integrable
  have hi₀ : Integrable (fun z ↦ K z • f (w₀ - z)) := by
    simpa only [L, ContinuousLinearMap.lsmul_apply] using
      (ConvolutionExists.of_memLp_memLp L hk hf w₀).integrable
  have hshift : (K ⋆[L] f) w - (K ⋆[L] f) w₀ =
      ((fun z ↦ K (z + (w - w₀)) - K z) ⋆[L] f) w₀ := by
    simp only [L, convolution_def, ContinuousLinearMap.lsmul_apply]
    rw [← integral_add_right_eq_self (fun z ↦ K z • f (w - z)) (w - w₀)]
    simp_rw [show ∀ z : ℂ, w - (z + (w - w₀)) = w₀ - z by intro z; abel]
    rw [← integral_sub hiw hi₀]
    simp_rw [sub_smul]
  rw [cauchyTransform_eq_truncatedCauchyKernel_convolution hs hw,
    cauchyTransform_eq_truncatedCauchyKernel_convolution hs hw₀, ← smul_sub, hshift,
    norm_pi_inv_smul]
  have he : ‖((fun z ↦ K (z + (w - w₀)) - K z) ⋆[L] f) w₀‖ₑ ≤
      eLpNorm (fun z ↦ K (z + (w - w₀)) - K z) q volume * eLpNorm f p volume := by
    calc _ ≤ ‖L‖ₑ * eLpNorm (fun z ↦ K (z + (w - w₀)) - K z) q volume * eLpNorm f p volume :=
          eNorm_convolution_le L (hkw.sub hk).aestronglyMeasurable hf.aestronglyMeasurable w₀
      _ ≤ 1 * eLpNorm (fun z ↦ K (z + (w - w₀)) - K z) q volume * eLpNorm f p volume := by
          gcongr
          exact ContinuousLinearMap.opENorm_lsmul_le
      _ = _ := by rw [one_mul]
  have hfin : eLpNorm (fun z ↦ K (z + (w - w₀)) - K z) q volume * eLpNorm f p volume ≠ ⊤ := by
    have := (hkw.sub hk).eLpNorm_lt_top
    have := hf.eLpNorm_lt_top
    finiteness
  have hreal : ‖((fun z ↦ K (z + (w - w₀)) - K z) ⋆[L] f) w₀‖ ≤
      (eLpNorm (fun z ↦ K (z + (w - w₀)) - K z) q volume).toReal *
        (eLpNorm f p volume).toReal := by
    simpa only [ENNReal.toReal_mul, toReal_eNorm] using ENNReal.toReal_mono hfin he
  calc Real.pi⁻¹ * ‖((fun z ↦ K (z + (w - w₀)) - K z) ⋆[L] f) w₀‖
      ≤ Real.pi⁻¹ * ((eLpNorm (fun z ↦ K (z + (w - w₀)) - K z) q volume).toReal *
          (eLpNorm f p volume).toReal) :=
        mul_le_mul_of_nonneg_left hreal (inv_nonneg.2 Real.pi_pos.le)
    _ = _ := (mul_assoc _ _ _).symm

/-- **Continuity of the Cauchy transform of supercritical data.** For compactly supported `Lᵖ`
data whose conjugate exponent satisfies `q < 2` (so `p > 2`, including `p = ∞`, `q = 1`), the
Cauchy transform is continuous on the whole plane: on any neighbourhood of `w₀`, moving the pole
translates a fixed truncated reciprocal kernel continuously in `L^q`. -/
theorem continuous_cauchyTransform_of_memLp [p.HolderConjugate q] (hq : q < 2)
    (hf : MemLp f p volume) (hs : support f ⊆ closedBall c r) :
    Continuous (cauchyTransform f) := by
  refine continuous_iff_continuousAt.2 fun w₀ ↦ tendsto_iff_norm_sub_tendsto_zero.2 ?_
  set R₀ := dist w₀ c + 1
  have hk : MemLp (truncatedCauchyKernel (r + R₀)) q volume :=
    memLp_truncatedCauchyKernel hq (r + R₀)
  have hq1 : 1 ≤ q := ENNReal.HolderConjugate.one_le (p := q) (q := p)
  have hw₀ : w₀ ∈ closedBall c R₀ := mem_closedBall.2 (by dsimp [R₀]; linarith)
  have hbound : ∀ᶠ w in 𝓝 w₀, ‖cauchyTransform f w - cauchyTransform f w₀‖ ≤
      Real.pi⁻¹ * (eLpNorm (fun z ↦ truncatedCauchyKernel (r + R₀) (z + (w - w₀)) -
        truncatedCauchyKernel (r + R₀) z) q volume).toReal * (eLpNorm f p volume).toReal := by
    filter_upwards [ball_mem_nhds w₀ zero_lt_one] with w hw
    exact norm_cauchyTransform_sub_le hq hf hs
      (mem_closedBall.2 ((dist_triangle w w₀ c).trans (by linarith [mem_ball.1 hw]))) hw₀
  have hsub0 : Tendsto (fun w : ℂ ↦ w - w₀) (𝓝 w₀) (𝓝 0) := by
    simpa only [id_eq, sub_self] using (tendsto_id (x := 𝓝 w₀)).sub_const w₀
  have hlim0 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    ((hk.tendsto_eLpNorm_comp_add_sub hq1 (ne_top_of_lt hq)).comp hsub0)).const_mul Real.pi⁻¹
      |>.mul_const (eLpNorm f p volume).toReal
  simp only [ENNReal.toReal_zero, Function.comp_def, mul_zero, zero_mul] at hlim0
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hbound hlim0

/-- **Continuity of the Cauchy transform of bounded data.** The Cauchy transform of an essentially
bounded measurable map supported in a closed disc is continuous on the whole plane. -/
theorem continuous_cauchyTransform_of_norm_le (hf : AEStronglyMeasurable f volume)
    (hs : support f ⊆ closedBall c r) {M : ℝ} (hM : ∀ᵐ z, ‖f z‖ ≤ M) :
    Continuous (cauchyTransform f) :=
  continuous_cauchyTransform_of_memLp (p := ∞) (q := 1) (by norm_num)
    (memLp_top_of_bound hf M hM) hs

end TauCeti
