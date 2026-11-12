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

/-!
# Pointwise bounds for the Cauchy transform of supercritical data

For compactly supported `Lᵖ` data with `p > 2`, the Cauchy integral exists at every point,
not just almost everywhere. On an output disc its norm is bounded by the input `Lᵖ` norm
times the `L^q` norm of the reciprocal kernel truncated at the sum of the input and output
radii, where `q` is conjugate to `p`. The latter norm is finite because `q < 2`.
These bounds are useful for Cauchy integral equations with rough zeroth-order coefficients.
The exponent hypotheses are expressed by a Hölder conjugate pair, allowing `p = ∞`, `q = 1`.

The normalization is `T f = π⁻¹ ∫ (w - z)⁻¹ • f z`, inverting
`bar∂ = (∂ₛ + i ∂ₜ)/2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the Cauchy integral equation in the similarity principle).
-/

public noncomputable section

open MeasureTheory Metric Set Function
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

end TauCeti
