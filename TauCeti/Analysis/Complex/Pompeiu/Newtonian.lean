/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Potential
public import TauCeti.Analysis.Complex.Pompeiu.Basic
public import TauCeti.Analysis.Complex.Pompeiu.Holder.Basic
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Gradient
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import TauCeti.Topology.MetricSpace.Holder

/-!
# Cauchy and Newtonian potentials

The Cauchy kernel is the complex combination of the two real first derivatives of the planar
Newtonian kernel. Integration by parts identifies the same combination of derivatives of an
actual Newtonian potential with the actual Cauchy integral.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix B.
-/

public noncomputable section

open MeasureTheory ContinuousLinearMap Complex
open scoped Convolution NNReal

namespace TauCeti

variable {f : ℂ → ℝ}

/-- The derivative of a smooth-data Newtonian potential can be taken on the weak derivative
of the logarithmic kernel, although that kernel is singular at zero. -/
theorem _root_.HasCompactSupport.fderiv_planarNewtonianKernel_convolution_apply
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w v : ℂ) :
    fderiv ℝ (planarNewtonianKernel ⋆ f) w v =
      ∫ z, fderiv ℝ planarNewtonianKernel z v * f (w - z) := by
  have hD := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    locallyIntegrable_planarNewtonianKernel hf w
  rw [hD.fderiv, convolution_precompR_apply _ locallyIntegrable_planarNewtonianKernel
    (hc.fderiv ℝ) (hf.continuous_fderiv one_ne_zero), convolution_def]
  simp only [lsmul_apply, smul_eq_mul]
  let g : ℂ → ℝ := fun z ↦ f (w - z)
  have hg : ContDiff ℝ 1 g := hf.comp (contDiff_const.sub contDiff_id)
  have hcg : HasCompactSupport g := hc.comp_homeomorph (Homeomorph.subLeft w)
  have hderiv (z : ℂ) : fderiv ℝ g z v = -fderiv ℝ f (w - z) v := by
    have h := ((hf.differentiable one_ne_zero (w - z)).hasFDerivAt.comp z
      ((hasFDerivAt_const w z).sub (hasFDerivAt_id z))).fderiv
    simpa only [g, Function.comp_def, zero_sub, ContinuousLinearMap.comp_neg,
      ContinuousLinearMap.comp_id, neg_apply] using congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v) h
  have h := integral_planarNewtonianKernel_mul_fderiv_eq_neg_fderiv_mul hg hcg v
  simp_rw [hderiv, mul_neg] at h
  rw [integral_neg] at h
  exact neg_injective h

/-- The normalized reciprocal is the complex combination of the two real derivatives of the
logarithmic fundamental solution. -/
theorem pi_inv_mul_inv_eq_planarNewtonianKernel_fderiv {z : ℂ} (hz : z ≠ 0) :
    (Real.pi : ℂ)⁻¹ * z⁻¹ =
      -2 * ((fderiv ℝ planarNewtonianKernel z 1 : ℂ) -
        Complex.I * (fderiv ℝ planarNewtonianKernel z Complex.I : ℂ)) := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  apply Complex.ext <;>
    simp [fderiv_planarNewtonianKernel_apply hz, Complex.normSq_eq_norm_sq] <;>
    field_simp [Real.pi_ne_zero, hn] <;> simp [pow_two]

/-- The normalized Cauchy transform of real data is minus four times the complex-linear
Wirtinger derivative of its Newtonian potential, expressed in the two real directions. -/
theorem _root_.HasCompactSupport.pi_inv_smul_integral_sub_inv_smul_eq_newtonian_deriv
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w : ℂ) :
    (Real.pi : ℂ)⁻¹ • (∫ z, (w - z)⁻¹ • (f z : ℂ)) =
      -2 * ((fderiv ℝ (planarNewtonianKernel ⋆ f) w 1 : ℂ) -
        I * (fderiv ℝ (planarNewtonianKernel ⋆ f) w I : ℂ)) := by
  have hfc : Continuous (fun z ↦ f (w - z)) :=
    hf.continuous.comp (continuous_const.sub continuous_id)
  have hfs : HasCompactSupport (fun z ↦ f (w - z)) :=
    hc.comp_homeomorph (Homeomorph.subLeft w)
  have hi (v : ℂ) : Integrable (fun z ↦ fderiv ℝ planarNewtonianKernel z v * f (w - z)) := by
    simpa [mul_comm] using
      (locallyIntegrable_fderiv_planarNewtonianKernel.integrable_smul_left_of_hasCompactSupport
        hfc hfs).apply_continuousLinearMap v
  have hiC (v : ℂ) :
      Integrable (fun z ↦ (fderiv ℝ planarNewtonianKernel z v : ℂ) * (f (w - z) : ℂ)) := by
    simpa using Complex.ofRealCLM.integrable_comp (hi v)
  have hiEq (v : ℂ) :
      (∫ z, fderiv ℝ planarNewtonianKernel z v * f (w - z) : ℝ) =
        ∫ z, (fderiv ℝ planarNewtonianKernel z v : ℂ) * (f (w - z) : ℂ) := by
    simpa using (Complex.ofRealCLM.integral_comp_comm (hi v)).symm
  have hswap : (∫ z, (w - z)⁻¹ * (f z : ℂ)) = ∫ z, z⁻¹ * (f (w - z) : ℂ) := by
    simpa only [sub_sub_cancel] using
      (integral_sub_left_eq_self (fun z : ℂ ↦ (w - z)⁻¹ * (f z : ℂ)) volume w).symm
  simp only [smul_eq_mul]
  rw [hswap]
  calc
    _ = ∫ z, ((Real.pi : ℂ)⁻¹ * z⁻¹) * (f (w - z) : ℂ) := by
      rw [← integral_const_mul]
      congr 1
      funext z
      ring
    _ = ∫ z, -2 * ((fderiv ℝ planarNewtonianKernel z 1 : ℂ) -
        I * (fderiv ℝ planarNewtonianKernel z I : ℂ)) * (f (w - z) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
      rw [pi_inv_mul_inv_eq_planarNewtonianKernel_fderiv hz]
    _ = ∫ z, (-2 : ℂ) * ((fderiv ℝ planarNewtonianKernel z 1 : ℂ) * (f (w - z) : ℂ) -
        I * ((fderiv ℝ planarNewtonianKernel z I : ℂ) * (f (w - z) : ℂ))) := by
      congr 1
      funext z
      ring
    _ = -2 * ((∫ z, (fderiv ℝ planarNewtonianKernel z 1 : ℂ) * (f (w - z) : ℂ)) -
        I * (∫ z, (fderiv ℝ planarNewtonianKernel z I : ℂ) * (f (w - z) : ℂ))) := by
      rw [integral_const_mul, integral_sub (hiC 1) ((hiC I).const_mul I), integral_const_mul]
    _ = _ := by
      rw [← hiEq 1, ← hiEq I,
        ← hc.fderiv_planarNewtonianKernel_convolution_apply hf w 1,
        ← hc.fderiv_planarNewtonianKernel_convolution_apply hf w I]

/-- The two real first derivatives of a Newtonian potential preserve Hölder estimates on a
fixed output disc. The bound is independent of all derivatives of the smooth source. -/
theorem holderOnWith_fderiv_planarNewtonianKernel_convolution
    {c : ℂ} {r R : ℝ} {H α : ℝ≥0} (hα : 0 < α) (hf : HolderWith H α f)
    (hf1 : ContDiff ℝ 1 f) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hs : Function.support f ⊆ Metric.closedBall c r) :
    HolderOnWith ((2 * (r + R)).toNNReal * H) α
      (fun w ↦ fderiv ℝ (planarNewtonianKernel ⋆ f) w 1) (Metric.closedBall c R) ∧
    HolderOnWith ((2 * (r + R)).toNNReal * H) α
      (fun w ↦ fderiv ℝ (planarNewtonianKernel ⋆ f) w I) (Metric.closedBall c R) := by
  have hc := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) hs
  have hfC : HolderWith H α (fun z ↦ (f z : ℂ)) := by
    simpa only [RCLike.ofReal_eq_complex_ofReal, Function.comp_def, one_mul,
      NNReal.one_rpow, mul_one, NNReal.coe_one, NNReal.rpow_one] using
        (RCLike.lipschitzWith_ofReal (K := ℂ)).holderWith.comp hf
  have hsC : Function.support (fun z ↦ (f z : ℂ)) ⊆ Metric.closedBall c r := by
    intro z hz
    apply hs
    intro h
    exact hz (by change (f z : ℂ) = 0; rw [h]; simp)
  have hT := holderOnWith_pi_inv_smul_integral_sub_inv_smul hα hfC hr hR hsC
  let T : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (f z : ℂ)
  have hEq (w : ℂ) := hc.pi_inv_smul_integral_sub_inv_smul_eq_newtonian_deriv hf1 w
  have hdist (x y : ℂ) :
      dist (fderiv ℝ (planarNewtonianKernel ⋆ f) x 1)
          (fderiv ℝ (planarNewtonianKernel ⋆ f) y 1) ≤ dist (T x) (T y) ∧
        dist (fderiv ℝ (planarNewtonianKernel ⋆ f) x I)
          (fderiv ℝ (planarNewtonianKernel ⋆ f) y I) ≤ dist (T x) (T y) := by
    have hre : (T x - T y).re = -2 *
        (fderiv ℝ (planarNewtonianKernel ⋆ f) x 1 -
          fderiv ℝ (planarNewtonianKernel ⋆ f) y 1) := by
      dsimp only [T]
      rw [hEq x, hEq y]
      simp
      ring
    have him : (T x - T y).im = 2 *
        (fderiv ℝ (planarNewtonianKernel ⋆ f) x I -
          fderiv ℝ (planarNewtonianKernel ⋆ f) y I) := by
      dsimp only [T]
      rw [hEq x, hEq y]
      simp
      ring
    have hrn := abs_re_le_norm (T x - T y)
    have hin := abs_im_le_norm (T x - T y)
    rw [hre, abs_mul] at hrn
    rw [him, abs_mul] at hin
    norm_num at hrn hin
    simp only [dist_eq_norm, Real.norm_eq_abs]
    constructor <;> linarith [abs_nonneg
      (fderiv ℝ (planarNewtonianKernel ⋆ f) x 1 -
        fderiv ℝ (planarNewtonianKernel ⋆ f) y 1),
      abs_nonneg (fderiv ℝ (planarNewtonianKernel ⋆ f) x I -
        fderiv ℝ (planarNewtonianKernel ⋆ f) y I)]
  constructor <;> apply HolderOnWith.of_dist_le <;> intro x hx y hy
  · exact (hdist x y).1.trans (hT.dist_le hx hy)
  · exact (hdist x y).2.trans (hT.dist_le hx hy)

/-- The first directional derivatives of a Newtonian potential have uniform fixed-disc bounds
depending on the source supremum, without using its derivatives. -/
theorem norm_fderiv_planarNewtonianKernel_convolution_le
    {c w : ℂ} {r R M : ℝ} (hf : ContDiff ℝ 1 f) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hs : Function.support f ⊆ Metric.closedBall c r) (hM : ∀ z, ‖f z‖ ≤ M)
    (hw : w ∈ Metric.closedBall c R) :
    |fderiv ℝ (planarNewtonianKernel ⋆ f) w 1| ≤ 2 * (r + R) * M ∧
      |fderiv ℝ (planarNewtonianKernel ⋆ f) w I| ≤ 2 * (r + R) * M := by
  have hc := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) hs
  have hsC : Function.support (fun z ↦ (f z : ℂ)) ⊆ Metric.closedBall c r := by
    intro z hz
    apply hs
    intro h
    exact hz (by change (f z : ℂ) = 0; rw [h]; simp)
  have hMC (z : ℂ) : ‖(f z : ℂ)‖ ≤ M := by simpa using hM z
  let T : ℂ := (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (f z : ℂ)
  have hT : ‖T‖ ≤ 2 * (r + R) * M :=
    norm_pi_inv_smul_integral_sub_inv_smul_le hr hR hsC hMC hw
  have hEq := hc.pi_inv_smul_integral_sub_inv_smul_eq_newtonian_deriv hf w
  have hre : T.re = -2 * fderiv ℝ (planarNewtonianKernel ⋆ f) w 1 := by
    dsimp only [T]
    rw [hEq]
    simp
  have him : T.im = 2 * fderiv ℝ (planarNewtonianKernel ⋆ f) w I := by
    dsimp only [T]
    rw [hEq]
    simp
  have hrn := abs_re_le_norm T
  have hin := abs_im_le_norm T
  rw [hre, abs_mul] at hrn
  rw [him, abs_mul] at hin
  norm_num at hrn hin
  constructor <;> linarith [abs_nonneg (fderiv ℝ (planarNewtonianKernel ⋆ f) w 1),
    abs_nonneg (fderiv ℝ (planarNewtonianKernel ⋆ f) w I)]

end TauCeti
