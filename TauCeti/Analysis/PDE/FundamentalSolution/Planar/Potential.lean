/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FundamentalSolution.Planar.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
import TauCeti.Analysis.PDE.FundamentalSolution.Planar.DistributionalLaplacian

/-!
# Differentiation and the Poisson equation for planar Newtonian potentials

The first derivative of a smooth real-data potential is convolution with the locally integrable
first derivative of the singular kernel
(`HasCompactSupport.fderiv_planarNewtonianKernel_convolution_apply`).

For `f : ℂ → F` with compact support, the **Newtonian potential** of `f` in the plane is the
convolution `u = G ⋆ f`, `u z = ∫ G(z - w) f(w) dw`, of `f` with the logarithmic kernel
`G = TauCeti.planarNewtonianKernel`, `G z = -(2π)⁻¹ log ‖z‖`. For `f` of class `C²` with compact
support:

* `u` is as smooth as `f`;
* `u` solves **Poisson's equation** `-Δu = f` on all of `ℂ`;
* `u` is harmonic off the support of `f`;
* `u` grows like `G` times the total mass of `f`: `u z - G z • ∫ f → 0` as `z → ∞` (already for
  any `f` with compact support);
* `u` is the **unique** `C²` solution `v` of `-Δv = f` with `v z - G z • ∫ f → 0` at infinity.

Unlike in dimension `n ≥ 3` (`TauCeti.laplacian_newtonianKernel_convolution`), the potential does
not tend to zero at infinity unless `∫ f = 0`; the logarithmic term `G z • ∫ f` is the correct
normalization at infinity. Poisson's equation follows from the distributional identity
`-ΔG = δ` (`TauCeti.integral_laplacian_mul_planarNewtonianKernel_sub`) by
`TauCeti.laplacian_convolution_eq_neg_of_integral_laplacian_mul`, which moves the Laplacian onto
`f` under the convolution. Uniqueness
holds because a harmonic function on `ℂ` that vanishes at infinity is zero
(`InnerProductSpace.HarmonicOnNhd.eq_zero_of_tendsto_cocompact`).

## Main declarations

* `TauCeti.contDiff_planarNewtonianKernel_convolution`: `G ⋆ f` is `C^k` when `f` is `C^k` with
  compact support.
* `TauCeti.laplacian_planarNewtonianKernel_convolution`: `Δ (G ⋆ f) = -f`.
* `TauCeti.harmonicOnNhd_planarNewtonianKernel_convolution`: `G ⋆ f` is harmonic off
  `tsupport f`.
* `TauCeti.tendsto_planarNewtonianKernel_convolution_sub_cocompact`:
  `(G ⋆ f) z - G z • ∫ f → 0` at infinity.
* `TauCeti.eq_planarNewtonianKernel_convolution_of_laplacian_eq_neg`: uniqueness among solutions
  with this behaviour at infinity.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.1, Theorem 1 (the case `n = 2`).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.4 and Section 4.2.
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter InnerProductSpace Laplacian MeasureTheory Metric Set Topology
open scoped Convolution

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℂ → F}

/-- The planar Newtonian potential `G ⋆ f` of a `C^k` function `f` with compact support is
`C^k`. -/
theorem contDiff_planarNewtonianKernel_convolution {k : ℕ∞} (hf : ContDiff ℝ k f)
    (hc : HasCompactSupport f) : ContDiff ℝ k (planarNewtonianKernel ⋆ f) :=
  hc.contDiff_convolution_right _ locallyIntegrable_planarNewtonianKernel hf

/-- **The planar Newtonian potential solves Poisson's equation.** For `f` of class `C²` with
compact support on `ℂ`, the Newtonian potential `u = G ⋆ f` satisfies `-Δu = f`. -/
theorem laplacian_planarNewtonianKernel_convolution [CompleteSpace F] (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : Δ (planarNewtonianKernel ⋆ f) = -f :=
  laplacian_convolution_eq_neg_of_integral_laplacian_mul locallyIntegrable_planarNewtonianKernel
    (fun _ hφ hφc x ↦ by
      simp_rw [planarNewtonianKernel_sub_comm x]
      exact integral_laplacian_mul_planarNewtonianKernel_sub hφ hφc x) hf hc

/-- The planar Newtonian potential of a `C²` function `f` with compact support is harmonic off
the support of `f`. -/
theorem harmonicOnNhd_planarNewtonianKernel_convolution (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    HarmonicOnNhd (planarNewtonianKernel ⋆ f) (tsupport f)ᶜ := fun x hx => by
  refine ⟨(contDiff_planarNewtonianKernel_convolution hf hc).contDiffAt, ?_⟩
  by_cases hF : CompleteSpace F
  swap
  · have h0 : planarNewtonianKernel ⋆ f = 0 :=
      funext fun y => by simp [convolution_def, integral_of_not_completeSpace hF]
    exact Eventually.of_forall fun y => by
      rw [h0]
      exact congrFun (laplacian_const (c := (0 : F))) y
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  rw [laplacian_planarNewtonianKernel_convolution hf hc, Pi.neg_apply,
    image_eq_zero_of_notMem_tsupport hy, neg_zero, Pi.zero_apply]

/-- If `f` vanishes off `closedBall 0 R` and `R + 1 < ‖z‖`, then `y ↦ G (z - y) • f y` is
integrable if and only if `f` is: on the support of `f` the kernel `y ↦ G (z - y)` is bounded and
bounded away from zero. -/
private theorem integrable_planarNewtonianKernel_sub_smul_iff {R : ℝ}
    (hR : Function.support f ⊆ closedBall 0 R) {z : ℂ} (hz : R + 1 < ‖z‖) :
    Integrable (fun w ↦ planarNewtonianKernel (z - w) • f w) ↔ Integrable f := by
  have hz1 : ∀ w ∈ closedBall (0 : ℂ) R, 1 < ‖z - w‖ := fun w hw => by
    linarith [norm_sub_norm_le z w, mem_closedBall_zero_iff.1 hw]
  have hne : ∀ w ∈ closedBall (0 : ℂ) R, planarNewtonianKernel (z - w) ≠ 0 := fun w hw => by
    rw [planarNewtonianKernel_def]
    exact mul_ne_zero (neg_ne_zero.2 (inv_ne_zero (by positivity))) (Real.log_pos (hz1 w hw)).ne'
  have hzw : ∀ w ∈ closedBall (0 : ℂ) R, z - w ≠ 0 := fun w hw =>
    norm_pos_iff.1 (by linarith [hz1 w hw])
  have hcont : ContinuousOn (fun w ↦ planarNewtonianKernel (z - w)) (closedBall 0 R) :=
    fun w hw => ((contDiffAt_planarNewtonianKernel (n := 2) (hzw w hw)).continuousAt.comp
      (continuousAt_const.sub continuousAt_id)).continuousWithinAt
  have hsupp : Function.support (fun w ↦ planarNewtonianKernel (z - w) • f w) ⊆ closedBall 0 R :=
    (Function.support_smul_subset_right _ _).trans hR
  rw [← integrableOn_iff_integrable_of_support_subset hsupp,
    ← integrableOn_iff_integrable_of_support_subset hR]
  refine ⟨fun hg => ?_, fun hf => hf.continuousOn_smul hcont (isCompact_closedBall _ _)⟩
  refine (hg.continuousOn_smul (hcont.inv₀ hne) (isCompact_closedBall _ _)).congr_fun
    (fun w hw => ?_) measurableSet_closedBall
  simp only [Pi.inv_apply, smul_smul, inv_mul_cancel₀ (hne w hw), one_smul]

/-- **The planar Newtonian potential grows logarithmically.** For `f` with compact
support on `ℂ`, `(G ⋆ f) z - G z • ∫ f → 0` as `z → ∞`: far from the support of `f`, the
potential is that of a point mass `∫ f` at the origin. -/
theorem tendsto_planarNewtonianKernel_convolution_sub_cocompact
    (hc : HasCompactSupport f) :
    Tendsto (fun z ↦ (planarNewtonianKernel ⋆ f) z - planarNewtonianKernel z • ∫ w, f w)
      (cocompact ℂ) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRs : Function.support f ⊆ closedBall 0 R := (subset_tsupport f).trans hR
  -- The pointwise bound off a large ball.
  have hbound : ∀ z : ℂ, 2 * R' < ‖z‖ →
      ‖(planarNewtonianKernel ⋆ f) z - planarNewtonianKernel z • ∫ w, f w‖ ≤
        Real.pi⁻¹ * (R' / ‖z‖) * ∫ w, ‖f w‖ := by
    intro z hz
    have hz₀ : 0 < ‖z‖ := by linarith
    have hz1 : R + 1 < ‖z‖ := by linarith [le_max_left R 1, le_max_right R 1]
    have hiff := integrable_planarNewtonianKernel_sub_smul_iff hRs hz1
    by_cases hfi : Integrable f
    swap
    · rw [convolution_lsmul_swap, integral_undef (mt hiff.1 hfi), integral_undef hfi, smul_zero,
        sub_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (inv_nonneg.2 Real.pi_pos.le) (div_nonneg hR'.le hz₀.le))
        (integral_nonneg fun _ => norm_nonneg _)
    have hconv := hiff.2 hfi
    rw [convolution_lsmul_swap, ← integral_smul, ← integral_sub hconv
      (hfi.smul (planarNewtonianKernel z) : Integrable fun w ↦ planarNewtonianKernel z • f w),
      ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hfi.norm.const_mul _) (ae_of_all _ fun w => ?_)
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    by_cases hw : w ∈ tsupport f
    · have hwR : ‖w‖ ≤ R' := (mem_closedBall_zero_iff.1 (hR hw)).trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_right (abs_planarNewtonianKernel_sub_sub_le hwR hz.le hz₀)
        (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hw]
  have hlim : Tendsto (fun z : ℂ ↦ Real.pi⁻¹ * (R' / ‖z‖) * ∫ w, ‖f w‖) (cocompact ℂ)
      (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (tendsto_norm_cocompact_atTop (E := ℂ))).const_mul R'
    simpa [Function.comp_def, div_eq_mul_inv] using
      (h.const_mul Real.pi⁻¹).mul_const (∫ w, ‖f w‖)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (2 * R')] with z hz
  exact hbound z hz

/-- **Uniqueness for Poisson's equation in the plane.** For `f` of class `C²` with compact
support on `ℂ`, the Newtonian potential `G ⋆ f` is the only `C²` solution `v` of `-Δv = f` with
`v z - G z • ∫ f → 0` at infinity. -/
theorem eq_planarNewtonianKernel_convolution_of_laplacian_eq_neg [CompleteSpace F]
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {v : ℂ → F} (hv : ContDiff ℝ 2 v)
    (hΔ : Δ v = -f)
    (hv₀ : Tendsto (fun z ↦ v z - planarNewtonianKernel z • ∫ w, f w) (cocompact ℂ) (𝓝 0)) :
    v = planarNewtonianKernel ⋆ f := by
  have hu := contDiff_planarNewtonianKernel_convolution hf hc
  have hw : HarmonicOnNhd (v - planarNewtonianKernel ⋆ f) univ := fun x _ =>
    ⟨(hv.sub hu).contDiffAt, Eventually.of_forall fun y => by
      rw [hv.contDiffAt.laplacian_sub hu.contDiffAt, hΔ,
        laplacian_planarNewtonianKernel_convolution hf hc, sub_self, Pi.zero_apply]⟩
  have hw₀ := hv₀.sub (tendsto_planarNewtonianKernel_convolution_sub_cocompact hc)
  rw [sub_zero] at hw₀
  refine sub_eq_zero.1 (hw.eq_zero_of_tendsto_cocompact ?_)
  refine hw₀.congr fun z => ?_
  simp

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

end TauCeti
