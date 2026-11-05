/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Complex.Pompeiu.Basic
import TauCeti.Analysis.Complex.CauchyKernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Local solutions of the inhomogeneous Cauchy–Riemann equation

The Cauchy transform gives a right inverse for `bar∂` on compactly supported `Cⁿ`
functions into a complex Banach space, for `n ≥ 1`. Cutting off the source inside an
open disc gives a solution on any smaller closed disc, hence near any specified point of an open
domain, with the same regularity.
This supplies integrating factors for scalar Cauchy–Riemann equations.

The construction uses the right-inverse identity in `TauCeti.Analysis.Complex.Pompeiu.Basic`,
where the transform normalized by `(2π)⁻¹` inverts `2 bar∂`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter I.
-/

public noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Real Convolution ContDiff

namespace TauCeti

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  {n : ℕ∞}

/-- A compactly supported `Cⁿ` source, for `n ≥ 1`, has a global `Cⁿ` `bar∂` primitive. -/
theorem exists_contDiff_conjWirtingerDeriv_apply_one_eq_of_hasCompactSupport {f : ℂ → W}
    (hn : 1 ≤ n) (hf : ContDiff ℝ n f) (hfc : HasCompactSupport f) :
    ∃ g : ℂ → W, ContDiff ℝ n g ∧ ∀ z, conjWirtingerDeriv g z 1 = f z := by
  let T := fun w ↦ (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z
  have hT : ContDiff ℝ n T := by
    have hc : ContDiff ℝ n (fun w ↦ ∫ z, (w - z)⁻¹ • f z) := by
      convert hfc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
        Complex.locallyIntegrable_inv hf using 1
      funext w
      simp only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply]
    exact hc.const_smul _
  refine ⟨fun w ↦ (2 : ℂ) • T w, hT.const_smul _, fun z ↦ ?_⟩
  have he := hfc.fderiv_apply_one_add_I_smul_apply_I_two_pi_inv_smul_integral_sub_inv_smul
    (hf.of_le (by exact_mod_cast hn)) z
  rw [conjWirtingerDeriv_apply, fderiv_fun_const_smul (hT.differentiable (by exact_mod_cast
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))) z) (2 : ℂ)]
  simp only [smul_apply, smul_eq_mul, mul_one]
  rw [smul_comm I (2 : ℂ), ← smul_add, smul_smul,
    inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
  exact he

/-- A `Cⁿ` source on an open disc `ball c R`, for `n ≥ 1`, admits a global `Cⁿ` function whose
`bar∂` agrees with the source on any smaller closed disc `closedBall c r`, `0 < r < R`. -/
theorem exists_contDiff_conjWirtingerDeriv_apply_one_eq_on_closedBall {f : ℂ → W} {c : ℂ}
    {r R : ℝ} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f (Metric.ball c R)) (hr : 0 < r) (hrR : r < R) :
    ∃ g : ℂ → W, ContDiff ℝ n g ∧ ∀ z ∈ Metric.closedBall c r, conjWirtingerDeriv g z 1 = f z := by
  let χ : ContDiffBump c := ⟨r, (r + R) / 2, hr, by linarith⟩
  have hs : tsupport χ ⊆ Metric.ball c R := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [χ]; linarith)
  have hcut : ContDiff ℝ n (fun w ↦ χ w • f w) := by
    apply contDiff_iff_contDiffAt.mpr
    intro w
    by_cases hw : w ∈ tsupport χ
    · exact (χ.contDiff (n := n)).contDiffAt.smul
        ((hf w (hs hw)).contDiffAt (Metric.isOpen_ball.mem_nhds (hs hw)))
    · apply (contDiffAt_const (c := (0 : W))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hw] with y hy
      simp [hy]
  obtain ⟨g, hg, heq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq_of_hasCompactSupport
    hn hcut χ.hasCompactSupport.smul_right
  exact ⟨g, hg, fun z hz ↦ by rw [heq, χ.one_of_mem_closedBall hz, one_smul]⟩

/-- A `Cⁿ` source on an open domain, for `n ≥ 1`, admits a global `Cⁿ` function whose
`bar∂` agrees with the source near any specified point of the domain. -/
theorem exists_contDiff_conjWirtingerDeriv_apply_one_eventually_eq {f : ℂ → W} {U : Set ℂ}
    (hn : 1 ≤ n) (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) {z : ℂ} (hz : z ∈ U) :
    ∃ g : ℂ → W, ContDiff ℝ n g ∧ ∀ᶠ w in 𝓝 z, conjWirtingerDeriv g w 1 = f w := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  obtain ⟨g, hg, heq⟩ := exists_contDiff_conjWirtingerDeriv_apply_one_eq_on_closedBall hn
    (hf.mono hsub) (half_pos hr) (half_lt_self hr)
  exact ⟨g, hg, eventually_of_mem (Metric.closedBall_mem_nhds z (half_pos hr)) heq⟩

end TauCeti
