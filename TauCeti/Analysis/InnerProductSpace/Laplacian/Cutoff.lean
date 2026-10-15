/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Dilated cutoffs with Laplacian bounds

In a finite-dimensional real inner product space, dilating a fixed smooth bump by `R` gives cutoffs
`χ_R`, equal to `1` on `ball 0 R` and to `0` off `closedBall 0 (2R)`, with
`‖Dχ_R‖ = O(1/R)` and `|Δχ_R| = O(1/R²)` uniformly in `R`
(`TauCeti.exists_forall_contDiff_cutoff_ball_norm_laplacian_le`). These are the truncations used
to localize solutions of the Poisson equation: the error `Δ(χ_R u) - χ_R Δu` lives on the annulus
`R ≤ ‖x‖ ≤ 2R` and is controlled by the decay of `u` and `Du` there.
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter Metric Topology
open scoped ContDiff Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Dilated cutoffs with Laplacian bounds.** There is a constant `C` such that for every `R > 0`
some smooth compactly supported `χ` equals `1` near every point of `ball 0 R`, equals `0` near
every point outside `closedBall 0 (2R)`, and satisfies `‖Dχ‖ ≤ C / R` and `|Δχ| ≤ C / R²`. The
cutoff is `x ↦ b (R⁻¹ • x)` for a fixed smooth bump `b` equal to `1` on `closedBall 0 1` and
supported in `closedBall 0 2`. -/
theorem exists_forall_contDiff_cutoff_ball_norm_laplacian_le :
    ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ x, ‖x‖ < R → χ =ᶠ[𝓝 x] fun _ => 1) ∧
        (∀ x, 2 * R < ‖x‖ → χ =ᶠ[𝓝 x] fun _ => 0) ∧ (∀ x, ‖fderiv ℝ χ x‖ ≤ C / R) ∧
          ∀ x, ‖Δ χ x‖ ≤ C / R ^ 2 := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hb : ContDiff ℝ ∞ b := b.contDiff
  obtain ⟨C₁, hC₁⟩ := (hb.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (b.hasCompactSupport.fderiv (𝕜 := ℝ))
  obtain ⟨C₂, hC₂⟩ := (continuousOn_univ.1 ((hb.of_le (by simp)).contDiffOn.continuousOn_laplacian
    isOpen_univ)).bounded_above_of_compact_support
      (b.hasCompactSupport.mono' ((subset_tsupport _).trans (tsupport_laplacian_subset _)))
  refine ⟨max C₁ C₂, fun R hR => ⟨fun x => b (R⁻¹ • x), hb.comp (contDiff_id.const_smul R⁻¹),
    b.hasCompactSupport.comp_smul (inv_ne_zero hR.ne'), fun x hx => ?_, fun x hx => ?_,
    fun x => ?_, fun x => ?_⟩⟩
  · filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
    refine b.one_of_mem_closedBall (mem_closedBall_zero_iff.2 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, inv_mul_le_iff₀ hR, mul_one]
    exact (mem_ball_zero_iff.1 hy).le
  · filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    refine b.zero_of_le_dist ?_
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR,
      le_inv_mul_iff₀ hR]
    have hy' : 2 * R < ‖y‖ := hy
    linarith
  · have h : HasFDerivAt (fun x => b (R⁻¹ • x)) _ x :=
      ((hb.differentiable (by simp)) (R⁻¹ • x)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul R⁻¹)
    rw [h.fderiv]
    refine (opNorm_comp_le _ _).trans ?_
    rw [div_eq_mul_inv]
    refine mul_le_mul ((hC₁ _).trans (le_max_left _ _)) ?_ (norm_nonneg _)
      ((norm_nonneg _).trans ((hC₁ 0).trans (le_max_left _ _)))
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    exact mul_le_of_le_one_right (inv_nonneg.2 hR.le) (norm_id_le)
  · rw [laplacian_comp_smul_right, norm_smul, Real.norm_eq_abs, div_eq_mul_inv, ← inv_pow,
      abs_pow, abs_inv, abs_of_pos hR, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hC₂ _).trans (le_max_right _ _)) (by positivity)

end TauCeti
