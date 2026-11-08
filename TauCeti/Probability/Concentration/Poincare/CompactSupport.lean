/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.LogSobolev
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compactly supported tests for the Poincaré inequality

For a probability measure on a finite-dimensional real normed space, it is enough to check
the smooth-test Poincaré inequality on compactly supported smooth functions. Spatial cutoffs
converge both in variance and in derivative energy. The measure may be singular, and the
criterion holds for every real constant.

This permits a Poincaré estimate proved for bounded functions with bounded derivatives to
apply to the canonical square-integrable, finite-energy test class.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, §2.3.
* The cutoff argument is adapted from the KLS formalization,
  `FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean`, at
  https://github.com/human-ai-mathematics/kls-lean/tree/65810c73f9dd7945fc646ab484cb19d673f5291d.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} [IsProbabilityMeasure μ] {C : ℝ}

/-- The smooth-test Poincaré inequality can be checked on compactly supported smooth functions. -/
theorem poincareInequality_iff_forall_hasCompactSupport :
    PoincareInequality μ C ↔
      ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        variance f μ ≤ C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  constructor
  · intro h f hf hc
    exact h.apply f hf (hf.continuous.memLp_of_hasCompactSupport hc)
      ((hf.continuous_fderiv (by simp)).norm.memLp_of_hasCompactSupport (hc.fderiv ℝ).norm)
  · intro h
    rw [PoincareInequality_def]
    intro f hf hfL hdf
    obtain ⟨M, hM, hcut⟩ := TauCeti.exists_cutoff_fderiv_bound (E := E)
    have hr (n : ℕ) : (0 : ℝ) < n + 1 := by positivity
    choose χ χ' hχs hχb hχone hχzero hχd hχbound using
      fun n : ℕ ↦ hcut 0 ((n : ℝ) + 1) (hr n)
    let g (n : ℕ) : E → ℝ := fun x ↦ χ n x * f x
    have hgs (n : ℕ) : ContDiff ℝ ∞ (g n) := (hχs n ⊤).mul hf
    have hgc (n : ℕ) : HasCompactSupport (g n) := by
      have hc : HasCompactSupport (χ n) := by
        apply (isCompact_closedBall (0 : E) (2 * ((n : ℝ) + 1))).of_isClosed_subset
          isClosed_closure
        apply closure_minimal _ Metric.isClosed_closedBall
        intro x hx
        rw [Metric.mem_closedBall]
        exact le_of_not_gt fun hx' ↦ hx (hχzero n x hx')
      simpa only [g, Pi.mul_def] using (hc.mul_right (f' := f))
    have hbound (n : ℕ) (x : E) : ‖g n x‖ ≤ ‖f x‖ := by
      dsimp only [g]
      rw [norm_mul, Real.norm_of_nonneg (hχb n x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχb n x).2
    have hgL (n : ℕ) : MemLp (g n) 2 μ :=
      hfL.norm.mono' (hgs n).continuous.aestronglyMeasurable (.of_forall (hbound n))
    have heq (x : E) : ∀ᶠ n : ℕ in atTop, g n =ᶠ[𝓝 x] f := by
      filter_upwards [eventually_ge_atTop (Nat.ceil ‖x‖)] with n hn
      have hx : ‖x‖ < (n : ℝ) + 1 := by
        have hceil := Nat.le_ceil ‖x‖
        have hn' : (Nat.ceil ‖x‖ : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have hxball : x ∈ Metric.ball (0 : E) ((n : ℝ) + 1) := by
        simpa only [Metric.mem_ball, dist_zero_right] using hx
      filter_upwards [Metric.isOpen_ball.mem_nhds hxball] with y hy
      simp only [g, hχone n y (Metric.ball_subset_closedBall hy), one_mul]
    have hgpt (x : E) : Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) := by
      have hp : (fun n ↦ g n x) =ᶠ[atTop] fun _ ↦ f x :=
        (heq x).mono fun _ hn ↦ hn.self_of_nhds
      exact tendsto_const_nhds.congr' hp.symm
    have hmean : Tendsto (fun n ↦ ∫ x, g n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
      tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
        (fun n ↦ (hgs n).continuous.aestronglyMeasurable)
        (hfL.integrable one_le_two).norm (fun n ↦ .of_forall (hbound n)) (.of_forall hgpt)
    have hsecond : Tendsto (fun n ↦ ∫ x, g n x ^ 2 ∂μ) atTop
        (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun x ↦ f x ^ 2)
        (fun n ↦ ((hgs n).continuous.pow 2).aestronglyMeasurable) hfL.integrable_sq
      · intro n
        exact .of_forall fun x ↦ by
          simpa only [Pi.pow_apply, Real.norm_eq_abs,
            abs_of_nonneg (sq_nonneg (g n x)), sq_abs] using
            (sq_le_sq₀ (norm_nonneg (g n x)) (norm_nonneg (f x))).2 (hbound n x)
      · exact .of_forall fun x ↦ (hgpt x).pow 2
    have hvar : Tendsto (fun n ↦ variance (g n) μ) atTop (𝓝 (variance f μ)) := by
      simp_rw [variance_eq_sub (hgL _), variance_eq_sub hfL]
      exact hsecond.sub (hmean.pow 2)
    have hdg (n : ℕ) (x : E) :
        fderiv ℝ (g n) x = χ n x • fderiv ℝ f x + f x • χ' n x := by
      exact ((hχd n x).mul ((hf.differentiable (by simp) x).hasFDerivAt)).fderiv
    have hgrad (n : ℕ) (x : E) :
        ‖fderiv ℝ (g n) x‖ ≤ ‖fderiv ℝ f x‖ + M * ‖f x‖ := by
      have hd : ‖χ' n x‖ ≤ M := (hχbound n x).trans <| by
        exact mul_le_of_le_one_right hM
          ((inv_le_one₀ (hr n)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n]))
      rw [hdg]
      calc
        _ ≤ ‖χ n x • fderiv ℝ f x‖ + ‖f x • χ' n x‖ := norm_add_le _ _
        _ = χ n x * ‖fderiv ℝ f x‖ + ‖f x‖ * ‖χ' n x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (hχb n x).1]
        _ ≤ ‖fderiv ℝ f x‖ + ‖f x‖ * M :=
          add_le_add (mul_le_of_le_one_left (norm_nonneg _) (hχb n x).2)
            (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
        _ = ‖fderiv ℝ f x‖ + M * ‖f x‖ := by rw [mul_comm ‖f x‖ M]
    have hdomL : MemLp (fun x ↦ ‖fderiv ℝ f x‖ + M * ‖f x‖) 2 μ :=
      hdf.add (hfL.norm.const_mul M)
    have henergy : Tendsto (fun n ↦ ∫ x, ‖fderiv ℝ (g n) x‖ ^ 2 ∂μ) atTop
        (𝓝 (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence
        (fun x ↦ (‖fderiv ℝ f x‖ + M * ‖f x‖) ^ 2)
        (fun n ↦ (((hgs n).continuous_fderiv (by simp)).norm.pow 2).aestronglyMeasurable)
        hdomL.integrable_sq
      · intro n
        exact .of_forall fun x ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _)
            (mul_nonneg hM (norm_nonneg _)))).2 (hgrad n x)
      · refine .of_forall fun x ↦ ?_
        have hp : (fun n ↦ ‖fderiv ℝ (g n) x‖ ^ 2) =ᶠ[atTop]
            fun _ ↦ ‖fderiv ℝ f x‖ ^ 2 :=
          (heq x).mono fun _ hn ↦ congrArg (fun L : E →L[ℝ] ℝ ↦ ‖L‖ ^ 2)
            (hn.fderiv_eq (𝕜 := ℝ))
        exact tendsto_const_nhds.congr' hp.symm
    exact le_of_tendsto_of_tendsto' hvar (henergy.const_mul C)
      fun n ↦ h (g n) (hgs n) (hgc n)

end MeasureTheory.Measure
