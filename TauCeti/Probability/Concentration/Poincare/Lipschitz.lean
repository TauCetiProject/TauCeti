/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.LogSobolev
public import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Poincaré variance bound for Lipschitz functions

On a finite-dimensional real normed space, the smooth-test Poincaré inequality with a
nonnegative constant `C` implies `Var_μ(f) ≤ C * K²` for every square-integrable
`K`-Lipschitz function `f`. The probability measure may be singular.

Smooth uniform approximation preserves the Lipschitz constant. Dominated convergence of
the first and second moments then passes the variance bound to the limit.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni,
  *An Introduction to Random Matrices*, §2.3.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology NNReal

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsProbabilityMeasure μ] {C : ℝ} {K : ℝ≥0} {f : E → ℝ}

/-- A nonnegative Poincaré constant bounds the variance of a square-integrable Lipschitz
function by the constant times the square of its Lipschitz bound. -/
theorem PoincareInequality.variance_le_of_lipschitzWith
    (hP : PoincareInequality μ C) (hC : 0 ≤ C) (hf : LipschitzWith K f)
    (hfL : MemLp f 2 μ) : variance f μ ≤ C * (K : ℝ) ^ 2 := by
  classical
  have hε (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose g hgs hgK hgf using fun n ↦ hf.exists_contDiff_lipschitzWith_dist_lt (hε n)
  have hε_le (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hbound (n : ℕ) (x : E) : ‖g n x‖ ≤ ‖f x‖ + 1 := by
    have hd : ‖g n x - f x‖ ≤ 1 / ((n : ℝ) + 1) := by
      simpa only [dist_eq_norm] using (hgf n x).le
    calc
      ‖g n x‖ ≤ ‖g n x - f x‖ + ‖f x‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + ‖f x‖ := by linarith [hd.trans (hε_le n)]
      _ = ‖f x‖ + 1 := add_comm _ _
  have hbL : MemLp (fun x ↦ ‖f x‖ + 1) 2 μ := hfL.norm.add (memLp_const 1)
  have hgL (n : ℕ) : MemLp (g n) 2 μ :=
    hbL.mono' (hgs n).continuous.aestronglyMeasurable (.of_forall (hbound n))
  have hg_tendsto (x : E) : Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (hgf n x).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hmean : Tendsto (fun n ↦ ∫ x, g n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖ + 1)
      (fun n ↦ (hgs n).continuous.aestronglyMeasurable) (hbL.integrable one_le_two)
      (fun n ↦ .of_forall (hbound n)) (.of_forall hg_tendsto)
  have hsecond : Tendsto (fun n ↦ ∫ x, g n x ^ 2 ∂μ) atTop
      (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ (‖f x‖ + 1) ^ 2)
      (fun n ↦ ((hgs n).continuous.pow 2).aestronglyMeasurable) hbL.integrable_sq
    · intro n
      exact .of_forall fun x ↦ by
        simpa only [Pi.pow_apply, Real.norm_eq_abs, sq_abs,
          abs_of_nonneg (sq_nonneg (g n x))] using
          (sq_le_sq₀ (norm_nonneg (g n x)) (by positivity)).2 (hbound n x)
    · exact .of_forall fun x ↦ (hg_tendsto x).pow 2
  have hvar : Tendsto (fun n ↦ variance (g n) μ) atTop (𝓝 (variance f μ)) := by
    simp_rw [variance_eq_sub (hgL _), variance_eq_sub hfL]
    exact hsecond.sub (hmean.pow 2)
  apply le_of_tendsto hvar
  exact .of_forall fun n ↦ by
    have hgrad (x : E) : ‖fderiv ℝ (g n) x‖ ≤ K := norm_fderiv_le_of_lipschitz ℝ (hgK n)
    have hgradL : MemLp (fun x ↦ ‖fderiv ℝ (g n) x‖) 2 μ :=
      MemLp.of_bound ((hgs n).continuous_fderiv (by simp)).norm.aestronglyMeasurable K
        (.of_forall fun x ↦ by simpa only [norm_norm] using hgrad x)
    calc
      variance (g n) μ ≤ C * ∫ x, ‖fderiv ℝ (g n) x‖ ^ 2 ∂μ :=
        hP.apply _ (hgs n) (hgL n) hgradL
      _ ≤ C * ∫ _ : E, (K : ℝ) ^ 2 ∂μ := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact integral_mono hgradL.integrable_sq (integrable_const _) fun x ↦
          (sq_le_sq₀ (norm_nonneg _) K.coe_nonneg).2 (hgrad x)
      _ = C * (K : ℝ) ^ 2 := by simp

end MeasureTheory.Measure
