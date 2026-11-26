/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import TauCeti.Analysis.ODE.OneStep.Consistency
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Checks for consistency implies convergence

These examples test the hypotheses of `TauCeti.exists_forall_norm_sub_oneStepSeq_le_of_consistent`.

* For a jointly continuous field `f` that is Lipschitz in the state, the increment
  `Φ t u s = f t u + s • v` with a fixed vector `v` is consistent, so its numerical solutions
  converge.
* Consistency is needed: on `ℝ`, the increment `Φ t u s = 2 u` is jointly continuous and
  `2`-Lipschitz in `u`, and `y = exp` solves `y' = y`, but `Φ t u 0 = 2 u ≠ u`. On the uniform mesh
  of `[0, 1]` with `N` steps the numerical solution started at `1` ends at `(1 + 2 / N) ^ N`, which
  tends to `e²` and not to `e`, so the error at the last node stays above `1`.
* Continuity in the step is needed: `Φ t u s = u` for `s = 0` and `2 u` for `s ≠ 0` is consistent
  with `y' = y` and `2`-Lipschitz in `u`, and on meshes with positive steps its numerical solution
  is that of the previous check.
-/

public section

namespace TauCeti.Examples.OneStep

open TauCeti Filter Real Set Topology
open scoped NNReal

/-! ### A consistent perturbation of the Euler method -/

/-- For a jointly continuous field `f` that is `L`-Lipschitz in the state, the one-step method with
increment `f t u + s • v`, for a fixed vector `v`, converges along every solution `y` on
`[a, b]`. -/
theorem exists_forall_norm_sub_oneStepSeq_add_smul_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E → E} {y : ℝ → E} {a b : ℝ} {L : ℝ≥0} (v : E)
    (hf : Continuous fun q : ℝ × E ↦ f q.1 q.2) (hL : ∀ t, LipschitzWith L (f t))
    (hy : IsIntegralCurveOn y f (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (h : ℕ → ℝ) (N : ℕ), (∀ n < N, 0 ≤ h n ∧ h n ≤ δ) → meshNode a h N ≤ b →
      ∀ n ≤ N, ‖y (meshNode a h n) - oneStepSeq (fun t u s ↦ f t u + s • v) a h (y a) n‖ ≤ ε :=
  exists_forall_norm_sub_oneStepSeq_le_of_consistent one_pos hy
    ((hf.comp (continuous_fst.prodMk continuous_snd.fst)).add (continuous_snd.snd.smul
      continuous_const))
    (fun t u ↦ by simp)
    (fun t s _ _ ↦ LipschitzWith.of_dist_le_mul fun u w ↦ by
      rw [dist_add_right]
      exact (hL t).dist_le_mul u w)
    hε

/-! ### Consistency and continuity in the step are needed -/

-- The hypotheses other than consistency hold: `exp` solves `y' = y` on `[0, 1]`, and the
-- increments below are `2`-Lipschitz in the state.
example : IsIntegralCurveOn exp (fun _ u ↦ u) (Icc 0 1) :=
  fun t _ ↦ (hasDerivAt_exp t).hasDerivWithinAt

example : LipschitzWith 2 fun u : ℝ ↦ 2 * u := by
  simpa [smul_eq_mul] using lipschitzWith_smul (β := ℝ) (2 : ℝ)

/-- If a method multiplies by `1 + 2 / N` at each step of the uniform mesh of `[0, 1]` with `N`
steps, it does not converge along `exp`: no step size makes its error at the nodes at most `1`. -/
private theorem not_exists_forall_norm_exp_sub_oneStepSeq_le {Φ : ℝ → ℝ → ℝ → ℝ}
    (hΦ : ∀ N : ℕ, 0 < N → oneStepSeq Φ 0 (fun _ ↦ 1 / N) 1 N = (1 + 2 / N) ^ N) :
    ¬∃ δ > 0, ∀ (h : ℕ → ℝ) (N : ℕ), (∀ n < N, 0 ≤ h n ∧ h n ≤ δ) → meshNode 0 h N ≤ 1 →
      ∀ n ≤ N, ‖exp (meshNode 0 h n) - oneStepSeq Φ 0 h (exp 0) n‖ ≤ 1 := by
  rintro ⟨δ, hδ, H⟩
  -- For large `N` the step `1 / N` is at most `δ` and `(1 + 2 / N) ^ N` is close to `e²`.
  obtain ⟨N, ⟨hNδ, hNe⟩, hN⟩ := ((tendsto_const_div_atTop_nhds_zero_nat 1).eventually
    (Iic_mem_nhds hδ) |>.and ((tendsto_one_add_div_pow_exp 2).eventually
      (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))) |>.and
      (eventually_gt_atTop 0)).exists
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have herr := H (fun _ ↦ 1 / N) N (fun _ _ ↦ ⟨by positivity, hNδ⟩)
    (by simp [mul_inv_cancel₀ hN']) N le_rfl
  simp only [meshNode_const, zero_add, mul_one_div_cancel hN', exp_zero, hΦ N hN,
    Real.norm_eq_abs] at herr
  rw [Real.dist_eq] at hNe
  -- But `e² - e = e (e - 1) ≥ 2`.
  have he : 2 ≤ exp 1 := by linarith [add_one_le_exp 1]
  have he2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
  have := (abs_sub_lt_iff.1 hNe).2
  have := (abs_le.1 herr).1
  nlinarith

/-- **Consistency is needed.** The increment `Φ t u s = 2 u` is jointly continuous and
`2`-Lipschitz in `u` but not consistent with `y' = y`: its numerical solution started at `exp 0`
does not converge to `exp` on `[0, 1]`. -/
theorem not_exists_forall_norm_exp_sub_oneStepSeq_two_mul_le :
    ¬∃ δ > 0, ∀ (h : ℕ → ℝ) (N : ℕ), (∀ n < N, 0 ≤ h n ∧ h n ≤ δ) → meshNode 0 h N ≤ 1 →
      ∀ n ≤ N, ‖exp (meshNode 0 h n) - oneStepSeq (fun _ u _ ↦ 2 * u) 0 h (exp 0) n‖ ≤ 1 := by
  refine not_exists_forall_norm_exp_sub_oneStepSeq_le fun N _ ↦ ?_
  suffices ∀ n, oneStepSeq (fun _ (u : ℝ) _ ↦ 2 * u) 0 (fun _ ↦ 1 / N) 1 n = (1 + 2 / N) ^ n from
    this N
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [oneStepSeq_succ, ih, smul_eq_mul, pow_succ]
    ring

/-- **Continuity in the step is needed.** The increment `Φ t u s = u` for `s = 0` and `2 u` for
`s ≠ 0` is consistent with `y' = y` and `2`-Lipschitz in `u`, but not continuous in `s`: its
numerical solution started at `exp 0` does not converge to `exp` on `[0, 1]`. -/
theorem not_exists_forall_norm_exp_sub_oneStepSeq_ite_le :
    ¬∃ δ > 0, ∀ (h : ℕ → ℝ) (N : ℕ), (∀ n < N, 0 ≤ h n ∧ h n ≤ δ) → meshNode 0 h N ≤ 1 →
      ∀ n ≤ N, ‖exp (meshNode 0 h n) -
        oneStepSeq (fun _ u s ↦ if s = 0 then u else 2 * u) 0 h (exp 0) n‖ ≤ 1 := by
  refine not_exists_forall_norm_exp_sub_oneStepSeq_le fun N hN ↦ ?_
  have hN' : (1 : ℝ) / N ≠ 0 := by positivity
  suffices ∀ n, oneStepSeq (fun _ (u : ℝ) s ↦ if s = 0 then u else 2 * u) 0 (fun _ ↦ 1 / N) 1 n =
      (1 + 2 / N) ^ n from this N
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [oneStepSeq_succ, ih, hN', ↓reduceIte, smul_eq_mul, pow_succ]
    ring

end TauCeti.Examples.OneStep
