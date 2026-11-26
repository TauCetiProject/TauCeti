/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.ODE.Gronwall.Discrete
public import TauCeti.Analysis.ODE.OneStep.Basic
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Discrete stability of one-step methods

A one-step method whose increment function is `L`-Lipschitz in the state is *stable*: two
sequences that satisfy its recursion up to residuals `‖z (n + 1) - z n - h n • Φ (t_n) (z n) (h n)‖
≤ h n τ` and `‖Y (n + 1) - Y n - h n • Φ (t_n) (Y n) (h n)‖ ≤ ρ n` on a mesh with nonnegative
steps differ at the node `t_n` by at most

  `gronwallBound (‖z 0 - Y 0‖ + ∑ k < n, ρ k) L τ (t_n - t₀)`,

which is `e^(L (t_n - t₀)) (‖z 0 - Y 0‖ + ∑ k < n, ρ k) + (τ / L) (e^(L (t_n - t₀)) - 1)` for
`L > 0`. In the convergence theory `z n = y (t_n)` samples an exact solution, `h n τ` bounds its
defect, and `Y` is the numerical solution, possibly perturbed by rounding errors `ρ n`.

The errors `e n = ‖z n - Y n‖` satisfy `e (n + 1) ≤ (1 + h n L) e n + h n τ + ρ n`, and the
one-step discrete Grönwall inequality `TauCeti.le_gronwallBound_add_of_le_one_add_mul_add`
propagates the bound from one node to the next.

## Main results

* `TauCeti.norm_sub_le_gronwallBound_of_oneStep`: the discrete stability theorem.
* `TauCeti.norm_sub_le_gronwallBound_of_oneStep_of_lipschitzOnWith`: its local form, for an
  increment function that is only Lipschitz on balls of radius `r` around the `z n`, as long as
  the bound stays below `r`.
* `TauCeti.norm_sub_le_gronwallBound_of_perturbed_oneStep`: the error of a numerical solution
  perturbed by at most `ε` in each step.
* `TauCeti.norm_oneStepSeq_sub_oneStepSeq_le`: Lipschitz dependence of the numerical solution on
  the initial value, with constant `e^(L (t_n - t₀))`.

## References

* E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, University of
  Oxford, 2022, Theorem 4 and (25). There the space is `ℝ`, the mesh is uniform and `ρ = 0`.
-/

public section

open Finset Metric
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The error recursion of one step: if `φ` is `L`-Lipschitz between `z` and `y`, and `z'`, `y'`
follow one step of size `s ≥ 0` up to residuals `s τ` and `ρ`, the error grows to at most
`(1 + s L) ‖z - y‖ + s τ + ρ`. -/
private theorem norm_sub_le_one_add_mul_mul_add {φ : E → E} {z z' y y' : E} {s L τ ρ : ℝ}
    (hs : 0 ≤ s) (hφ : ‖φ z - φ y‖ ≤ L * ‖z - y‖) (hz : ‖z' - z - s • φ z‖ ≤ s * τ)
    (hy : ‖y' - y - s • φ y‖ ≤ ρ) :
    ‖z' - y'‖ ≤ (1 + s * L) * ‖z - y‖ + s * τ + ρ := by
  have hsplit : z' - y' = (z' - z - s • φ z) - (y' - y - s • φ y) + (z - y) + s • (φ z - φ y) := by
    rw [smul_sub]
    abel
  have hsmul : ‖s • (φ z - φ y)‖ ≤ s * (L * ‖z - y‖) := by
    rw [norm_smul, Real.norm_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hφ hs
  rw [hsplit]
  calc _ ≤ ‖z' - z - s • φ z‖ + ‖y' - y - s • φ y‖ + ‖z - y‖ + ‖s • (φ z - φ y)‖ :=
        (norm_add_le _ _).trans <| add_le_add_left
          ((norm_add_le _ _).trans <| add_le_add_left (norm_sub_le _ _) _) _
    _ ≤ (1 + s * L) * ‖z - y‖ + s * τ + ρ := by linarith

/-- **Discrete stability, local form.** Let the steps be nonnegative and `τ ≥ 0`. If
`u ↦ Φ (t_n) u (h n)` is `L`-Lipschitz on the closed ball of radius `r` around `z n` for each
`n < N`, and the Grönwall bound at `n = N` is at most `r`, then the bound of
`TauCeti.norm_sub_le_gronwallBound_of_oneStep` holds for every `n ≤ N`: the sequence `Y` never
leaves the balls. -/
theorem norm_sub_le_gronwallBound_of_oneStep_of_lipschitzOnWith {Φ : ℝ → E → ℝ → E}
    {t₀ τ r : ℝ} {h ρ : ℕ → ℝ} {L : ℝ≥0} {N : ℕ} {z Y : ℕ → E} (hh : ∀ n < N, 0 ≤ h n)
    (hτ : 0 ≤ τ)
    (hΦ : ∀ n < N,
      LipschitzOnWith L (fun u ↦ Φ (meshNode t₀ h n) u (h n)) (closedBall (z n) r))
    (hz : ∀ n < N, ‖z (n + 1) - z n - h n • Φ (meshNode t₀ h n) (z n) (h n)‖ ≤ h n * τ)
    (hY : ∀ n < N, ‖Y (n + 1) - Y n - h n • Φ (meshNode t₀ h n) (Y n) (h n)‖ ≤ ρ n)
    (hr : gronwallBound (‖z 0 - Y 0‖ + ∑ k ∈ range N, ρ k) L τ (meshNode t₀ h N - t₀) ≤ r)
    {n : ℕ} (hn : n ≤ N) :
    ‖z n - Y n‖ ≤
      gronwallBound (‖z 0 - Y 0‖ + ∑ k ∈ range n, ρ k) L τ (meshNode t₀ h n - t₀) := by
  have hρ : ∀ n < N, 0 ≤ ρ n := fun n hn ↦ (norm_nonneg _).trans (hY n hn)
  have hδ : ∀ n ≤ N, 0 ≤ ‖z 0 - Y 0‖ + ∑ k ∈ range n, ρ k := fun n hn ↦
    add_nonneg (norm_nonneg _) <| sum_nonneg fun k hk ↦ hρ k ((mem_range.1 hk).trans_le hn)
  have hx : ∀ n ≤ N, 0 ≤ meshNode t₀ h n - t₀ := fun n hn ↦
    sub_nonneg.2 (self_le_meshNode hh hn)
  -- The Grönwall bound at `n ≤ N` is at most the one at `N`, hence at most `r`.
  have hmono : ∀ n ≤ N,
      gronwallBound (‖z 0 - Y 0‖ + ∑ k ∈ range n, ρ k) L τ (meshNode t₀ h n - t₀) ≤ r := by
    intro n hn
    refine le_trans ?_ hr
    have hsum : ∑ k ∈ range n, ρ k ≤ ∑ k ∈ range N, ρ k :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hn) fun k hk _ ↦
        hρ k (mem_range.1 hk)
    calc _ ≤ gronwallBound (‖z 0 - Y 0‖ + ∑ k ∈ range N, ρ k) L τ (meshNode t₀ h n - t₀) :=
          gronwallBound_mono_δ _ _ _ (add_le_add_right hsum _)
      _ ≤ _ := gronwallBound_mono (hδ N le_rfl) hτ L.coe_nonneg <|
          sub_le_sub_right (monotoneOn_meshNode hh (Set.mem_Iic.2 hn) (Set.mem_Iic.2 le_rfl) hn) _
  induction n with
  | zero => simp [gronwallBound_x0]
  | succ n ih =>
    have hnN : n < N := hn
    have ih := ih hnN.le
    have hmem : Y n ∈ closedBall (z n) r := by
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact ih.trans (hmono n hnN.le)
    have hstep := norm_sub_le_one_add_mul_mul_add (φ := fun u ↦ Φ (meshNode t₀ h n) u (h n))
      (hh n hnN)
      ((hΦ n hnN).norm_sub_le (mem_closedBall_self (dist_nonneg.trans hmem)) hmem)
      (hz n hnN) (hY n hnN)
    convert le_gronwallBound_add_of_le_one_add_mul_add (hδ n hnN.le) L.coe_nonneg hτ (hh n hnN)
      (hρ n hnN) (hx n hnN.le) ih hstep using 2
    · rw [sum_range_succ, add_assoc]
    · rw [meshNode_succ]
      ring

/-- **Discrete stability of one-step methods.** On a mesh with nonnegative steps, let
`u ↦ Φ (t_n) u (h n)` be `L`-Lipschitz for each `n < N`, and let `z` and `Y` satisfy the
recursion of the method up to residuals of norm at most `h n * τ` and `ρ n`. Then for `n ≤ N`,
`‖z n - Y n‖ ≤ gronwallBound (‖z 0 - Y 0‖ + ∑ k < n, ρ k) L τ (t_n - t₀)`.

No sign condition on `τ` is needed: if `τ < 0` the residual bound forces all steps to vanish. -/
theorem norm_sub_le_gronwallBound_of_oneStep {Φ : ℝ → E → ℝ → E} {t₀ τ : ℝ} {h ρ : ℕ → ℝ}
    {L : ℝ≥0} {N : ℕ} {z Y : ℕ → E} (hh : ∀ n < N, 0 ≤ h n)
    (hΦ : ∀ n < N, LipschitzWith L fun u ↦ Φ (meshNode t₀ h n) u (h n))
    (hz : ∀ n < N, ‖z (n + 1) - z n - h n • Φ (meshNode t₀ h n) (z n) (h n)‖ ≤ h n * τ)
    (hY : ∀ n < N, ‖Y (n + 1) - Y n - h n • Φ (meshNode t₀ h n) (Y n) (h n)‖ ≤ ρ n)
    {n : ℕ} (hn : n ≤ N) :
    ‖z n - Y n‖ ≤
      gronwallBound (‖z 0 - Y 0‖ + ∑ k ∈ range n, ρ k) L τ (meshNode t₀ h n - t₀) := by
  rcases le_or_gt 0 τ with hτ | hτ
  · exact norm_sub_le_gronwallBound_of_oneStep_of_lipschitzOnWith hh hτ
      (fun n hn ↦ (hΦ n hn).lipschitzOnWith) hz hY le_rfl hn
  · -- A negative `τ` forces every step to vanish, so all nodes equal `t₀`; apply the case
    -- `τ = 0`, at which the Grönwall bound at time `0` is the same.
    have h0 : ∀ n < N, h n = 0 := fun n hn ↦
      le_antisymm (nonpos_of_mul_nonneg_left ((norm_nonneg _).trans (hz n hn)) hτ) (hh n hn)
    have hz' : ∀ n < N, ‖z (n + 1) - z n - h n • Φ (meshNode t₀ h n) (z n) (h n)‖ ≤ h n * 0 := by
      intro n hn
      simpa [h0 n hn] using hz n hn
    have hnode : meshNode t₀ h n - t₀ = 0 := by
      rw [meshNode_sub_self]
      exact sum_eq_zero fun k hk ↦ h0 k ((mem_range.1 hk).trans_le hn)
    have := norm_sub_le_gronwallBound_of_oneStep_of_lipschitzOnWith hh le_rfl
      (fun n hn ↦ (hΦ n hn).lipschitzOnWith) hz' hY le_rfl hn
    rw [hnode, gronwallBound_x0] at this ⊢
    exact this

/-- **Perturbed steps.** On a mesh with nonnegative steps and an `L`-Lipschitz increment
function, if the defect of the curve `y` at the nodes is at most `h n * τ` and each step of `Y`
is the step of the method perturbed by `r n` with `‖r n‖ ≤ ε`, then
`‖y (t_n) - Y n‖ ≤ gronwallBound (‖y t₀ - Y 0‖ + n ε) L τ (t_n - t₀)` for `n ≤ N`. -/
theorem norm_sub_le_gronwallBound_of_perturbed_oneStep {Φ : ℝ → E → ℝ → E} {y : ℝ → E}
    {t₀ τ ε : ℝ} {h : ℕ → ℝ} {L : ℝ≥0} {N : ℕ} {Y r : ℕ → E} (hh : ∀ n < N, 0 ≤ h n)
    (hΦ : ∀ n < N, LipschitzWith L fun u ↦ Φ (meshNode t₀ h n) u (h n))
    (hy : ∀ n < N, ‖oneStepDefect Φ y (meshNode t₀ h n) (h n)‖ ≤ h n * τ)
    (hY : ∀ n < N, Y (n + 1) = Y n + h n • Φ (meshNode t₀ h n) (Y n) (h n) + r n)
    (hr : ∀ n < N, ‖r n‖ ≤ ε) {n : ℕ} (hn : n ≤ N) :
    ‖y (meshNode t₀ h n) - Y n‖ ≤
      gronwallBound (‖y t₀ - Y 0‖ + n * ε) L τ (meshNode t₀ h n - t₀) := by
  have := norm_sub_le_gronwallBound_of_oneStep (z := fun n ↦ y (meshNode t₀ h n))
    (Y := Y) (ρ := fun _ ↦ ε) hh hΦ (fun n hn ↦ by rw [← oneStepDefect_meshNode]; exact hy n hn)
    (fun n hn ↦ by rw [hY n hn, add_assoc, add_sub_cancel_left, add_sub_cancel_left]; exact hr n hn)
    hn
  simpa using this

/-- **Dependence on the initial value.** On a mesh with nonnegative steps and an `L`-Lipschitz
increment function, the numerical solutions started at `y₀` and `y₀'` satisfy
`‖Y n - Y' n‖ ≤ e^(L (t_n - t₀)) ‖y₀ - y₀'‖` for `n ≤ N`. -/
theorem norm_oneStepSeq_sub_oneStepSeq_le {Φ : ℝ → E → ℝ → E} {t₀ : ℝ} {h : ℕ → ℝ}
    {L : ℝ≥0} {N : ℕ} (hh : ∀ n < N, 0 ≤ h n)
    (hΦ : ∀ n < N, LipschitzWith L fun u ↦ Φ (meshNode t₀ h n) u (h n)) (y₀ y₀' : E) {n : ℕ}
    (hn : n ≤ N) :
    ‖oneStepSeq Φ t₀ h y₀ n - oneStepSeq Φ t₀ h y₀' n‖ ≤
      Real.exp (L * (meshNode t₀ h n - t₀)) * ‖y₀ - y₀'‖ := by
  have := norm_sub_le_gronwallBound_of_oneStep (z := oneStepSeq Φ t₀ h y₀)
    (Y := oneStepSeq Φ t₀ h y₀') (τ := 0) (ρ := fun _ ↦ 0) hh hΦ
    (fun n _ ↦ by simp) (fun n _ ↦ by simp) hn
  simpa [gronwallBound_ε0, mul_comm] using this

end TauCeti
