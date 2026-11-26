/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.OneStep.Stability
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The convergence theorem for one-step methods

A one-step method with increment function `Φ` has *order `p`* along a curve `y` if its defect
`TauCeti.oneStepDefect Φ y t s` is at most `C s ^ (p + 1)` for small steps `s ≥ 0`. If moreover
`Φ` is `L`-Lipschitz in the state, the discrete stability theorem
`TauCeti.norm_sub_le_gronwallBound_of_oneStep`, applied with `τ = C hmax ^ p`, bounds the global
error on every mesh with steps in `[0, hmax]`:

  `‖y (t_n) - Y n‖ ≤ gronwallBound ‖y t₀ - y₀‖ L (C hmax ^ p) (t_n - t₀)`.

The curve `y` need not solve a differential equation: the theorem compares `y` with the method
through the defect alone. For `p ≥ 1` and `y₀ = y t₀` the bound therefore tends to `0` with
`hmax`; on uniform meshes this is `TauCeti.exists_forall_norm_sub_oneStepSeq_uniform_le`.

## Main results

* `TauCeti.norm_sub_oneStepSeq_le`: the convergence theorem on meshes with variable steps.
* `TauCeti.norm_sub_le_gronwallBound_of_perturbed_oneStep_of_defect_le`: the same bound for a
  numerical solution perturbed by at most `ε` in each step, with `n ε` added to the initial
  error.
* `TauCeti.norm_sub_oneStepSeq_uniform_le`: on the uniform mesh of `N` steps of `[t₀, b]`, the
  error at every node is at most `gronwallBound 0 L (C ((b - t₀) / N) ^ p) (b - t₀)`.
* `TauCeti.exists_forall_norm_sub_oneStepSeq_uniform_le`: for `p ≥ 1` this bound tends to `0`,
  so the method converges on uniform meshes.

## References

* E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, University of
  Oxford, 2022, Theorem 4 with Definition 3. There the space is `ℝ` and the mesh is uniform.
-/

public section

open Filter Finset Topology
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A defect bound `C s ^ (p + 1)` for steps `s ∈ [0, hmax]` inside `[t₀, b]` gives the defect
bound `h n * (C hmax ^ p)` at the nodes of a mesh with steps in `[0, hmax]` and `t_N ≤ b`. If
`C < 0` the hypothesis forces every step to vanish. -/
private theorem norm_oneStepDefect_meshNode_le {Φ : ℝ → E → ℝ → E} {y : ℝ → E}
    {t₀ b hmax C : ℝ} {p N : ℕ} {h : ℕ → ℝ} (hh : ∀ n < N, 0 ≤ h n ∧ h n ≤ hmax)
    (hb : meshNode t₀ h N ≤ b)
    (hdef : ∀ t s, t₀ ≤ t → 0 ≤ s → s ≤ hmax → t + s ≤ b →
      ‖oneStepDefect Φ y t s‖ ≤ C * s ^ (p + 1))
    {n : ℕ} (hn : n < N) :
    ‖oneStepDefect Φ y (meshNode t₀ h n) (h n)‖ ≤ h n * (C * hmax ^ p) := by
  have hh0 : ∀ n < N, 0 ≤ h n := fun n hn ↦ (hh n hn).1
  have hend : meshNode t₀ h n + h n ≤ b := by
    rw [← meshNode_succ]
    exact (monotoneOn_meshNode hh0 (Set.mem_Iic.2 hn) (Set.mem_Iic.2 le_rfl) hn).trans hb
  have hd := hdef _ _ (self_le_meshNode hh0 hn.le) (hh n hn).1 (hh n hn).2 hend
  rcases (hh n hn).1.eq_or_lt with h0 | hpos
  · simp [← h0]
  · have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hd) (by positivity)
    calc _ ≤ C * h n ^ (p + 1) := hd
      _ = h n * (C * h n ^ p) := by ring
      _ ≤ h n * (C * hmax ^ p) := by
          gcongr
          exact (hh n hn).2

/-- **Perturbed steps with a defect of order `p`.** If the defect of `y` is at most `C s ^ (p + 1)`
for steps `s ∈ [0, hmax]` inside `[t₀, b]`, the increment function is `L`-Lipschitz at the nodes,
and each step of `Y` is the step of the method perturbed by `r n` with `‖r n‖ ≤ ε`, then on a mesh
with steps in `[0, hmax]` and `t_N ≤ b`,
`‖y (t_n) - Y n‖ ≤ gronwallBound (‖y t₀ - Y 0‖ + n ε) L (C hmax ^ p) (t_n - t₀)` for `n ≤ N`. -/
theorem norm_sub_le_gronwallBound_of_perturbed_oneStep_of_defect_le {Φ : ℝ → E → ℝ → E}
    {y : ℝ → E} {t₀ b hmax C ε : ℝ} {L : ℝ≥0} {p N : ℕ} {h : ℕ → ℝ} {Y r : ℕ → E}
    (hh : ∀ n < N, 0 ≤ h n ∧ h n ≤ hmax) (hb : meshNode t₀ h N ≤ b)
    (hΦ : ∀ n < N, LipschitzWith L fun u ↦ Φ (meshNode t₀ h n) u (h n))
    (hdef : ∀ t s, t₀ ≤ t → 0 ≤ s → s ≤ hmax → t + s ≤ b →
      ‖oneStepDefect Φ y t s‖ ≤ C * s ^ (p + 1))
    (hY : ∀ n < N, Y (n + 1) = Y n + h n • Φ (meshNode t₀ h n) (Y n) (h n) + r n)
    (hr : ∀ n < N, ‖r n‖ ≤ ε) {n : ℕ} (hn : n ≤ N) :
    ‖y (meshNode t₀ h n) - Y n‖ ≤
      gronwallBound (‖y t₀ - Y 0‖ + n * ε) L (C * hmax ^ p) (meshNode t₀ h n - t₀) :=
  norm_sub_le_gronwallBound_of_perturbed_oneStep (fun n hn ↦ (hh n hn).1) hΦ
    (fun _ hn ↦ norm_oneStepDefect_meshNode_le hh hb hdef hn) hY hr hn

/-- **The convergence theorem.** If the defect of `y` is at most `C s ^ (p + 1)` for steps
`s ∈ [0, hmax]` inside `[t₀, b]` and the increment function is `L`-Lipschitz at the nodes, then
on every mesh with steps in `[0, hmax]` and `t_N ≤ b` the numerical solution started at `y₀`
satisfies `‖y (t_n) - Y n‖ ≤ gronwallBound ‖y t₀ - y₀‖ L (C hmax ^ p) (t_n - t₀)` for `n ≤ N`.
No sign condition on `C` is needed. -/
theorem norm_sub_oneStepSeq_le {Φ : ℝ → E → ℝ → E} {y : ℝ → E} {t₀ b hmax C : ℝ} {L : ℝ≥0}
    {p N : ℕ} {h : ℕ → ℝ} (y₀ : E) (hh : ∀ n < N, 0 ≤ h n ∧ h n ≤ hmax)
    (hb : meshNode t₀ h N ≤ b)
    (hΦ : ∀ n < N, LipschitzWith L fun u ↦ Φ (meshNode t₀ h n) u (h n))
    (hdef : ∀ t s, t₀ ≤ t → 0 ≤ s → s ≤ hmax → t + s ≤ b →
      ‖oneStepDefect Φ y t s‖ ≤ C * s ^ (p + 1))
    {n : ℕ} (hn : n ≤ N) :
    ‖y (meshNode t₀ h n) - oneStepSeq Φ t₀ h y₀ n‖ ≤
      gronwallBound ‖y t₀ - y₀‖ L (C * hmax ^ p) (meshNode t₀ h n - t₀) := by
  simpa using norm_sub_le_gronwallBound_of_perturbed_oneStep_of_defect_le (ε := 0)
    (Y := oneStepSeq Φ t₀ h y₀) (r := 0) hh hb hΦ hdef (fun n _ ↦ by simp) (fun n _ ↦ by simp) hn

/-- **The convergence theorem on uniform meshes.** On the uniform mesh of `N ≥ 1` steps of
length `(b - t₀) / N` on `[t₀, b]`, the error at every node of the numerical solution started at
`y t₀` is at most `gronwallBound 0 L (C ((b - t₀) / N) ^ p) (b - t₀)`. -/
theorem norm_sub_oneStepSeq_uniform_le {Φ : ℝ → E → ℝ → E} {y : ℝ → E} {t₀ b C : ℝ}
    {L : ℝ≥0} {p N : ℕ} (hN : 0 < N) (htb : t₀ ≤ b)
    (hΦ : ∀ n < N, LipschitzWith L fun u ↦ Φ (t₀ + n * ((b - t₀) / N)) u ((b - t₀) / N))
    (hdef : ∀ t s, t₀ ≤ t → 0 ≤ s → s ≤ (b - t₀) / N → t + s ≤ b →
      ‖oneStepDefect Φ y t s‖ ≤ C * s ^ (p + 1))
    {n : ℕ} (hn : n ≤ N) :
    ‖y (t₀ + n * ((b - t₀) / N)) - oneStepSeq Φ t₀ (fun _ ↦ (b - t₀) / N) (y t₀) n‖ ≤
      gronwallBound 0 L (C * ((b - t₀) / N) ^ p) (b - t₀) := by
  set η := (b - t₀) / N with hη
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hη0 : 0 ≤ η := div_nonneg (sub_nonneg.2 htb) N.cast_nonneg
  have hNη : N * η = b - t₀ := by rw [hη, mul_div_cancel₀ _ hN']
  have hnη : n * η ≤ b - t₀ := by
    rw [← hNη]
    gcongr
  have herr := norm_sub_oneStepSeq_le (y₀ := y t₀) (h := fun _ ↦ η) (hmax := η) (b := b)
    (fun _ _ ↦ ⟨hη0, le_rfl⟩) (by simp [hNη]) (by simpa using hΦ) hdef hn
  simp only [meshNode_const, sub_self, norm_zero, add_sub_cancel_left] at herr
  refine herr.trans ?_
  -- The bound is monotone in time as soon as its rate `C η ^ p` is nonnegative, which the
  -- defect hypothesis forces when `η > 0`.
  rcases hη0.eq_or_lt with h0 | hpos
  · -- If `η = 0`, both times `n η` and `b - t₀ = N η` vanish.
    rw [← hNη, ← h0]
    simp
  · have hηb : t₀ + η ≤ b := by
      have : η ≤ b - t₀ := by
        rw [hη]
        exact div_le_self (sub_nonneg.2 htb) (Nat.one_le_cast.2 hN)
      linarith
    have hC : 0 ≤ C := nonneg_of_mul_nonneg_left
      ((norm_nonneg _).trans (hdef t₀ η le_rfl hη0 le_rfl hηb)) (by positivity)
    exact gronwallBound_mono le_rfl (by positivity) L.coe_nonneg hnη

/-- **Convergence on uniform meshes.** If, for every time `t ≥ t₀` and step `s ≥ 0` with
`t + s ≤ b`, the increment function is `L`-Lipschitz in the state and the defect of `y` is at most
`C s ^ (p + 1)` with `p ≥ 1`, then for every `ε > 0` the numerical solution started at `y t₀` on
the uniform mesh with `N` steps of `[t₀, b]` is within `ε` of `y` at every node, for all large
`N`. -/
theorem exists_forall_norm_sub_oneStepSeq_uniform_le {Φ : ℝ → E → ℝ → E} {y : ℝ → E}
    {t₀ b C : ℝ} {L : ℝ≥0} {p : ℕ} (hp : p ≠ 0) (htb : t₀ ≤ b)
    (hΦ : ∀ t s, t₀ ≤ t → 0 ≤ s → t + s ≤ b → LipschitzWith L fun u ↦ Φ t u s)
    (hdef : ∀ t s, t₀ ≤ t → 0 ≤ s → t + s ≤ b → ‖oneStepDefect Φ y t s‖ ≤ C * s ^ (p + 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n ≤ N,
      ‖y (t₀ + n * ((b - t₀) / N)) - oneStepSeq Φ t₀ (fun _ ↦ (b - t₀) / N) (y t₀) n‖ ≤ ε := by
  -- The bound of `norm_sub_oneStepSeq_uniform_le` tends to `0`, because its rate does.
  have hrate : Tendsto (fun N : ℕ ↦ C * ((b - t₀) / N) ^ p) atTop (𝓝 0) := by
    simpa [zero_pow hp] using
      ((tendsto_const_div_atTop_nhds_zero_nat (b - t₀)).pow p).const_mul C
  have hbound := ((gronwallBound_continuous_ε 0 L (b - t₀)).tendsto 0).comp hrate
  rw [gronwallBound_ε0_δ0] at hbound
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hbound.eventually (Iic_mem_nhds hε))
  refine ⟨max N₀ 1, fun N hN n hn ↦ ?_⟩
  have hN1 : 0 < N := lt_of_lt_of_le one_pos (le_of_max_le_right hN)
  have hη0 : 0 ≤ (b - t₀) / N := div_nonneg (sub_nonneg.2 htb) N.cast_nonneg
  have hNη : N * ((b - t₀) / N) = b - t₀ := mul_div_cancel₀ _ (by positivity)
  -- The nodes `t₀ + k η` with `k < N` lie in `[t₀, b - η]`.
  have hnode : ∀ k < N, t₀ + k * ((b - t₀) / N) + (b - t₀) / N ≤ b := fun k hk ↦ by
    have : ((k : ℝ) + 1) * ((b - t₀) / N) ≤ N * ((b - t₀) / N) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hη0
    linarith
  exact (norm_sub_oneStepSeq_uniform_le hN1 htb
    (fun k hk ↦ hΦ _ _ (le_add_of_nonneg_right (by positivity)) hη0 (hnode k hk))
    (fun t s ht hs _ hts ↦ hdef t s ht hs hts) hn).trans (hN₀ N (le_of_max_le_left hN))

end TauCeti
