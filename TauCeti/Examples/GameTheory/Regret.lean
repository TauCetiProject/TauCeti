/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GameTheory.Regret
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Examples of external and swap regret

These examples test the conventions of `TauCeti.GameTheory.Regret` on two actions. The simplex
consists of the nonnegative vectors of sum one. A range bounds the spread of the payoffs at each
time, not their size: the payoffs `(t, t + 1)` have range `1` although they are unbounded. Against
the payoffs `(0, 1)`, always playing the first action has regret `T` against the second action and
swap regret `T`, attained by the constant swap to the second action, while always playing the
second action has regret `-T` against the first action and swap regret `0`, attained by the
identity swap.
-/

public section

namespace TauCeti.Examples.Regret

open Finset

/-! ## The simplex on two actions -/

example : ![1 / 2, 1 / 2] ∈ simplex (Fin 2) := by
  norm_num [mem_simplex_iff, Fin.forall_fin_two]

example : ![1, 0] ∈ simplex (Fin 2) := by
  norm_num [mem_simplex_iff, Fin.forall_fin_two]

-- Sum one, but a negative weight.
example : ![2, -1] ∉ simplex (Fin 2) := by
  norm_num [mem_simplex_iff, Fin.forall_fin_two]

-- Nonnegative, but sum `3 / 4`.
example : ![1 / 2, 1 / 4] ∉ simplex (Fin 2) := by
  norm_num [mem_simplex_iff]

/-! ## Ranges -/

-- The payoffs `(t, t + 1)` have range `1` ...
example : HasRange (fun t : ℕ ↦ ![(t : ℝ), t + 1]) 1 :=
  hasRange_iff.2 ⟨fun t ↦ t, fun t ↦ by simp [Fin.forall_fin_two]⟩

-- ... although they are not bounded.
example : ¬ ∃ M : ℝ, ∀ t a, |![(t : ℝ), t + 1] a| ≤ M := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have := hM n 0
  simp only [Matrix.cons_val_zero, Nat.abs_cast] at this
  linarith

-- The constant payoffs `(0, 1)` have range `Δ` exactly when `1 ≤ Δ`.
example {Δ : ℝ} : HasRange (fun _ ↦ ![(0 : ℝ), 1]) Δ ↔ 1 ≤ Δ := by
  rw [hasRange_iff]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun h ↦ ⟨fun _ ↦ 0, fun _ ↦ ?_⟩⟩
  · have h0 := (hc 0 0).1
    have h1 := (hc 0 1).2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    linarith
  · simp [Fin.forall_fin_two, h, zero_le_one.trans h]

/-! ## Always playing the first action against the payoffs `(0, 1)` -/

example (T : ℕ) : regret (fun _ ↦ ![1, 0]) (fun _ ↦ ![0, 1]) T 1 = T := by
  simp [regret_def, dotProduct]

-- The swap regret is `T`, attained by the constant swap to the second action.
example (T : ℕ) : swapRegret (fun _ ↦ ![1, 0]) (fun _ ↦ ![0, 1]) T = T := by
  have hconst : ∑ t ∈ range T, ∑ a, ![(1 : ℝ), 0] a *
      (![(0 : ℝ), 1] (Function.const _ 1 a) - ![0, 1] a) = T := by
    simp
  refine le_antisymm (swapRegret_le_iff.2 fun φ ↦ ?_)
    (hconst.symm.le.trans (le_swapRegret _ _ T _))
  have h : ![(0 : ℝ), 1] (φ 0) ≤ 1 := by
    rcases Fin.exists_fin_two.1 ⟨φ 0, rfl⟩ with h | h <;> simp [h]
  calc
    _ = ∑ _t ∈ range T, ![(0 : ℝ), 1] (φ 0) := by simp
    _ ≤ ∑ _t ∈ range T, (1 : ℝ) := sum_le_sum fun _ _ ↦ h
    _ = T := by simp

/-! ## Always playing the second action against the payoffs `(0, 1)` -/

example (T : ℕ) : regret (fun _ ↦ ![0, 1]) (fun _ ↦ ![0, 1]) T 0 = -T := by
  simp [regret_def, dotProduct]

example (T : ℕ) : regret (fun _ ↦ ![0, 1]) (fun _ ↦ ![0, 1]) T 1 = 0 := by
  simp [regret_def, dotProduct]

-- The swap regret is `0`, attained by the identity swap.
example (T : ℕ) : swapRegret (fun _ ↦ ![0, 1]) (fun _ ↦ ![0, 1]) T = 0 := by
  refine le_antisymm (swapRegret_le_iff.2 fun φ ↦ ?_) (swapRegret_nonneg _ _ T)
  have h : ![(0 : ℝ), 1] (φ 1) ≤ 1 := by
    rcases Fin.exists_fin_two.1 ⟨φ 1, rfl⟩ with h | h <;> simp [h]
  refine sum_nonpos fun _ _ ↦ ?_
  simpa using h

end TauCeti.Examples.Regret
