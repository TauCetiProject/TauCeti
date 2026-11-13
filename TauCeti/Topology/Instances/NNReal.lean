/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Finite grids in nonnegative real intervals

Every compact nonnegative real interval admits a monotone grid with prescribed positive
cell count and mesh at most the interval length divided by that count. These grids allow
pathwise variation estimates to be applied on intervals with arbitrary endpoints.
-/

public section

namespace NNReal

/-- A compact nonnegative real interval has a monotone grid with `n` cells, the prescribed
endpoints, and mesh at most its length divided by `n`. Degenerate intervals are allowed. -/
theorem exists_monotone_grid (S T : ℝ≥0) (hST : S ≤ T) (n : ℕ) (hn : 0 < n) :
    ∃ u : ℕ → ℝ≥0, Monotone u ∧ u 0 = S ∧ u n = T ∧
      ∀ i, dist (u (i + 1)) (u i) ≤ ((T - S : ℝ≥0) : ℝ) / n := by
  let u (i : ℕ) : ℝ≥0 := S + i * (T - S) / n
  have hu : Monotone u := by
    intro i j hij
    dsimp [u]
    gcongr
  refine ⟨u, hu, by simp [u], ?_, ?_⟩
  · have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [u, mul_div_cancel_left₀ _ hn']
    exact add_tsub_cancel_of_le hST
  · intro i
    rw [NNReal.dist_eq]
    simp only [u, NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
    push_cast
    have he : ((S : ℝ) + (i + 1 : ℝ) * (T - S : ℝ≥0) / n) -
        (S + i * (T - S : ℝ≥0) / n) = (T - S : ℝ≥0) / n := by ring
    rw [he, abs_of_nonneg (by positivity)]

end NNReal
