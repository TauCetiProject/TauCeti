/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Separation of a real number from the nonpositive integers

A real number `x` that is not one of `0, -1, -2, …` keeps a uniform positive distance from all
of them: only the finitely many `n ≤ ⌈-x⌉₊` can come close, and every larger `n` is at distance
at least `1`. This is the form in which poles of the Gamma function at the nonpositive integers
are avoided along a vertical line.

## Main results

* `Real.exists_pos_forall_le_abs_add_natCast`: if `x ≠ -n` for every `n : ℕ`, there is `η > 0`
  with `η ≤ |x + n|` for every `n : ℕ`.
-/

public section

namespace Real

/-- A real number that is not a nonpositive integer keeps a positive distance from all of them:
there is `η > 0` with `η ≤ |x + n|` for every `n : ℕ`. -/
theorem exists_pos_forall_le_abs_add_natCast {x : ℝ} (hx : ∀ n : ℕ, x ≠ -n) :
    ∃ η > 0, ∀ n : ℕ, η ≤ |x + n| := by
  set N := ⌈-x⌉₊
  have hne : (Finset.range (N + 1)).Nonempty := Finset.nonempty_range_add_one
  refine ⟨min 1 ((Finset.range (N + 1)).inf' hne fun k ↦ |x + k|),
    lt_min one_pos ((Finset.lt_inf'_iff hne).2 fun k _ ↦
      abs_pos.2 fun h ↦ hx k (by linarith)), fun n ↦ ?_⟩
  rcases le_or_gt n N with hn | hn
  · exact (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 (by omega)))
  · refine (min_le_left _ _).trans (le_abs.2 (Or.inl ?_))
    have hN : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith [Nat.le_ceil (-x)]

end Real
