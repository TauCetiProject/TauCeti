/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Summing the increments of a quadratic sequence

If a real sequence `G` has increments `G (k + 1) - G k` within `D` of
`a * u + (k * a + a / 2) * a * X` for `k < n`, where `n * a = 1`, then `G n - G 0` is within
`n * D` of `u + X / 2`. The expected increments are those of the quadratic
`t ↦ t * u + t ^ 2 * X / 2` along the grid `k * a`; they are summed by telescoping, and the
errors add up with the triangle inequality.

## Main results

* `TauCeti.abs_sub_sub_add_div_two_le_of_forall_lt`: the bound on `G n - G 0` from the bounds on
  the increments.
-/

public section

namespace TauCeti

/-- If the increments `G (k + 1) - G k` of a real sequence are within `D` of
`a * u + (k * a + a / 2) * a * X` for `k < n`, and `n * a = 1`, then `G n - G 0` is within
`n * D` of `u + X / 2`. -/
theorem abs_sub_sub_add_div_two_le_of_forall_lt {G : ℕ → ℝ} {a u X D : ℝ} {n : ℕ}
    (hna : (n : ℝ) * a = 1)
    (hstep : ∀ k < n, |G (k + 1) - G k - (a * u + (k * a + a / 2) * a * X)| ≤ D) :
    |G n - G 0 - (u + X / 2)| ≤ n * D := by
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.range m, (a * u + (k * a + a / 2) * a * X) =
      m * a * u + (m * a) ^ 2 * X / 2 := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hbound := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk =>
    hstep k (Finset.mem_range.1 hk))
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub G, hsum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, hna] at hbound
  convert hbound using 2
  ring

end TauCeti
