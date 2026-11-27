/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Cast

/-!
# Integer-cast bounds in linearly ordered rings

This file records a small-perturbation criterion for integer casts in a linearly ordered ring: if
`u ≥ -1` (and `u ≥ 0` when `k = 0`) and a perturbation `u + δ` with `-e ≤ δ` crosses below a
nonpositive integer `k` while `e` stays strictly below `1`, `u` (when `0 < u`), and `u + 1` (when
`0 < u + 1`), then `u = k`.

## Main results

* `TauCeti.eq_intCast_of_add_lt_intCast`: if `u + δ < (k : R)` for a nonpositive integer `k` and
  a lower-bounded perturbation `-e ≤ δ` smaller than the margins to `0`, `-1`, and `1`, then
  `u = k`.
-/

public section

namespace TauCeti

/-- Scalar cutoff for a small-perturbation argument: if `u ≥ -1` (and `u ≥ 0` when `k = 0`) and a
perturbation `u + δ` with `-e ≤ δ` crosses below a nonpositive integer `k` within the step-size
tolerances at `0` and `-1`, then `u = k`. -/
theorem eq_intCast_of_add_lt_intCast {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    {u δ e : R} {k : ℤ} (hu1 : -1 ≤ u) (hk : k < 0 ∨ k = 0 ∧ 0 ≤ u)
    (h0 : 0 < u → e < u) (h1 : 0 < u + 1 → e < u + 1) (he1 : e < 1) (hneg : -e ≤ δ)
    (hlt : u + δ < k) : u = k := by
  have hsub : u - e ≤ u + δ := by
    rw [sub_eq_add_neg]
    exact add_le_add_right hneg u
  obtain rfl | rfl | hk2 : k = 0 ∨ k = -1 ∨ k ≤ -2 := by
    rcases hk with hk | ⟨rfl, -⟩ <;> omega
  · simp only [Int.cast_zero] at hlt ⊢
    rcases (hk.resolve_left (by omega)).2.eq_or_lt with h0' | h0'
    · exact h0'.symm
    · exact absurd (sub_lt_zero.mp (hsub.trans_lt hlt)) (h0 h0').not_gt
  · simp only [Int.cast_neg, Int.cast_one] at hlt ⊢
    rcases hu1.eq_or_lt with h1' | h1'
    · exact h1'.symm
    · have hu1pos : 0 < u + 1 := neg_lt_iff_pos_add.mp h1'
      have hlt' : u + 1 - e < 0 := by
        rw [add_sub_right_comm]
        exact (add_lt_add_left (hsub.trans_lt hlt) (1 : R)).trans_eq (neg_add_cancel (1 : R))
      exact absurd (sub_lt_zero.mp hlt') (h1 hu1pos).not_gt
  · have hk2' : (k : R) ≤ -2 := by exact_mod_cast hk2
    have hlt' : (-1 : R) - e < -2 :=
      ((sub_le_sub_right hu1 e).trans_lt (hsub.trans_lt hlt)).trans_le hk2'
    have hlt'' : (1 : R) - e < 0 := by
      have h := (add_lt_add_left hlt' (2 : R)).trans_eq (neg_add_cancel (2 : R))
      rwa [sub_add_eq_add_sub, ← one_add_one_eq_two, ← add_assoc, neg_add_cancel, zero_add] at h
    exact absurd (sub_lt_zero.mp hlt'') he1.not_gt

end TauCeti
