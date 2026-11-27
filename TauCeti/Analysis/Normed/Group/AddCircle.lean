/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Multiples of small points of the circle

On `AddCircle p` the norm is the distance to the nearest multiple of the period, so it is at most
`|p| / 2`. Multiplying a point `x` by `n` multiplies its norm by `n` as long as `n * ‖x‖` stays
at most `|p| / 2`. Consequently, if `x ≠ 0` and `2 ^ n • x = 0`, the repeated doublings of `x`
cannot all stay small: some `2 ^ k • x` with `k < n` has norm at least `|p| / 4`. This is the
expansion estimate behind the topological entropy of the doubling map.

## Main results

* `AddCircle.norm_nsmul_of_mul_norm_le`: `‖n • x‖ = n * ‖x‖` when `n * ‖x‖ ≤ |p| / 2`.
* `AddCircle.exists_le_norm_two_pow_nsmul`: a nonzero point killed by `2 ^ n` has a multiple
  `2 ^ k • x`, `k < n`, of norm at least `|p| / 4`.
-/

public section

namespace AddCircle

variable {p : ℝ}

/-- Multiplying a point `x` of the circle by `n` multiplies its norm by `n`, as long as
`n * ‖x‖` is at most half the period. -/
theorem norm_nsmul_of_mul_norm_le {x : AddCircle p} {n : ℕ} (h : n * ‖x‖ ≤ |p| / 2) :
    ‖n • x‖ = n * ‖x‖ := by
  induction x using QuotientAddGroup.induction_on with | H t => ?_
  set s := t - round (p⁻¹ * t) * p
  have hst : (s : AddCircle p) = t := by
    rw [coe_sub, sub_eq_self, coe_eq_zero_iff]
    exact ⟨round (p⁻¹ * t), by simp⟩
  have hs : ‖(t : AddCircle p)‖ = |s| := norm_eq p
  have habs : |(n : ℝ) * s| = n * |s| := by rw [abs_mul, Nat.abs_cast]
  rw [hs, ← habs] at h
  rw [hs, ← habs, ← hst, ← coe_nsmul, nsmul_eq_mul]
  rcases eq_or_ne p 0 with rfl | hp
  · exact norm_eq_of_zero
  · exact (norm_coe_eq_abs_iff p hp).mpr h

/-- If `x ≠ 0` and `2 ^ n • x = 0`, then some `2 ^ k • x` with `k < n` has norm at least a
quarter of the period. -/
theorem exists_le_norm_two_pow_nsmul {x : AddCircle p} (hx : x ≠ 0) {n : ℕ}
    (hn : 2 ^ n • x = 0) : ∃ k < n, |p| / 4 ≤ ‖2 ^ k • x‖ := by
  by_contra! h
  have key : ∀ k ≤ n, ‖2 ^ k • x‖ = 2 ^ k * ‖x‖ := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_nsmul, norm_nsmul_of_mul_norm_le (by push_cast; linarith [h k (by omega)]),
        ih (by omega)]
      push_cast
      ring
  have := key n le_rfl
  rw [hn, norm_zero] at this
  exact hx (norm_eq_zero.mp
    ((mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero n two_ne_zero)))

end AddCircle
