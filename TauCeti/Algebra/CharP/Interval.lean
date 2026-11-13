/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Order.Interval.Set.SuccPred
public import Mathlib.Order.SuccPred.Int

/-!
# Integer casting on integer intervals

In characteristic `p`, integer casting is injective on `Set.Ico s t` when `t - s ≤ p`
and on `Set.Icc s t` when `t - s < p`. For positive `p`, these conditions are also
necessary, including for empty intervals. In particular, including both endpoints of a
full period destroys injectivity.
-/

public section

namespace CharP

variable (R : Type*) [AddGroupWithOne R] (p : ℕ) [CharP R p]

/-- A half-open integer interval casts injectively when its signed endpoint difference
is at most the characteristic. -/
theorem intCast_injOn_Ico_of_sub_le {s t : ℤ} (h : t - s ≤ p) :
    Set.InjOn (Int.cast : ℤ → R) (Set.Ico s t) := by
  intro x hx y hy hxy
  have hx' : x - s ∈ Set.Ico (0 : ℤ) p := by
    rcases hx with ⟨_, _⟩
    constructor <;> omega
  have hy' : y - s ∈ Set.Ico (0 : ℤ) p := by
    rcases hy with ⟨_, _⟩
    constructor <;> omega
  have he := intCast_injOn_Ico R p hx' hy' (by simpa using congrArg (· - (s : R)) hxy)
  omega

/-- A closed integer interval casts injectively when its signed endpoint difference
is strictly less than the characteristic. -/
theorem intCast_injOn_Icc_of_sub_lt {s t : ℤ} (h : t - s < p) :
    Set.InjOn (Int.cast : ℤ → R) (Set.Icc s t) := by
  rw [← Set.Ico_add_one_right_eq_Icc s t]
  exact intCast_injOn_Ico_of_sub_le R p (by omega)

variable [NeZero p]

/-- A half-open integer interval casts injectively exactly when its length is at most
the positive characteristic. This also includes empty intervals. -/
theorem intCast_injOn_Ico_iff (s t : ℤ) :
    Set.InjOn (Int.cast : ℤ → R) (Set.Ico s t) ↔ t - s ≤ p := by
  have hp0 : p ≠ 0 := NeZero.ne p
  have hp : (0 : ℤ) < p := by omega
  constructor
  · intro h
    by_contra! hlen
    have he := h (x₁ := s) (by constructor <;> omega)
      (x₂ := s + p) (by constructor <;> omega) (by simp)
    omega
  · exact intCast_injOn_Ico_of_sub_le R p

/-- A closed integer interval casts injectively exactly when its signed endpoint difference
`t - s` is strictly less than the positive characteristic, including for empty intervals. -/
theorem intCast_injOn_Icc_iff (s t : ℤ) :
    Set.InjOn (Int.cast : ℤ → R) (Set.Icc s t) ↔ t - s < p := by
  rw [← Set.Ico_add_one_right_eq_Icc s t, intCast_injOn_Ico_iff R p]
  omega

end CharP
