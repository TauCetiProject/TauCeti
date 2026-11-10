/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Algebra.CharP.Basic

/-!
# Integer intervals in positive characteristic

Integer casting is injective on a half-open interval exactly when its length is at most
the positive characteristic. The closed-interval version retains the strict length bound;
in particular, adding both endpoints of a full period destroys injectivity.
-/

public section

namespace CharP

variable (R : Type*) [AddGroupWithOne R] (p : ℕ) [CharP R p] [NeZero p]

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
  · intro hlen x hx y hy hxy
    have hx' : x - s ∈ Set.Ico (0 : ℤ) p := by
      rcases hx with ⟨_, _⟩
      constructor <;> omega
    have hy' : y - s ∈ Set.Ico (0 : ℤ) p := by
      rcases hy with ⟨_, _⟩
      constructor <;> omega
    have he := intCast_injOn_Ico R p hx' hy' (by simpa using congrArg (· - (s : R)) hxy)
    omega

/-- A closed integer interval casts injectively exactly when the distance between its
endpoints is strictly less than the positive characteristic. -/
theorem intCast_injOn_Icc_iff (s t : ℤ) :
    Set.InjOn (Int.cast : ℤ → R) (Set.Icc s t) ↔ t - s < p := by
  have hset : Set.Icc s t = Set.Ico s (t + 1) := by
    ext x
    simp only [Set.mem_Icc, Set.mem_Ico]
    omega
  rw [hset, intCast_injOn_Ico_iff R p]
  omega

end CharP
