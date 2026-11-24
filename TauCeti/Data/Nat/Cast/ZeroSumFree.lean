/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Data.Nat.Cast.Defs

/-!
# Natural-number casts in zero-sum-free additive monoids

Mathlib expresses that a sum vanishes only when every summand does by the triviality of the
additive units, `Subsingleton (AddUnits R)`. Natural-number casts commute with each other, so if
the additive units are trivial and `1 ≠ 0`, no positive natural number casts to zero; this needs
no commutativity of the addition. Such a cast need not be injective: in the Boolean semiring
`1 + 1 = 1`. This is what lets natural-coefficient polynomials be evaluated without
cancellation.
-/

public section

namespace TauCeti

/-- In an additive monoid with one with trivial additive units, in which `1 ≠ 0`, a natural
number casts to zero only if it is zero. -/
@[simp]
theorem natCast_eq_zero_iff {R : Type*} [AddMonoidWithOne R] [Subsingleton (AddUnits R)]
    [NeZero (1 : R)] {n : ℕ} : (n : R) = 0 ↔ n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  obtain _ | n := n
  · rfl
  · let u : AddUnits R :=
      ⟨1, n, by rw [← Nat.cast_one_add, Nat.add_comm, h], by rw [← Nat.cast_succ, h]⟩
    exact absurd (congrArg AddUnits.val (Subsingleton.elim u 0)) (NeZero.ne 1)

end TauCeti
