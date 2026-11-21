/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.WithOne.Basic
public import Mathlib.Algebra.Group.Units.Basic

/-!
# Units of a semigroup with an adjoined identity

In `WithOne α`, a product of two elements of `α` lies in `α`, so the adjoined identity is the
only unit. Additively, the adjoined zero is the only additive unit of `WithZero α`; for a
commutative `α`, this says that in `WithZero α` a sum vanishes only when every summand does.
This applies to the zero-adjoined coefficient semifields of cluster algebras.
-/

public section

namespace TauCeti

/-- The adjoined identity is the only unit of `WithOne α`. -/
@[to_additive /-- The adjoined zero is the only additive unit of `WithZero α`. -/]
instance instSubsingletonUnitsWithOne {α : Type*} [Semigroup α] : Subsingleton (WithOne α)ˣ :=
  Subsingleton.units_of_isUnit fun a ha ↦ by
    obtain ⟨b, h⟩ := ha.exists_right_inv
    induction a using WithOne.recOneCoe <;> induction b using WithOne.recOneCoe
    all_goals simp_all [← WithOne.coe_mul]

end TauCeti
