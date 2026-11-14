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

Adjoining an identity to a semigroup creates no new units. Additively, adjoining zero to an
additive semigroup therefore makes it zero-sum-free: `Subsingleton (AddUnits (WithZero α))`.
-/

public section

@[to_additive /-- Adjoining zero to an additive semigroup makes it zero-sum-free. -/]
instance WithZero.instSubsingletonUnits {α : Type*} [Semigroup α] : Subsingleton (WithOne α)ˣ :=
  Subsingleton.units_of_isUnit fun a ha => by
    obtain ⟨b, h⟩ := ha.exists_right_inv
    induction a using WithOne.recOneCoe <;> induction b using WithOne.recOneCoe
    all_goals simp_all [← WithOne.coe_mul]
