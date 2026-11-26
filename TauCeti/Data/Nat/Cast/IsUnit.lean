/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Commute
public import Mathlib.Data.Nat.Cast.NeZero

/-!
# Natural numbers casting to units in a semiring

Because natural-number casts commute with every element of a semiring, any divisor of an invertible
natural cast is again a unit. A natural number casting to a unit of a nontrivial semiring is
nonzero, and any ring homomorphism preserves invertibility of natural casts.

## Main results

* `IsUnit.neZero_natCast`: a natural number invertible in a nontrivial semiring is nonzero.
* `IsUnit.natCast_of_dvd`: a divisor of a natural number casting to a unit also casts to a unit.
* `IsUnit.natCast_map`: a ring homomorphism preserves invertibility of natural-number casts.
-/

public section

/-- A natural number invertible in a nontrivial semiring is nonzero as a natural number. -/
theorem IsUnit.neZero_natCast {R : Type*} [Semiring R] [Nontrivial R] {m : ℕ}
    (hm : IsUnit (m : R)) : NeZero m :=
  haveI : NeZero (m : R) := ⟨hm.ne_zero⟩
  .of_neZero_natCast R

/-- A divisor of a natural number casting to a unit in a semiring also casts to a unit. -/
theorem IsUnit.natCast_of_dvd {R : Type*} [Semiring R] {m n : ℕ}
    (hn : IsUnit (n : R)) (hmn : m ∣ n) : IsUnit (m : R) := by
  obtain ⟨k, rfl⟩ := hmn
  rw [Nat.cast_mul, (Nat.cast_commute m (k : R)).isUnit_mul_iff] at hn
  exact hn.1

/-- A ring homomorphism preserves invertibility of natural-number casts. -/
theorem IsUnit.natCast_map {F R S : Type*} [Semiring R] [Semiring S]
    [FunLike F R S] [RingHomClass F R S] (f : F) {n : ℕ} (hn : IsUnit (n : R)) :
    IsUnit (n : S) :=
  map_natCast f n ▸ hn.map f
