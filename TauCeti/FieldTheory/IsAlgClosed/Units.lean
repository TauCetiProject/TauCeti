/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Divisible

/-!
# The units of an algebraically closed field

The unit group of an algebraically closed field is nontrivial, since the field is infinite.
Every unit of an algebraically closed field has an `n`-th root for each nonzero natural
number `n`, in every characteristic. The resulting rootability instance allows the additive
type tag of the unit group to be used as a divisible group, for example to extend characters
from subgroups by Baer's criterion.
-/

public section

namespace TauCeti.IsAlgClosed

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- The unit group of an algebraically closed field is divisible. -/
noncomputable instance unitsRootableByNat : RootableBy kˣ ℕ :=
  rootableByOfPowLeftSurj kˣ ℕ fun {n} hn a ↦ by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact a.ne_zero (by simpa [zero_pow hn] using hz.symm)
    exact ⟨Units.mk0 z hz0, Units.ext hz⟩

/-- The unit group of an algebraically closed field is nontrivial: the field is infinite, so it
has an element other than `0` and `1`. -/
instance unitsNontrivial : Nontrivial kˣ := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  exact nontrivial_of_ne (Units.mk0 x hx.1) 1 fun h ↦ hx.2 (congrArg Units.val h)

end TauCeti.IsAlgClosed
