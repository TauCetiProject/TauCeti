/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.RingTheory.IntegralDomain

/-!
# Nonzero elements of a field with a nontrivial power

A field with more than `k + 1` elements has a nonzero element whose `k`-th power is not one, for
every positive `k`: the field is finite, its unit group is cyclic of order `Nat.card F - 1 > k`,
and a generator has order larger than `k`. For `k = 2` and fields with at least four elements this
is the input to the perfectness of the special linear groups in rank two.

## Main results

* `TauCeti.FiniteField.exists_ne_zero_pow_ne_one`: a field with more than `k + 1` elements has a
  nonzero element `a` with `a ^ k ≠ 1`.
-/

public section

namespace TauCeti.FiniteField

variable {F : Type*} [Field F]

/-- A field with more than `k + 1` elements has a nonzero element whose `k`-th power is not one,
for every positive `k`. Such a field is finite with a cyclic unit group of order larger than `k`,
so this is `exists_pow_ne_one_of_isCyclic`. -/
theorem exists_ne_zero_pow_ne_one {k : ℕ} (hk : k ≠ 0) (hF : k + 1 < Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ k ≠ 1 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨a, ha⟩ := exists_pow_ne_one_of_isCyclic (G := Fˣ) hk
    (by rw [Nat.card_eq_card_units_add_one F] at hF; omega)
  exact ⟨a, a.ne_zero, fun h ↦ ha (Units.ext <| by simpa using h)⟩

end TauCeti.FiniteField
