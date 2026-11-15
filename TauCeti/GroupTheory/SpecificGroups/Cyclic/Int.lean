/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Ordered integer coordinates on the range of a homomorphism

The range of a nonzero homomorphism to `ℤ` is order-additively isomorphic to `ℤ`.
The inverse image of one is its positive generator. We choose the equivalence supplied by
`LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int`.
-/

public section

namespace AddMonoidHom

variable {S : Type*} [AddGroup S] (c : S →+ ℤ)

/-- Ordered integer coordinates on the range of a nonzero homomorphism to `ℤ`. -/
noncomputable def rangeOrderAddEquivInt (hc : c ≠ 0) : c.range ≃+o ℤ := by
  haveI : Nontrivial c.range := (AddSubgroup.nontrivial_iff_ne_bot _).mpr
    (fun h => hc (AddMonoidHom.range_eq_bot_iff.mp h))
  exact (LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int.mp
    (inferInstance : IsAddCyclic c.range)).some

/-- The inverse image of one is a strictly positive integer in the range. -/
theorem rangeOrderAddEquivInt_symm_one_pos (hc : c ≠ 0) :
    0 < ((c.rangeOrderAddEquivInt hc).symm 1 : ℤ) := by
  have h : (0 : c.range) < (c.rangeOrderAddEquivInt hc).symm 1 := by
    rw [← map_zero (c.rangeOrderAddEquivInt hc).symm]
    exact (c.rangeOrderAddEquivInt hc).symm.strictMono zero_lt_one
  exact Subtype.coe_lt_coe.mpr h

end AddMonoidHom
