/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.RamificationGroup
public import TauCeti.RingTheory.LocalRing.RamificationGroup

/-!
# Function-field and local-ring ramification groups

The lower ramification groups of a place are the generic local-ring ramification filtration of
its valuation ring. More precisely, for a place `P` of `F' / k` over `F`, this file identifies

`Place.ramificationGroup F P i`

with `IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers i`.
The comparison rests on the equality between the place filtration and powers of the maximal
ideal of `P.integers`.

The decomposition group acts faithfully on the valuation ring: agreement there implies
agreement on its fraction field. Consequently, after rewriting along the comparison, the generic
lower index (`IsLocalRing.mem_ramificationGroup_iff_le_lowerIndex`) and Hilbert counting identity
(`IsLocalRing.sum_addVal_smul_sub_eq_finsum_card_ramificationGroup_sub_one`) apply directly to
the function-field groups.

## Main results

* `TauCeti.Place.ramificationGroup_eq_isLocalRing_ramificationGroup`: the two lower ramification
  filtrations agree.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Theorem 3.8.7.
* J.-P. Serre, *Local Fields*, Chapter IV, Section 1.
-/

public section

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

/-- The lower ramification groups defined using the order filtration of the function field are
the generic local-ring ramification groups of the valuation ring. -/
theorem ramificationGroup_eq_isLocalRing_ramificationGroup (P : Place k F') (i : ℕ) :
    ramificationGroup F P i =
      IsLocalRing.ramificationGroup (P.integers.decompositionSubgroup F) P.integers i := by
  ext g
  rw [mem_ramificationGroup_iff, IsLocalRing.mem_ramificationGroup_natCast_iff]
  constructor
  · intro h x
    rw [P.mem_maximalIdeal_pow_iff_coe_mem_filtration, AddSubgroupClass.coe_sub,
      ValuationSubring.coe_decompositionSubgroup_smul, Nat.cast_add, Nat.cast_one]
    exact h x x.2
  · intro h x hx
    have h' := (P.mem_maximalIdeal_pow_iff_coe_mem_filtration (i + 1) _).mp (h ⟨x, hx⟩)
    rwa [AddSubgroupClass.coe_sub, ValuationSubring.coe_decompositionSubgroup_smul,
      Nat.cast_add, Nat.cast_one] at h'

end Place

end TauCeti
