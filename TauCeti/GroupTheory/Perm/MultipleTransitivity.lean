/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import TauCeti.GroupTheory.Perm.Basic

/-!
# Long cycles and transitivity

A permutation group containing a cycle on all points is transitive, and a transitive permutation
group containing a cycle on all but one point is doubly transitive. In the second case, the
missing point is the unique fixed point of the cycle. Its stabilizer contains the cycle and is
therefore transitive on the complement; the usual point-stabilizer criterion then gives double
transitivity of the original action.

## Main results

* `TauCeti.isPretransitive_of_isCycle_mem_of_support_eq_univ`: a permutation group containing a
  cycle with full support is transitive.
* `TauCeti.card_support_add_one_eq_card_iff_existsUnique_fixedPoint`: a permutation moves all but
  one point exactly when it has a unique fixed point.
* `TauCeti.is_two_pretransitive_of_isCycle_mem_of_existsUnique_fixedPoint`: a transitive
  permutation group containing a cycle with a unique fixed point is doubly transitive.
* `TauCeti.isPreprimitive_of_isCycle_mem_of_existsUnique_fixedPoint`: such a group is primitive.
* `TauCeti.is_two_pretransitive_of_isCycle_mem_of_card_support_add_one_eq_card`: a transitive
  finite permutation group that contains a cycle moving all but one point is doubly transitive.
* `TauCeti.isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq_card`: such a group is
  primitive.

These results are part of the generic recognition package in Layer 1 of
`TauCetiRoadmap/PolynomialGaloisGroups/README.md`, which supports both the degree-at-most-five
classification and Layer 9. The long-cycle criterion is used specifically in Layer 9's three-prime
construction of polynomials with full symmetric Galois group.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, §2.1.
* H. Wielandt, *Finite Permutation Groups*, Chapter II.

The point-stabilizer step is adapted from `Mathlib/GroupTheory/GroupAction/Jordan.lean`, by Antoine
Chambert-Loir; the cycle-transitivity argument generalizes that file's
`Equiv.Perm.isPretransitive_of_isCycle_mem` from finite support to a unique fixed point.
-/

public section

namespace TauCeti

open MulAction

variable {α : Type*}

/-- A transitive permutation group containing a cycle with a unique fixed point is doubly
transitive. -/
theorem is_two_pretransitive_of_isCycle_mem_of_existsUnique_fixedPoint
    (G : Subgroup (Equiv.Perm α)) [IsPretransitive G α] {σ : Equiv.Perm α}
    (hσ : σ.IsCycle) (hσG : σ ∈ G) (hfix : ∃! x : α, σ x = x) :
    IsMultiplyPretransitive G α 2 := by
  obtain ⟨x, hx, hunique⟩ := hfix
  have hσFixing : (⟨σ, hσG⟩ : G) ∈ fixingSubgroup G ({x} : Set α) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact hx
  let σ' : fixingSubgroup G ({x} : Set α) := ⟨⟨σ, hσG⟩, hσFixing⟩
  have htrans :
      IsPretransitive (fixingSubgroup G ({x} : Set α))
        (SubMulAction.ofFixingSubgroup G ({x} : Set α)) := by
    refine ⟨?_⟩
    intro y z
    rcases y with ⟨y, hy⟩
    rcases z with ⟨z, hz⟩
    have hy_ne : y ≠ x := by
      simpa only [Set.mem_singleton_iff] using
        (SubMulAction.mem_ofFixingSubgroup_iff G).mp hy
    have hz_ne : z ≠ x := by
      simpa only [Set.mem_singleton_iff] using
        (SubMulAction.mem_ofFixingSubgroup_iff G).mp hz
    have hσy : σ y ≠ y := fun hy_fixed ↦ hy_ne (hunique y hy_fixed)
    have hσz : σ z ≠ z := fun hz_fixed ↦ hz_ne (hunique z hz_fixed)
    obtain ⟨i, hi⟩ := hσ.exists_zpow_eq hσy hσz
    refine ⟨σ' ^ i, ?_⟩
    apply Subtype.ext
    exact hi
  rw [SubMulAction.ofStabilizer.isMultiplyPretransitive (a := x)]
  rw [is_one_pretransitive_iff]
  exact IsPretransitive.of_surjective_map
    SubMulAction.ofFixingSubgroup_of_singleton_bijective.surjective htrans

/-- A transitive permutation group containing a cycle with a unique fixed point is primitive. -/
theorem isPreprimitive_of_isCycle_mem_of_existsUnique_fixedPoint
    (G : Subgroup (Equiv.Perm α)) [IsPretransitive G α] {σ : Equiv.Perm α}
    (hσ : σ.IsCycle) (hσG : σ ∈ G) (hfix : ∃! x : α, σ x = x) :
    IsPreprimitive G α :=
  isPreprimitive_of_is_two_pretransitive
    (is_two_pretransitive_of_isCycle_mem_of_existsUnique_fixedPoint G hσ hσG hfix)

variable [Fintype α] [DecidableEq α]

/-- A permutation subgroup containing a cycle with full support acts transitively. -/
theorem isPretransitive_of_isCycle_mem_of_support_eq_univ {G : Subgroup (Equiv.Perm α)}
    {g : Equiv.Perm α} (hgc : g.IsCycle) (hg : g ∈ G) (hsupp : g.support = Finset.univ) :
    IsPretransitive G α := by
  have h := Equiv.Perm.isPretransitive_of_isCycle_mem hgc hg
  rw [hsupp, Finset.coe_univ, Set.compl_univ] at h
  exact IsPretransitive.of_surjective_map
    SubMulAction.ofFixingSubgroupEmpty_equivariantMap_bijective.surjective h

/-- A transitive subgroup of a finite symmetric group that contains a cycle moving all but one
point is doubly transitive. -/
theorem is_two_pretransitive_of_isCycle_mem_of_card_support_add_one_eq_card
    (G : Subgroup (Equiv.Perm α)) [IsPretransitive G α] {σ : Equiv.Perm α}
    (hσ : σ.IsCycle) (hσG : σ ∈ G)
    (hcard : σ.support.card + 1 = Fintype.card α) :
    IsMultiplyPretransitive G α 2 :=
  is_two_pretransitive_of_isCycle_mem_of_existsUnique_fixedPoint G hσ hσG
    ((card_support_add_one_eq_card_iff_existsUnique_fixedPoint σ).mp hcard)

/-- A transitive subgroup of a finite symmetric group that contains a cycle moving all but one
point is primitive. -/
theorem isPreprimitive_of_isCycle_mem_of_card_support_add_one_eq_card
    (G : Subgroup (Equiv.Perm α)) [IsPretransitive G α] {σ : Equiv.Perm α}
    (hσ : σ.IsCycle) (hσG : σ ∈ G)
    (hcard : σ.support.card + 1 = Fintype.card α) :
    IsPreprimitive G α :=
  isPreprimitive_of_isCycle_mem_of_existsUnique_fixedPoint G hσ hσG
    ((card_support_add_one_eq_card_iff_existsUnique_fixedPoint σ).mp hcard)

end TauCeti
