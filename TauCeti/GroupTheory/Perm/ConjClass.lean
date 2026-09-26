/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import TauCeti.Algebra.Group.Subgroup.Finite
public import TauCeti.GroupTheory.Perm.Partition

/-!
# The conjugacy classes of a cycle type in a group of permutations

An `S_n`-cycle type can meet several conjugacy classes of a subgroup `G ≤ S_n`, and can meet none,
so the elements of `G` of a prescribed full cycle type are counted by a sum over a finite index
set of `G`-classes rather than by a single class size. This file names that index set, for a
group of permutations of any finite carrier, and identifies the union of those classes with the
elements of that cycle type.

## Main results

* `TauCeti.Subgroup.classesOfType`: the conjugacy classes of `G` whose members have full cycle type
  `mu`.
* `TauCeti.Subgroup.mem_iUnion_classesOfType`: the elements of `G` of full cycle type `mu` are
  exactly the members of the classes of that type.

## References

* [Belyi maps, dessins d'enfants, and three-point covers](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/BelyiMaps/README.md),
  Layer 3.4 step 1, which asks for the finite index set `classesOfType G λ` of `G`-conjugacy
  classes of a full cycle type `λ` and for the identification of the elements of `G` of that type
  with the union of those classes. The names here follow it, for a group of permutations of any
  finite carrier.
* `Mathlib/Algebra/Group/ConjFinite.lean`, whose `Fintype` structure on `ConjClasses` is what
  makes the index set a `Finset`.
-/

open Equiv

attribute [local instance] Subgroup.fintypeOfFinite

public section

namespace TauCeti

variable {α : Type*} [Fintype α] [DecidableEq α]

open scoped Classical in
/-- The conjugacy classes of the subgroup `G` whose members have full cycle type `mu`.

One `S_n`-cycle type can meet several `G`-classes, and can meet none, so the elements of `G` of a
prescribed cycle type are counted by a sum over this index set rather than by one class size. -/
noncomputable def _root_.Subgroup.classesOfType (G : Subgroup (Equiv.Perm α)) (mu : Multiset ℕ) :
    Finset (ConjClasses G) :=
  {C ∈ (Finset.univ : Finset (ConjClasses G)) | ∃ g : G, ConjClasses.mk g = C ∧
    (g : Equiv.Perm α).fullCycleType = mu}

@[simp]
theorem _root_.Subgroup.mem_classesOfType {G : Subgroup (Equiv.Perm α)} {mu : Multiset ℕ}
    {C : ConjClasses G} :
    C ∈ G.classesOfType mu ↔
      ∃ g : G, ConjClasses.mk g = C ∧ (g : Equiv.Perm α).fullCycleType = mu := by
  simp [Subgroup.classesOfType]

/-- **The elements of `G` of full cycle type `mu` are the members of its classes of that type.**
One cycle type can meet several classes, and this says that the union of the classes recorded by
`TauCeti.Subgroup.classesOfType` is exactly the set of elements of that type. -/
theorem _root_.Subgroup.mem_iUnion_classesOfType (G : Subgroup (Equiv.Perm α))
    (mu : Multiset ℕ) (g : G) :
    (g : Equiv.Perm α).fullCycleType = mu ↔
      g ∈ ⋃ C ∈ G.classesOfType mu, C.carrier := by
  constructor
  · intro hg
    refine Set.mem_iUnion.2 ⟨ConjClasses.mk g, ?_⟩
    refine Set.mem_iUnion.2 ⟨Subgroup.mem_classesOfType.2 ⟨g, rfl, hg⟩, ?_⟩
    exact ConjClasses.mem_carrier_iff_mk_eq.2 rfl
  · intro hg
    have hg' : ∃ C : ConjClasses G, g ∈ ⋃ (_h : C ∈ G.classesOfType mu), C.carrier :=
      Set.mem_iUnion.1 hg
    obtain ⟨C, hgC⟩ := hg'
    have hgC' : ∃ (_h : C ∈ G.classesOfType mu), g ∈ C.carrier := Set.mem_iUnion.1 hgC
    obtain ⟨hCs, hgCs⟩ := hgC'
    obtain ⟨c, hmk, hc⟩ := Subgroup.mem_classesOfType.1 hCs
    have hgmk : ConjClasses.mk g = C := ConjClasses.mem_carrier_iff_mk_eq.1 hgCs
    have hconj : IsConj (g : Equiv.Perm α) (c : Equiv.Perm α) := by
      exact G.subtype.map_isConj (ConjClasses.mk_eq_mk_iff_isConj.1 (hgmk.trans hmk.symm))
    calc (g : Equiv.Perm α).fullCycleType = (c : Equiv.Perm α).fullCycleType :=
        Equiv.Perm.fullCycleType_eq_of_isConj hconj
      _ = mu := hc

end TauCeti
