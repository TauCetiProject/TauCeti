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
elements of that cycle type. A finite group has only finitely many conjugacy classes, so the
classes of a given cycle type form a `Finset`, and the count over them is a finite sum of class
sizes.

## Main results

* `TauCeti.Subgroup.classesOfFullCycleType`: the conjugacy classes of `G` whose members have full
  cycle type `mu`.
* `TauCeti.Subgroup.iUnionClassesOfFullCycleType`: the set of the elements of `G` of full cycle
  type `mu`, the union of those classes.
* `TauCeti.Subgroup.mem_iUnionClassesOfFullCycleType`: an element of `G` is a member of one of the
  classes of type `mu` exactly when it has full cycle type `mu`.
* `TauCeti.Subgroup.mem_iUnion_classesOfFullCycleType`: that same characterization with the union
  of the classes written out.
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
noncomputable def _root_.Subgroup.classesOfFullCycleType (G : Subgroup (Equiv.Perm α))
    (mu : Multiset ℕ) : Finset (ConjClasses G) :=
  {C ∈ (Finset.univ : Finset (ConjClasses G)) | ∃ g : G, ConjClasses.mk g = C ∧
    (g : Equiv.Perm α).fullCycleType = mu}

@[simp]
theorem _root_.Subgroup.mem_classesOfFullCycleType {G : Subgroup (Equiv.Perm α)}
    {mu : Multiset ℕ} {C : ConjClasses G} :
    C ∈ G.classesOfFullCycleType mu ↔
      ∃ g : G, ConjClasses.mk g = C ∧ (g : Equiv.Perm α).fullCycleType = mu := by
  simp [Subgroup.classesOfFullCycleType]

/-- The elements of `G` of full cycle type `mu`: the union of the conjugacy classes recorded by
`TauCeti.Subgroup.classesOfFullCycleType`. This is the set whose membership
`TauCeti.Subgroup.mem_iUnionClassesOfFullCycleType` characterizes, and the set whose size is the
sum of those class sizes. -/
noncomputable def _root_.Subgroup.iUnionClassesOfFullCycleType
    (G : Subgroup (Equiv.Perm α)) (mu : Multiset ℕ) : Set G :=
  ⋃ C ∈ G.classesOfFullCycleType mu, C.carrier

/-- **An element of `G` is a member of one of its classes of type `mu` exactly when it has full
cycle type `mu`.** One cycle type can meet several classes, and this says that the union of the
classes recorded by `TauCeti.Subgroup.classesOfFullCycleType` is exactly the set of elements of
that type. -/
theorem _root_.Subgroup.mem_iUnion_classesOfFullCycleType (G : Subgroup (Equiv.Perm α))
    (mu : Multiset ℕ) (g : G) :
    g ∈ ⋃ C ∈ G.classesOfFullCycleType mu, C.carrier ↔
      (g : Equiv.Perm α).fullCycleType = mu := by
  constructor
  · intro hg
    have hg' : ∃ C : ConjClasses G, g ∈ ⋃ (_h : C ∈ G.classesOfFullCycleType mu), C.carrier :=
      Set.mem_iUnion.1 hg
    obtain ⟨C, hgC⟩ := hg'
    have hgC' : ∃ (_h : C ∈ G.classesOfFullCycleType mu), g ∈ C.carrier := Set.mem_iUnion.1 hgC
    obtain ⟨hCs, hgCs⟩ := hgC'
    obtain ⟨c, hmk, hc⟩ := Subgroup.mem_classesOfFullCycleType.1 hCs
    have hgmk : ConjClasses.mk g = C := ConjClasses.mem_carrier_iff_mk_eq.1 hgCs
    have hconj : IsConj (g : Equiv.Perm α) (c : Equiv.Perm α) := by
      exact G.subtype.map_isConj (ConjClasses.mk_eq_mk_iff_isConj.1 (hgmk.trans hmk.symm))
    calc (g : Equiv.Perm α).fullCycleType = (c : Equiv.Perm α).fullCycleType :=
        Equiv.Perm.fullCycleType_eq_of_isConj hconj
      _ = mu := hc
  · intro hg
    refine Set.mem_iUnion.2 ⟨ConjClasses.mk g, ?_⟩
    refine Set.mem_iUnion.2 ⟨Subgroup.mem_classesOfFullCycleType.2 ⟨g, rfl, hg⟩, ?_⟩
    exact ConjClasses.mem_carrier_iff_mk_eq.2 rfl

/-- The same characterization as `TauCeti.Subgroup.mem_iUnion_classesOfFullCycleType`, read on the
named set `TauCeti.Subgroup.iUnionClassesOfFullCycleType`, whose left-hand side is in simp normal
form and so normalizes membership to the cycle-type condition. -/
@[simp]
theorem _root_.Subgroup.mem_iUnionClassesOfFullCycleType {G : Subgroup (Equiv.Perm α)}
    {mu : Multiset ℕ} {g : G} :
    g ∈ G.iUnionClassesOfFullCycleType mu ↔ (g : Equiv.Perm α).fullCycleType = mu :=
  Subgroup.mem_iUnion_classesOfFullCycleType G mu g

/-- A conjugacy class of a permutation subgroup has a specified full cycle type if and only if
one (hence every) representative has that type. -/
theorem _root_.Subgroup.mem_classesOfFullCycleType_mk
    (G : Subgroup (Equiv.Perm α)) (mu : Multiset ℕ) (g : G) :
    ConjClasses.mk g ∈ G.classesOfFullCycleType mu ↔
      (g : Equiv.Perm α).fullCycleType = mu := by
  constructor
  · intro h
    apply (G.mem_iUnion_classesOfFullCycleType mu g).mp
    exact Set.mem_iUnion.mpr ⟨ConjClasses.mk g,
      Set.mem_iUnion.mpr ⟨h, ConjClasses.mem_carrier_iff_mk_eq.mpr rfl⟩⟩
  · intro h
    exact Subgroup.mem_classesOfFullCycleType.mpr ⟨g, rfl, h⟩

end TauCeti
