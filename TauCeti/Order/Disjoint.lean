/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.SupIndep

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Pairwise disjoint families

`Pairwise.disjoint_iff_ne` characterizes disjointness in a pairwise disjoint family by inequality
of the indices, as soon as one of the two elements is different from bottom. It reduces
disjointness questions for such a family to questions about its labels.

`Finset.SupIndep.map_finset_sup` and `Set.PairwiseDisjoint.map_finset_sup` show that any map
sending `⊥` to `0` and disjoint binary suprema to sums sends supremum-independent (and in a
distributive lattice, pairwise-disjoint) finite suprema to sums.
-/

public section

namespace Pairwise

/-- In a pairwise disjoint family, an element different from bottom is disjoint from another
member of the family exactly when their indices differ. -/
theorem disjoint_iff_ne {α : Type*} [PartialOrder α] [OrderBot α] {ι : Type*} {f : ι → α}
    (h : Pairwise (Function.onFun Disjoint f)) {i j : ι} (hi : f i ≠ ⊥) :
    Disjoint (f i) (f j) ↔ i ≠ j :=
  ⟨fun hd hij ↦ hd.ne hi (congrArg f hij), fun hij ↦ h hij⟩

end Pairwise

/-- A map out of a bounded lattice that sends `⊥` to `0` and disjoint binary suprema to addition
sends every supremum-independent finite supremum to a sum. -/
theorem Finset.SupIndep.map_finset_sup {α ι M : Type*}
    [Lattice α] [OrderBot α] [AddCommMonoid M]
    {s : Finset ι} {U : ι → α} (hind : s.SupIndep U)
    (φ : α → M) (hbot : φ ⊥ = 0)
    (hsup : ∀ ⦃a b : α⦄, Disjoint a b → φ (a ⊔ b) = φ a + φ b) :
    φ (s.sup U) = ∑ i ∈ s, φ (U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty, Finset.sum_empty, hbot]
  | insert a s ha ih =>
    have hda : Disjoint (U a) (s.sup U) :=
      hind (Finset.subset_insert a s) (Finset.mem_insert_self a s) ha
    rw [Finset.sup_insert, hsup hda, Finset.sum_insert ha,
      ih (hind.subset (Finset.subset_insert a s))]

/-- A map out of a bounded distributive lattice that sends `⊥` to `0` and disjoint binary suprema
to addition sends every pairwise-disjoint finite supremum to a sum. -/
theorem Set.PairwiseDisjoint.map_finset_sup {α ι M : Type*}
    [DistribLattice α] [OrderBot α] [AddCommMonoid M]
    {s : Finset ι} {U : ι → α} (hdisj : (s : Set ι).PairwiseDisjoint U)
    (φ : α → M) (hbot : φ ⊥ = 0)
    (hsup : ∀ ⦃a b : α⦄, Disjoint a b → φ (a ⊔ b) = φ a + φ b) :
    φ (s.sup U) = ∑ i ∈ s, φ (U i) :=
  hdisj.supIndep.map_finset_sup φ hbot hsup
