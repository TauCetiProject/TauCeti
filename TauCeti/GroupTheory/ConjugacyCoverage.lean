/-
Copyright (c) 2026 Robert Joseph. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Pairwise
public import Mathlib.GroupTheory.Index

/-!
# Conjugacy-class coverage from centralizer indices

A pairwise nonconjugate list in a finite group meets every conjugacy class if the sum of its
centralizer indices is the group order. The indices refer to the actual centralizers; proving
their values and the pairwise hypothesis remains the caller's responsibility.
-/

public section

variable {G : Type*} [Group G] [Finite G]

/-- A pairwise nonconjugate list covers a finite group when its centralizer indices sum to the
group order. No enumeration of the group or decidable conjugacy is required in the hypotheses. -/
theorem exists_mem_isConj_of_sum_centralizer_index_eq_card (l : List G)
    (hp : l.Pairwise fun x y => ¬ IsConj x y)
    (hm : (l.map fun x => (Subgroup.centralizer ({x} : Set G)).index).sum = Nat.card G)
    (g : G) : ∃ x ∈ l, IsConj x g := by
  classical
  let := Fintype.ofFinite G
  let c : G → Finset G := fun x => (conjugatesOf x).toFinset
  have hn : l.Nodup := by
    refine hp.imp fun {x y} h => ?_
    rintro rfl
    exact h (IsConj.refl x)
  let : Std.Symm (fun x y : G => ¬ IsConj x y) :=
    ⟨fun _ _ h h' => h h'.symm⟩
  have hd : (l.toFinset : Set G).PairwiseDisjoint c := by
    intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro z hxz hyz
    exact hp.forall (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hxy
      ((Set.mem_toFinset.mp hxz).trans (Set.mem_toFinset.mp hyz).symm)
  have hc : (l.toFinset.biUnion c).card = Fintype.card G := by
    rw [Finset.card_biUnion hd]
    simp only [c, ← Set.ncard_eq_toFinset_card', ← Subgroup.index_centralizer_eq_ncard]
    rw [List.sum_toFinset _ hn, hm, Nat.card_eq_fintype_card]
  have hu : l.toFinset.biUnion c = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using hc.ge)
  have hg : g ∈ l.toFinset.biUnion c := hu.symm ▸ Finset.mem_univ g
  obtain ⟨x, hx, hxg⟩ := Finset.mem_biUnion.mp hg
  exact ⟨x, List.mem_toFinset.mp hx, Set.mem_toFinset.mp hxg⟩
