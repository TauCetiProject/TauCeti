/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Matroid.Minor.Contract
public import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Tactic.TautoSet

/-!
# Ranks in deletions and contractions

This file computes the `ℕ∞`-valued rank function of a deletion and of a contraction of a
matroid in terms of the rank function of the matroid itself. The rank of `X` in `M ＼ D` is the
rank of `X \ D` in `M`, and the rank of `X` in `M ／ C` plus the rank of `C` is the rank of
`X ∪ C`. When the rank of `C` is finite, for instance when `C` is a nonloop singleton or `M` has
finite rank, the second identity expresses the rank in `M ／ C` as a difference. These formulas
drive the deletion–contraction recursions of rank-generating invariants, such as the Tutte
polynomial.

## Main declarations

* `Matroid.delete_eRk_eq`: the rank function of a deletion.
* `Matroid.eRank_deleteElem_of_not_isColoop`: deleting a non-coloop keeps the rank.
* `Matroid.eRk_contract_add_eRk`, `Matroid.eRank_contract_add_eRk`: the rank function and the
  rank of a contraction.
* `Matroid.IsNonloop.eRk_contractElem_add_one`, `Matroid.IsNonloop.eRank_contractElem_add_one`:
  the rank function and the rank of the contraction of a nonloop.
* `Matroid.IsNonloop.toNat_eRk_insert`, `Matroid.IsNonloop.toNat_eRank`: the same two formulas
  for the natural-number ranks of a matroid of finite rank.

## References

* J. Oxley, *Matroid Theory*, second edition, Oxford University Press, 2011,
  Proposition 3.1.6.
-/

public section

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {I : Set α} {e : α}

/-- The rank of a set in the deletion `M ＼ D` is the rank in `M` of its elements outside `D`. -/
lemma delete_eRk_eq (M : Matroid α) (D X : Set α) : (M ＼ D).eRk X = M.eRk (X \ D) := by
  rw [delete_eq_restrict, restrict_eRk_eq', ← eRk_inter_ground M (X \ D)]
  congr 1
  tauto_set

/-- Deleting an element that is not a coloop does not change the rank of a matroid. -/
lemma eRank_deleteElem_of_not_isColoop (he : ¬ M.IsColoop e) : (M ＼ {e}).eRank = M.eRank := by
  rw [delete_eq_restrict, eRank_restrict]
  exact (not_not.1 (isColoop_iff_sdiff_not_spanning.not.1 he)).eRk_eq

/-- For an independent set `I`, the rank of `X` in `M ／ I` plus the cardinality of `I` is the
rank of `X ∪ I` in `M`. -/
lemma Indep.eRk_contract_add_encard (hI : M.Indep I) (X : Set α) :
    (M ／ I).eRk X + I.encard = M.eRk (X ∪ I) := by
  have hX : (X ∩ M.E) \ I ⊆ (M ／ I).E := sdiff_subset_sdiff_left inter_subset_right
  obtain ⟨J, hJ⟩ := (M ／ I).exists_isBasis _ hX
  have hJI : Disjoint J I := (subset_sdiff.1 hJ.subset).2
  have h₁ : X ∩ (M ／ I).E = (X ∩ M.E) \ I := by
    rw [contract_ground]
    tauto_set
  have h₂ : (X ∪ I) ∩ M.E = (X ∩ M.E) \ I ∪ I := by
    have := hI.subset_ground
    tauto_set
  rw [← eRk_inter_ground, h₁, ← M.eRk_inter_ground, h₂, hJ.eRk_eq_encard,
    (hI.union_isBasis_union_of_contract_isBasis hJ).eRk_eq_encard, encard_union_eq hJI]

/-- The rank of a set `X` in the contraction `M ／ C` plus the rank of `C` in `M` is the rank of
`X ∪ C` in `M`. -/
lemma eRk_contract_add_eRk (M : Matroid α) (C X : Set α) :
    (M ／ C).eRk X + M.eRk C = M.eRk (X ∪ C) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' C
  rw [hI.contract_eq_contract_delete, delete_eRk_eq, ← hI.encard_eq_eRk,
    hI.indep.eRk_contract_add_encard, union_comm, hI.eRk_eq_eRk_union, union_comm X]
  have := hI.subset
  congr 1
  tauto_set

/-- For a nonloop `e`, the rank of a set `X` in the contraction `M ／ {e}` plus one is the rank
of `insert e X` in `M`. -/
lemma IsNonloop.eRk_contractElem_add_one (he : M.IsNonloop e) (X : Set α) :
    (M ／ {e}).eRk X + 1 = M.eRk (insert e X) := by
  simpa [he.eRk_eq, union_singleton] using M.eRk_contract_add_eRk {e} X

/-- The rank of the contraction `M ／ C` plus the rank of `C` is the rank of `M`. -/
lemma eRank_contract_add_eRk (M : Matroid α) (C : Set α) : (M ／ C).eRank + M.eRk C = M.eRank := by
  rw [← eRk_ground, eRk_contract_add_eRk, contract_ground, sdiff_union_self, eRk_ground_union]

/-- For a nonloop `e`, the rank of the contraction `M ／ {e}` plus one is the rank of `M`. -/
lemma IsNonloop.eRank_contractElem_add_one (he : M.IsNonloop e) :
    (M ／ {e}).eRank + 1 = M.eRank := by
  simpa [he.eRk_eq] using M.eRank_contract_add_eRk {e}

/-- In a matroid of finite rank, the natural-number rank of `insert e X` for a nonloop `e` is one
more than the natural-number rank of `X` in the contraction `M ／ {e}`. -/
lemma IsNonloop.toNat_eRk_insert [M.RankFinite] (he : M.IsNonloop e) (X : Set α) :
    (M.eRk (insert e X)).toNat = ((M ／ {e}).eRk X).toNat + 1 := by
  rw [← he.eRk_contractElem_add_one,
    ENat.toNat_add ((M ／ {e}).isRkFinite_set X).eRk_lt_top.ne ENat.one_ne_top, ENat.toNat_one]

/-- In a matroid of finite rank, the natural-number rank of `M` is one more than that of the
contraction `M ／ {e}` of a nonloop `e`. -/
lemma IsNonloop.toNat_eRank [M.RankFinite] (he : M.IsNonloop e) :
    M.eRank.toNat = (M ／ {e}).eRank.toNat + 1 := by
  rw [← he.eRank_contractElem_add_one, ENat.toNat_add _ ENat.one_ne_top, ENat.toNat_one]
  exact (M ／ {e}).eRank_ne_top_iff.2 inferInstance

end Matroid
