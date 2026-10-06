/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join
public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold

/-!
# Joins of standard combinatorial balls and spheres

The join of two simplices is a simplex. The join of a simplex boundary with a simplex or
another simplex boundary is obtained by one stellar subdivision of a simplex or its boundary,
respectively. These identities classify the joins of the standard ball and sphere models and
supply the standard-model calculation for links of new vertices in stellar subdivisions.

The dimensions add with an extra `1`: the join of an `m`-sphere and an `n`-sphere is an
`(m + n + 1)`-sphere, and the join of an `m`-sphere and an `n`-ball is an
`(m + n + 1)`-ball. The assertions here concern standard models; transport to arbitrary
combinatorial balls and spheres requires preservation of stellar equivalence under joins.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2 and 3.
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2
  (1999), 299-320.
-/

public section

open Finset Function Sum

namespace PreAbstractSimplicialComplex

variable {α β : Type*}
  {V : Finset α} {W : Finset β} {w : β} {m n : ℕ}

/-- The join of two simplices is the simplex on the disjoint union of their vertices. -/
@[simp]
theorem join_simplex_simplex (V : Finset α) (W : Finset β) :
    join (simplex V) (simplex W) = simplex (V.disjSum W) := by
  refine SetLike.ext fun τ => ?_
  simp only [mem_join_iff, mem_simplex, subset_disjSum]
  grind [Finset.nonempty_iff_ne_empty, Finset.empty_subset]

variable [DecidableEq α] [DecidableEq β]

/-- Starring the left face of a simplex produces the join of its boundary with the simplex
on the right vertices together with the chosen vertex `w`. The formula also allows `w ∈ W`. -/
@[simp]
theorem stellarSubdivision_simplex_disjSum (hV : V.Nonempty) :
    stellarSubdivision (simplex (V.disjSum W)) (V.map Embedding.inl) (inr w) =
      join (simplexBoundary V) (simplex (insert w W)) := by
  refine SetLike.ext fun τ => ?_
  have herase : (τ.erase (inr w)).toLeft = τ.toLeft := by ext x; simp
  have herase' : (τ.erase (inr w)).toRight = τ.toRight.erase w := by ext x; simp
  have hnonempty : (τ.erase (inr w) ∪ V.map Embedding.inl).Nonempty :=
    (hV.map (f := Embedding.inl)).mono subset_union_right
  have hleft : (V.map (Embedding.inl : α ↪ α ⊕ β)).toLeft = V := by
    simp [← disjSum_empty]
  have hright : (V.map (Embedding.inl : α ↪ α ⊕ β)).toRight = ∅ := by
    simp [← disjSum_empty]
  by_cases hmem : inr w ∈ τ
  · simp only [mem_stellarSubdivision_iff, hmem, not_true_eq_false, false_and, false_or,
      true_and, mem_simplex, hnonempty, mem_join_iff, mem_simplexBoundary,
      subset_disjSum, map_inl_subset_iff_subset_toLeft,
      herase, herase', hleft, hright, union_subset_iff, subset_refl, Finset.ssubset_iff_subset_ne]
    have hne : τ.Nonempty := ⟨inr w, hmem⟩
    have hsub : τ.toRight.erase w ⊆ W ↔ τ.toRight ⊆ insert w W :=
      subset_insert_iff.symm
    rw [hsub]
    grind [Finset.nonempty_iff_ne_empty, Finset.empty_subset]
  · have hnot : w ∉ τ.toRight := by simpa using hmem
    have hsub : τ.toRight ⊆ insert w W ↔ τ.toRight ⊆ W :=
      subset_insert_iff_of_notMem hnot
    simp only [mem_stellarSubdivision_iff, hmem, not_false_eq_true, true_and, false_and,
      or_false, mem_simplex, mem_join_iff, mem_simplexBoundary,
      subset_disjSum, map_inl_subset_iff_subset_toLeft, Finset.ssubset_iff_subset_ne, hsub]
    grind [Finset.nonempty_iff_ne_empty, Finset.empty_subset]

/-- The stellar subdivision of a simplex boundary along its left vertex set is the join
of that set's boundary with the boundary on the right vertices and the fresh vertex `w`. -/
@[simp]
theorem stellarSubdivision_simplexBoundary_disjSum (hV : V.Nonempty) (hw : w ∉ W) :
    stellarSubdivision (simplexBoundary (V.disjSum W)) (V.map Embedding.inl) (inr w) =
      join (simplexBoundary V) (simplexBoundary (insert w W)) := by
  refine SetLike.ext fun τ => ?_
  have herase : (τ.erase (inr w)).toLeft = τ.toLeft := by ext x; simp
  have herase' : (τ.erase (inr w)).toRight = τ.toRight.erase w := by ext x; simp
  have hnonempty : (τ.erase (inr w) ∪ V.map Embedding.inl).Nonempty :=
    (hV.map (f := Embedding.inl)).mono subset_union_right
  have hleft : (V.map (Embedding.inl : α ↪ α ⊕ β)).toLeft = V := by
    simp [← disjSum_empty]
  have hright : (V.map (Embedding.inl : α ↪ α ⊕ β)).toRight = ∅ := by
    simp [← disjSum_empty]
  by_cases hmem : inr w ∈ τ
  · have hne : τ.Nonempty := ⟨inr w, hmem⟩
    have hsub : τ.toRight.erase w ⊆ W ↔ τ.toRight ⊆ insert w W :=
      subset_insert_iff.symm
    have heq : τ.toRight.erase w = W ↔ τ.toRight = insert w W :=
      erase_eq_iff_eq_insert (Finset.mem_toRight.mpr hmem) hw
    simp only [mem_stellarSubdivision_iff, hmem, not_true_eq_false, false_and, false_or,
      true_and, mem_simplexBoundary, hnonempty, mem_join_iff,
      Finset.ssubset_iff_subset_ne, subset_disjSum, map_inl_subset_iff_subset_toLeft,
      herase, herase', hleft, hright, union_subset_iff, subset_refl, hsub]
    simp only [ne_eq, Finset.eq_disjSum_iff]
    simp only [toLeft_union, toRight_union, herase, herase', hleft, hright, union_empty, heq]
    grind [Finset.nonempty_iff_ne_empty, Finset.empty_subset, Finset.union_eq_right]
  · have hnot : w ∉ τ.toRight := by simpa using hmem
    have hsub : τ.toRight ⊆ insert w W ↔ τ.toRight ⊆ W :=
      subset_insert_iff_of_notMem hnot
    simp only [mem_stellarSubdivision_iff, hmem, not_false_eq_true, true_and, false_and,
      or_false, mem_simplexBoundary, mem_join_iff,
      Finset.ssubset_iff_subset_ne, subset_disjSum, map_inl_subset_iff_subset_toLeft,
      hsub]
    simp only [ne_eq, Finset.eq_disjSum_iff]
    grind [Finset.nonempty_iff_ne_empty, Finset.empty_subset, Finset.mem_insert_self]

/-- The join of a standard `m`-sphere with a standard `n`-ball is a combinatorial
`(m + n + 1)`-ball. -/
theorem isCombinatorialBall_join_simplexBoundary_simplex
    (hV : V.card = m + 2) (hW : W.card = n + 1) :
    IsCombinatorialBall (join (simplexBoundary V) (simplex W)) (m + n + 1) := by
  have hVne : V.Nonempty := card_pos.mp (by omega)
  obtain ⟨w, hw⟩ := card_pos.mp (by omega : 0 < W.card)
  have hmodel : IsCombinatorialBall (simplex (V.disjSum (W.erase w))) (m + n + 1) := by
    apply isCombinatorialBall_simplex
    rw [card_disjSum, card_erase_of_mem hw, hV, hW]
    omega
  have hface : V.map Embedding.inl ∈ simplex (V.disjSum (W.erase w)) := by
    rw [mem_simplex]
    exact ⟨hVne.map, by simp [subset_disjSum, ← disjSum_empty]⟩
  have hfresh : ({inr w} : Finset (α ⊕ β)) ∉ simplex (V.disjSum (W.erase w)) := by
    simp
  have hstar := hmodel.stellarSubdivision hface hfresh
  rwa [stellarSubdivision_simplex_disjSum hVne, insert_erase hw] at hstar

/-- The join of standard `m`- and `n`-spheres is a combinatorial `(m + n + 1)`-sphere. -/
theorem isCombinatorialSphere_join_simplexBoundary_simplexBoundary
    (hV : V.card = m + 2) (hW : W.card = n + 2) :
    IsCombinatorialSphere (join (simplexBoundary V) (simplexBoundary W)) (m + n + 1) := by
  have hVne : V.Nonempty := card_pos.mp (by omega)
  obtain ⟨w, hw⟩ := card_pos.mp (by omega : 0 < W.card)
  have hWne : (W.erase w).Nonempty := card_pos.mp (by
    rw [card_erase_of_mem hw, hW]
    omega)
  have hmodel : IsCombinatorialSphere
      (simplexBoundary (V.disjSum (W.erase w))) (m + n + 1) := by
    apply isCombinatorialSphere_simplexBoundary
    rw [card_disjSum, card_erase_of_mem hw, hV, hW]
    omega
  have hface : V.map Embedding.inl ∈ simplexBoundary (V.disjSum (W.erase w)) := by
    rw [mem_simplexBoundary]
    refine ⟨hVne.map, ?_⟩
    rw [← disjSum_empty]
    exact disjSum_ssubset_disjSum_of_subset_of_ssubset Subset.rfl
      (empty_ssubset.mpr hWne)
  have hfresh : ({inr w} : Finset (α ⊕ β)) ∉
      simplexBoundary (V.disjSum (W.erase w)) := by
    intro h
    exact (notMem_erase w W) (by
      have hsub := (mem_simplexBoundary.mp h).2.subset
      simpa using hsub (mem_singleton_self (inr w)))
  have hstar := hmodel.stellarSubdivision hface hfresh
  rwa [stellarSubdivision_simplexBoundary_disjSum hVne (notMem_erase w W),
    insert_erase hw] at hstar

end PreAbstractSimplicialComplex
