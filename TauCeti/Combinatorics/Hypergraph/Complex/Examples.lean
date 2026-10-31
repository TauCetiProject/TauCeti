/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Complex.Counting
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic

/-!
# Finite-complex bridge examples

The filled triangle has three vertices, three pairs and one triple. Its triple is in level
three, although its simplicial dimension is two. The examples also check the empty face,
a rank-zero complex on an empty host, and conversion on an infinite ambient vertex type.
All computations use the public membership and round-trip lemmas. The labeled-copy examples
count all six injections into the filled triangle, distinguish it from its boundary, and
check the empty pattern.
-/

public section

namespace TauCeti.HypergraphComplex

open Finset _root_.PreAbstractSimplicialComplex

/-- The filled triangle, obtained by adjoining the empty face to the abstract two-simplex. -/
noncomputable def filledTriangle : HypergraphComplex 3 (Fin 3) :=
  .ofPreAbstractSimplicialComplex (simplex univ) (finite_faces_simplex univ)

/-- The faces of the filled triangle are the subsets of its three vertices at each level. -/
@[simp]
theorem faces_filledTriangle (k : ℕ) (hk : k ≤ 3) :
    filledTriangle.faces k hk = (univ : Finset (Fin 3)).powersetCard k := by
  ext s
  simp only [filledTriangle, mem_faces_ofPreAbstractSimplicialComplex,
    mem_simplex, subset_univ, and_true, mem_powersetCard, true_and]
  exact and_iff_right_of_imp (fun _ => s.eq_empty_or_nonempty)

example : filledTriangle.faces 0 (by decide) = {∅} := filledTriangle.faces_zero

example : #(filledTriangle.faces 1 (by decide)) = 3 := by
  rw [faces_filledTriangle]
  decide

example : #(filledTriangle.faces 2 (by decide)) = 3 := by
  rw [faces_filledTriangle]
  decide

example : #(filledTriangle.faces 3 (by decide)) = 1 := by
  rw [faces_filledTriangle]
  decide

example : (univ : Finset (Fin 3)) ∈ filledTriangle.faces 3 (by decide) := by
  rw [faces_filledTriangle]
  simp

example : filledTriangle.toPreAbstractSimplicialComplex = simplex (univ : Finset (Fin 3)) := by
  exact toPreAbstractSimplicialComplex_ofPreAbstractSimplicialComplex _ _
    (fun s hs => by simpa using card_le_card (mem_simplex.mp hs).2)

-- The simplex on no vertices has only the empty face after conversion.
example : (ofPreAbstractSimplicialComplex (r := 0)
    (simplex (∅ : Finset (Fin 0))) (Set.toFinite _)).faces 0 (by decide) = {∅} := by
  ext s
  have hs : s = ∅ := eq_empty_of_isEmpty s
  subst s
  simp

-- No finite ambient type is required when the original face set is finite.
example : (ofPreAbstractSimplicialComplex (simplex ({4, 9, 16} : Finset ℕ))
    (finite_faces_simplex _) :
      HypergraphComplex 3 ℕ).toPreAbstractSimplicialComplex = simplex {4, 9, 16} := by
  exact toPreAbstractSimplicialComplex_ofPreAbstractSimplicialComplex _ _
    (fun s hs => by simpa using card_le_card (mem_simplex.mp hs).2)

/-! ### Labeled copies -/

/-- The boundary of the triangle has all three edges but no triple face. Its rank bound is two. -/
noncomputable def triangleBoundary : HypergraphComplex 2 (Fin 3) :=
  .ofPreAbstractSimplicialComplex (simplexBoundary univ) (finite_faces_simplexBoundary univ)

/-- Every set of at most two of the three vertices is a face of the boundary. -/
@[simp]
theorem faces_triangleBoundary (k : ℕ) (hk : k ≤ 2) :
    triangleBoundary.faces k hk = (univ : Finset (Fin 3)).powersetCard k := by
  ext a
  simp only [triangleBoundary, mem_faces_ofPreAbstractSimplicialComplex, mem_powersetCard,
    subset_univ, true_and]
  refine ⟨And.right, fun hcard ↦ ⟨?_, hcard⟩⟩
  obtain rfl | hne := a.eq_empty_or_nonempty
  · exact Or.inl rfl
  · refine Or.inr (mem_simplexBoundary.2 ⟨hne, ?_⟩)
    exact Finset.ssubset_iff_subset_ne.2 ⟨subset_univ _, fun he ↦ by
      have := congrArg Finset.card he
      simp only [card_univ, Fintype.card_fin, hcard] at this
      omega⟩

/-- Every complex on three labeled vertices has six copies in the filled triangle.
The source faces may be missing: copies preserve faces but need not preserve nonfaces. -/
theorem labelledCopyCount_filledTriangle {r : ℕ} (C : HypergraphComplex r (Fin 3)) :
    filledTriangle.labelledCopyCount C = 6 := by
  have hall : filledTriangle.copies C = univ := by
    apply eq_univ_of_forall
    intro f
    rw [mem_copies, isCopy_iff]
    intro k hk a ha
    have hcard : #(a.map f) = k := (card_map _).trans (C.face_card k hk a ha)
    have hk' : k ≤ 3 := by
      have := card_le_univ (a.map f)
      simpa only [hcard, Fintype.card_fin] using this
    refine ⟨hk', ?_⟩
    rw [faces_filledTriangle]
    exact mem_powersetCard.2 ⟨subset_univ _, hcard⟩
  rw [labelledCopyCount_def, hall, card_univ, Fintype.card_embedding_eq]
  decide

example : filledTriangle.labelledCopyCount filledTriangle = 6 :=
  labelledCopyCount_filledTriangle _

-- A boundary copy is allowed to acquire a triple face in the host.
example : filledTriangle.labelledCopyCount triangleBoundary = 6 :=
  labelledCopyCount_filledTriangle _

-- The reverse direction fails because the triple face must be preserved.
example : triangleBoundary.labelledCopyCount filledTriangle = 0 := by
  apply labelledCopyCount_eq_zero_of_rank_lt _ _ (by decide : 3 ≤ 3)
    (a := univ) _ (by decide)
  rw [faces_filledTriangle]
  simp

-- The unique empty vertex injection preserves the empty face, giving one copy.
example : filledTriangle.labelledCopyCount
    (ofPreAbstractSimplicialComplex (r := 0) (simplex (∅ : Finset (Fin 0)))
      (finite_faces_simplex _)) = 1 := by
  classical
  let C : HypergraphComplex 0 (Fin 0) :=
    ofPreAbstractSimplicialComplex (simplex ∅) (finite_faces_simplex _)
  have hall : filledTriangle.copies C = univ := by
    apply eq_univ_of_forall
    intro f
    rw [mem_copies, isCopy_iff]
    intro k hk a ha
    have hk0 : k = 0 := by omega
    subst k
    have ha0 : a = ∅ := card_eq_zero.1 (C.face_card 0 hk a ha)
    subst a
    exact ⟨by decide, by simp⟩
  rw [labelledCopyCount_def, hall, card_univ, Fintype.card_embedding_eq]
  decide

end TauCeti.HypergraphComplex
