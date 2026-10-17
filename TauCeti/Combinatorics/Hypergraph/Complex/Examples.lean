/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Complex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic

/-!
# Finite-complex bridge examples

The filled triangle has three vertices, three pairs and one triple. Its triple is in level
three, although its simplicial dimension is two. The examples also check the empty face,
a rank-zero complex on an empty host, and conversion on an infinite ambient vertex type.
All computations use the public membership and round-trip lemmas.
-/

public section

namespace TauCeti.HypergraphComplex

open Finset PreAbstractSimplicialComplex

/-- The filled triangle, obtained by adjoining the empty face to the abstract two-simplex. -/
noncomputable def filledTriangle : HypergraphComplex 3 (Fin 3) :=
  ofPreAbstractSimplicialComplex (simplex univ) (finite_faces_simplex univ)
    (fun s hs => by simpa using card_le_card (mem_simplex.mp hs).2)

/-- Every subset of the three vertices is a face of the filled triangle. -/
@[simp]
theorem faces_filledTriangle : filledTriangle.faces = (univ : Finset (Fin 3)).powerset := by
  ext s
  simp only [filledTriangle, mem_faces_ofPreAbstractSimplicialComplex, mem_simplex,
    subset_univ, and_true, mem_powerset]
  exact iff_true_intro s.eq_empty_or_nonempty

private theorem slice_filledTriangle (n : ℕ) :
    filledTriangle.faces.slice n = (univ : Finset (Fin 3)).powersetCard n := by
  ext s
  simp [Finset.mem_slice]

example : filledTriangle.faces.slice 0 = {∅} := filledTriangle.slice_zero

example : #(filledTriangle.faces.slice 1) = 3 := by
  rw [slice_filledTriangle]
  decide

example : #(filledTriangle.faces.slice 2) = 3 := by
  rw [slice_filledTriangle]
  decide

example : #(filledTriangle.faces.slice 3) = 1 := by
  rw [slice_filledTriangle]
  decide

example : (univ : Finset (Fin 3)) ∈ filledTriangle.faces.slice 3 := by
  rw [slice_filledTriangle]
  simp

example : filledTriangle.faces.slice 4 = ∅ :=
  filledTriangle.slice_eq_empty_of_lt (by decide)

example : filledTriangle.toPreAbstractSimplicialComplex = simplex (univ : Finset (Fin 3)) := by
  apply SetLike.ext
  intro s
  simp only [mem_toPreAbstractSimplicialComplex, faces_filledTriangle,
    mem_powerset, subset_univ, true_and, mem_simplex, and_true]

-- The simplex on no vertices has only the empty face after conversion.
example : (ofPreAbstractSimplicialComplex (r := 0)
    (simplex (∅ : Finset (Fin 0))) (Set.toFinite _)
    (fun s hs => by simpa using card_le_card (mem_simplex.mp hs).2)).faces = {∅} := by
  ext s
  have hs : s = ∅ := eq_empty_of_isEmpty s
  subst s
  simp

-- No finite ambient type is required when the original face set is finite.
example : (ofPreAbstractSimplicialComplex (simplex ({4, 9, 16} : Finset ℕ))
    (finite_faces_simplex _) (fun s hs => by simpa using card_le_card (mem_simplex.mp hs).2) :
      HypergraphComplex 3 ℕ).toPreAbstractSimplicialComplex = simplex {4, 9, 16} := by
  simp

end TauCeti.HypergraphComplex
