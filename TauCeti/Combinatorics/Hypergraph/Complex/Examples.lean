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

end TauCeti.HypergraphComplex
