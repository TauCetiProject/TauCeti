/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Artin
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The simply laced Artin presentation of a graph

A simple graph determines the Coxeter matrix with diagonal entries `1`,
adjacent entries `3` and distinct nonadjacent entries `2`. A family of group
elements satisfying the graph's commuting and three-generator braid relations
extends to its Artin group by the existing Artin-Tits universal property.

This is the presentation bridge for the arbitrary finite-graph zigzag action.
-/

public section
noncomputable section

namespace SimpleGraph

universe u
variable {V : Type u} (G : SimpleGraph V)

/-- The simply laced Coxeter matrix associated to a graph. -/
def coxeterMatrix : CoxeterMatrix V := by
  classical
  exact
    { M := fun i j ↦ if i = j then 1 else if G.Adj i j then 3 else 2
      isSymm := by
        unfold Matrix.IsSymm
        ext i j
        -- Transposition swaps the two vertex indices.
        change (if j = i then (1 : ℕ) else if G.Adj j i then 3 else 2) =
          (if i = j then 1 else if G.Adj i j then 3 else 2)
        by_cases hij : i = j
        · subst j
          simp
        · by_cases h : G.Adj i j
          · simp [hij, Ne.symm hij, h, h.symm]
          · simp [hij, Ne.symm hij, h, show ¬ G.Adj j i from fun h' ↦ h h'.symm]
      diagonal := by simp
      off_diagonal := by
        intro i j hij
        simp only [ite_eq_right hij]
        split_ifs <;> decide }

/-- Adjacent vertices give the three-letter Artin braid relation. -/
@[simp]
theorem coxeterMatrix_apply_of_adj {i j : V} (h : G.Adj i j) :
    G.coxeterMatrix i j = 3 := by
  classical
  simp [coxeterMatrix, h.ne, h]

/-- Distinct nonadjacent vertices give the commuting Artin relation. -/
@[simp]
theorem coxeterMatrix_apply_of_not_adj {i j : V} (hij : i ≠ j) (h : ¬ G.Adj i j) :
    G.coxeterMatrix i j = 2 := by
  classical
  simp [coxeterMatrix, hij, h]

end SimpleGraph

namespace TauCeti

universe u v
variable {V : Type u} (G : SimpleGraph V) {H : Type v} [Group H]

/-- A graph-braid family of group elements extends to the graph's Artin group. -/
def ArtinGroup.liftGraph (f : V → H)
    (commute : ∀ {i j}, i ≠ j → ¬ G.Adj i j → f i * f j = f j * f i)
    (braid : ∀ {i j}, G.Adj i j → f i * f j * f i = f j * f i * f j) :
    ArtinGroup G.coxeterMatrix →* H :=
  ArtinGroup.lift G.coxeterMatrix f (by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · by_cases h : G.Adj i j
      · simpa only [CoxeterSystem.braidWord, G.coxeterMatrix_apply_of_adj h,
          G.coxeterMatrix_apply_of_adj h.symm, prod_map_alternatingWord_three] using
          (braid h).symm
      · have hji : ¬ G.Adj j i := fun h' ↦ h h'.symm
        simpa only [CoxeterSystem.braidWord, G.coxeterMatrix_apply_of_not_adj hij h,
          G.coxeterMatrix_apply_of_not_adj (Ne.symm hij) hji, prod_map_alternatingWord_two] using
          commute hij h)

/-- The graph-presentation extension sends each standard generator to its supplied element. -/
@[simp]
theorem ArtinGroup.liftGraph_gen (f : V → H) (commute braid) (i : V) :
    ArtinGroup.liftGraph G f commute braid (ArtinGroup.gen G.coxeterMatrix i) = f i := by
  simp only [ArtinGroup.liftGraph, ArtinGroup.lift_gen]

end TauCeti
