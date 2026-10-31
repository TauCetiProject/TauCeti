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
elements satisfying the graph's commuting and length-three braid relations
extends to its Artin group by the existing Artin-Tits universal property.

The rank-two entries specify the two types of alternating-word relators.

Conversely, a Coxeter matrix `M` determines its *Coxeter graph* `CoxeterMatrix.graph`, joining two
distinct indices exactly when their entry is not `2`, that is, when the corresponding simple
reflections do not commute. Entries `0`, which encode infinite order, are edges too. This forgets
the edge labels, and on simply laced matrices it inverts the first construction
(`SimpleGraph.graph_coxeterMatrix`). Simple reflections whose indices are not adjacent in the
Coxeter graph commute (`CoxeterSystem.commute_simple_of_not_adj`).
-/

public section
noncomputable section

namespace SimpleGraph

open TauCeti

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
        dsimp only [Matrix.transpose]
        by_cases hij : i = j
        · subst j
          simp
        · by_cases h : G.Adj i j
          · simp [hij, Ne.symm hij, h, h.symm]
          · have hji : ¬ G.Adj j i := fun h' ↦ h h'.symm
            simp [hij, Ne.symm hij, h, hji]
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

universe v
variable {H : Type v} [Group H]

/-- A graph-braid family of group elements extends to the graph's Artin group. -/
def artinGroupLift (f : V → H)
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
theorem artinGroupLift_gen (f : V → H) (commute braid) (i : V) :
    artinGroupLift G f commute braid (ArtinGroup.gen G.coxeterMatrix i) = f i := by
  simp only [artinGroupLift, ArtinGroup.lift_gen]

end SimpleGraph

namespace CoxeterMatrix

variable {B : Type*} (M : CoxeterMatrix B)

/-- The **Coxeter graph** of a Coxeter matrix: two distinct indices are adjacent exactly when their
entry is not `2`, so that nonadjacent simple reflections commute. The edge labels `M i j` are
forgotten. -/
def graph : SimpleGraph B where
  Adj i j := i ≠ j ∧ M i j ≠ 2
  symm := ⟨fun i j h ↦ ⟨h.1.symm, M.symmetric i j ▸ h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

@[simp]
theorem graph_adj {i j : B} : M.graph.Adj i j ↔ i ≠ j ∧ M i j ≠ 2 := Iff.rfl

end CoxeterMatrix

/-- The Coxeter graph of the simply laced Coxeter matrix of a graph is the graph itself. -/
@[simp]
theorem SimpleGraph.graph_coxeterMatrix {V : Type*} (G : SimpleGraph V) :
    G.coxeterMatrix.graph = G := by
  ext i j
  rw [CoxeterMatrix.graph_adj]
  by_cases hij : i = j
  · simp [hij]
  · by_cases h : G.Adj i j <;> simp [hij, h]

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Two simple reflections commute when their indices are not adjacent in the Coxeter graph. -/
theorem commute_simple_of_not_adj {i i' : B} (h : ¬M.graph.Adj i i') :
    Commute (cs.simple i) (cs.simple i') := by
  rcases eq_or_ne i i' with rfl | hii'
  · exact Commute.refl _
  · exact cs.commute_simple_of_eq_two (not_not.mp fun h' ↦ h (M.graph_adj.mpr ⟨hii', h'⟩))

end CoxeterSystem
