/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.AdditiveFunction
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification

/-!
# Simple graphs of finite type

A finite simple graph `G` with adjacency matrix `A` is read as a simply-laced diagram through its
generalized Cartan matrix `2I - A` (`SimpleGraph.graphCartanMatrix`). This file connects that
matrix with the finite-type Cartan matrices of `TauCeti.IsFiniteType` and their classification:
the diagram of `2I - A` is `G` itself, a positive definite `2I - A` over any linear ordered field is
of finite type, and a connected graph whose `2I - A` is of finite type is isomorphic to the diagram
of the standard Cartan matrix of a valid Dynkin type. In other words, a connected simple graph
whose form `2I - A` is positive definite is a Dynkin diagram, and a connected graph which is not a
Dynkin diagram has a form `2I - A` which is not positive definite.

## Main results

* `SimpleGraph.diagramGraph_graphCartanMatrix`: the diagram of `2I - A` is `G`.
* `SimpleGraph.isFiniteType_graphCartanMatrix_of_posDef`: if `2I - A` is positive definite over a
  linear ordered field, then it is of finite type.
* `SimpleGraph.exists_dynkinType_iso_of_isFiniteType_graphCartanMatrix`: a connected graph whose
  `2I - A` is of finite type is isomorphic to the diagram of a valid Dynkin type.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.
* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4.
-/

public section

namespace SimpleGraph

open Matrix TauCeti

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The diagram of the generalized Cartan matrix `2I - A` of a simple graph is the graph itself. -/
@[simp]
theorem diagramGraph_graphCartanMatrix : diagramGraph (G.graphCartanMatrix ℤ) = G := by
  ext i j
  rw [diagramGraph_adj, graphCartanMatrix_apply, graphCartanMatrix_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp only [hij, hij.symm, ne_eq, not_false_eq_true, ↓reduceIte, true_and, G.adj_comm j i]
    split_ifs <;> simp_all

variable {G} [Fintype V]

/-- **A positive definite graph Cartan matrix is of finite type.** If `2I - A` is positive
definite over some linear ordered field, then the integer matrix `2I - A` is of finite type. -/
theorem isFiniteType_graphCartanMatrix_of_posDef {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [StarRing R] [TrivialStar R] (h : (G.graphCartanMatrix R).PosDef) :
    IsFiniteType (G.graphCartanMatrix ℤ) := by
  refine isFiniteType_of_posDef_map_intCast (fun i ↦ by simp) (fun i j hij ↦ ?_) ?_
  · simp only [graphCartanMatrix_apply, hij, ↓reduceIte]
    split_ifs <;> simp
  have hmap : (G.graphCartanMatrix ℤ).map (Int.cast : ℤ → ℚ) = G.graphCartanMatrix ℚ :=
    graphCartanMatrix_map G (Int.castRingHom ℚ)
  rw [hmap, posDef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_iff_isSymm.mpr (isSymm_graphCartanMatrix G), fun x hx ↦ ?_⟩
  -- Read the rational vector `x` in `R`, where the form is positive.
  have hx' : Rat.castHom R ∘ x ≠ 0 := fun h0 ↦
    hx (funext fun i ↦ by simpa using congrFun h0 i)
  have hpos := h.dotProduct_mulVec_pos hx'
  rw [← graphCartanMatrix_map G (Rat.castHom R), star_trivial] at hpos
  have hcast : Rat.castHom R (x ⬝ᵥ G.graphCartanMatrix ℚ *ᵥ x) =
      Rat.castHom R ∘ x ⬝ᵥ (G.graphCartanMatrix ℚ).map (Rat.castHom R) *ᵥ (Rat.castHom R ∘ x) := by
    rw [RingHom.map_dotProduct]
    congr 1
    funext i
    exact RingHom.map_mulVec _ _ _ i
  rw [← hcast, Rat.coe_castHom, Rat.cast_pos] at hpos
  rwa [star_trivial]

/-- **A connected graph of finite type is a Dynkin diagram.** If the generalized Cartan matrix
`2I - A` of a connected simple graph `G` is of finite type, then `G` is isomorphic to the diagram
of the standard Cartan matrix of a valid Dynkin type. -/
theorem exists_dynkinType_iso_of_isFiniteType_graphCartanMatrix (hG : G.Connected)
    (h : IsFiniteType (G.graphCartanMatrix ℤ)) :
    ∃ t : DynkinType, t.Valid ∧ Nonempty (G ≃g diagramGraph t.cartanMatrix) := by
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    h.existsUnique_dynkinType ((diagramGraph_graphCartanMatrix G).symm ▸ hG)
  have hG' : G = (diagramGraph t.cartanMatrix).comap e := by
    rw [← diagramGraph_submatrix e.injective, ← diagramGraph_graphCartanMatrix G]
    exact congrArg diagramGraph (Matrix.ext he)
  refine ⟨t, ht, ⟨?_⟩⟩
  rw [hG']
  exact Iso.comap e _

end SimpleGraph
