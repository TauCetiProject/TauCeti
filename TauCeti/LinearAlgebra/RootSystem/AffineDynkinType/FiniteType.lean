/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimpleGraph
import TauCeti.Combinatorics.SimpleGraph.CoefficientGame

/-!
# Affine simply-laced diagrams are not of finite type

The generalized Cartan matrix `C` of a valid affine simply-laced diagram has the marks `δ`, which
are positive at every node, as a null vector: `Cδ = 0`. A matrix of finite type admits no nonzero
vector `x` with `xᵢ (Cx)ᵢ ≤ 0` at every node
(`TauCeti.IsFiniteType.eq_zero_of_forall_mul_sum_apply_mul_nonpos`), so `C` is not of finite
type. This holds uniformly over the family, `Ã₁` included.

Away from `Ã₁` the matrix `C` is `2I - A` for the underlying simple graph, and a connected graph
whose `2I - A` is positive definite is a simply-laced Dynkin diagram and conversely
(`SimpleGraph.posDef_graphCartanMatrix_iff`). Hence the graph of a valid affine diagram other than
`Ã₁` is not isomorphic to the diagram of any valid finite Dynkin type. This is the hypothesis under
which the non-Dynkin theorems about preprojective and zigzag algebras are stated, so those
theorems apply to every affine diagram `Ãₙ` (`n ≥ 2`) and to affine `Dₙ`, `E₆`, `E₇` and `E₈`. The
exclusion of `Ã₁` is necessary: its graph is a single edge, the diagram of `A₂`; only its Cartan
matrix `!![2, -2; -2, 2]` records the double edge.

More strongly, a graph whose `2I - A` is positive definite contains no copy of the graph of such
a diagram, induced or not. Extending the marks by zero along a copy gives a nonzero nonnegative
vector with no positive coordinate under `2I - A`: an extra edge only lowers the coordinates, since
the marks are positive (`SimpleGraph.not_isContained_of_posDef_of_two_mul_le_sum`).

## Main results

* `TauCeti.AffineDynkinType.not_isFiniteType_cartanMatrix`: the generalized Cartan matrix of a
  valid affine diagram is not of finite type.
* `TauCeti.AffineDynkinType.not_exists_dynkinType_iso`: the graph of a valid affine diagram other
  than `Ã₁` is not a finite Dynkin diagram.
* `TauCeti.AffineDynkinType.not_isContained_of_posDef`: a graph with positive definite `2I - A`,
  such as a finite simply-laced Dynkin diagram, contains no copy of such a graph.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., Chapter 4, Theorem 4.3 and §4.8.
-/

public section

namespace TauCeti

namespace AffineDynkinType

variable {t : AffineDynkinType}

/-- **An affine Cartan matrix is not of finite type.** The generalized Cartan matrix of a valid
affine simply-laced diagram, `Ã₁` included, has the positive marks as a null vector, which a
matrix of finite type does not allow. -/
theorem not_isFiniteType_cartanMatrix (ht : t.Valid) : ¬ IsFiniteType t.cartanMatrix := by
  intro h
  have hnull (i : Fin t.nodes) : ∑ j, (t.cartanMatrix i j : ℚ) * (t.marks j : ℚ) = 0 := by
    exact_mod_cast congrFun (cartanMatrix_mulVec_marks_eq_zero ht) i
  have h0 := h.eq_zero_of_forall_mul_sum_apply_mul_nonpos (x := fun i ↦ (t.marks i : ℚ))
    fun i ↦ by rw [hnull, mul_zero]
  have hpos : (0 : ℚ) < t.marks 0 := by exact_mod_cast marks_pos 0
  exact hpos.ne' (congrFun h0 0)

open SimpleGraph in
/-- **A graph with positive definite `2I - A` contains no graph of a valid affine diagram other
than `Ã₁`.** If `2I - A` is positive definite over a linearly ordered ring, then `G` contains no
copy, induced or not, of the graph of a valid affine simply-laced diagram other than `Ã₁`. In
particular no finite simply-laced Dynkin diagram contains one
(`SimpleGraph.posDef_graphCartanMatrix_of_iso`). -/
theorem not_isContained_of_posDef {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [StarRing R] [TrivialStar R] {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (ht : t.Valid) (hg : t.IsGraphical)
    (hC : (G.graphCartanMatrix R).PosDef) : ¬ t.graph ⊑ G :=
  G.not_isContained_of_posDef_of_two_mul_le_sum hC (m := fun u ↦ (t.marks u : R))
    (fun u ↦ (Int.cast_pos.mpr (marks_pos u)).le)
    (fun h ↦ (Int.cast_pos.mpr (marks_pos 0)).ne' (congrFun h 0))
    fun u ↦ by exact_mod_cast (sum_marks_neighborFinset_eq_two_mul ht hg u).ge

/-- **The graph of an affine diagram is not a finite Dynkin diagram.** For a valid affine
simply-laced diagram other than `Ã₁`, the underlying graph is not isomorphic to the diagram of any
valid Dynkin type. -/
theorem not_exists_dynkinType_iso (ht : t.Valid) (hg : t.IsGraphical) :
    ¬ ∃ s : DynkinType, s.Valid ∧ Nonempty (t.graph ≃g diagramGraph s.cartanMatrix) :=
  fun ⟨_, _, ⟨φ⟩⟩ ↦ not_isContained_of_posDef ht hg
    (SimpleGraph.posDef_graphCartanMatrix_of_iso φ) (.refl _)

end AffineDynkinType

end TauCeti
