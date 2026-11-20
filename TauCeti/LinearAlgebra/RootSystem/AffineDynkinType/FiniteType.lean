/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.SimpleGraph

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
a diagram, induced or not. Extending the marks by zero along a copy gives a nonzero vector at
which the form of `2I - A` is nonpositive: an extra edge only lowers the form, since the marks are
positive.

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

/-- **The graph of an affine diagram is not a finite Dynkin diagram.** For a valid affine
simply-laced diagram other than `Ã₁`, the underlying graph is not isomorphic to the diagram of any
valid Dynkin type. -/
theorem not_exists_dynkinType_iso (ht : t.Valid) (hg : t.IsGraphical) :
    ¬ ∃ s : DynkinType, s.Valid ∧ Nonempty (t.graph ≃g diagramGraph s.cartanMatrix) := by
  intro h
  have hpd := (SimpleGraph.posDef_graphCartanMatrix_iff (graph_connected ht)).2
    ((SimpleGraph.exists_valid_isSimplyLaced_dynkinType_iso_iff t.graph).2 h)
  have hft := SimpleGraph.isFiniteType_graphCartanMatrix_of_posDef hpd
  rw [← cartanMatrix_eq_graphCartanMatrix hg] at hft
  exact not_isFiniteType_cartanMatrix ht hft

open SimpleGraph in
/-- **A graph with positive definite `2I - A` contains no affine graph.** If `2I - A` is positive
definite over a linearly ordered ring, then `G` contains no copy, induced or not, of the graph of
a valid affine simply-laced diagram other than `Ã₁`. In particular no finite simply-laced Dynkin
diagram contains one (`SimpleGraph.posDef_graphCartanMatrix_of_iso`). -/
theorem not_isContained_of_posDef {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [StarRing R] [TrivialStar R] {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (ht : t.Valid) (hg : t.IsGraphical)
    (hC : (G.graphCartanMatrix R).PosDef) : ¬ t.graph ⊑ G := by
  classical
  have := Fintype.ofFinite V
  rintro ⟨f⟩
  -- Extend the marks by zero along the copy.
  set m : Fin t.nodes → R := fun u ↦ (t.marks u : R)
  set x : V → R := Function.extend f m 0
  have hx (u : Fin t.nodes) : x (f u) = m u := f.injective.extend_apply m 0 u
  have hx0 (v : V) (hv : v ∉ Set.range f) : x v = 0 := Function.extend_apply' m (0 : V → R) v hv
  have hm (u : Fin t.nodes) : 0 < m u := Int.cast_pos.mpr (marks_pos u)
  have hx0le (v : V) : 0 ≤ x v := by
    by_cases hv : v ∈ Set.range f
    · obtain ⟨u, rfl⟩ := hv
      rw [hx]
      exact (hm u).le
    · exact (hx0 v hv).ge
  have hpos := hC.dotProduct_mulVec_pos (x := x) fun h ↦
    (hm 0).ne' (by rw [← hx, h, Pi.zero_apply])
  rw [star_trivial] at hpos
  refine hpos.not_ge ?_
  -- Only the vertices of the copy contribute to the form.
  rw [dotProduct, ← Fintype.sum_of_injective f f.injective
    (fun u ↦ m u * (G.graphCartanMatrix R).mulVec x (f u)) _
    (fun v hv ↦ by rw [hx0 v hv, zero_mul])
    fun u ↦ by rw [hx]]
  refine Finset.sum_nonpos fun u _ ↦ mul_nonpos_of_nonneg_of_nonpos (hm u).le ?_
  -- At a vertex of the copy, the neighbours in `G` include the images of the neighbours in the
  -- affine graph, whose marks already sum to twice the mark of the vertex.
  have hsum : ∑ w ∈ t.graph.neighborFinset u, x (f w) = 2 * m u := by
    simp only [hx, m]
    exact_mod_cast sum_marks_neighborFinset_eq_two_mul ht hg u
  rw [graphCartanMatrix_mulVec_apply, hx, sub_nonpos, ← hsum]
  exact f.sum_neighborFinset_comp_le hx0le u

end AffineDynkinType

end TauCeti
