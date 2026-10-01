/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.Signless
public import TauCeti.RepresentationTheory.Quiver.Zigzag.PathAlgebra

/-!
# The signless relator of a simple graph

For the doubled quiver `TauCeti.DoubledQuiver G` of a simple graph `G`, at any vertex `v` with
finite neighbourhood the signless preprojective relator `TauCeti.signlessPreprojectiveRelator` is
`∑_{j ∼ v} (v → j → v)`, the sum of the backtracks along the edges at `v`. This is the relation
which Huerfano and Khovanov find in the quadratic dual of the zigzag algebra of `G`.

For a graph on `Fin n`, the class of the doubled arrow from `i` to `j` in the signless algebra
is recorded as a function `TauCeti.signlessArrow` of two natural numbers, zero unless they are
adjacent vertices. Products of these classes are the classes of paths, and the relator at `v`
becomes `∑ w, signlessArrow w v * signlessArrow v w = 0`; indexing by natural numbers lets the
computations along the arms of a Dynkin diagram use ordinary arithmetic on vertex labels.

## Main definitions

* `TauCeti.signlessArrow`: the class of the doubled arrow between two vertices of a graph on
  `Fin n`, or zero.

## Main results

* `TauCeti.signlessPreprojectiveRelator_vertex`: at a vertex with finite neighbourhood, the
  relator is the sum of the backtracks `TauCeti.DoubledQuiver.backtrackElem` over the neighbours.
* `TauCeti.signlessPreprojectiveMk_ofArrow_eq_signlessArrow`: the class of every doubled arrow is
  a `TauCeti.signlessArrow`.
* `TauCeti.sum_signlessArrow_mul_signlessArrow`: the relation at a vertex, as a sum over all
  vertices.

## References

S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u w

variable (k : Type w) {V : Type u} [Semiring k] (G : SimpleGraph V)

/-- **The signless relator of a simple graph** at `v` is `∑_{j ∼ v} (v → j → v)`, the sum of the
backtracks along the edges at `v`. -/
theorem signlessPreprojectiveRelator_vertex (v : V) [Fintype (G.neighborSet v)] :
    signlessPreprojectiveRelator k (DoubledQuiver.vertex G v) =
      ∑ w : G.neighborSet v, DoubledQuiver.backtrackElem G k ((G.mem_neighborSet v w).1 w.2) := by
  rw [signlessPreprojectiveRelator_def,
    ← (DoubledQuiver.starEquivNeighborSet G v).symm.sum_comp]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [DoubledQuiver.starEquivNeighborSet_symm_apply, DoubledQuiver.backtrackElem_eq_ofPath,
    DoubledQuiver.backtrackPath_eq_comp, DoubledQuiver.arrowPath_eq_toPath,
    DoubledQuiver.arrowPath_eq_toPath]
  -- The reverse of the arrow along `w` is the arrow of the symmetric adjacency.
  rfl

/-! ### Arrow classes of a graph on `Fin n` -/

section FinArrow

open DoubledQuiver

variable (k : Type w) [CommRing k] {n : ℕ} (G : SimpleGraph (Fin n))
  [∀ i, Fintype (G.neighborSet i)]

open scoped Classical in
/-- The class of the doubled arrow from `i` to `j` in the signless algebra of a graph `G` on
`Fin n`, or zero if `i` and `j` are not adjacent vertices of `G`. The vertices are given as natural
numbers, so that arithmetic on vertex labels needs no bounds. -/
noncomputable def signlessArrow (i j : ℕ) : signlessPreprojectiveAlgebra k (DoubledQuiver G) :=
  if h : i < n ∧ j < n then
    if hij : G.Adj ⟨i, h.1⟩ ⟨j, h.2⟩ then signlessPreprojectiveMk k _ (ofArrow (arrow G hij))
    else 0
  else 0

variable {G}

/-- Between adjacent vertices, `signlessArrow` is the class of the doubled arrow. -/
theorem signlessArrow_of_adj {i j : Fin n} (h : G.Adj i j) :
    signlessArrow k G i j = signlessPreprojectiveMk k _ (ofArrow (arrow G h)) := by
  simp [signlessArrow, h]

/-- Between non-adjacent vertices, `signlessArrow` vanishes. -/
theorem signlessArrow_eq_zero {i j : ℕ} (h : ∀ (hi : i < n) (hj : j < n), ¬G.Adj ⟨i, hi⟩ ⟨j, hj⟩) :
    signlessArrow k G i j = 0 := by
  by_cases hn : i < n ∧ j < n
  · simp [signlessArrow, hn, h hn.1 hn.2]
  · simp [signlessArrow, hn]

/-- The class of an arbitrary doubled arrow of `G` is the `signlessArrow` between its endpoints. -/
theorem signlessPreprojectiveMk_ofArrow_eq_signlessArrow {i j : DoubledQuiver G} (e : i ⟶ j) :
    signlessPreprojectiveMk k _ (ofArrow e) =
      signlessArrow k G ((vertexEquiv G).symm i) ((vertexEquiv G).symm j) := by
  obtain ⟨i, rfl⟩ := exists_eq_vertex G i
  obtain ⟨j, rfl⟩ := exists_eq_vertex G j
  rw [vertexEquiv_symm_vertex, vertexEquiv_symm_vertex,
    signlessArrow_of_adj k ((nonempty_hom_iff G).1 ⟨e⟩)]
  exact congrArg (fun e => signlessPreprojectiveMk k _ (ofArrow e)) (Subsingleton.elim _ _)

variable (G) in
/-- **The signless relation at a vertex `v`**: the backtracks `v → w → v` sum to zero, the sum
running over all vertices `w`, of which only the neighbours of `v` contribute. -/
theorem sum_signlessArrow_mul_signlessArrow (v : Fin n) :
    ∑ w : Fin n, signlessArrow k G w v * signlessArrow k G v w = 0 := by
  classical
  have hrel := signlessPreprojectiveMk_signlessPreprojectiveRelator k (vertex G v)
  rw [signlessPreprojectiveRelator_congr k (vertex G v) _ inferInstance,
    signlessPreprojectiveRelator_vertex, map_sum] at hrel
  -- Only the neighbours of `v` contribute, and they contribute the backtracks of the relator.
  calc ∑ w : Fin n, signlessArrow k G w v * signlessArrow k G v w
      = ∑ w ∈ Finset.univ.filter (G.Adj v), signlessArrow k G w v * signlessArrow k G v w := by
        refine (Finset.sum_filter_of_ne fun w _ hw => ?_).symm
        by_contra h
        exact hw (by rw [signlessArrow_eq_zero k fun _ _ h' => h (G.adj_symm (by simpa using h')),
          zero_mul])
    _ = ∑ w : G.neighborSet v, signlessArrow k G w v * signlessArrow k G v w :=
        Finset.sum_subtype _ (fun w => by simp) _
    _ = 0 := by
        rw [← hrel]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← ofArrow_symm_mul_ofArrow _ k w.2, map_mul, ← signlessArrow_of_adj k w.2,
          ← signlessArrow_of_adj k (G.adj_symm w.2)]

end FinArrow

end TauCeti
