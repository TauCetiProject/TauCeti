/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import TauCeti.Combinatorics.SimpleGraph.Dart.Basic

/-!
# Quadratic forms of the adjacency, degree and Laplacian matrices

For a finite simple graph `G` and a vector `u : V → R`, the quadratic forms of the adjacency
matrix `A`, the degree matrix `D` and the Laplacian `L = D - A` are sums over the edges of `G`:

* `uᵀ A u = 2 ∑_{xy ∈ E} u_x u_y` over a commutative semiring,
* `uᵀ D u = ∑_{xy ∈ E} (u_x² + u_y²)` over a semiring,
* `uᵀ L u = ∑_{xy ∈ E} (u_x - u_y)²` over a ring.

Each edge is counted once. Mathlib's `SimpleGraph.lapMatrix_toLinearMap₂'` gives the Laplacian
form over a field of characteristic zero as half of a double sum over the ordered adjacent pairs;
the form here holds over every ring.

## Main results

* `SimpleGraph.dotProduct_mulVec_adjMatrix_self`: the quadratic form of `A`.
* `SimpleGraph.dotProduct_mulVec_degMatrix_self`: the quadratic form of `D`.
* `SimpleGraph.dotProduct_mulVec_lapMatrix_self`: the quadratic form of `L`.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Springer Universitext (2012), §1.1.
-/

public section

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The quadratic form of the adjacency matrix: `uᵀ A u = 2 ∑_{xy ∈ E} u_x u_y`. -/
theorem dotProduct_mulVec_adjMatrix_self {R : Type*} [CommSemiring R] (u : V → R) :
    u ⬝ᵥ (G.adjMatrix R *ᵥ u) =
      2 * ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun x y ↦ u x * u y, fun _ _ ↦ mul_comm _ _⟩ e := by
  rw [dotProduct_mulVec_adjMatrix, sum_sum_ite_adj_eq_sum_edgeFinset, mul_sum]
  refine sum_congr rfl fun e _ ↦ ?_
  induction e using Sym2.ind with | _ x y => simp [mul_comm (u y), two_mul]

variable [DecidableEq V]

/-- The quadratic form of the degree matrix: `uᵀ D u = ∑_{xy ∈ E} (u_x² + u_y²)`. -/
theorem dotProduct_mulVec_degMatrix_self {R : Type*} [Semiring R] (u : V → R) :
    u ⬝ᵥ (G.degMatrix R *ᵥ u) =
      ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun x y ↦ u x ^ 2 + u y ^ 2, fun _ _ ↦ add_comm _ _⟩ e := by
  rw [← sum_sum_ite_adj_eq_sum_edgeFinset]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [degMatrix_mulVec_apply, G.degree_eq_sum_if_adj (R := R), sum_mul, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp [sq]

/-- The quadratic form of the Laplacian: `uᵀ L u = ∑_{xy ∈ E} (u_x - u_y)²`. -/
theorem dotProduct_mulVec_lapMatrix_self {R : Type*} [Ring R] (u : V → R) :
    u ⬝ᵥ (G.lapMatrix R *ᵥ u) =
      ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun x y ↦ (u x - u y) ^ 2,
        fun _ _ ↦ by dsimp only; rw [← neg_sub, neg_sq]⟩ e := by
  rw [lapMatrix, sub_mulVec, dotProduct_sub, dotProduct_mulVec_degMatrix_self,
    dotProduct_mulVec_adjMatrix, sum_sum_ite_adj_eq_sum_edgeFinset, ← sum_sub_distrib]
  refine sum_congr rfl fun e _ ↦ ?_
  induction e using Sym2.ind with | _ x y => simp only [Sym2.lift_mk]; noncomm_ring

end SimpleGraph
