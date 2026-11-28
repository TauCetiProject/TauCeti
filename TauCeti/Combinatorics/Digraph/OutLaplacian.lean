/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The out-degree Laplacian of a weighted digraph

A weighted digraph on a finite vertex type `V` is a weight function `w : V → V → R`: `w u v` is
the weight of the arcs from `u` to `v`, and `w v v` is the weight of the loops at `v`. Its
out-degree Laplacian is the diagonal matrix of out-weights `∑ u, w v u` minus the matrix of
weights. The loop weight `w v v` cancels on the diagonal, so the diagonal entry at `v` is
`∑_(u ≠ v) w v u`, and every row sums to `0`. This is the matrix of the directed matrix-tree
theorem: its principal minors count the spanning arborescences.

## Main definitions

* `TauCeti.outLaplacian`: the out-degree Laplacian `diagonal (fun v => ∑ u, w v u) - of w`.

## Main results

* `TauCeti.outLaplacian_apply_self`, `TauCeti.outLaplacian_apply_of_ne`: the entries.
* `TauCeti.sum_outLaplacian_apply`, `TauCeti.outLaplacian_mulVec_one`: every row sums to `0`.
* `TauCeti.det_outLaplacian`: over a commutative ring the determinant is `0` when `V` is
  nonempty.
* `TauCeti.outLaplacian_eq_outLaplacian_iff`: two weight functions have the same Laplacian
  exactly when they agree off the diagonal, so the loop weights do not matter.
* `TauCeti.outLaplacian_of_mem_rowStochastic`: for a stochastic matrix `P` the Laplacian is
  `1 - P`; `TauCeti.outLaplacian_of_sum_eq_zero`: for a matrix whose rows sum to `0` it is the
  negative of the matrix.
* `TauCeti.outLaplacian_mulVec_apply`, `TauCeti.vecMul_outLaplacian_apply`: the action on
  column and row vectors.
* `TauCeti.outLaplacian_adjMatrix`: for the adjacency matrix of a simple graph it is the
  Laplacian `SimpleGraph.lapMatrix`.

## References

* R. P. Stanley, *Algebraic Combinatorics*, 2nd ed., Theorem 10.4.
-/

public section

open Finset Matrix

namespace TauCeti

variable {V : Type*} [Fintype V] [DecidableEq V]

section AddCommGroup

variable {R : Type*} [AddCommGroup R]

/-- The out-degree Laplacian of a weight function `w : V → V → R`: the diagonal matrix of the
out-weights `∑ u, w v u` minus the matrix of the weights. A loop weight `w v v` cancels on the
diagonal. -/
def outLaplacian (w : V → V → R) : Matrix V V R :=
  diagonal (fun v => ∑ u, w v u) - of w

/-- The definition of the out-degree Laplacian. -/
theorem outLaplacian_def (w : V → V → R) :
    outLaplacian w = diagonal (fun v => ∑ u, w v u) - of w :=
  (rfl)

/-- An entry of the out-degree Laplacian: the out-weight of `u` on the diagonal, minus the
weight `w u v`. -/
theorem outLaplacian_apply (w : V → V → R) (u v : V) :
    outLaplacian w u v = (if u = v then ∑ x, w u x else 0) - w u v := by
  simp [outLaplacian, diagonal_apply]

/-- The diagonal entry of the out-degree Laplacian at `v` is the total weight of the arcs from
`v` to the other vertices. -/
@[simp]
theorem outLaplacian_apply_self (w : V → V → R) (v : V) :
    outLaplacian w v v = ∑ u ∈ univ.erase v, w v u := by
  simp [outLaplacian_apply, sum_erase_eq_sub (mem_univ v)]

/-- An entry of the out-degree Laplacian off the diagonal is the negative of the weight. -/
@[simp]
theorem outLaplacian_apply_of_ne (w : V → V → R) {u v : V} (h : u ≠ v) :
    outLaplacian w u v = -w u v := by
  simp [outLaplacian_apply, h]

/-- Every row of the out-degree Laplacian sums to `0`. -/
@[simp]
theorem sum_outLaplacian_apply (w : V → V → R) (v : V) : ∑ u, outLaplacian w v u = 0 := by
  simp [outLaplacian_apply, sum_sub_distrib]

/-- Two weight functions have the same out-degree Laplacian exactly when they agree off the
diagonal. In particular the loop weights `w v v` do not change the Laplacian. -/
theorem outLaplacian_eq_outLaplacian_iff {w w' : V → V → R} :
    outLaplacian w = outLaplacian w' ↔ ∀ u v, u ≠ v → w u v = w' u v := by
  refine ⟨fun h u v huv => ?_, fun h => ?_⟩
  · simpa [huv] using congr($h u v)
  · ext u v
    obtain rfl | huv := eq_or_ne u v
    · simp only [outLaplacian_apply_self]
      exact sum_congr rfl fun x hx => h u x (ne_of_mem_erase hx).symm
    · simp [huv, h u v huv]

/-- For a weight function whose rows sum to `0`, such as the generator of a continuous-time
Markov chain, the out-degree Laplacian is the negative of the matrix of weights. -/
theorem outLaplacian_of_sum_eq_zero {w : V → V → R} (h : ∀ v, ∑ u, w v u = 0) :
    outLaplacian w = -of w := by
  simp [outLaplacian_def, h]

/-- The out-degree Laplacian of the zero weight function is `0`. -/
@[simp]
theorem outLaplacian_zero : outLaplacian (0 : V → V → R) = 0 := by
  ext u v
  simp [outLaplacian_apply]

/-- The out-degree Laplacian is additive in the weights. -/
theorem outLaplacian_add (w w' : V → V → R) :
    outLaplacian (w + w') = outLaplacian w + outLaplacian w' := by
  ext u v
  simp only [Matrix.add_apply, outLaplacian_apply, Pi.add_apply, sum_add_distrib]
  split_ifs <;> abel

/-- The out-degree Laplacian of the negated weights is the negated Laplacian. -/
theorem outLaplacian_neg (w : V → V → R) : outLaplacian (-w) = -outLaplacian w := by
  ext u v
  simp only [Matrix.neg_apply, outLaplacian_apply, Pi.neg_apply, sum_neg_distrib]
  split_ifs <;> abel

/-- The out-degree Laplacian of a difference of weights is the difference of the Laplacians. -/
theorem outLaplacian_sub (w w' : V → V → R) :
    outLaplacian (w - w') = outLaplacian w - outLaplacian w' := by
  rw [sub_eq_add_neg, outLaplacian_add, outLaplacian_neg, sub_eq_add_neg]

/-- The out-degree Laplacian commutes with scalar multiplication of the weights. -/
theorem outLaplacian_smul {S : Type*} [DistribSMul S R] (c : S)
    (w : V → V → R) : outLaplacian (c • w) = c • outLaplacian w := by
  ext u v
  simp only [Matrix.smul_apply, outLaplacian_apply, Pi.smul_apply, ← smul_sum, smul_sub]
  split_ifs <;> simp

/-- The out-degree Laplacian commutes with an additive homomorphism applied to the weights. -/
theorem map_outLaplacian {S : Type*} [AddCommGroup S] (f : R →+ S) (w : V → V → R) :
    (outLaplacian w).map f = outLaplacian (fun u v => f (w u v)) := by
  ext u v
  simp only [map_apply, outLaplacian_apply, map_sub]
  split_ifs <;> simp

end AddCommGroup

section Ring

/-- The out-degree Laplacian applied to a vector `x` at `v` is the weighted sum of the
differences `x v - x u`. -/
theorem outLaplacian_mulVec_apply {R : Type*} [NonUnitalNonAssocRing R] (w : V → V → R)
    (x : V → R) (v : V) : (outLaplacian w *ᵥ x) v = ∑ u, w v u * (x v - x u) := by
  simp [mulVec, dotProduct, outLaplacian_apply, sub_mul, ite_mul, mul_sub, sum_mul]

/-- A row vector `x` times the out-degree Laplacian at `v` is the outflow `∑ u, x v * w v u`
minus the inflow `∑ u, x u * w u v`. -/
theorem vecMul_outLaplacian_apply {R : Type*} [NonUnitalNonAssocRing R] (w : V → V → R)
    (x : V → R) (v : V) : (x ᵥ* outLaplacian w) v = ∑ u, (x v * w v u - x u * w u v) := by
  simp [vecMul, dotProduct, outLaplacian_apply, mul_sub, mul_ite, mul_sum, sum_sub_distrib]

/-- The out-degree Laplacian sends the all-ones vector to `0`. -/
@[simp]
theorem outLaplacian_mulVec_one {R : Type*} [NonAssocRing R] (w : V → V → R) :
    outLaplacian w *ᵥ 1 = 0 := by
  ext v
  simp [outLaplacian_mulVec_apply]

/-- Over a commutative ring, the out-degree Laplacian on a nonempty vertex type has
determinant `0`. -/
@[simp]
theorem det_outLaplacian {R : Type*} [CommRing R] [Nonempty V] (w : V → V → R) :
    (outLaplacian w).det = 0 :=
  det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (outLaplacian_mulVec_one w)
    (i := Classical.arbitrary V) (one_mem _)

/-- For a weight function whose rows sum to `1` the out-degree Laplacian is `1 - of w`. -/
theorem outLaplacian_of_sum_eq_one {R : Type*} [AddCommGroupWithOne R] {w : V → V → R}
    (h : ∀ v, ∑ u, w v u = 1) : outLaplacian w = 1 - of w := by
  simp [outLaplacian_def, h, diagonal_one]

/-- For a row-stochastic matrix `P` the out-degree Laplacian is `1 - P`. -/
theorem outLaplacian_of_mem_rowStochastic {R : Type*} [Ring R] [PartialOrder R]
    [IsOrderedRing R] {P : Matrix V V R} (hP : P ∈ rowStochastic R V) :
    outLaplacian P = 1 - P :=
  outLaplacian_of_sum_eq_one (sum_row_of_mem_rowStochastic hP)

/-- The out-degree Laplacian of the adjacency matrix of a simple graph is its Laplacian. -/
@[simp]
theorem outLaplacian_adjMatrix {R : Type*} [AddCommGroupWithOne R] (G : SimpleGraph V)
    [DecidableRel G.Adj] : outLaplacian (G.adjMatrix R) = G.lapMatrix R := by
  ext u v
  rw [outLaplacian_apply (G.adjMatrix R), SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    Matrix.sub_apply, diagonal_apply, G.degree_eq_sum_if_adj]
  simp [SimpleGraph.adjMatrix_apply]

end Ring

end TauCeti

example {R : Type*} [AddCommGroup R] (a b c d : R) :
    TauCeti.outLaplacian ![![a, b], ![c, d]] = !![b, -b; -c, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]
