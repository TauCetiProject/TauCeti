/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Real
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Quantum integers as eigenvectors on path graphs

On the path graph `SimpleGraph.pathGraph (k + 1)` (the Dynkin graph `A_(k+1)` with vertices
`0, …, k`), the quantum-integer three-term recurrence `[t] + [t + 2] = δ * [t + 1]` together with
`[0] = 0` says that the neighbour sum of `u ↦ qInt R δ (u + 1)` at a vertex `v` equals
`δ * qInt R δ (v + 1)` up to the boundary defect `[k + 2]` at the top vertex `v = k`.

Accordingly, `u ↦ qInt R δ (u + 1)` satisfies the adjacency eigenvector equation with eigenvalue `δ`
at every interior vertex `v < k` over any commutative ring, and globally on `pathGraph (k + 1)`
whenever `[k + 2] = 0` — in particular at `δ = 2 * cos (π / (k + 2))` over `ℝ`.

## Main results

* `TauCeti.sum_neighborFinset_pathGraph_qInt_eq`: the neighbour sum of `[u + 1]` on
  `pathGraph (k + 1)` equals `δ * [v + 1]` minus `[k + 2]` at `v = k`.
* `TauCeti.sum_neighborFinset_pathGraph_qInt_of_lt`: the adjacency eigenvector equation at every
  vertex `v < k`.
* `TauCeti.sum_neighborFinset_pathGraph_qInt_of_eq_zero`: the global adjacency eigenvector equation
  on `pathGraph (k + 1)` whenever `qInt R δ (k + 2) = 0`.
* `TauCeti.sum_neighborFinset_pathGraph_qInt_two_mul_cos_pi_div`: the `A_(k+1)` eigenvector
  equation at `δ = 2 * cos (π / (k + 2))`.

## References

* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989 (Perron–Frobenius eigenvectors of `A_n`).
* L. H. Kauffman and S. L. Lins, *Temperley–Lieb Recoupling Theory and Invariants of
  3-Manifolds*, Annals of Mathematics Studies 134, Princeton University Press, 1994.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, §4.5.
-/

public section

namespace TauCeti

open Real SimpleGraph

/-- On the path graph `pathGraph (k + 1)` with vertices `0, …, k`, the sum of the quantum integers
`[u + 1]` over the neighbours `u` of `v` equals `δ * [v + 1]` minus the missing top term `[k + 2]`
when `v = k`, over any commutative ring. -/
theorem sum_neighborFinset_pathGraph_qInt_eq {R : Type*} [CommRing R] (δ : R) {k : ℕ}
    (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) =
      δ * qInt R δ (v + 1) - if v.val = k then qInt R δ (k + 2) else 0 := by
  rw [neighborFinset_eq_filter, Finset.sum_filter]
  simp only [pathGraph_adj]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ if v.val + 1 = j ∨ j + 1 = v.val then qInt R δ (j + 1) else 0)]
  have h (j : ℕ) : (if v.val + 1 = j ∨ j + 1 = v.val then qInt R δ (j + 1) else 0) =
      (if v.val + 1 = j then qInt R δ (j + 1) else 0) +
        (if j + 1 = v.val then qInt R δ (j + 1) else 0) := by
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
  have h1 : (if v.val + 1 ∈ Finset.range (k + 1) then qInt R δ (v + 1 + 1) else 0) =
      qInt R δ (v + 2) - if v.val = k then qInt R δ (k + 2) else 0 := by
    split_ifs with hv hvk hvk
    · exfalso; simp at hv; omega
    · exact (sub_zero _).symm
    · rw [hvk, sub_self]
    · exfalso; simp at hv; omega
  have h2 : ∑ j ∈ Finset.range (k + 1), (if j + 1 = v.val then qInt R δ (j + 1) else 0) =
      qInt R δ v := by
    obtain ⟨_ | w, hw⟩ := v
    · simp
    · simp only [Nat.add_right_cancel_iff]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega))]
  rw [h1, h2, qInt_add_two]
  ring

/-- At every interior vertex `v < k` of `pathGraph (k + 1)`, the quantum integers `[t + 1]` satisfy
the adjacency recurrence `[v] + [v + 2] = δ * [v + 1]` over any commutative ring. -/
theorem sum_neighborFinset_pathGraph_qInt_of_lt {R : Type*} [CommRing R] (δ : R) {k : ℕ}
    {v : Fin (k + 1)} (hv : v.val < k) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1) := by
  rw [sum_neighborFinset_pathGraph_qInt_eq, ite_eq_right hv.ne, sub_zero]

/-- Whenever `[k + 2] = 0` in a commutative ring `R`, the quantum integers `[t + 1]` form an
eigenvector of the adjacency matrix of `pathGraph (k + 1)` with eigenvalue `δ`. -/
theorem sum_neighborFinset_pathGraph_qInt_of_eq_zero {R : Type*} [CommRing R] {δ : R} {k : ℕ}
    (hδ : qInt R δ (k + 2) = 0) (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt R δ (u + 1) = δ * qInt R δ (v + 1) := by
  rw [sum_neighborFinset_pathGraph_qInt_eq, hδ, ite_self, sub_zero]

/-- At `δ = 2 cos (π / (k + 2))`, the quantum integers `[t + 1]` on the vertices `t` of the path
graph on `k + 1` vertices, the Dynkin graph `A_(k+1)`, form an eigenvector of its adjacency
matrix with eigenvalue `δ`: this is the recurrence `[t] + [t + 2] = δ [t + 1]`, with `[0] = 0` at
one end of the graph and `[k + 2] = 0` at the other. -/
theorem sum_neighborFinset_pathGraph_qInt_two_mul_cos_pi_div {k : ℕ} (v : Fin (k + 1)) :
    ∑ u ∈ (pathGraph (k + 1)).neighborFinset v, qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (u + 1) =
      2 * cos (π / (k + 2 : ℕ)) * qInt ℝ (2 * cos (π / (k + 2 : ℕ))) (v + 1) :=
  sum_neighborFinset_pathGraph_qInt_of_eq_zero (qInt_two_mul_cos_pi_div_eq_zero (by omega)) v

end TauCeti
