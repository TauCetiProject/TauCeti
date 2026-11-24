/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import TauCeti.Combinatorics.PlanarMatching.Counting

/-!
# Walk counts on a path graph

On the path graph with vertices `0, …, N`, the number of `n`-step walks from `0` to `k`
is the ballot number `TauCeti.halfCount n k`, provided `n ≤ N`. Thus the sum of the
squares of the endpoint multiplicities is `catalan n`. These are the block sizes and
total dimension of the path algebra used in the Temperley–Lieb half-line model: a
cutoff at least `n` does not affect walks of length `n` starting at zero.

The proof uses the adjacency-matrix walk-counting theorem and the existing ballot
recurrence, including the vanishing of the upper boundary term.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, §4.4.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of
  algebras*, MSRI Publications 14, Springer, 1989.
-/

public section

namespace TauCeti

open Finset SimpleGraph

/-- The ballot vector evolves under the path adjacency matrix by one step, before
the upper boundary can affect the count at `v`. -/
private theorem sum_neighborFinset_pathGraph_halfCount {N n : ℕ}
    (v : Fin (N + 1)) (hn : n + v < 2 * N + 1) :
    ∑ u ∈ (pathGraph (N + 1)).neighborFinset v, halfCount n u = halfCount (n + 1) v := by
  rw [neighborFinset_eq_filter, sum_filter]
  simp only [pathGraph_adj]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ if v.val + 1 = j ∨ j + 1 = v.val then halfCount n j else 0)]
  have h (j : ℕ) :
      (if v.val + 1 = j ∨ j + 1 = v.val then halfCount n j else 0) =
        (if v.val + 1 = j then halfCount n j else 0) +
          (if j + 1 = v.val then halfCount n j else 0) := by
    split_ifs <;> omega
  simp_rw [h]
  rw [sum_add_distrib, sum_ite_eq]
  have hu : (if v.val + 1 ∈ range (N + 1) then halfCount n (v.val + 1) else 0) =
      halfCount n (v.val + 1) := by
    split_ifs with hv
    · rfl
    · symm
      apply halfCount_eq_zero_of_lt
      simp only [mem_range, not_lt] at hv
      omega
  rw [hu]
  obtain ⟨_ | k, hk⟩ := v
  · simp [halfCount_succ_zero]
  · simp only [Nat.add_right_cancel_iff]
    rw [sum_ite_eq', ite_eq_left (mem_range.mpr (by omega)), halfCount_succ_succ]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using add_comm (halfCount n (k + 2)) (halfCount n k)

/-- The ballot formula for the entries of a path adjacency-matrix power starting at zero.
The bound ensures that a walk cannot cross the upper boundary and return to `v`. -/
theorem pathGraph_adjMatrix_pow_apply_zero_eq_halfCount {N n : ℕ} {v : Fin (N + 1)}
    (hn : n + v ≤ 2 * N + 1) :
    ((pathGraph (N + 1)).adjMatrix ℕ ^ n) 0 v = halfCount n v := by
  induction n generalizing v with
  | zero =>
    obtain ⟨_ | k, hk⟩ := v
    · simp
    · simp
  | succ n ih =>
    rw [pow_succ, mul_adjMatrix_apply]
    rw [sum_congr rfl fun u hu ↦ ih (v := u) (by
      have hadj := ((pathGraph (N + 1)).mem_neighborFinset v u).mp hu
      rw [pathGraph_adj] at hadj
      omega)]
    exact sum_neighborFinset_pathGraph_halfCount v (by omega)

/-- The number of length-`n` walks from the end vertex of a path graph to `v` is a
ballot number, as long as no walk can cross the upper boundary and return to `v`. -/
theorem card_walk_length_pathGraph {N n : ℕ} {v : Fin (N + 1)}
    (hn : n + v ≤ 2 * N + 1) :
    Fintype.card {p : (pathGraph (N + 1)).Walk 0 v | p.length = n} = halfCount n v := by
  calc
    _ = ((pathGraph (N + 1)).adjMatrix ℕ ^ n) 0 v := by
      simpa only [Nat.cast_id] using
        (adjMatrix_pow_apply_eq_card_walk (G := pathGraph (N + 1)) n 0 v (α := ℕ)).symm
    _ = halfCount n v := pathGraph_adjMatrix_pow_apply_zero_eq_halfCount hn

/-- The sum of the squared endpoint multiplicities of `n`-step walks on a path graph
with at least `n + 1` vertices is the Catalan number `catalan n`. In the half-line
path algebra these are precisely the dimensions of its matrix blocks. -/
theorem sum_sq_card_walk_length_pathGraph {N n : ℕ} (hn : n ≤ N) :
    ∑ v : Fin (N + 1),
      Fintype.card {p : (pathGraph (N + 1)).Walk 0 v | p.length = n} ^ 2 = catalan n := by
  have hcard (v : Fin (N + 1)) := card_walk_length_pathGraph (n := n) (v := v) (by omega)
  simp_rw [hcard]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ halfCount n k ^ 2)]
  calc
    ∑ k ∈ range (N + 1), halfCount n k ^ 2 =
        ∑ k ∈ range (n + 1), halfCount n k ^ 2 := by
      symm
      apply sum_subset (range_mono (by omega))
      intro k _ hk
      simp only [mem_range, not_lt] at hk
      simp [halfCount_eq_zero_of_lt (by omega : n < k)]
    _ = catalan n := sum_halfCount_sq n

end TauCeti
