/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.LapMatrix.Eigenvalues
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Laplacian eigenvalues under adding edges

Adding edges to a finite simple graph moves its sorted Laplacian eigenvalues
`SimpleGraph.lapEigenvalues` (listed in nonincreasing order, index `0` the largest) in a
controlled way.

* Adding edges lowers no eigenvalue: if `G ≤ H`, the eigenvalue of `G` at index `i` is at most the
  eigenvalue of `H` at index `i` (`SimpleGraph.lapEigenvalues_le_of_le`).
* Adding `r` edges raises no eigenvalue above the eigenvalue of the original graph `r` places
  before it: if `H` has `r` edges not in `G` and `i + r ≤ k`, the eigenvalue of `H` at index `k`
  is at most the eigenvalue of `G` at index `i`
  (`SimpleGraph.lapEigenvalues_le_of_add_card_sdiff_le`). This needs no comparison between `G`
  and `H`.

For one added edge these are the interlacing `ν_(i+1)(H) ≤ νᵢ(G) ≤ νᵢ(H)` of Brouwer and Haemers.
Both rest on the decomposition `L(H) = L(G) + L(H \ G)` for `G ≤ H`
(`SimpleGraph.lapMatrix_sdiff_of_le`). The Laplacian `L(H \ G)` is positive semidefinite, so
Weyl's inequality gives the first statement; its rank is at most the number of edges of `H \ G`
(`SimpleGraph.rank_lapMatrix_le_card_edgeFinset`), so rank interlacing gives the second.

As consequences, the largest eigenvalue and the algebraic connectivity do not decrease when
edges are added (`SimpleGraph.largestLapEigenvalue_le_of_le`,
`SimpleGraph.algebraicConnectivity_le_of_le`).

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Springer Universitext (2012),
  Proposition 3.2.1 (ii) (interlacing for one added edge) and Theorem 2.8.1 (the Courant–Weyl
  inequalities).
-/

public section

open Finset Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V} [DecidableRel G.Adj]
  [DecidableRel H.Adj]

/-- Adding edges lowers no Laplacian eigenvalue: if `G ≤ H`, the eigenvalue of `G` at each index
is at most the eigenvalue of `H` at the same index. -/
theorem lapEigenvalues_le_of_le (h : G ≤ H) (i : Fin (Fintype.card V)) :
    G.lapEigenvalues i ≤ H.lapEigenvalues i := by
  have hn : 0 < Fintype.card V := Fin.pos i
  let j : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have hsum : G.lapMatrix ℝ + (H \ G).lapMatrix ℝ = H.lapMatrix ℝ := by
    rw [lapMatrix_sdiff_of_le ℝ h, add_sub_cancel]
  -- Weyl: `λᵢ(L(G)) + λ_min(L(H \ G)) ≤ λᵢ(L(G) + L(H \ G))`, and `λ_min(L(H \ G)) ≥ 0`.
  have hweyl := (G.isHermitian_lapMatrix ℝ).le_eigenvalues₀_add
    ((H \ G).isHermitian_lapMatrix ℝ) (i := i) (j := j) (k := i) (by simp only [j]; omega)
  rw [IsHermitian.eigenvalues₀_congr hsum _ (H.isHermitian_lapMatrix ℝ)] at hweyl
  have hj := (H \ G).lapEigenvalues_nonneg j
  simp only [lapEigenvalues_def] at hweyl hj ⊢
  linarith

/-- Adding `r` edges raises no Laplacian eigenvalue above the eigenvalue `r` places before it: if
`H` has at most `r` edges that are not edges of `G` and `i + r ≤ k`, then the eigenvalue of `H` at
index `k` is at most the eigenvalue of `G` at index `i`. No comparison between `G` and `H` is
assumed. -/
theorem lapEigenvalues_le_of_add_card_sdiff_le {i k : Fin (Fintype.card V)}
    (hk : (i : ℕ) + #(H.edgeFinset \ G.edgeFinset) ≤ k) :
    H.lapEigenvalues k ≤ G.lapEigenvalues i := by
  -- Compare `H` with `G ⊔ H`, which contains `G` and has the same edges outside `G`.
  refine (lapEigenvalues_le_of_le (H := G ⊔ H) le_sup_right k).trans ?_
  have hrank : ((G ⊔ H).lapMatrix ℝ - G.lapMatrix ℝ).rank ≤ #(H.edgeFinset \ G.edgeFinset) := by
    rw [← lapMatrix_sdiff_of_le ℝ le_sup_left]
    refine (rank_lapMatrix_le_card_edgeFinset _).trans_eq ?_
    simp [edgeFinset]
  rw [lapEigenvalues_def, lapEigenvalues_def]
  exact ((G ⊔ H).isHermitian_lapMatrix ℝ).eigenvalues₀_le_of_rank_sub_le
    (G.isHermitian_lapMatrix ℝ) hrank hk

/-- Adding edges does not decrease the largest Laplacian eigenvalue. -/
theorem largestLapEigenvalue_le_of_le [Nonempty V] (h : G ≤ H) :
    G.largestLapEigenvalue ≤ H.largestLapEigenvalue := by
  rw [largestLapEigenvalue_def, largestLapEigenvalue_def]
  exact lapEigenvalues_le_of_le h _

/-- Adding edges does not decrease the algebraic connectivity. -/
theorem algebraicConnectivity_le_of_le (h : G ≤ H) :
    G.algebraicConnectivity ≤ H.algebraicConnectivity := by
  by_cases hn : 2 ≤ Fintype.card V
  · rw [G.algebraicConnectivity_of_two_le hn, H.algebraicConnectivity_of_two_le hn]
    exact lapEigenvalues_le_of_le h _
  · rw [G.algebraicConnectivity_of_lt_two (by omega), H.algebraicConnectivity_of_lt_two (by omega)]

end SimpleGraph
