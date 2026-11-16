/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.PathModel
public import TauCeti.QuantumGroups.QuantumInteger.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Analysis.Real.Sqrt

import TauCeti.QuantumGroups.QuantumInteger.PathGraph

/-!
# Truncated half-line path-model eigenvectors on path graphs

On the truncated half-line `SimpleGraph.pathGraph (n + 1)` with base vertex `0`, every walk of
`k < n` steps from `0` ends at a vertex `< n`, strictly below the boundary vertex `n`. Combining
this distance bound with the path-graph quantum-integer adjacency recurrence
(`TauCeti.sum_neighborFinset_pathGraph_qInt_of_lt`) shows that any vertex weights `r` satisfying
`r t ^ 2 = qInt R δ (t + 1)` satisfy `TauCeti.TemperleyLieb.IsSqWalkEigenvectorUpTo` from `0` up
to `n` steps without requiring `[n + 2] = 0`. In particular, when `[1], …, [n + 1]` are nonnegative
reals, the real weights `√[t + 1]` give a truncated path-model eigenvector on `pathGraph (n + 1)`
(which maps along any non-unital ring homomorphism via `IsSqWalkEigenvectorUpTo.map`).

## Main results

* `TauCeti.TemperleyLieb.isSqWalkEigenvectorUpTo_pathGraph_of_sq_eq_qInt`: any vertex weights on
  `pathGraph (n + 1)` whose squares are the quantum integers `[t + 1]` satisfy
  `IsSqWalkEigenvectorUpTo` from `0` up to `n` steps.
* `TauCeti.TemperleyLieb.isSqWalkEigenvectorUpTo_pathGraph_sqrt_qInt`: the real weights `√[t + 1]`
  on `pathGraph (n + 1)` satisfy `IsSqWalkEigenvectorUpTo` from `0` up to `n` steps whenever
  `[1], …, [n + 1]` are nonnegative.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, §§4.4–4.5.
-/

public section

namespace TauCeti.TemperleyLieb

/-- Any vertex weights `r` on `SimpleGraph.pathGraph (n + 1)` whose squares are the quantum
integers `[t + 1]` satisfy the walk-endpoint eigenvector equation from `0` up to `n` steps: every
walk of `k < n` steps from `0` ends at a vertex `< n`, away from the boundary vertex `n`. -/
theorem isSqWalkEigenvectorUpTo_pathGraph_of_sq_eq_qInt {R : Type*} [CommRing R] {δ : R} {n : ℕ}
    {r : Fin (n + 1) → R} (hr : ∀ t : Fin (n + 1), r t ^ 2 = qInt R δ (t + 1)) :
    IsSqWalkEigenvectorUpTo (SimpleGraph.pathGraph (n + 1)) 0 r δ n := by
  rw [isSqWalkEigenvectorUpTo_iff]
  intro k hk s hs
  have hv : (s (Fin.last k)).val < n := by
    have hle := hs.apply_le_add (f := Fin.val)
      (fun _ _ huv ↦ by rw [SimpleGraph.pathGraph_adj] at huv; omega) (Fin.last k)
    simp only [Fin.val_zero, zero_add, Fin.val_last] at hle
    omega
  simp_rw [hr]
  exact sum_neighborFinset_pathGraph_qInt_of_lt δ hv

/-- When the quantum integers `[1], …, [n + 1]` are nonnegative, the real weights `√[t + 1]` on
`SimpleGraph.pathGraph (n + 1)` satisfy the walk-endpoint eigenvector equation from `0` up to `n`
steps. -/
theorem isSqWalkEigenvectorUpTo_pathGraph_sqrt_qInt {δ : ℝ} {n : ℕ}
    (hnonneg : ∀ j ∈ Finset.Icc 1 (n + 1), 0 ≤ qInt ℝ δ j) :
    IsSqWalkEigenvectorUpTo (SimpleGraph.pathGraph (n + 1)) 0
      (fun t : Fin (n + 1) ↦ √(qInt ℝ δ (t + 1))) δ n :=
  isSqWalkEigenvectorUpTo_pathGraph_of_sq_eq_qInt fun t ↦
    Real.sq_sqrt (hnonneg (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))

end TauCeti.TemperleyLieb
