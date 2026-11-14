/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# The Hasse graph of the natural numbers

Mathlib defines `SimpleGraph.hasse α` for any preorder `α`, and specializes it to `Fin n` as
`SimpleGraph.pathGraph n`, providing decidable adjacency only when `α` is finite. On `ℕ`, covering
is adjacency of consecutive natural numbers (`u + 1 = v ∨ v + 1 = u`), so `SimpleGraph.hasse ℕ` is
the infinite half-line graph with base vertex `0` of degree `1` and every positive vertex of degree
`2`. This file provides its `DecidableRel` and `LocallyFinite` instances and explicit
`neighborFinset` formulas.

## Main results

* `SimpleGraph.hasse_nat_adj`: two natural numbers are adjacent in `hasse ℕ` iff they differ by `1`.
* `SimpleGraph.neighborFinset_hasse_nat_zero`, `SimpleGraph.neighborFinset_hasse_nat_succ`:
  the neighbour finsets `{1}` at `0` and `{v, v + 2}` at `v + 1`.
-/

public section

namespace SimpleGraph

/-- Two natural numbers are adjacent in `hasse ℕ` exactly when they are consecutive. -/
theorem hasse_nat_adj {u v : ℕ} : (hasse ℕ).Adj u v ↔ u + 1 = v ∨ v + 1 = u := by
  simp only [hasse_adj, CovBy]
  refine ⟨?_, ?_⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; by_contra h; exact @h2 (u + 1) (by omega) (by omega)
    · right; by_contra h; exact @h2 (v + 1) (by omega) (by omega)
  · rintro (rfl | rfl)
    · exact Or.inl ⟨by omega, fun _ _ ↦ by omega⟩
    · exact Or.inr ⟨by omega, fun _ _ ↦ by omega⟩

instance instDecidableRelHasseNat : DecidableRel (hasse ℕ).Adj :=
  fun _ _ ↦ decidable_of_iff' _ hasse_nat_adj

instance instLocallyFiniteHasseNat : LocallyFinite (hasse ℕ)
  | 0 => Fintype.ofFinset {1} fun w ↦ by
      simp only [Finset.mem_singleton, mem_neighborSet, hasse_nat_adj]
      omega
  | v + 1 => Fintype.ofFinset {v, v + 2} fun w ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton, mem_neighborSet, hasse_nat_adj]
      omega

@[simp]
theorem neighborFinset_hasse_nat_zero : (hasse ℕ).neighborFinset 0 = {1} := by
  ext w
  simp only [mem_neighborFinset, hasse_nat_adj, Finset.mem_singleton]
  omega

@[simp]
theorem neighborFinset_hasse_nat_succ (v : ℕ) :
    (hasse ℕ).neighborFinset (v + 1) = {v, v + 2} := by
  ext w
  simp only [mem_neighborFinset, hasse_nat_adj, Finset.mem_insert, Finset.mem_singleton]
  omega

end SimpleGraph
