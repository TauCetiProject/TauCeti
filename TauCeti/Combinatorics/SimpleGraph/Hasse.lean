/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
/-! # The Hasse graph of the natural numbers

On `ℕ`, covering is adjacency of consecutive natural numbers (`u + 1 = v ∨ v + 1 = u`), giving
`DecidableRel` and `LocallyFinite` instances and `neighborFinset` formulas for `hasse ℕ`. -/
public section
namespace SimpleGraph
/-- Two natural numbers are adjacent in `hasse ℕ` iff they differ by `1`. -/
theorem hasse_nat_adj {u v : ℕ} : (hasse ℕ).Adj u v ↔ u + 1 = v ∨ v + 1 = u := by
  simp only [hasse_adj, Nat.covBy_iff_add_one_eq]
instance instDecidableRelHasseNat : DecidableRel (hasse ℕ).Adj :=
  fun _ _ ↦ decidable_of_iff' _ hasse_nat_adj
instance instLocallyFiniteHasseNat : LocallyFinite (hasse ℕ)
  | 0 => Fintype.ofFinset {1} fun _ ↦ by
      simp only [Finset.mem_singleton, mem_neighborSet, hasse_nat_adj]; omega
  | v + 1 => Fintype.ofFinset {v, v + 2} fun _ ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton, mem_neighborSet, hasse_nat_adj]; omega
/-- In `hasse ℕ`, the unique neighbour of `0` is `1`. -/
@[simp] theorem neighborFinset_hasse_nat_zero : (hasse ℕ).neighborFinset 0 = {1} := by
  ext; simp only [mem_neighborFinset, hasse_nat_adj, Finset.mem_singleton]; omega
/-- In `hasse ℕ`, the neighbours of `v + 1` are `v` and `v + 2`. -/
@[simp] theorem neighborFinset_hasse_nat_succ (v : ℕ) : (hasse ℕ).neighborFinset (v + 1) =
    {v, v + 2} := by
  ext; simp only [mem_neighborFinset, hasse_nat_adj, Finset.mem_insert, Finset.mem_singleton]; omega
end SimpleGraph
