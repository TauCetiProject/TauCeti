/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Data.Fin.Tuple.OrderStatistic
import Mathlib.Topology.LocallyFinite

/-!
# Continuity of order statistics

Each order statistic depends continuously on the entries of a finite tuple in a linearly
ordered space with closed order. This includes tuples with repeated entries: although the
sorting permutation can jump at a tie, the sorted values remain continuous.

On each closed chamber specified by a sorting permutation, an order statistic is a fixed
coordinate projection. These finitely many chambers cover the tuple space.
-/

public section

open Set

namespace TauCeti

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] {n : ℕ}

/-- Every order statistic is continuous, including at tuples with ties. -/
@[fun_prop]
theorem continuous_orderStatistic (k : Fin n) :
    Continuous (orderStatistic k : (Fin n → α) → α) := by
  let C (σ : Equiv.Perm (Fin n)) : Set (Fin n → α) := {x | Monotone (x ∘ σ)}
  apply (locallyFinite_of_finite C).continuous
  · ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨Tuple.sort x, Tuple.monotone_sort x⟩
  · intro σ
    exact (isClosed_monotone (α := α) (β := Fin n)).preimage
      (f := fun x : Fin n → α ↦ x ∘ σ) (by fun_prop)
  · intro σ
    apply (continuous_apply (σ k)).continuousOn.congr
    intro x hx
    simpa only [orderStatistic_def, Function.comp_apply] using
      congrFun (Tuple.unique_monotone (Tuple.monotone_sort x) hx) k

end TauCeti
