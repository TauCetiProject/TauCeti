/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr

/-!
# Concavity of the partial sums of an antitone sequence

The partial sums `S n = ∑ i ∈ range n, T i` of an antitone sequence `T` are a concave function of
`n`: `S (m + u + v) + S m ≤ S (m + u) + S (m + v)`. Composed with a modular rank function on a
lattice, this makes `S ∘ rank` submodular; it is the inequality behind the supermodularity of a
degree shifted by the partial sums of a dominant tuple.
-/

public section

open Finset

/-- Partial sums of an antitone sequence are concave:
`S (m + u + v) + S m ≤ S (m + u) + S (m + v)` for `S n = ∑ i ∈ range n, T i`. -/
theorem Antitone.sum_range_add_add_sum_range_le {M : Type*} [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {T : ℕ → M} (hT : Antitone T) (m u v : ℕ) :
    ∑ i ∈ range (m + u + v), T i + ∑ i ∈ range m, T i ≤
      ∑ i ∈ range (m + u), T i + ∑ i ∈ range (m + v), T i := by
  have h : ∑ x ∈ range u, T (m + v + x) ≤ ∑ x ∈ range u, T (m + x) :=
    sum_le_sum fun x _ ↦ hT (by omega)
  have e1 : ∑ i ∈ range (m + u + v), T i =
      ∑ i ∈ range (m + v), T i + ∑ x ∈ range u, T (m + v + x) := by
    rw [add_right_comm, sum_range_add]
  rw [e1, sum_range_add _ m u]
  calc _ = (∑ i ∈ range m, T i + ∑ i ∈ range (m + v), T i) + ∑ x ∈ range u, T (m + v + x) := by
        abel
    _ ≤ (∑ i ∈ range m, T i + ∑ i ∈ range (m + v), T i) + ∑ x ∈ range u, T (m + x) := by gcongr
    _ = _ := by abel
