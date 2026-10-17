/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Set.PartialUnion
public import Mathlib.Topology.Basic

/-!
# Open partial unions

This file records that a partial union of a sequence of open sets is open.
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X]

/-- A partial union is open when each set occurring in it is open. -/
lemma isOpen_partialUnion {U : ℕ → Set X} {n : ℕ}
    (hU : ∀ i ≤ n, IsOpen (U i)) : IsOpen (partialUnion U n) := by
  induction n with
  | zero => simpa only [partialUnion_zero] using hU 0 le_rfl
  | succ n ih =>
    rw [partialUnion_succ]
    exact (ih fun i hi ↦ hU i (hi.trans n.le_succ)).union (hU (n + 1) le_rfl)

end TauCeti
