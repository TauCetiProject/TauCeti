/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Order.PartialSups
import Mathlib.Order.SuccPred.Nat

/-!
# Path-connected unions and intersections

If every member of a family of path-connected sets contains a path-connected set `C`, and two
distinct members meet inside `C`, then every pairwise intersection of the family is path
connected: it is a member of the family or `C` itself. This is the hypothesis on pairwise
intersections in the generation half of the Seifert--van Kampen theorem, and the form in which it
holds for the summands of a wedge sum.

Finite partial unions are path connected when each member is path connected and each new
member meets the preceding union. The partial unions use Mathlib's `partialSups`.

## Main declarations

* `TauCeti.isPathConnected_inter_of_pairwise`: pairwise intersections of such a family are path
  connected.
* `TauCeti.isPathConnected_partialSups`: path connectedness of successive finite unions.
-/

public section

open Set

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {U : ι → Set X} {C : Set X}

/-- If every member of the family contains `C` and two distinct members meet inside `C`, then
every pairwise intersection is path connected as soon as `C` and the members are. -/
theorem isPathConnected_inter_of_pairwise (hUp : ∀ i, IsPathConnected (U i))
    (hC : IsPathConnected C) (hCU : ∀ i, C ⊆ U i) (hUC : Pairwise fun i j ↦ U i ∩ U j ⊆ C)
    (i j : ι) : IsPathConnected (U i ∩ U j) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [inter_self]
    exact hUp i
  · rwa [(hUC hij).antisymm (subset_inter (hCU i) (hCU j))]

/-- Finite partial unions are path connected if each member is path connected and each
new member meets the preceding union. Only the first `n + 1` members are constrained. -/
theorem isPathConnected_partialSups (U : ℕ → Set X) (n : ℕ)
    (hU : ∀ i ≤ n, IsPathConnected (U i))
    (hOverlap : ∀ i < n, (partialSups U i ∩ U (i + 1)).Nonempty) :
    IsPathConnected (partialSups U n) := by
  induction n with
  | zero => exact hU 0 le_rfl
  | succ n ih =>
    have hStep : partialSups U (n + 1) = partialSups U n ∪ U (n + 1) :=
      partialSups_succ U n
    rw [hStep]
    exact (ih (fun i hi => hU i (by omega))
      (fun i hi => hOverlap i (by omega))).union (hU (n + 1) le_rfl)
        (hOverlap n (by omega))

end TauCeti
