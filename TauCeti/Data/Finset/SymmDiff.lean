/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SymmDiff

/-!
# Cardinality bounds for symmetric differences of finite sets

The symmetric difference `s ∆ t` of two finite sets is the disjoint union `(s \ t) ∪ (t \ s)`.
This file records the resulting cardinality identity, its specialization `#(s ∆ t) = 2 * #(s \ t)`
when `#s = #t`, the cardinality-difference bound `#s - #t ≤ #(s ∆ t)`, and the symmetric-difference
triangle inequality `#(s ∆ u) ≤ #(s ∆ t) + #(t ∆ u)` matching `MeasureTheory.le_measure_symmDiff`
and `MeasureTheory.measure_symmDiff_le`.

## Main results

* `Finset.card_symmDiff_eq_card_sdiff_add_card_sdiff`: `#(s ∆ t) = #(s \ t) + #(t \ s)`.
* `Finset.card_symmDiff_of_card_eq`: `#(s ∆ t) = 2 * #(s \ t)` when `#s = #t`.
* `Finset.le_card_symmDiff`: `#s - #t ≤ #(s ∆ t)`.
* `Finset.card_symmDiff_le`: `#(s ∆ u) ≤ #(s ∆ t) + #(t ∆ u)`.
-/

public section

open scoped symmDiff

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- The cardinality of `s ∆ t` is the sum of the cardinalities of the two one-sided differences. -/
theorem card_symmDiff_eq_card_sdiff_add_card_sdiff (s t : Finset α) :
    #(s ∆ t) = #(s \ t) + #(t \ s) := by
  rw [Finset.symmDiff_def, card_union_of_disjoint disjoint_sdiff_sdiff]

/-- Two finite sets of equal cardinality have `#(s ∆ t) = 2 * #(s \ t)`. -/
theorem card_symmDiff_of_card_eq {s t : Finset α} (h : #s = #t) :
    #(s ∆ t) = 2 * #(s \ t) := by
  rw [card_symmDiff_eq_card_sdiff_add_card_sdiff, ← card_sdiff_comm h, Nat.two_mul]

/-- The cardinality difference `#s - #t` is bounded by `#(s ∆ t)`. -/
theorem le_card_symmDiff (s t : Finset α) : #s - #t ≤ #(s ∆ t) :=
  (le_card_sdiff t s).trans (card_le_card symmDiff_subset_sdiff)

/-- Triangle inequality for the cardinality of symmetric differences of finite sets. -/
theorem card_symmDiff_le (s t u : Finset α) : #(s ∆ u) ≤ #(s ∆ t) + #(t ∆ u) :=
  (card_le_card (symmDiff_triangle s t u)).trans (card_union_le _ _)

end Finset
