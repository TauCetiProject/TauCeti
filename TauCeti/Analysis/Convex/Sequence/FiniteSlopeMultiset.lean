/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.SlopeData
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite slope multisets

The finite slopes of a convex height sequence are the slopes of all of its unit edges,
counted with multiplicity. This file packages that invariant on `FiniteSlopeData`, the
canonical presentation of a nonempty convex height sequence with finite domain.

The multiset has cardinality equal to the horizontal length of the polygon. Its sum is the
difference between the endpoint heights.

## Main results

* `FiniteSlopeData.slopeMultiset`: the multiset of unit slopes.
* `FiniteSlopeData.card_slopeMultiset`: its cardinality is the horizontal length.
* `FiniteSlopeData.sum_slopeMultiset`: its sum is the total height change.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
-/

public section

open Finset

namespace TauCeti

namespace FiniteSlopeData

variable {Γ : Type*} [Preorder Γ]

/-- The multiset of the slopes of the unit edges of finite slope data.

Each `i : Fin length` contributes one copy of `slope i`, so repeated slopes retain their
multiplicity. In particular, slope data of length zero has the empty slope multiset. -/
def slopeMultiset (d : FiniteSlopeData Γ) : Multiset Γ :=
  List.ofFn d.slope

/-- A value occurs in the slope multiset exactly when it is the slope of a unit edge. -/
@[simp]
theorem mem_slopeMultiset {d : FiniteSlopeData Γ} {m : Γ} :
    m ∈ d.slopeMultiset ↔ ∃ i : Fin d.length, d.slope i = m := by
  simp [slopeMultiset]

/-- The slope multiset is empty exactly when the represented polygon is a singleton. -/
@[simp]
theorem slopeMultiset_eq_zero_iff {d : FiniteSlopeData Γ} :
    d.slopeMultiset = 0 ↔ d.length = 0 := by
  simp [slopeMultiset]

/-- The number of finite unit slopes is the horizontal length of the polygon. -/
@[simp]
theorem card_slopeMultiset (d : FiniteSlopeData Γ) :
    d.slopeMultiset.card = d.length := by
  simp [slopeMultiset]

section AddCommMonoid

variable [AddCommMonoid Γ]

/-- The sum of the finite slopes is the sum over the unit edges. -/
theorem sum_slopeMultiset_eq_sum (d : FiniteSlopeData Γ) :
    d.slopeMultiset.sum = ∑ i, d.slope i := by
  simp [slopeMultiset, List.sum_ofFn]

/-- The sum of the finite slopes gives the right endpoint height. -/
theorem heights_start_add_length_eq (d : FiniteSlopeData Γ) :
    d.heights (d.start + d.length) =
      ((d.initialHeight + d.slopeMultiset.sum : Γ) : WithTop Γ) := by
  rw [d.heights_start_add_length, d.sum_slopeMultiset_eq_sum]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup Γ]

/-- The sum of the finite slopes is the difference between the endpoint heights. -/
theorem sum_slopeMultiset (d : FiniteSlopeData Γ) :
    d.slopeMultiset.sum =
      (d.heights (d.start + d.length)).untop₀ - (d.heights d.start).untop₀ := by
  rw [d.heights_start_add_length_eq, d.heights_start]
  simp

end AddCommGroup

end FiniteSlopeData

end TauCeti
