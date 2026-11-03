/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Lebesgue integrals over a finite union

The Lebesgue integral over the union of finitely many sets is at most the sum of the integrals over
the sets, without any disjointness or measurability assumption. This is the finite form of
`MeasureTheory.lintegral_iUnion_le`, and the subadditive counterpart of
`MeasureTheory.lintegral_biUnion_finset`. It is how a local estimate on finitely many open sets
covering a compact space becomes a global one.

## Main statements

* `TauCeti.lintegral_biUnion_finset_le`: `∫_{⋃ b ∈ s, t b} f ≤ ∑ b ∈ s, ∫_{t b} f`.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The Lebesgue integral over a finite union is at most the sum of the integrals over the sets. -/
theorem lintegral_biUnion_finset_le (s : Finset β) (t : β → Set α) (f : α → ℝ≥0∞) :
    ∫⁻ a in ⋃ b ∈ s, t b, f a ∂μ ≤ ∑ b ∈ s, ∫⁻ a in t b, f a ∂μ := by
  rw [← iUnion_subtype (· ∈ s) fun b ↦ t b]
  refine (lintegral_iUnion_le _ _).trans_eq ?_
  rw [tsum_fintype]
  exact Finset.sum_coe_sort s fun b ↦ ∫⁻ a in t b, f a ∂μ

end TauCeti
