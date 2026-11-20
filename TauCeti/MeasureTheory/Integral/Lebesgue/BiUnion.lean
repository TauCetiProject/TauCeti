/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Lebesgue integrals over a union

The Lebesgue integral over the union of finitely many sets is at most the sum of the integrals over
the sets, without any disjointness or measurability assumption. This is the finite form of
`MeasureTheory.lintegral_iUnion_le`, and the subadditive counterpart of
`MeasureTheory.lintegral_biUnion_finset`. It is how a local estimate on finitely many open sets
covering a compact space becomes a global one.

## Main statements

* `TauCeti.lintegral_biUnion_finset_le`: `∫_{⋃ b ∈ s, t b} f ≤ ∑ b ∈ s, ∫_{t b} f`.
* `TauCeti.setLIntegral_le_card_mul_of_subset_biUnion`: if `u ⊆ ⋃ b ∈ s, t b` and each
  `∫_{t b} f ≤ c`, then `∫_u f ≤ #s * c`.
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

/-- If a set `u` is covered by the sets `t b`, `b ∈ s`, for a finite `s`, and the integral of `f`
over each `t b` is at most `c`, then the integral of `f` over `u` is at most `#s * c`. -/
theorem setLIntegral_le_card_mul_of_subset_biUnion {s : Finset β} {t : β → Set α} {u : Set α}
    (hu : u ⊆ ⋃ b ∈ s, t b) {f : α → ℝ≥0∞} {c : ℝ≥0∞} (hc : ∀ b ∈ s, ∫⁻ a in t b, f a ∂μ ≤ c) :
    ∫⁻ a in u, f a ∂μ ≤ s.card * c :=
  (lintegral_mono_set hu).trans <| (lintegral_biUnion_finset_le s t f).trans <|
    (Finset.sum_le_card_nsmul s _ c hc).trans_eq (nsmul_eq_mul _ _)

end TauCeti
