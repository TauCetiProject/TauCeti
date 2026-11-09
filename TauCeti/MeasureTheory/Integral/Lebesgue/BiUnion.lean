/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.Exhaustion

/-!
# Lebesgue integrals over a union

The Lebesgue integral over the union of finitely many sets is at most the sum of the integrals over
the sets, without any disjointness or measurability assumption. This is the finite form of
`MeasureTheory.lintegral_iUnion_le`, and the subadditive counterpart of
`MeasureTheory.lintegral_biUnion_finset`. It is how a local estimate on finitely many open sets
covering a compact space becomes a global one.

Along an increasing sequence of sets `V n` covering `A`, the integral over `A` is bounded by any
limit of bounds on the integrals over the pieces `A ∩ V n`, as when an estimate proved on each
set of an exhaustion is passed to the whole domain.

## Main statements

* `TauCeti.lintegral_biUnion_finset_le`: `∫_{⋃ b ∈ s, t b} f ≤ ∑ b ∈ s, ∫_{t b} f`.
* `TauCeti.setLIntegral_le_of_forall_inter_le`: `∫_A g ≤ c` when the integrals over the pieces
  `A ∩ V n` of an exhaustion are eventually bounded by a sequence converging to `c`.
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

/-- If the integrals of `g` over `A ∩ V n`, for an increasing sequence of sets `V n` covering `A`,
are eventually bounded by a sequence converging to `c`, then the integral of `g` over `A` is at
most `c`. -/
theorem setLIntegral_le_of_forall_inter_le {A : Set α} {V : ℕ → Set α} (hV : Monotone V)
    (hA : A ⊆ ⋃ n, V n) {g : α → ℝ≥0∞} {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : Filter.Tendsto f Filter.atTop (nhds c))
    (h : ∀ᶠ n in Filter.atTop, ∫⁻ x in A ∩ V n, g x ∂μ ≤ f n) :
    ∫⁻ x in A, g x ∂μ ≤ c := by
  have hAV : ⋃ n, A ∩ V n = A := by rw [← inter_iUnion, inter_eq_left.2 hA]
  have h1 := tendsto_setLIntegral_of_monotone (μ := μ) (f := g) (s := fun n => A ∩ V n)
    fun m n hmn => inter_subset_inter_right A (hV hmn)
  rw [hAV] at h1
  exact le_of_tendsto_of_tendsto h1 hf h

end TauCeti
