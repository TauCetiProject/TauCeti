/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Lebesgue integrals over a union

The Lebesgue integral over the union of finitely many sets is at most the sum of the integrals over
the sets, without any disjointness or measurability assumption. This is the finite form of
`MeasureTheory.lintegral_iUnion_le`, and the subadditive counterpart of
`MeasureTheory.lintegral_biUnion_finset`. It is how a local estimate on finitely many open sets
covering a compact space becomes a global one.

The same subadditivity bounds an integral by a weighted countable cover. Let `(S i)` be a countable
family of sets with weights `w i`, and suppose almost every point `x` of a set `s` lies in some
`S i` with `f x · ρ (S i) ≤ w i`. The integral of `f` over the points of `S i` where that bound
holds is at most `w i` (`TauCeti.setLIntegral_le_of_measure_le_of_forall_mul_le`), whether or not
`S i` is null, and these points cover almost all of `s`, so `∫_s f dρ ≤ ∑ᵢ w i`. No measurability
of `f`, `s` or the `S i` is needed.

## Main statements

* `TauCeti.lintegral_biUnion_finset_le`: `∫_{⋃ b ∈ s, t b} f ≤ ∑ b ∈ s, ∫_{t b} f`.
* `TauCeti.setLIntegral_le_tsum_of_ae_exists_mul_measure_le`: the bound `∫_s f dρ ≤ ∑ᵢ w i` by a
  weighted countable cover.
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

/-- **Integrals over a weighted countable cover.** Let `(S i)` be a countable family of sets with
weights `w i`. If almost every `x ∈ s` lies in some `S i` with `f x · μ (S i) ≤ w i`, then
`∫_s f dμ ≤ ∑ᵢ w i`. -/
theorem setLIntegral_le_tsum_of_ae_exists_mul_measure_le {ι : Type*} [Countable ι] {s : Set α}
    {f : α → ℝ≥0∞} {S : ι → Set α} {w : ι → ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, x ∈ s → ∃ i, x ∈ S i ∧ f x * μ (S i) ≤ w i) :
    ∫⁻ x in s, f x ∂μ ≤ ∑' i, w i := by
  -- The points of `S i` where the bound holds cover almost all of `s`.
  let T (i : ι) : Set α := {x | x ∈ S i ∧ f x * μ (S i) ≤ w i}
  have h_cover : s ≤ᵐ[μ] ⋃ i, T i :=
    h.mono fun x hx hxs ↦ mem_iUnion.2 (hx hxs)
  calc ∫⁻ x in s, f x ∂μ
    _ ≤ ∫⁻ x in ⋃ i, T i, f x ∂μ := lintegral_mono_set' h_cover
    _ ≤ ∑' i, ∫⁻ x in T i, f x ∂μ := lintegral_iUnion_le T f
    _ ≤ ∑' i, w i := tsum_le_tsum fun i ↦
        setLIntegral_le_of_measure_le_of_forall_mul_le (measure_mono fun _ hx ↦ hx.1)
          fun _ hx ↦ hx.2

end TauCeti
