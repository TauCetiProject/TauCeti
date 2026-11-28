/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Left-invariant measure of a finite union of left cosets

Let `H` be a measurable group with a left-invariant measure `μ`, and let `J` be a measurable
subgroup of `H`. Each fibre `(QuotientGroup.mk : H → H ⧸ J) ⁻¹' {t}` is a left coset `g • J`,
hence measurable of measure `μ J`. Summing over a finite nonempty set `s ⊆ H ⧸ J` gives
`μ (QuotientGroup.mk ⁻¹' s) = s.ncard * μ J`.

## Main results

* `TauCeti.measurableSet_preimage_quotientGroup_mk_singleton`: every fibre of
  `QuotientGroup.mk : H → H ⧸ J` is measurable when `J` is measurable.
* `TauCeti.measure_preimage_quotientGroup_mk_singleton`: every fibre of `QuotientGroup.mk` has
  measure `μ J` under a left-invariant measure `μ`.
* `TauCeti.measure_preimage_quotientGroup_mk_eq_ncard_mul`: the preimage of a set `s ⊆ H ⧸ J`
  with `s.ncard ≠ 0` has measure `s.ncard * μ J`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/UpperBound/Seesaw/IntegralAsCosetSum.lean`, declaration `New.Seesaw.measure_union_cosets`.
-/

public section

open MeasureTheory Measure QuotientGroup Set
open scoped Pointwise

namespace TauCeti

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H] {J : Subgroup H}

/-- Each fibre of the quotient map `QuotientGroup.mk : H → H ⧸ J` is a left coset of `J`, hence
measurable whenever `J` is measurable. -/
theorem measurableSet_preimage_quotientGroup_mk_singleton
    (hJ : MeasurableSet (J : Set H)) (t : H ⧸ J) :
    MeasurableSet (QuotientGroup.mk (s := J) ⁻¹' {t}) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
  rw [show QuotientGroup.mk (s := J) ⁻¹' {↑g} = g • (J : Set H) from
    QuotientGroup.eq_class_eq_leftCoset J g]
  exact hJ.const_smul g

/-- Under a left-invariant measure `μ`, every fibre of `QuotientGroup.mk : H → H ⧸ J` has
measure `μ J`. -/
theorem measure_preimage_quotientGroup_mk_singleton {μ : Measure H} [IsMulLeftInvariant μ]
    (t : H ⧸ J) :
    μ (QuotientGroup.mk (s := J) ⁻¹' {t}) = μ J := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
  rw [show QuotientGroup.mk (s := J) ⁻¹' {↑g} = g • (J : Set H) from
    QuotientGroup.eq_class_eq_leftCoset J g, measure_smul]

/-- A union of `n ≥ 1` left cosets of a measurable subgroup `J` has measure `n * μ J` for any
left-invariant measure `μ`. -/
theorem measure_preimage_quotientGroup_mk_eq_ncard_mul {μ : Measure H} [IsMulLeftInvariant μ]
    (hJ : MeasurableSet (J : Set H)) {s : Set (H ⧸ J)} (hs : s.ncard ≠ 0) :
    μ (QuotientGroup.mk (s := J) ⁻¹' s) = s.ncard * μ J := by
  lift s to Finset (H ⧸ J) using Set.finite_of_ncard_ne_zero hs
  rw [← sum_measure_preimage_singleton _ fun t _ ↦
    measurableSet_preimage_quotientGroup_mk_singleton hJ t]
  simp [measure_preimage_quotientGroup_mk_singleton]

end TauCeti
