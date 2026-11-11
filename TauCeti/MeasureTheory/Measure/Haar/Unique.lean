/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Consequences of the uniqueness of Haar measure

A continuous group isomorphism into a second-countable locally compact group is nonsingular for
any Haar measures chosen on its source and target. Thus null sets can be transported between the
groups independently of the normalizations of their measures. Both multiplicative and additive
versions are provided.

This uses `MeasureTheory.Measure.absolutelyContinuous_isHaarMeasure` for the pushforward,
which is again a Haar measure.

A finite Haar measure lives on a compact group, where every finite left-invariant measure is a
multiple of it (`MeasureTheory.Measure.isMulInvariant_eq_smul_of_compactSpace`). Hence it is
determined by its total mass among left-invariant measures, and it is also right-invariant and
inversion-invariant.

## Main results

* `ContinuousMulEquiv.quasiMeasurePreserving_haar`: a continuous group isomorphism
  is quasi measure preserving for Haar measures on its source and target.
* `ContinuousAddEquiv.quasiMeasurePreserving_addHaar`: the additive version.
* `MeasureTheory.Measure.haar_apply_le_haar_apply_iff`: two Haar measures on a second-countable
  locally compact group compare sets the same way, since they differ by a positive finite factor.
  The additive version is `MeasureTheory.Measure.addHaar_apply_le_addHaar_apply_iff`.
* `MeasureTheory.Measure.isMulLeftInvariant_eq_of_measure_univ_eq`: a left-invariant measure
  with the same total mass as a finite Haar measure coincides with it.
* `MeasureTheory.Measure.isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure` and
  `MeasureTheory.Measure.isInvInvariant_of_isHaarMeasure_of_isFiniteMeasure`: a finite Haar
  measure is right-invariant and inversion-invariant.

All three have additive versions.
-/

public section

open MeasureTheory MeasureTheory.Measure

/-- A continuous group isomorphism into a second-countable locally compact group is nonsingular
for any Haar measures on its source and target. -/
@[to_additive
/-- A continuous additive equivalence into a second-countable locally compact group is nonsingular
for any additive Haar measures on its source and target. -/]
theorem ContinuousMulEquiv.quasiMeasurePreserving_haar {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (μ : Measure G) (ν : Measure H)
    [IsHaarMeasure μ] [IsHaarMeasure ν] : QuasiMeasurePreserving e μ ν :=
  ⟨e.continuous.measurable, absolutelyContinuous_isHaarMeasure (μ.map e) ν⟩

namespace MeasureTheory.Measure

section FiniteHaar

open Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- A left-invariant measure with the same total mass as a finite Haar measure on a locally
compact group coincides with it. -/
@[to_additive /-- A left-invariant measure with the same total mass as a finite additive Haar
measure on a locally compact additive group coincides with it. -/]
theorem isMulLeftInvariant_eq_of_measure_univ_eq (μ' μ : Measure G)
    [μ'.IsMulLeftInvariant] [μ.IsHaarMeasure] [IsFiniteMeasure μ] (h : μ' univ = μ univ) :
    μ' = μ := by
  have : CompactSpace G := by
    by_contra H
    rw [not_compactSpace_iff] at H
    exact measure_ne_top μ univ (measure_univ_of_isMulLeftInvariant μ)
  have : IsFiniteMeasure μ' := ⟨h ▸ measure_lt_top μ univ⟩
  obtain ⟨c, rfl⟩ : ∃ c : NNReal, μ' = c • μ :=
    ⟨_, isMulInvariant_eq_smul_of_compactSpace μ' μ⟩
  have hc : (c : ENNReal) * μ univ = 1 * μ univ := by simpa using h
  rw [ENNReal.mul_left_inj (NeZero.ne _) (measure_ne_top _ _), ENNReal.coe_eq_one] at hc
  rw [hc, one_smul]

/-- Every finite Haar measure on a locally compact group is right-invariant. -/
@[to_additive /-- Every finite additive Haar measure on a locally compact additive group is
right-invariant. -/]
theorem isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsFiniteMeasure μ] : μ.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have : (map (· * g) μ).IsHaarMeasure := isHaarMeasure_map_mul_right μ g
    refine isMulLeftInvariant_eq_of_measure_univ_eq _ _ ?_
    rw [map_apply (measurable_mul_const g) .univ, preimage_univ]

/-- Every finite Haar measure on a locally compact group is invariant under inversion. -/
@[to_additive /-- Every finite additive Haar measure on a locally compact additive group is
invariant under negation. -/]
theorem isInvInvariant_of_isHaarMeasure_of_isFiniteMeasure (μ : Measure G)
    [μ.IsHaarMeasure] [IsFiniteMeasure μ] : μ.IsInvInvariant := by
  have : μ.IsMulRightInvariant := isMulRightInvariant_of_isHaarMeasure_of_isFiniteMeasure μ
  exact ⟨isMulLeftInvariant_eq_of_measure_univ_eq _ _ <| by simp [inv_apply]⟩

end FiniteHaar

/-- Two Haar measures on a second-countable locally compact group are positive finite multiples
of each other, so they compare sets the same way. -/
@[to_additive /-- Two additive Haar measures on a second-countable locally compact group are
positive finite multiples of each other, so they compare sets the same way. -/]
theorem haar_apply_le_haar_apply_iff {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [IsHaarMeasure μ] [IsHaarMeasure ν]
    {s t : Set G} : μ s ≤ μ t ↔ ν s ≤ ν t := by
  rw [isMulLeftInvariant_eq_smul μ ν]
  simp [ENNReal.mul_le_mul_iff_right, (haarScalarFactor_pos_of_isHaarMeasure μ ν).ne']

end MeasureTheory.Measure

end
