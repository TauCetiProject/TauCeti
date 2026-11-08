/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PopulationSampling.Finite
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Distinct populations attain the exact sampling discrepancy

For a population `x : κ → α` of distinct values, a sampled word has distinct values exactly
when its index selection is injective. If an injective selection exists, the all-distinct event
has probability one under sampling without replacement. Its with-replacement probability is
`(n)_m / n^m`, where `m = Fintype.card ι` and `n = Fintype.card κ`.

When an embedding `ι ↪ κ` exists, this event attains the largest excess of the
without-replacement law over the with-replacement law. Consequently the exact collision bound
is sharp, and Mathlib's total variation distance `etvDist` is twice the collision probability.
The value space is arbitrary; the all-distinct event is explicitly assumed measurable.

## Main declarations

* `sampleWithoutReplacement_apply_injective`: the all-distinct event has mass one.
* `sampleWithReplacement_apply_injective`: its mass is the exact injective-selection ratio.
* `iSup_sampleWithoutReplacement_sub_sampleWithReplacement_eq`: the exact excess.
* `etvDist_sampleWithoutReplacement_sampleWithReplacement_eq`: twice that excess.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764, Theorem 13.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {ι κ α : Type*}
  [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSpace α]

/-- For distinct population values, sampling without replacement gives an all-distinct word
with probability one, provided an injective selection exists. -/
theorem sampleWithoutReplacement_apply_injective [Finite κ] {x : κ → α}
    (hx : Function.Injective x) (e : ι ↪ κ)
    (hI : MeasurableSet {f : ι → α | Function.Injective f}) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac x)
      {f | Function.Injective f} = 1 := by
  have : Finite ι := Finite.of_injective e e.injective
  have hsample : Measurable (fun k : ι → κ => fun i => x (k i)) :=
    measurable_reindexPopulation.comp measurable_prodMk_right
  rw [sampleWithoutReplacement_dirac, Measure.map_apply hsample hI]
  have hpre : (fun k : ι → κ => fun i => x (k i)) ⁻¹'
      {f | Function.Injective f} = {k | Function.Injective k} := by
    ext k
    exact hx.of_comp_iff k
  rw [hpre]
  exact uniformOn_self (Set.toFinite _) ⟨e, e.injective⟩

variable [Fintype ι] [Fintype κ]

/-- For distinct population values, the with-replacement probability of an all-distinct word
is the number of injective selections divided by the number of all selections. This also
holds when no selection exists, in which case both sides are zero. -/
theorem sampleWithReplacement_apply_injective {x : κ → α}
    (hx : Function.Injective x)
    (hI : MeasurableSet {f : ι → α | Function.Injective f}) :
    sampleWithReplacement (ι := ι) (Measure.dirac x) {f | Function.Injective f} =
      (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  have hsample : Measurable (fun k : ι → κ => fun i => x (k i)) :=
    measurable_reindexPopulation.comp measurable_prodMk_right
  rw [sampleWithReplacement_dirac, Measure.map_apply hsample hI]
  have hpre : (fun k : ι → κ => fun i => x (k i)) ⁻¹'
      {f | Function.Injective f} = {k | Function.Injective k} := by
    ext k
    exact hx.of_comp_iff k
  rw [hpre, uniformOn_injective_apply_eq]

/-- The exact largest excess between sampling a distinct-valued population without and with
replacement. The all-distinct event attains the supremum. -/
theorem iSup_sampleWithoutReplacement_sub_sampleWithReplacement_eq {x : κ → α}
    (hx : Function.Injective x) (e : ι ↪ κ)
    (hI : MeasurableSet {f : ι → α | Function.Injective f}) :
    (⨆ (A : Set (ι → α)) (_ : MeasurableSet A),
      sampleWithoutReplacement (Measure.dirac x) A -
        sampleWithReplacement (Measure.dirac x) A) =
      1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  let : Nonempty (ι → κ) := ⟨e⟩
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    simpa only [uniformOn_not_injective_apply_eq] using tsub_le_iff_left.mpr
      (sampleWithoutReplacement_le_sampleWithReplacement_add_collision
        (ρ := Measure.dirac x) hA)
  · simpa only [sampleWithoutReplacement_apply_injective hx e hI,
      sampleWithReplacement_apply_injective hx hI] using
      (le_iSup₂ (f := fun (A : Set (ι → α)) (_ : MeasurableSet A) =>
        sampleWithoutReplacement (Measure.dirac x) A -
          sampleWithReplacement (Measure.dirac x) A)
        {f | Function.Injective f} hI)

/-- For a distinct-valued population, Mathlib's total variation distance between the sampling
laws is twice the exact collision probability. The embedding assumption also covers empty
sample and population indices: both laws then have mass one and the distance is zero. -/
theorem etvDist_sampleWithoutReplacement_sampleWithReplacement_eq {x : κ → α}
    (hx : Function.Injective x) (e : ι ↪ κ)
    (hI : MeasurableSet {f : ι → α | Function.Injective f}) :
    etvDist (sampleWithoutReplacement (ι := ι) (Measure.dirac x))
      (sampleWithReplacement (ι := ι) (Measure.dirac x)) =
      2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) := by
  let : Nonempty (ι → κ) := ⟨e⟩
  let := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac x) e
  let := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac x)
  rw [etvDist_eq_two_mul_iSup_sub (by rw [measure_univ, measure_univ]),
    iSup_sampleWithoutReplacement_sub_sampleWithReplacement_eq hx e hI]

end TauCeti.Probability
