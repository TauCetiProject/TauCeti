/-
Copyright (c) 2026 Alexander Richard Towell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Richard Towell
-/
module

public import TauCeti.Probability.PopulationSampling.Finite
public import TauCeti.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Sharpness of the finite-sampling collision bound

For an injective population `x : κ → α`, the event that all observed values are distinct
has probability one without replacement and probability `(|κ|)_(|ι|) / |κ|^|ι|` with
replacement. Thus its discrepancy attains the collision error. The signed-measure total
variation has twice that value, by the existing eventwise upper bound and the Jordan
decomposition's supremum characterization.

An embedding of the sample index into the population index ensures sampling without replacement
is a probability law. Both index types may be empty. The conclusion concerns these specified
sampling laws, not the best approximation over every mixture of independent laws. Repeated
population values can strictly reduce the discrepancy of observed samples.

Measurability of the all-distinct event is explicit. It holds in particular for finite discrete
state spaces, where the identity population is the canonical example.

The counting and coupling argument is classical; the proof uses the existing sampling
construction, exact injection count, and total-variation API, following P. Diaconis and
D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8 (1980), 745–764.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {ι κ : Type*} [MeasurableSpace κ] [MeasurableSingletonClass κ]
  {α : Type*} [MeasurableSpace α]

/-- Sampling without replacement from a population of distinct values gives the all-distinct
event probability one whenever an injective selection exists. -/
theorem sampleWithoutReplacement_dirac_apply_injective [Finite κ] (x : κ → α)
    (hx : Function.Injective x) (e : ι ↪ κ)
    (hA : MeasurableSet {f : ι → α | Function.Injective f}) :
    sampleWithoutReplacement (ι := ι) (Measure.dirac x)
      {f | Function.Injective f} = 1 := by
  have : Finite ι := Finite.of_injective e e.injective
  have hpre : (fun k : ι → κ => fun i => x (k i)) ⁻¹' {f | Function.Injective f} =
      {k | Function.Injective k} := by
    ext k
    exact hx.of_comp_iff k
  have hmap : Measurable (fun k : ι → κ => fun i => x (k i)) :=
    measurable_reindexPopulation.comp measurable_prodMk_right
  rw [sampleWithoutReplacement_def, samplePopulation_dirac,
    Measure.map_apply hmap hA, hpre]
  exact uniformOn_self (Set.toFinite _) ⟨e, e.injective⟩

variable [Fintype ι] [Fintype κ]

/-- Sampling with replacement from a population of distinct values gives the all-distinct
event the injection-count mass. This formula also covers oversampling and empty selection spaces;
it is a probability when a selection exists. -/
@[simp]
theorem sampleWithReplacement_dirac_apply_injective (x : κ → α)
    (hx : Function.Injective x) (hA : MeasurableSet {f : ι → α | Function.Injective f}) :
    sampleWithReplacement (ι := ι) (Measure.dirac x) {f | Function.Injective f} =
      (Fintype.card κ).descFactorial (Fintype.card ι) /
        (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι := by
  have hpre : (fun k : ι → κ => fun i => x (k i)) ⁻¹' {f | Function.Injective f} =
      {k | Function.Injective k} := by
    ext k
    exact hx.of_comp_iff k
  have hmap : Measurable (fun k : ι → κ => fun i => x (k i)) :=
    measurable_reindexPopulation.comp measurable_prodMk_right
  rw [sampleWithReplacement_eq_samplePopulation_uniformOn, samplePopulation_dirac,
    Measure.map_apply hmap hA, hpre]
  exact uniformOn_injective_apply_eq

/-- The signed-measure total variation between the two sampling laws of a distinct population
is exactly twice the collision probability. This is sharpness for these sampling laws, not an
optimality statement over all possible product-mixture approximations. -/
theorem totalVariation_sampleWithoutReplacement_sub_sampleWithReplacement_dirac_eq_collision
    (x : κ → α) (hx : Function.Injective x) (e : ι ↪ κ)
    (hA : MeasurableSet {f : ι → α | Function.Injective f}) :
    ((sampleWithoutReplacement (ι := ι) (Measure.dirac x)).toSignedMeasure -
      (sampleWithReplacement (ι := ι) (Measure.dirac x)).toSignedMeasure).totalVariation
      Set.univ =
        2 * (1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
          (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι) := by
  let _ : Nonempty (ι → κ) := ⟨e⟩
  let _ := isProbabilityMeasure_sampleWithoutReplacement (Measure.dirac x) e
  let _ := isProbabilityMeasure_sampleWithReplacement (ι := ι) (Measure.dirac x)
  let s := (sampleWithoutReplacement (ι := ι) (Measure.dirac x)).toSignedMeasure -
    (sampleWithReplacement (ι := ι) (Measure.dirac x)).toSignedMeasure
  apply le_antisymm
  · rw [two_mul]
    apply Measure.totalVariation_toSignedMeasure_sub_univ_le
    · intro A hA
      simpa using
        sampleWithoutReplacement_le_sampleWithReplacement_add_collision
          (ρ := Measure.dirac x) hA
    · intro A hA
      simpa using
        sampleWithReplacement_le_sampleWithoutReplacement_add_collision
          (ρ := Measure.dirac x) hA
  · have hwithout := sampleWithoutReplacement_dirac_apply_injective x hx e hA
    have hwith := sampleWithReplacement_dirac_apply_injective x hx hA
    have hlower :
        1 - (Fintype.card κ).descFactorial (Fintype.card ι) /
            (Fintype.card κ : ℝ≥0∞) ^ Fintype.card ι ≤
          s.toJordanDecomposition.posPart Set.univ := by
      rw [Measure.toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_iSup,
        ← hwithout, ← hwith]
      exact le_iSup₂_of_le _ hA le_rfl
    rw [SignedMeasure.totalVariation, Measure.add_apply,
      ← Measure.toJordanDecomposition_toSignedMeasure_sub_posPart_univ_eq_negPart_univ
        (by simp)]
    simpa [two_mul] using add_le_add hlower hlower

end TauCeti.Probability
