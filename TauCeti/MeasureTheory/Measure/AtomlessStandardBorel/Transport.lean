/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.AtomlessStandardBorel
public import TauCeti.MeasureTheory.Measure.UnitIntervalMap

/-!
# Transport from atomless standard Borel spaces

An atomless standard Borel probability space admits a measurable map with any prescribed
standard Borel probability law. The source is measure-preservingly mapped to the unit interval
by `MeasureTheory.Measure.exists_mpModNull_equiv_unitInterval`, and the requested law is
realized from that interval by `MeasureTheory.Measure.exists_measurePreserving_from_unitInterval`.
The resulting map may collapse sets of positive measure when the target has atoms.

Normalization extends this to finite measures of equal mass, including zero mass when the
target is nonempty. On a countable measurable source partition, one measurable map can
simultaneously realize a prescribed law of matching mass on each cell.

This is the nonatomic feasibility result for the Monge transport problem. It also supplies
the map realization needed when approximating couplings by graph plans.

See S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*,
Theorems A.7 and A.9, for the two standard Borel transport results being composed.
-/

public section

open Function MeasureTheory

namespace MeasureTheory.Measure

/-- Every probability law on a standard Borel target is the image of an atomless standard Borel
probability law under a measurable map. The target may have atoms.

Mathlib's `Measure.exists_measurable_map_eq` starts from the unit interval; the atomless source
is mapped to that interval first. -/
theorem exists_measurePreserving_of_nullSingleton
    {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    ∃ T : X → Y, MeasurePreserving T μ ν := by
  obtain ⟨f, -, hf, -⟩ := μ.exists_mpModNull_equiv_unitInterval
  obtain ⟨g, hg⟩ := ν.exists_measurePreserving_from_unitInterval
  exact ⟨g ∘ f, hg.comp hf⟩

/-- An atomless finite measure on a standard Borel space can be mapped measurably to any
standard Borel measure of the same total mass. The nonempty target permits a map even when
both measures vanish. -/
theorem exists_measurePreserving_of_nullSingleton_of_measure_univ_eq
    {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (ν : Measure Y) (h : μ Set.univ = ν Set.univ) :
    ∃ T : X → Y, MeasurePreserving T μ ν := by
  classical
  by_cases hμ : μ = 0
  · have hν : ν = 0 := Measure.measure_univ_eq_zero.mp (by simpa [hμ] using h.symm)
    exact ⟨fun _ ↦ Classical.choice inferInstance, measurable_const, by simp [hμ, hν]⟩
  have hμ0 : μ Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hμ
  have hμtop : μ Set.univ ≠ ⊤ := measure_ne_top μ Set.univ
  have : IsProbabilityMeasure ((μ Set.univ)⁻¹ • μ) :=
    ⟨by simp [Measure.smul_apply, ENNReal.inv_mul_cancel hμ0 hμtop]⟩
  have : IsProbabilityMeasure ((μ Set.univ)⁻¹ • ν) :=
    ⟨by simp [Measure.smul_apply, ← h, ENNReal.inv_mul_cancel hμ0 hμtop]⟩
  have : NullSingletonClass ((μ Set.univ)⁻¹ • μ) :=
    ⟨fun x ↦ by simp [Measure.smul_apply]⟩
  obtain ⟨T, hT⟩ := exists_measurePreserving_of_nullSingleton
    ((μ Set.univ)⁻¹ • μ) ((μ Set.univ)⁻¹ • ν)
  exact ⟨T, by simpa [smul_smul, ENNReal.mul_inv_cancel hμ0 hμtop] using
    hT.smul_measure (μ Set.univ)⟩

/-- Realize prescribed laws cell by cell on a countable measurable partition of an atomless
finite standard Borel measure. Each cell has the total mass of its prescribed law. One
measurable map simultaneously realizes all these laws, and their sum is its full image law. -/
theorem exists_measurePreserving_sum_of_nullSingleton
    {X Y ι : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] [Countable ι]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {A : ι → Set X} (hAm : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) (hAu : (⋃ i, A i) = Set.univ)
    (ν : ι → Measure Y) (hmass : ∀ i, μ (A i) = ν i Set.univ) :
    ∃ T : X → Y, MeasurePreserving T μ (Measure.sum ν) ∧
      ∀ i, MeasurePreserving T (μ.restrict (A i)) (ν i) := by
  classical
  choose T hT using fun i ↦ exists_measurePreserving_of_nullSingleton_of_measure_univ_eq
    (μ.restrict (A i)) (ν i) (by simpa using hmass i)
  have hcompat (i j : ι) (x : X) (hi : x ∈ A i) (hj : x ∈ A j) : T i x = T j x := by
    by_cases hij : i = j
    · subst j; rfl
    · exact (Set.disjoint_left.mp (hAd hij) hi hj).elim
  let S := Set.liftCover A (fun i x ↦ T i x) hcompat hAu
  have hSm : Measurable S := measurable_liftCover A hAm _
    (fun i ↦ (hT i).measurable.comp measurable_subtype_coe) hcompat hAu
  have hS (i : ι) : MeasurePreserving S (μ.restrict (A i)) (ν i) :=
    (hT i).congr hSm <| (ae_restrict_mem (hAm i)).mono fun x hx ↦
      (Set.liftCover_of_mem (f := fun i x ↦ T i x) (hf := hcompat) (hS := hAu) hx).symm
  refine ⟨S, ⟨hSm, ?_⟩, hS⟩
  have hμ : μ = Measure.sum (fun i ↦ μ.restrict (A i)) := by
    rw [← Measure.restrict_iUnion hAd hAm, hAu, Measure.restrict_univ]
  rw [hμ, Measure.map_sum hSm.aemeasurable]
  exact congrArg Measure.sum (funext fun i ↦ (hS i).map_eq)

end MeasureTheory.Measure
