/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Basic
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Almost-everywhere equal labels and relabeling of itineraries

A finite or countable measurable partition is given by a label `a : X → ι`, and its entropy
`TauCeti.countablePartitionEntropy μ a` only sees the masses of the atoms `a ⁻¹' {i}`, so the
entropies of labels and joins depend only on the label up to `μ`-almost-everywhere equality
(`TauCeti.countablePartitionEntropy_congr_ae`). This file records that, when `T` is
quasi-measure-preserving, the entropies of itineraries and the entropy rate depend only on the
label up to `μ`-almost-everywhere equality as well, and that relabeling a label by an injection,
for instance a finite alphabet into `ℕ`, changes neither its itinerary entropies nor its entropy
rate. Consequently the entropy rate of a measurable countable label of finite entropy, in
particular of a measurable finite label, is at most the Kolmogorov–Sinai entropy
`TauCeti.measureEntropy μ T`, which is defined with labels into `ℕ`.

## Main results

* `TauCeti.iteratedPartitionLabel_ae_eq`: almost-everywhere equality passes to itineraries under
  a quasi-measure-preserving map, hence `TauCeti.partitionEntropyRate_congr_ae`.
* `TauCeti.partitionEntropyRate_comp_of_injective`: relabeling by an injection does not change
  the entropy rate.
* `TauCeti.partitionEntropyRate_comp_le`: coarsening a countable label does not increase its
  entropy rate.
* `TauCeti.partitionEntropyRate_le_measureEntropy_of_countable` and
  `TauCeti.partitionEntropyRate_le_measureEntropy_of_finite`: the rate of a measurable countable
  label of finite entropy, or of a measurable finite label, is at most the measure entropy.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace TauCeti

variable {X ι ι' : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- Under a quasi-measure-preserving map, for instance a measure-preserving one, almost-everywhere
equal labels have almost-everywhere equal itineraries: preimages of null sets are null. -/
theorem iteratedPartitionLabel_ae_eq {T : X → X} (hT : QuasiMeasurePreserving T μ μ)
    {a a' : X → ι} (h : a =ᵐ[μ] a') (n : ℕ) :
    iteratedPartitionLabel T a n =ᵐ[μ] iteratedPartitionLabel T a' n := by
  have hk : ∀ k : Fin n, ∀ᵐ x ∂μ, a (T^[k] x) = a' (T^[k] x) := fun k ↦
    (hT.iterate k).ae_eq_comp h
  filter_upwards [ae_all_iff.mpr hk] with x hx
  exact funext fun k ↦ by simpa using hx k

/-- Under a quasi-measure-preserving map, almost-everywhere equal labels have equal itinerary
entropies. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_congr_ae {T : X → X}
    (hT : QuasiMeasurePreserving T μ μ) {a a' : X → ι} (h : a =ᵐ[μ] a') (n : ℕ) :
    countablePartitionEntropy μ (iteratedPartitionLabel T a n) =
      countablePartitionEntropy μ (iteratedPartitionLabel T a' n) :=
  countablePartitionEntropy_congr_ae (iteratedPartitionLabel_ae_eq hT h n)

/-- Under a quasi-measure-preserving map, almost-everywhere equal labels have equal entropy
rates. -/
theorem partitionEntropyRate_congr_ae {T : X → X} (hT : QuasiMeasurePreserving T μ μ)
    {a a' : X → ι} (h : a =ᵐ[μ] a') :
    partitionEntropyRate μ T a = partitionEntropyRate μ T a' := by
  simp only [partitionEntropyRate_def,
    countablePartitionEntropy_iteratedPartitionLabel_congr_ae hT h]

/-- Relabeling by an injection does not change the itinerary entropies. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_comp_of_injective (T : X → X)
    (a : X → ι) {e : ι → ι'} (he : Function.Injective e) (n : ℕ) :
    countablePartitionEntropy μ (iteratedPartitionLabel T (e ∘ a) n) =
      countablePartitionEntropy μ (iteratedPartitionLabel T a n) := by
  rw [iteratedPartitionLabel_comp]
  exact countablePartitionEntropy_comp_of_injective _ he.comp_left

/-- Relabeling by an injection does not change the entropy rate. -/
theorem partitionEntropyRate_comp_of_injective (T : X → X) (a : X → ι) {e : ι → ι'}
    (he : Function.Injective e) :
    partitionEntropyRate μ T (e ∘ a) = partitionEntropyRate μ T a := by
  simp only [partitionEntropyRate_def,
    countablePartitionEntropy_iteratedPartitionLabel_comp_of_injective T a he]

/-- **Coarsening.** Coarsening a countable label does not increase its entropy rate, for every
measure and every map. -/
theorem partitionEntropyRate_comp_le [Countable ι] (T : X → X) (a : X → ι) (f : ι → ι') :
    partitionEntropyRate μ T (f ∘ a) ≤ partitionEntropyRate μ T a := by
  simp only [partitionEntropyRate_def, iteratedPartitionLabel_comp]
  gcongr
  exact countablePartitionEntropy_comp_le _ _

/-- The entropy rate of a measurable countable label of finite entropy is at most the
Kolmogorov–Sinai entropy: embed the alphabet into `ℕ`. -/
theorem partitionEntropyRate_le_measureEntropy_of_countable [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (T : X → X) {a : X → ι} (ha : Measurable a)
    (hfin : countablePartitionEntropy μ a ≠ ∞) :
    partitionEntropyRate μ T a ≤ measureEntropy μ T := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  rw [← partitionEntropyRate_comp_of_injective T a he]
  refine partitionEntropyRate_le_measureEntropy ((measurable_of_countable e).comp ha) ?_
  rwa [countablePartitionEntropy_comp_of_injective a he]

/-- The entropy rate of a measurable label into a finite alphabet is at most the
Kolmogorov–Sinai entropy. -/
theorem partitionEntropyRate_le_measureEntropy_of_finite [Finite ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (T : X → X) {a : X → ι} (ha : Measurable a) :
    partitionEntropyRate μ T a ≤ measureEntropy μ T :=
  partitionEntropyRate_le_measureEntropy_of_countable T ha
    (countablePartitionEntropy_ne_top μ a)

end TauCeti
