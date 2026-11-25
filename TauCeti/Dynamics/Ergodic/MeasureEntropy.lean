/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.PartitionEntropy
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Kolmogorov–Sinai entropy

For a map `T : X → X` and a countable label `a : X → ι`, the length-`n` itinerary
`iteratedPartitionLabel T a n` sends `x` to `(a x, a (T x), …, a (T^[n-1] x))`; it labels the join
of the partitions `T^[-k] a`, `k < n`. At `n = 0` it is the unique empty tuple.

* `TauCeti.partitionEntropyRate μ T a` is `⨅ n ≥ 1, H(iteratedPartitionLabel T a n) / n`, in
  `[0, ∞]`.
* `TauCeti.measureEntropy μ T`, the Kolmogorov–Sinai (measure-theoretic) entropy, is the supremum
  of these rates over the measurable labels `a : X → ℕ` of finite entropy. Every countable label
  space embeds in `ℕ` (`TauCeti.countablePartitionEntropy_comp_of_injective`). The value lies in
  `[0, ∞]`, so infinite entropy is retained.

## Main results

* `TauCeti.measurable_iteratedPartitionLabel`: itineraries of a measurable label under a
  measurable map are measurable.
* `TauCeti.measureEntropy_id`: the identity has entropy zero; its itineraries repeat one label.
* `TauCeti.measureEntropy_of_forall`: if every measurable label has entropy zero, for instance
  under a Dirac probability (`TauCeti.countablePartitionEntropy_dirac`) or the zero measure,
  then every map has entropy zero.

## References

* The definitions follow the roadmap GeometryOfNumbersAndQuadraticArithmetic, §4.2, Entropy and
  Haar measure on leaves.
-/

public section

open MeasureTheory Real Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X ι : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- The length-`n` itinerary of the label `a` under `T`: `x ↦ (a x, a (T x), …, a (T^[n-1] x))`.
It labels the join of the partitions given by `a ∘ T^[k]` for `k < n`. -/
def iteratedPartitionLabel (T : X → X) (a : X → ι) (n : ℕ) : X → (Fin n → ι) :=
  fun x k ↦ a (T^[k] x)

theorem iteratedPartitionLabel_apply (T : X → X) (a : X → ι) (n : ℕ) (x : X) (k : Fin n) :
    iteratedPartitionLabel T a n x k = a (T^[k] x) :=
  (rfl)

/-- Itineraries of a measurable label under a measurable map are measurable. -/
theorem measurable_iteratedPartitionLabel [MeasurableSpace ι] {T : X → X} (hT : Measurable T)
    {a : X → ι} (ha : Measurable a) (n : ℕ) : Measurable (iteratedPartitionLabel T a n) :=
  measurable_pi_iff.mpr fun k ↦ ha.comp (hT.iterate k)

/-- The entropy rate of the label `a` under `T`: the infimum over `n ≥ 1` of the entropy of the
length-`n` itinerary divided by `n`. -/
noncomputable def partitionEntropyRate (μ : Measure X) (T : X → X) (a : X → ι) : ℝ≥0∞ :=
  ⨅ n : ℕ, countablePartitionEntropy μ (iteratedPartitionLabel T a (n + 1)) / (n + 1)

theorem partitionEntropyRate_def (μ : Measure X) (T : X → X) (a : X → ι) :
    partitionEntropyRate μ T a =
      ⨅ n : ℕ, countablePartitionEntropy μ (iteratedPartitionLabel T a (n + 1)) / (n + 1) :=
  (rfl)

/-- The Kolmogorov–Sinai entropy of `T` with respect to `μ`: the supremum of the entropy rates of
the measurable labels `a : X → ℕ` of finite entropy. -/
noncomputable def measureEntropy (μ : Measure X) (T : X → X) : ℝ≥0∞ :=
  ⨆ (a : X → ℕ) (_ : Measurable a) (_ : countablePartitionEntropy μ a ≠ ∞),
    partitionEntropyRate μ T a

theorem measureEntropy_def (μ : Measure X) (T : X → X) :
    measureEntropy μ T = ⨆ (a : X → ℕ) (_ : Measurable a)
      (_ : countablePartitionEntropy μ a ≠ ∞), partitionEntropyRate μ T a :=
  (rfl)

/-- The rate of a measurable label of finite entropy is at most the measure entropy. -/
theorem partitionEntropyRate_le_measureEntropy {T : X → X} {a : X → ℕ} (ha : Measurable a)
    (hfin : countablePartitionEntropy μ a ≠ ∞) :
    partitionEntropyRate μ T a ≤ measureEntropy μ T :=
  le_iSup₂_of_le a ha (le_iSup_of_le hfin le_rfl)

/-- The entropy rate is at most the entropy of the label itself. -/
theorem partitionEntropyRate_le (μ : Measure X) (T : X → X) (a : X → ι) :
    partitionEntropyRate μ T a ≤ countablePartitionEntropy μ a := by
  refine iInf_le_of_le 0 ?_
  simp only [Nat.cast_zero, zero_add, div_one]
  rw [show iteratedPartitionLabel T a 1 = Function.const (Fin 1) ∘ a from
    funext fun x ↦ funext fun k ↦ by simp [iteratedPartitionLabel, Fin.fin_one_eq_zero k]]
  exact (countablePartitionEntropy_comp_of_injective a Function.const_injective).le

/-- Under the identity the length-`(n + 1)` itinerary is the label repeated `n + 1` times, and so
has the same entropy as the label. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_id (μ : Measure X) (a : X → ι)
    (n : ℕ) :
    countablePartitionEntropy μ (iteratedPartitionLabel id a (n + 1)) =
      countablePartitionEntropy μ a := by
  rw [show iteratedPartitionLabel id a (n + 1) = Function.const (Fin (n + 1)) ∘ a from
    funext fun x ↦ funext fun k ↦ by simp [iteratedPartitionLabel]]
  exact countablePartitionEntropy_comp_of_injective a Function.const_injective

/-- A label of finite entropy has rate zero under the identity. -/
theorem partitionEntropyRate_id {a : X → ι} (hfin : countablePartitionEntropy μ a ≠ ∞) :
    partitionEntropyRate μ id a = 0 := by
  rw [partitionEntropyRate_def]
  simp only [countablePartitionEntropy_iteratedPartitionLabel_id]
  have h : Tendsto (fun n : ℕ ↦ ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    refine (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)).congr fun n ↦ ?_
    simp
  have h' : Tendsto (fun n : ℕ ↦ countablePartitionEntropy μ a / ((n : ℝ≥0∞) + 1)) atTop
      (𝓝 0) := by
    simpa [div_eq_mul_inv] using ENNReal.Tendsto.const_mul h (Or.inr hfin)
  exact le_antisymm (ge_of_tendsto' h' fun n ↦ iInf_le _ n) bot_le

/-- The identity has Kolmogorov–Sinai entropy zero. -/
@[simp]
theorem measureEntropy_id : measureEntropy μ id = 0 := by
  simp only [measureEntropy_def]
  exact ENNReal.iSup_eq_zero.mpr fun a ↦ ENNReal.iSup_eq_zero.mpr fun _ ↦
    ENNReal.iSup_eq_zero.mpr fun hfin ↦ partitionEntropyRate_id hfin

/-- If every measurable label into `ℕ` has entropy zero, every map has entropy zero. -/
theorem measureEntropy_of_forall
    (h : ∀ a : X → ℕ, Measurable a → countablePartitionEntropy μ a = 0) (T : X → X) :
    measureEntropy μ T = 0 := by
  simp only [measureEntropy_def]
  exact ENNReal.iSup_eq_zero.mpr fun a ↦ ENNReal.iSup_eq_zero.mpr fun ha ↦
    ENNReal.iSup_eq_zero.mpr fun _ ↦ le_antisymm ((partitionEntropyRate_le μ T a).trans
      (h a ha).le) bot_le

/-- Under a Dirac probability every atom has mass `0` or `1`, so every partition has entropy
zero. -/
@[simp]
theorem countablePartitionEntropy_dirac [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {a : X → ι} (ha : Measurable a) (x : X) :
    countablePartitionEntropy (Measure.dirac x) a = 0 := by
  classical
  rw [countablePartitionEntropy_def]
  refine tsum_eq_zero_iff.mpr fun i ↦ ?_
  rw [measureReal_def, Measure.dirac_apply' _ (ha (measurableSet_singleton i))]
  by_cases h : x ∈ a ⁻¹' {i} <;> simp [h]

/-- The Kolmogorov–Sinai entropy of any map with respect to a Dirac probability is zero. -/
@[simp]
theorem measureEntropy_dirac (x : X) (T : X → X) : measureEntropy (Measure.dirac x) T = 0 :=
  measureEntropy_of_forall (fun _ ha ↦ countablePartitionEntropy_dirac ha x) T

/-- The Kolmogorov–Sinai entropy of any map with respect to the zero measure is zero. -/
@[simp]
theorem measureEntropy_zero_measure (T : X → X) : measureEntropy (0 : Measure X) T = 0 :=
  measureEntropy_of_forall (fun a _ ↦ countablePartitionEntropy_zero_measure a) T

end TauCeti
