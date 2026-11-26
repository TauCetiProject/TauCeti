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
* `TauCeti.measureEntropy_eq_zero_of_forall`: if every measurable label has entropy zero, for
  instance under a Dirac probability (`TauCeti.countablePartitionEntropy_dirac`) or the zero
  measure, then every map has entropy zero.

## References

* G. A. Margulis and G. M. Tomanov, Invariant measures for actions of unipotent groups over local
  fields on homogeneous spaces, Invent. Math. 116 (1994), 347–392, §9.3, pp. 381–383,
  doi:10.1007/BF01231565.
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

@[simp]
theorem iteratedPartitionLabel_apply (T : X → X) (a : X → ι) (n : ℕ) (x : X) (k : Fin n) :
    iteratedPartitionLabel T a n x k = a (T^[k] x) :=
  (rfl)

/-- The length-zero itinerary is the unique empty tuple. -/
@[simp]
theorem iteratedPartitionLabel_zero (T : X → X) (a : X → ι) :
    iteratedPartitionLabel T a 0 = fun _ ↦ Fin.elim0 :=
  funext fun _ ↦ funext fun k ↦ k.elim0

/-- The length-one itinerary is the label itself, viewed as a constant tuple. -/
theorem iteratedPartitionLabel_one (T : X → X) (a : X → ι) :
    iteratedPartitionLabel T a 1 = Function.const (Fin 1) ∘ a :=
  funext fun x ↦ funext fun k ↦ by simp [Fin.fin_one_eq_zero k]

/-- Under the identity every itinerary repeats the label. -/
theorem iteratedPartitionLabel_id (a : X → ι) (n : ℕ) :
    iteratedPartitionLabel id a n = Function.const (Fin n) ∘ a :=
  funext fun x ↦ funext fun k ↦ by simp

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

/-- The entropy rate is at most the entropy of every positive-length itinerary divided by its
length. -/
theorem partitionEntropyRate_le_div {n : ℕ} (hn : 0 < n) (μ : Measure X) (T : X → X)
    (a : X → ι) :
    partitionEntropyRate μ T a ≤
      countablePartitionEntropy μ (iteratedPartitionLabel T a n) / n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [zero_add, Nat.cast_succ]
  exact iInf_le _ m

/-- A lower bound for the entropy rate is a lower bound for every normalised itinerary entropy of
positive length. -/
theorem le_partitionEntropyRate_iff {T : X → X} {a : X → ι} {c : ℝ≥0∞} :
    c ≤ partitionEntropyRate μ T a ↔
      ∀ n, 0 < n → c ≤ countablePartitionEntropy μ (iteratedPartitionLabel T a n) / n := by
  refine ⟨fun h n hn ↦ h.trans (partitionEntropyRate_le_div hn μ T a), fun h ↦ le_iInf fun n ↦ ?_⟩
  have := h (n + 1) n.succ_pos
  rwa [Nat.cast_succ] at this

/-- The Kolmogorov–Sinai entropy of `T` with respect to `μ`: the supremum of the entropy rates of
the measurable labels `a : X → ℕ` of finite entropy. -/
noncomputable def measureEntropy (μ : Measure X) (T : X → X) : ℝ≥0∞ :=
  ⨆ (a : X → ℕ) (_ : Measurable a) (_ : countablePartitionEntropy μ a ≠ ∞),
    partitionEntropyRate μ T a

theorem measureEntropy_def (μ : Measure X) (T : X → X) :
    measureEntropy μ T = ⨆ (a : X → ℕ) (_ : Measurable a)
      (_ : countablePartitionEntropy μ a ≠ ∞), partitionEntropyRate μ T a :=
  (rfl)

/-- An upper bound for the measure entropy is an upper bound for the rate of every measurable
label into `ℕ` of finite entropy. -/
theorem measureEntropy_le_iff {T : X → X} {c : ℝ≥0∞} :
    measureEntropy μ T ≤ c ↔ ∀ a : X → ℕ, Measurable a → countablePartitionEntropy μ a ≠ ∞ →
      partitionEntropyRate μ T a ≤ c := by
  simp only [measureEntropy_def, iSup_le_iff]

/-- The rate of a measurable label of finite entropy is at most the measure entropy. -/
theorem partitionEntropyRate_le_measureEntropy {T : X → X} {a : X → ℕ} (ha : Measurable a)
    (hfin : countablePartitionEntropy μ a ≠ ∞) :
    partitionEntropyRate μ T a ≤ measureEntropy μ T :=
  le_iSup₂_of_le a ha (le_iSup_of_le hfin le_rfl)

/-- The entropy rate is at most the entropy of the label itself. -/
theorem partitionEntropyRate_le (μ : Measure X) (T : X → X) (a : X → ι) :
    partitionEntropyRate μ T a ≤ countablePartitionEntropy μ a := by
  refine (partitionEntropyRate_le_div one_pos μ T a).trans_eq ?_
  rw [Nat.cast_one, div_one, iteratedPartitionLabel_one,
    countablePartitionEntropy_comp_of_injective a Function.const_injective]

/-- Under the identity the length-`(n + 1)` itinerary is the label repeated `n + 1` times, and so
has the same entropy as the label. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_id (μ : Measure X) (a : X → ι)
    (n : ℕ) :
    countablePartitionEntropy μ (iteratedPartitionLabel id a (n + 1)) =
      countablePartitionEntropy μ a := by
  rw [iteratedPartitionLabel_id]
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
theorem measureEntropy_id : measureEntropy μ id = 0 :=
  nonpos_iff_eq_zero.mp <|
    measureEntropy_le_iff.mpr fun _ _ hfin ↦ (partitionEntropyRate_id hfin).le

/-- If every measurable label into `ℕ` has entropy zero, every map has entropy zero. -/
theorem measureEntropy_eq_zero_of_forall
    (h : ∀ a : X → ℕ, Measurable a → countablePartitionEntropy μ a = 0) (T : X → X) :
    measureEntropy μ T = 0 :=
  nonpos_iff_eq_zero.mp (measureEntropy_le_iff.mpr fun a ha _ ↦
    (partitionEntropyRate_le μ T a).trans (h a ha).le)

/-- The Kolmogorov–Sinai entropy of any map with respect to a Dirac probability is zero. -/
@[simp]
theorem measureEntropy_dirac (x : X) (T : X → X) : measureEntropy (Measure.dirac x) T = 0 :=
  measureEntropy_eq_zero_of_forall (fun a _ ↦ countablePartitionEntropy_dirac a x) T

/-- The Kolmogorov–Sinai entropy of any map with respect to the zero measure is zero. -/
@[simp]
theorem measureEntropy_zero_measure (T : X → X) : measureEntropy (0 : Measure X) T = 0 :=
  measureEntropy_eq_zero_of_forall (fun a _ ↦ countablePartitionEntropy_zero_measure a) T

end TauCeti
