/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Congr

/-!
# Entropy of product systems: the lower bound

For measure-preserving maps `T` of `(X, μ)` and `S` of `(Y, ν)` with `μ`, `ν` probability
measures, a label `a` on `X` and a label `b` on `Y` give the product label `(a, b)` on `X × Y`.
Under `μ.prod ν` its two coordinates are independent (`ProbabilityTheory.indepFun_prod`), and so
are the itineraries of the two coordinates, so entropies and entropy rates add:
`H(join_n (a, b)) = H(join_n a) + H(join_n b)` and
`h_{μ × ν}(T × S, (a, b)) = h_μ(T, a) + h_ν(S, b)`. Taking suprema gives the lower bound
`h_μ(T) + h_ν(S) ≤ h_{μ × ν}(T × S)` of the product formula.

The reverse inequality needs approximation of every label on `X × Y` by product labels, from the
generator theory, and is not proved here.

## Main results

* `TauCeti.countablePartitionEntropy_iteratedPartitionLabel_prodMap`: the length-`n` itinerary of
  `(a, b)` under `T × S` has entropy `H(join_n a) + H(join_n b)`, from
  `TauCeti.countablePartitionEntropy_prod`.
* `TauCeti.partitionEntropyRate_prodMap`: `h_{μ × ν}(T × S, (a, b)) = h_μ(T, a) + h_ν(S, b)`.
* `TauCeti.measureEntropy_add_le_measureEntropy_prodMap`:
  `h_μ(T) + h_ν(S) ≤ h_{μ × ν}(T × S)`.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Problem 4.12, p. 131.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X Y ι κ : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y} {μ : Measure X}
  {ν : Measure Y}

/-- The itinerary of the product label under the product map is the pair of the itineraries of
the two coordinates, regrouped. -/
theorem iteratedPartitionLabel_prodMap (T : X → X) (S : Y → Y) (a : X → ι) (b : Y → κ)
    (n : ℕ) :
    iteratedPartitionLabel (Prod.map T S) (fun p ↦ (a p.1, b p.2)) n =
      (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ ι) (fun _ ↦ κ)).symm ∘
        fun p ↦ (iteratedPartitionLabel T a n p.1, iteratedPartitionLabel S b n p.2) := by
  funext p k
  simp [Prod.map_iterate]

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
  [MeasurableSpace κ] [MeasurableSingletonClass κ] [Countable κ]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Product itineraries.** Under a product of probability measures, the length-`n` itinerary of
a product label under a product map has entropy equal to the sum of the entropies of the
coordinate itineraries, for any measurable maps `T` and `S` (not necessarily measure-preserving).
-/
theorem countablePartitionEntropy_iteratedPartitionLabel_prodMap {T : X → X} {S : Y → Y}
    (hT : Measurable T) (hS : Measurable S) {a : X → ι} {b : Y → κ} (ha : Measurable a)
    (hb : Measurable b) (n : ℕ) :
    countablePartitionEntropy (μ.prod ν)
        (iteratedPartitionLabel (Prod.map T S) (fun p ↦ (a p.1, b p.2)) n) =
      countablePartitionEntropy μ (iteratedPartitionLabel T a n) +
        countablePartitionEntropy ν (iteratedPartitionLabel S b n) := by
  rw [iteratedPartitionLabel_prodMap,
    countablePartitionEntropy_comp_of_injective _ (Equiv.injective _)]
  exact countablePartitionEntropy_prod (measurable_iteratedPartitionLabel hT ha n)
    (measurable_iteratedPartitionLabel hS hb n)

/-- **Rates of product labels.** For measure-preserving maps of probability spaces and
measurable countable labels, the entropy rate of the product label under the product map is the
sum of the rates: `h_{μ × ν}(T × S, (a, b)) = h_μ(T, a) + h_ν(S, b)`. -/
theorem partitionEntropyRate_prodMap {T : X → X} {S : Y → Y} (hT : MeasurePreserving T μ μ)
    (hS : MeasurePreserving S ν ν) {a : X → ι} {b : Y → κ} (ha : Measurable a)
    (hb : Measurable b) :
    partitionEntropyRate (μ.prod ν) (Prod.map T S) (fun p ↦ (a p.1, b p.2)) =
      partitionEntropyRate μ T a + partitionEntropyRate ν S b := by
  have hTS : MeasurePreserving (Prod.map T S) (μ.prod ν) (μ.prod ν) := hT.prod hS
  refine tendsto_nhds_unique
    (tendsto_partitionEntropyRate hTS ((ha.comp measurable_fst).prodMk (hb.comp measurable_snd)))
    ?_
  have h := (tendsto_partitionEntropyRate hT ha).add (tendsto_partitionEntropyRate hS hb)
  refine h.congr fun n ↦ ?_
  rw [countablePartitionEntropy_iteratedPartitionLabel_prodMap hT.measurable hS.measurable ha hb,
    ENNReal.add_div]

/-- **Product lower bound.** For measure-preserving maps of probability spaces, the
Kolmogorov–Sinai entropy of the product map is at least the sum of the entropies:
`h_μ(T) + h_ν(S) ≤ h_{μ × ν}(T × S)`. -/
theorem measureEntropy_add_le_measureEntropy_prodMap {T : X → X} {S : Y → Y}
    (hT : MeasurePreserving T μ μ) (hS : MeasurePreserving S ν ν) :
    measureEntropy μ T + measureEntropy ν S ≤ measureEntropy (μ.prod ν) (Prod.map T S) := by
  have key : ∀ a : X → ℕ, Measurable a ∧ countablePartitionEntropy μ a ≠ ∞ →
      ∀ b : Y → ℕ, Measurable b ∧ countablePartitionEntropy ν b ≠ ∞ →
        partitionEntropyRate μ T a + partitionEntropyRate ν S b ≤
          measureEntropy (μ.prod ν) (Prod.map T S) := fun a ha b hb ↦ by
    rw [← partitionEntropyRate_prodMap hT hS ha.1 hb.1]
    refine partitionEntropyRate_le_measureEntropy_of_countable _
      ((ha.1.comp measurable_fst).prodMk (hb.1.comp measurable_snd)) ?_
    rw [countablePartitionEntropy_prod ha.1 hb.1]
    exact ENNReal.add_ne_top.mpr ⟨ha.2, hb.2⟩
  have hsplit : measureEntropy μ T + measureEntropy ν S =
      (⨆ (a : X → ℕ) (_ : Measurable a ∧ countablePartitionEntropy μ a ≠ ∞),
          partitionEntropyRate μ T a) +
        (⨆ (b : Y → ℕ) (_ : Measurable b ∧ countablePartitionEntropy ν b ≠ ∞),
          partitionEntropyRate ν S b) := by
    simp only [measureEntropy_def, iSup_and]
  rw [hsplit]
  exact ENNReal.biSup_add_biSup_le'
    ⟨fun _ ↦ 0, measurable_const, by simp [countablePartitionEntropy_const]⟩
    ⟨fun _ ↦ 0, measurable_const, by simp [countablePartitionEntropy_const]⟩ key

end TauCeti
