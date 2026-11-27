/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.FinitePartition
public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Iterate
public import TauCeti.InformationTheory.PartitionEntropy.Mismatch
import Mathlib.MeasureTheory.Measure.Real
import TauCeti.MeasureTheory.Measure.MonotoneApproximation

/-!
# The Kolmogorov–Sinai theorem for one-sided generators

A measurable countable label `ξ` of finite entropy is a one-sided generator of a measure-preserving
map `T` when the σ-algebras of the labels `ξ ∘ T^[k]`, `k : ℕ`, generate the σ-algebra of `X`
modulo `μ`-null sets. The Kolmogorov–Sinai theorem says that the entropy rate of such a generator
is the Kolmogorov–Sinai entropy: `h_μ(T) = h_μ(T, ξ)`.

The proof approximates every finite label `η` by labels `b` that factor through a finite
itinerary of `ξ` (`TauCeti.exists_measure_ne_le_of_monotone`, applied to the increasing
σ-algebras of the itineraries): the probability that `η` and `b` disagree can be made arbitrarily
small, and then so can the conditional entropy `H(η | b)`
(`TauCeti.tendsto_countablePartitionEntropy_mismatchLabel`). The bound
`h(T, η) ≤ h(T, b) + H(η | b)` of `TauCeti.partitionEntropyRate_le_add_conditionalPartitionEntropy`,
the bound `h(T, join_N ξ) ≤ h(T, ξ)` of `TauCeti.partitionEntropyRate_iteratedPartitionLabel_le`,
and the finite-partition formula `TauCeti.measureEntropy_eq_iSup_fin` then give the theorem.

## Main results

* `TauCeti.exists_measure_ne_comp_iteratedPartitionLabel_le`: for a one-sided generator `ξ`, every
  measurable finite label agrees, outside a set of small measure, with a label factoring through an
  itinerary of `ξ`.
* `TauCeti.partitionEntropyRate_le_of_generator`: `h(T, η) ≤ h(T, ξ)` for every measurable finite
  label `η` and one-sided generator `ξ`.
* `TauCeti.measureEntropy_eq_partitionEntropyRate_of_generator`: the Kolmogorov–Sinai theorem
  for one-sided generators.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Definition 4.4 and Theorem 4.4, p. 111
  (a one-sided generator there is a strong generator). Entropies there are in base 2; here they
  use natural logarithms.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X ι κ : Type*} {mX : MeasurableSpace X} {μ : Measure X} {T : X → X}

/-- **Approximation through itineraries.** Let `ξ` be a measurable countable label whose shifted
labels `ξ ∘ T^[k]` generate the σ-algebra of `X` modulo `μ`-null sets. Every measurable label `η`
into a finite type is approximated by labels factoring through an itinerary of `ξ`: for `ε > 0`
there are `N` and `g` with `μ {η ≠ g ∘ join_N ξ} ≤ card κ * ε`. -/
theorem exists_measure_ne_comp_iteratedPartitionLabel_le [IsFiniteMeasure μ] (hT : Measurable T)
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {ξ : X → ι} (hξ : Measurable ξ)
    (hgen : ∀ s : Set X, MeasurableSet s → ∃ t : Set X,
      MeasurableSet[⨆ k : ℕ, MeasurableSpace.comap (fun x ↦ ξ (T^[k] x)) ‹_›] t ∧ s =ᵐ[μ] t)
    [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] {η : X → κ}
    (hη : Measurable η) (κ₀ : κ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (N : ℕ) (g : (Fin N → ι) → κ),
      μ {x | η x ≠ g (iteratedPartitionLabel T ξ N x)} ≤ Fintype.card κ * ε := by
  classical
  obtain ⟨N, b, hb, hlt⟩ := exists_measure_ne_le_of_monotone
    (monotone_comap_iteratedPartitionLabel T ξ)
    (fun N ↦ (measurable_iteratedPartitionLabel hT hξ N).comap_le)
    (fun s hs ↦ (hgen s hs).imp fun _ ht ↦
      ⟨iSup_comap_iterate_le_iSup_comap_iteratedPartitionLabel T ξ _ ht.1, ht.2⟩) hη hε
  -- Each fiber of `b` is the preimage of a set of itineraries, so `b` factors through them.
  choose S _ hS using hb
  set g : (Fin N → ι) → κ := fun w ↦ if h : ∃ i, w ∈ S i then h.choose else κ₀
  have hbg : b = g ∘ iteratedPartitionLabel T ξ N := by
    funext x
    have hx : ∃ i, iteratedPartitionLabel T ξ N x ∈ S i :=
      ⟨b x, by rw [← Set.mem_preimage, hS]; rfl⟩
    have := hx.choose_spec
    rw [← Set.mem_preimage, hS] at this
    simp only [Function.comp_apply, g, dite_eq_left_of_eq_true (eq_true hx)]
    exact this
  exact ⟨N, g, by rwa [hbg] at hlt⟩

/-- The entropy rate of a measurable finite label is at most that of a one-sided generator. -/
theorem partitionEntropyRate_le_of_generator [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ξ : X → ι} (hξ : Measurable ξ)
    (hgen : ∀ s : Set X, MeasurableSet s → ∃ t : Set X,
      MeasurableSet[⨆ k : ℕ, MeasurableSpace.comap (fun x ↦ ξ (T^[k] x)) ‹_›] t ∧ s =ᵐ[μ] t)
    [Finite κ] [MeasurableSpace κ] [MeasurableSingletonClass κ] {η : X → κ}
    (hη : Measurable η) :
    partitionEntropyRate μ T η ≤ partitionEntropyRate μ T ξ := by
  classical
  have := Fintype.ofFinite κ
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hε (k : ℕ) : (0 : ℝ≥0∞) < ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
    ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
  choose N g hg using fun k : ℕ ↦
    exists_measure_ne_comp_iteratedPartitionLabel_le hT.measurable hξ hgen hη (η x₀) (hε k)
  set b : ℕ → X → κ := fun k ↦ g k ∘ iteratedPartitionLabel T ξ (N k)
  have hζ (k : ℕ) := measurable_iteratedPartitionLabel hT.measurable hξ (N k)
  have hb (k : ℕ) : Measurable (b k) := (measurable_of_countable _).comp (hζ k)
  have hsmall : Tendsto (fun k ↦ μ.real {x | η x ≠ b k x}) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun k ↦ ?_)
      ((tendsto_const_div_atTop_nhds_zero_nat (Fintype.card κ : ℝ)).comp
        (tendsto_add_atTop_nat 1))
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.2 (by positivity))) (hg k)
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      ← div_eq_mul_inv] at this
    exact this
  have hkey (k : ℕ) : partitionEntropyRate μ T η ≤
      partitionEntropyRate μ T ξ + countablePartitionEntropy μ (mismatchLabel η (b k)) :=
    calc partitionEntropyRate μ T η
        ≤ partitionEntropyRate μ T (iteratedPartitionLabel T ξ (N k)) +
            conditionalPartitionEntropy μ η (iteratedPartitionLabel T ξ (N k)) :=
          partitionEntropyRate_le_add_conditionalPartitionEntropy hT hη (hζ k)
      _ ≤ partitionEntropyRate μ T ξ + conditionalPartitionEntropy μ η (b k) :=
          add_le_add (partitionEntropyRate_iteratedPartitionLabel_le hT hξ _)
            (conditionalPartitionEntropy_le_comp _ (hζ k) _)
      _ ≤ _ := add_le_add le_rfl
          (conditionalPartitionEntropy_le_countablePartitionEntropy_mismatchLabel hη (hb k))
  have hlim := (tendsto_const_nhds (x := partitionEntropyRate μ T ξ)).add
    (tendsto_countablePartitionEntropy_mismatchLabel hη hb hsmall)
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim hkey

/-- **The Kolmogorov–Sinai theorem.** Let `T` preserve a probability measure `μ`, and let `ξ` be a
measurable countable label of finite entropy that is a one-sided generator: the σ-algebras of the
labels `ξ ∘ T^[k]`, `k : ℕ`, generate the σ-algebra of `X` modulo `μ`-null sets. Then the
Kolmogorov–Sinai entropy is the entropy rate of `ξ` (Sarig 2023, Theorem 4.4). -/
theorem measureEntropy_eq_partitionEntropyRate_of_generator [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {ξ : X → ι} (hξ : Measurable ξ) (hH : countablePartitionEntropy μ ξ ≠ ∞)
    (hgen : ∀ s : Set X, MeasurableSet s → ∃ t : Set X,
      MeasurableSet[⨆ k : ℕ, MeasurableSpace.comap (fun x ↦ ξ (T^[k] x)) ‹_›] t ∧ s =ᵐ[μ] t) :
    measureEntropy μ T = partitionEntropyRate μ T ξ := by
  refine le_antisymm ?_ (partitionEntropyRate_le_measureEntropy_of_countable T hξ hH)
  rw [measureEntropy_eq_iSup_fin hT]
  exact iSup₂_le fun n η ↦ iSup_le fun hη ↦ partitionEntropyRate_le_of_generator hT hξ hgen hη

end TauCeti
