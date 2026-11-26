/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Basic
public import Mathlib.Probability.Independence.Basic
import TauCeti.InformationTheory.PartitionEntropy.Independence

/-!
# Entropy rate of a label with independent iterates

The entropy rate of a label is at most its entropy, `h_μ(T, a) ≤ H_μ(a)`
(`TauCeti.partitionEntropyRate_le`). For a measure-preserving map of a probability space and a
measurable countable label, equality holds exactly when every itinerary has
the largest possible entropy, `H(join_n a) = n * H(a)`
(`TauCeti.partitionEntropyRate_eq_iff_forall`). This holds when the labels `a ∘ T^[k]` are
independent (`TauCeti.partitionEntropyRate_of_iIndepFun`): the itinerary of length `n + 1` is the
join of the itinerary of length `n` with the independent label `a ∘ T^[n]`.

For a label with finitely many values the converse holds
(`TauCeti.iIndepFun_of_partitionEntropyRate_eq`): if `H(join_n a) = n * H(a)` for every `n`, then
`H(join_{n+1} a) = H(join_n a) + H(a ∘ T^[n])`, so by the equality case of subadditivity
(`TauCeti.indepFun_of_countablePartitionEntropy_pair_eq_add`) the itinerary of length `n` is
independent of `a ∘ T^[n]`, and these independences combine into independence of all the labels
`a ∘ T^[k]`.

## Main results

* `TauCeti.countablePartitionEntropy_iteratedPartitionLabel_of_iIndepFun`: if the labels
  `a ∘ T^[k]` are independent, `H(join_n a) = n * H(a)`.
* `TauCeti.partitionEntropyRate_of_iIndepFun`: if the labels `a ∘ T^[k]` are independent, the
  rate of `a` is its entropy.
* `TauCeti.iIndepFun_of_forall_countablePartitionEntropy_iteratedPartitionLabel_eq`: for a label
  with finitely many values, `H(join_n a) = n * H(a)` for all `n` forces the labels `a ∘ T^[k]` to
  be independent.
* `TauCeti.partitionEntropyRate_eq_iff_iIndepFun`: for a label with finitely many values, the rate
  of `a` is its entropy exactly when the labels `a ∘ T^[k]` are independent.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Proposition 4.3, p. 106.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

variable {X ι : Type*} {mX : MeasurableSpace X} {μ : Measure X} {T : X → X} {a : X → ι}
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]

/-- **Independent iterates.** For a measure-preserving map of a probability space and a
measurable countable label `a` whose iterates `a ∘ T^[k]` are independent, the length-`n`
itinerary has entropy `n * H(a)`. -/
theorem countablePartitionEntropy_iteratedPartitionLabel_of_iIndepFun
    (hT : MeasurePreserving T μ μ) (ha : Measurable a)
    (hind : iIndepFun (fun k x ↦ a (T^[k] x)) μ) (n : ℕ) :
    countablePartitionEntropy μ (iteratedPartitionLabel T a n) =
      n * countablePartitionEntropy μ a := by
  have hmeas : ∀ k, Measurable fun x ↦ a (T^[k] x) := fun k ↦ ha.comp (hT.measurable.iterate k)
  have := hind.isProbabilityMeasure
  induction n with
  | zero => simp [iteratedPartitionLabel_zero]
  | succ n ih =>
    have hb := measurable_iteratedPartitionLabel hT.measurable ha
    -- The first `n` labels are independent of the label at time `n`.
    have hindep : IndepFun (iteratedPartitionLabel T a n)
        (fun x ↦ iteratedPartitionLabel T a 1 (T^[n] x)) μ := by
      have h := hind.indepFun_finset (Finset.range n) {n} (by simp) hmeas
      have hφ : Measurable fun (g : Finset.range n → ι) (k : Fin n) ↦
          g ⟨k, Finset.mem_range.mpr k.isLt⟩ :=
        measurable_pi_iff.mpr fun _ ↦ measurable_pi_apply _
      have hψ : Measurable fun (g : ({n} : Finset ℕ) → ι) (_ : Fin 1) ↦
          g ⟨n, Finset.mem_singleton_self n⟩ :=
        measurable_pi_iff.mpr fun _ ↦ measurable_pi_apply _
      convert h.comp hφ hψ using 1
      · funext x k
        simp
      · funext x k
        simp
    rw [countablePartitionEntropy_iteratedPartitionLabel_add]
    refine (countablePartitionEntropy_pair_of_indepFun (hb n)
      ((hb 1).comp (hT.measurable.iterate n)) hindep).trans ?_
    rw [ih, countablePartitionEntropy_comp_of_measurePreserving (hT.iterate n) (hb 1),
      countablePartitionEntropy_iteratedPartitionLabel_one, Nat.cast_succ, add_mul, one_mul]

/-- **Independent iterates.** For a measure-preserving map of a probability space and a
measurable countable label whose iterates `a ∘ T^[k]` are independent, the entropy rate is the
entropy: `h_μ(T, a) = H(a)`. -/
theorem partitionEntropyRate_of_iIndepFun (hT : MeasurePreserving T μ μ) (ha : Measurable a)
    (hind : iIndepFun (fun k x ↦ a (T^[k] x)) μ) :
    partitionEntropyRate μ T a = countablePartitionEntropy μ a :=
  partitionEntropyRate_eq_of_forall
    (countablePartitionEntropy_iteratedPartitionLabel_of_iIndepFun hT ha hind)

/-- For labels with independent past and present, intersections of preimages over an initial
segment `{0, ..., N - 1}` have product measure. -/
private lemma measure_biInter_range_eq_prod [IsProbabilityMeasure μ]
    (hstep : ∀ n, IndepFun (iteratedPartitionLabel T a n) (fun x ↦ a (T^[n] x)) μ)
    (t : ℕ → Set ι) (ht : ∀ i, MeasurableSet (t i)) (N : ℕ) :
    μ (⋂ i ∈ Finset.range N, (fun x ↦ a (T^[i] x)) ⁻¹' t i) =
      ∏ i ∈ Finset.range N, μ ((fun x ↦ a (T^[i] x)) ⁻¹' t i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hset : (⋂ i ∈ Finset.range N, (fun x ↦ a (T^[i] x)) ⁻¹' t i) =
        iteratedPartitionLabel T a N ⁻¹' {w | ∀ k : Fin N, w k ∈ t k} := by
      ext x
      simp only [Set.mem_iInter, Finset.mem_range, Set.mem_preimage, Set.mem_ofPred_eq,
        iteratedPartitionLabel_apply]
      exact ⟨fun h k ↦ h k k.isLt, fun h i hi ↦ h ⟨i, hi⟩⟩
    have hmeas : MeasurableSet {w : Fin N → ι | ∀ k : Fin N, w k ∈ t k} :=
      (Set.to_countable _).measurableSet
    rw [Finset.range_add_one, Finset.set_biInter_insert, Set.inter_comm, hset,
      (hstep N).measure_inter_preimage_eq_mul _ _ hmeas (ht N), ← hset, ih,
      Finset.prod_insert Finset.notMem_range_self, mul_comm]

/-- **Maximal itinerary entropies force independence.** For a measure-preserving map of a
probability space and a measurable label with finitely many values, if every itinerary has the
largest possible entropy, `H(join_n a) = n * H(a)`, then the labels `a ∘ T^[k]` are
independent. -/
theorem iIndepFun_of_forall_countablePartitionEntropy_iteratedPartitionLabel_eq [Finite ι]
    [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ) (ha : Measurable a)
    (h : ∀ n : ℕ, countablePartitionEntropy μ (iteratedPartitionLabel T a n) =
      n * countablePartitionEntropy μ a) :
    iIndepFun (fun k x ↦ a (T^[k] x)) μ := by
  have hb := measurable_iteratedPartitionLabel hT.measurable ha
  -- The itinerary of length `n` is independent of the label at time `n`.
  have hstep : ∀ n, IndepFun (iteratedPartitionLabel T a n) (fun x ↦ a (T^[n] x)) μ := by
    intro n
    have hpair : countablePartitionEntropy μ
        (fun x ↦ (iteratedPartitionLabel T a n x, iteratedPartitionLabel T a 1 (T^[n] x))) =
        countablePartitionEntropy μ (iteratedPartitionLabel T a n) +
          countablePartitionEntropy μ (iteratedPartitionLabel T a 1 ∘ T^[n]) := by
      rw [← countablePartitionEntropy_iteratedPartitionLabel_add, h (n + 1), h n,
        countablePartitionEntropy_comp_of_measurePreserving (hT.iterate n) (hb 1),
        countablePartitionEntropy_iteratedPartitionLabel_one, Nat.cast_succ, add_mul, one_mul]
    have hind := indepFun_of_countablePartitionEntropy_pair_eq_add (hb n)
      ((hb 1).comp (hT.measurable.iterate n)) hpair
    convert hind.comp measurable_id (measurable_pi_apply (0 : Fin 1)) using 1 <;>
      funext x <;> simp
  refine iIndepFun_iff_measure_inter_preimage_eq_mul.mpr fun S sets hsets ↦ ?_
  classical
  obtain ⟨N, hN⟩ : ∃ N, S ⊆ Finset.range N :=
    ⟨S.sup id + 1, fun i hi ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (S.le_sup (f := id) hi))⟩
  set t : ℕ → Set ι := fun i ↦ if i ∈ S then sets i else Set.univ
  have ht : ∀ i, MeasurableSet (t i) := fun i ↦ by
    by_cases hi : i ∈ S
    · simpa [t, hi] using hsets i hi
    · simp [t, hi]
  have key := measure_biInter_range_eq_prod hstep t ht N
  have hinter : (⋂ i ∈ Finset.range N, (fun x ↦ a (T^[i] x)) ⁻¹' t i) =
      ⋂ i ∈ S, (fun x ↦ a (T^[i] x)) ⁻¹' sets i := by
    ext x
    simp only [Set.mem_iInter, Set.mem_preimage, t]
    refine ⟨fun h i hi ↦ by simpa [hi] using h i (hN hi), fun h i _ ↦ ?_⟩
    by_cases hi : i ∈ S
    · simpa [hi] using h i hi
    · simp [hi]
  rw [← hinter, key, ← Finset.prod_subset hN fun i _ hi ↦ by simp [t, hi]]
  exact Finset.prod_congr rfl fun i hi ↦ by simp [t, hi]

/-- **Maximal rate forces independence.** For a measure-preserving map of a probability space and
a measurable label with finitely many values, if the entropy rate of `a` equals its entropy, the
labels `a ∘ T^[k]` are independent. -/
theorem iIndepFun_of_partitionEntropyRate_eq [Finite ι] [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a)
    (h : partitionEntropyRate μ T a = countablePartitionEntropy μ a) :
    iIndepFun (fun k x ↦ a (T^[k] x)) μ :=
  iIndepFun_of_forall_countablePartitionEntropy_iteratedPartitionLabel_eq hT ha
    ((partitionEntropyRate_eq_iff_forall hT ha).mp h)

/-- **Equality case of `h_μ(T, a) ≤ H_μ(a)`.** For a measure-preserving map of a probability space
and a measurable label with finitely many values, the entropy rate of `a` equals its entropy
exactly when the labels `a ∘ T^[k]` are independent. -/
theorem partitionEntropyRate_eq_iff_iIndepFun [Finite ι] [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (ha : Measurable a) :
    partitionEntropyRate μ T a = countablePartitionEntropy μ a ↔
      iIndepFun (fun k x ↦ a (T^[k] x)) μ :=
  ⟨iIndepFun_of_partitionEntropyRate_eq hT ha, partitionEntropyRate_of_iIndepFun hT ha⟩

end TauCeti
