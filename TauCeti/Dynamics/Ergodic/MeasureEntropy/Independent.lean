/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Entropy rate of a label with independent iterates

The entropy rate of a label is at most its entropy, `h_μ(T, a) ≤ H_μ(a)`
(`TauCeti.partitionEntropyRate_le`). For a measure-preserving map of a probability space and a
measurable countable label, equality holds exactly when every itinerary has
the largest possible entropy, `H(join_n a) = n * H(a)`
(`TauCeti.partitionEntropyRate_eq_iff_forall`). This holds when the labels `a ∘ T^[k]` are
independent (`TauCeti.partitionEntropyRate_of_iIndepFun`): the itinerary of length `n + 1` is the
join of the itinerary of length `n` with the independent label `a ∘ T^[n]`.

The converse, that equality forces independence for finite labels, needs the equality case of
subadditivity and is not proved here.

## Main results

* `TauCeti.countablePartitionEntropy_iteratedPartitionLabel_of_iIndepFun`: if the labels
  `a ∘ T^[k]` are independent, `H(join_n a) = n * H(a)`.
* `TauCeti.partitionEntropyRate_of_iIndepFun`: if the labels `a ∘ T^[k]` are independent, the
  rate of `a` is its entropy.

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

end TauCeti
