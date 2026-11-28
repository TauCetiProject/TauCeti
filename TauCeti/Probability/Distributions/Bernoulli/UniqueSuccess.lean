/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# One success among independent Bernoulli trials

The event that the unique success lies in a specified set is a disjoint union of singleton
assignments. Upper bounds on the success probabilities bound the cost of requiring every other
trial to fail, even when the trials have different probabilities.
-/

public section

open Finset MeasureTheory Set

namespace ProbabilityTheory

open Classical in
/-- For independent Bernoulli trials with probabilities `p`, the probability that exactly one
trial succeeds and its index belongs to `s` is the sum of the corresponding assignment masses. -/
theorem measureReal_pi_bernoulliMeasure_existsUnique_mem {ι : Type*} [Fintype ι]
    (p : ι → unitInterval) (s : Finset ι) :
    (Measure.pi fun i ↦ bernoulliMeasure true false (p i)).real
        {x | ∃ i ∈ s, ∀ j, x j = true ↔ j = i} =
      ∑ i ∈ s, (p i : ℝ) * ∏ j ∈ Finset.univ.erase i, (1 - (p j : ℝ)) := by
  classical
  let a (i : ι) (j : ι) := decide (j = i)
  have ha : Function.Injective a := by
    intro i j h
    simpa [a] using (congrFun h i).symm
  have he : {x | ∃ i ∈ s, ∀ j, x j = true ↔ j = i} = ⋃ i ∈ s, {a i} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    refine exists_congr (fun i ↦ and_congr_right fun _ ↦ ?_)
    rw [funext_iff]
    exact forall_congr' fun j ↦ by
      by_cases h : j = i <;> cases x j <;> simp [a, h]
  rw [he, measureReal_biUnion_finset (fun i _ j _ hij ↦ disjoint_singleton.mpr (ha.ne hij))
    (fun _ _ ↦ measurableSet_singleton _) (fun _ _ ↦ measure_ne_top _ _)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod,
    ← Finset.mul_prod_erase _ _ (mem_univ i)]
  simp only [← measureReal_def]
  congr 1
  · simp [a]
  · exact Finset.prod_congr rfl fun j hj ↦ by simp [a, (mem_erase.mp hj).1]

/-- If all trial probabilities are at most `δ` and those in `s` are at least `q`, the probability
of a unique success in `s` is at least `|s| * q * (1 - δ) ^ (|ι| - 1)`. -/
theorem le_measureReal_pi_bernoulliMeasure_existsUnique_mem {ι : Type*} [Fintype ι]
    (p : ι → unitInterval) (s : Finset ι) {q : ℝ} (δ : unitInterval)
    (hq : ∀ i ∈ s, q ≤ (p i : ℝ)) (hδ : ∀ i, (p i : ℝ) ≤ δ) :
    (s.card : ℝ) * q * (1 - (δ : ℝ)) ^ (Fintype.card ι - 1) ≤
      (Measure.pi fun i ↦ bernoulliMeasure true false (p i)).real
        {x | ∃ i ∈ s, ∀ j, x j = true ↔ j = i} := by
  classical
  rw [measureReal_pi_bernoulliMeasure_existsUnique_mem, mul_assoc, ← nsmul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hnonneg : 0 ≤ 1 - (δ : ℝ) := unitInterval.one_sub_nonneg δ
  calc
    _ ≤ (p i : ℝ) * (1 - (δ : ℝ)) ^ (Fintype.card ι - 1) := by gcongr; exact hq i hi
    _ ≤ _ := by
      rw [← Finset.card_univ, ← Finset.card_erase_of_mem (mem_univ i), ← Finset.prod_const]
      exact mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun _ _ ↦ hnonneg) (fun j _ ↦ sub_le_sub_left (hδ j) 1))
        (unitInterval.nonneg (p i))

end ProbabilityTheory
