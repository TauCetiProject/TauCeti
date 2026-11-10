/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.MarkovChain
public import TauCeti.Probability.Kernel.Composition.Power

/-!
# Uniform bounds on finite-window occupation

The expected number of visits to a state during a fixed finite horizon is largest when
started at that state. Consequently, the expected occupation of any time window is bounded
by the corresponding initial occupation of the chain started at the visited state, uniformly
in the location of the window and in the initial probability law.

The real averaged bound isolates the initial visit as a term `1`. It is useful for proving
pointwise decay of transition probabilities from vanishing Cesàro occupation at the target
state, even when the starting law varies with the observation time. No irreducibility,
aperiodicity, countability, or return-time moment hypothesis is required.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsMarkovKernel κ]

/-- Among all starting states, starting at `y` maximizes the expected number of visits to `y`
in the first `k` observations, including time zero. -/
theorem sum_range_pow_apply_singleton_le (x y : α) (k : ℕ) :
    ∑ i ∈ Finset.range k, (κ ^ i) x {y} ≤ ∑ i ∈ Finset.range k, (κ ^ i) y {y} := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    by_cases hxy : x = y
    · subst x
      exact le_rfl
    -- Before the first visit there is no contribution. Taking one step leaves a shorter
    -- horizon, whose occupation is bounded by the induction hypothesis.
    rw [Finset.sum_range_succ' (fun i => (κ ^ i) x {y})]
    simp only [pow_zero, Kernel.one_def, Kernel.id_apply]
    rw [Measure.dirac_apply' x (measurableSet_singleton y),
      Set.indicator_of_notMem (by simpa only [Set.mem_singleton_iff] using hxy), add_zero]
    calc
      ∑ i ∈ Finset.range k, (κ ^ (i + 1)) x {y} =
          ∫⁻ z, ∑ i ∈ Finset.range k, (κ ^ i) z {y} ∂κ x := by
        rw [lintegral_finsetSum _ (fun i _ => (κ ^ i).measurable_coe
          (measurableSet_singleton y))]
        apply Finset.sum_congr rfl
        intro i hi
        simpa [Nat.add_comm] using
          κ.pow_add_apply_eq_lintegral 1 i x (measurableSet_singleton y)
      _ ≤ ∫⁻ _, ∑ i ∈ Finset.range k, (κ ^ i) y {y} ∂κ x :=
        lintegral_mono fun z => ih z
      _ = ∑ i ∈ Finset.range k, (κ ^ i) y {y} := by simp
      _ ≤ ∑ i ∈ Finset.range (k + 1), (κ ^ i) y {y} := by
        rw [Finset.sum_range_succ]
        exact le_self_add

/-- The expected occupation of `y` during any window of `k` consecutive observations is at
most the initial occupation of the chain started at `y`, times the total initial mass.
The initial measure need not be finite or normalized. -/
theorem sum_range_pow_comp_apply_singleton_le (ν : Measure α) (y : α) (n k : ℕ) :
    ∑ i ∈ Finset.range k, ((κ ^ (n + i)) ∘ₘ ν) {y} ≤
      ν Set.univ * ∑ i ∈ Finset.range k, (κ ^ i) y {y} := by
  calc
    ∑ i ∈ Finset.range k, ((κ ^ (n + i)) ∘ₘ ν) {y} =
        ∫⁻ x, ∑ i ∈ Finset.range k, (κ ^ i) x {y} ∂((κ ^ n) ∘ₘ ν) := by
      rw [lintegral_finsetSum _ (fun i _ => (κ ^ i).measurable_coe
        (measurableSet_singleton y))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Measure.bind_apply (measurableSet_singleton y) (κ ^ i).aemeasurable,
        Measure.comp_assoc]
      simp [← Kernel.pow_add, Nat.add_comm]
    _ ≤ ∫⁻ _, ∑ i ∈ Finset.range k, (κ ^ i) y {y} ∂((κ ^ n) ∘ₘ ν) :=
      lintegral_mono fun x => κ.sum_range_pow_apply_singleton_le x y k
    _ = ν Set.univ * ∑ i ∈ Finset.range k, (κ ^ i) y {y} := by
      simp [mul_comm]

/-- Uniformly in the starting time, the mean of the next `k` singleton probabilities is at
most `(1 +` the expected number of positive-time visits through time `k` from `y`) / k`.
The formula also holds at `k = 0`, with Lean's zero-denominator convention. -/
theorem sum_range_pow_comp_real_singleton_div_le (ν : Measure α) [IsProbabilityMeasure ν]
    (y : α) (n k : ℕ) :
    (∑ i ∈ Finset.range k, ((κ ^ (n + i + 1)) ∘ₘ ν).real {y}) / k ≤
      (1 + ∑ i ∈ Finset.range k, ((κ ^ (i + 1)) y).real {y}) / k := by
  have h := κ.sum_range_pow_comp_apply_singleton_le ν y (n + 1) k
  simp only [measure_univ, one_mul] at h
  have hreal := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr fun i _ => measure_ne_top _ _) h
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top _ _),
    ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)] at hreal
  have hbound : ∑ i ∈ Finset.range k, ((κ ^ i) y).real {y} ≤
      1 + ∑ i ∈ Finset.range k, ((κ ^ (i + 1)) y).real {y} := by
    calc
      ∑ i ∈ Finset.range k, ((κ ^ i) y).real {y} ≤
          ∑ i ∈ Finset.range (k + 1), ((κ ^ i) y).real {y} := by
        rw [Finset.sum_range_succ]
        exact le_add_of_nonneg_right measureReal_nonneg
      _ = _ := by
        rw [Finset.sum_range_succ']
        simp [Kernel.one_def, Kernel.id_apply, Measure.real_def, add_comm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  simpa only [Measure.real_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hreal.trans hbound

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- The uniform averaged occupation bound for a Markov chain realized on any probability
space. Only its path law is specified; no canonical sample space is required. -/
theorem sum_range_measureReal_setOf_eq_div_le
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace Ω]
    {P : Measure Ω} {ν : Measure α} [IsProbabilityMeasure ν]
    {κ : Kernel α α} [IsMarkovKernel κ] {X : ℕ → Ω → α}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P) (y : α) (n k : ℕ) :
    (∑ i ∈ Finset.range k, P.real {ω | X (n + i + 1) ω = y}) / k ≤
      (1 + ∑ i ∈ Finset.range k, ((κ ^ (i + 1)) y).real {y}) / k := by
  have hprob (j : ℕ) : P.real {ω | X j ω = y} = ((κ ^ j) ∘ₘ ν).real {y} :=
    (HasLaw.eval_markovChainLaw ν κ hX j).measureReal_eq (measurableSet_singleton y)
  simp_rw [hprob]
  exact κ.sum_range_pow_comp_real_singleton_div_le ν y n k

end ProbabilityTheory.HasLaw
