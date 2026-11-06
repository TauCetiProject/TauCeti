/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Visits
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Vanishing occupation of transient states

If the probability of a positive-time return to `y` is less than one, visits to `y` are
almost surely finite from every finite initial measure. Consequently the fraction of times
`1, …, n` spent at `y` tends to zero, both almost surely and in expectation. The Green-function
identity also implies that the time-`n` mass of `y` tends to zero, without irreducibility or
aperiodicity. No convergence in total variation to the zero measure is asserted.

The occupation statements transfer to any realization with the same path law. Only measurable
singletons are needed on the state space, not countability or a topology. Expected occupation
fractions use bounded convergence, so no moment assumption on return times is needed.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.5 and 1.10.
-/

public section

open MeasureTheory ProbabilityTheory Filter TauCeti TauCeti.Probability
open scoped Topology

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (ν : Measure α) [IsFiniteMeasure ν] (κ : Kernel α α) [IsMarkovKernel κ] {y : α}

/-- **The occupation fraction of a transient state vanishes almost surely**, from every finite
initial measure. The count includes times `1` through `n`, not time zero. -/
theorem ae_tendsto_visitCount_div_of_return_lt_one
    (hy : markovChainLaw (dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} < 1) :
    ∀ᵐ x ∂markovChainLaw ν κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => x (k + 1)) y n : ℝ) / n) atTop (𝓝 0) := by
  classical
  have hfinite : ∀ᵐ x ∂markovChainLaw ν κ, {n | x n = y}.Finite := by
    simpa only [ae_iff, Set.Infinite] using
      markovChainLaw_setOf_infinite_setOf_eq_eq_zero ν κ hy
  filter_upwards [hfinite] with x hx
  have hs : {k | x (k + 1) = y}.Finite :=
    hx.preimage (Set.injOn_of_injective (fun a b h => Nat.add_right_cancel h))
  refine squeeze_zero (fun n => by positivity) (fun n => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (hs.toFinset.card : ℝ))
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast (by
    rw [visitCount_eq_count]
    exact Nat.count_le_card hs n)

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsMarkovKernel κ] {y : α}

/-- **The transition mass of a transient state tends to zero**, from every finite initial
measure. Neither irreducibility nor aperiodicity is required. -/
theorem tendsto_pow_comp_apply_singleton_zero_of_return_lt_one
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} < 1)
    (ν : Measure α) [IsFiniteMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν) {y}) atTop (𝓝 0) := by
  apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
  rw [tsum_pow_comp_apply_singleton, tsum_pow_apply_singleton_self]
  exact ENNReal.mul_ne_top (measure_ne_top _ _) (by
    simpa only [ne_eq, ENNReal.inv_eq_top, tsub_eq_zero_iff_le, not_le] using hy)

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSingletonClass α] {P : Measure Ω} {ν : Measure α} [IsFiniteMeasure ν]
  {X : Ω → ℕ → α} {κ : Kernel α α} [IsMarkovKernel κ] {y : α}

/-- The transient-state occupation limit holds for every realization with the given path law. -/
theorem ae_tendsto_visitCount_div_of_return_lt_one
    (hX : HasLaw X (markovChainLaw ν κ) P)
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} < 1) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n) atTop (𝓝 0) := by
  have h := ν.ae_tendsto_visitCount_div_of_return_lt_one κ hy
  rw [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

/-- **Expected occupation fractions of a transient state tend to zero.** This holds on any
realization of the chain, with any finite initial measure. -/
theorem tendsto_integral_visitCount_div_zero_of_return_lt_one
    (hX : HasLaw X (markovChainLaw ν κ) P)
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} < 1) :
    Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => X ω (k + 1)) y n : ℝ) / n ∂P)
      atTop (𝓝 0) := by
  classical
  let : IsFiniteMeasure P := hX.isFiniteMeasure
  have hm (n : ℕ) : Measurable (fun x : ℕ → α =>
      (visitCount (fun k => x (k + 1)) y n : ℝ) / n) :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_visitCount_comp (P := fun x : ℕ → α => fun k => x (k + 1))
        y n (measurableSet_singleton y) (fun i _ => measurable_pi_apply (i + 1)))).div_const n
  have hb (n : ℕ) : ∀ᵐ ω ∂P,
      ‖(visitCount (fun k => X ω (k + 1)) y n : ℝ) / n‖ ≤ 1 := by
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply div_le_one_of_le₀ _ (Nat.cast_nonneg n)
    rw [visitCount_eq_count, Nat.cast_le]
    exact Nat.count_le _
  simpa only [Function.comp_def, integral_zero] using
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => ((hm n).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable)
      (integrable_const 1) hb (hX.ae_tendsto_visitCount_div_of_return_lt_one hy)

/-- On any realization of the chain, the probability mass at a transient state vanishes. -/
theorem tendsto_measureReal_apply_eq_zero_of_return_lt_one
    (hX : HasLaw X (markovChainLaw ν κ) P)
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} < 1) :
    Tendsto (fun n : ℕ => P.real {ω | X ω n = y}) atTop (𝓝 0) := by
  have hm (n : ℕ) : P {ω | X ω n = y} = ((κ ^ n) ∘ₘ ν) {y} := by
    exact (hX.measure_eq ((measurableSet_singleton y).preimage (measurable_pi_apply n))).trans
      (Measure.markovChainLaw_setOf_apply_eq_comp ν κ n y)
  simpa only [Measure.real, hm, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp
      (κ.tendsto_pow_comp_apply_singleton_zero_of_return_lt_one hy ν)

end ProbabilityTheory.HasLaw
