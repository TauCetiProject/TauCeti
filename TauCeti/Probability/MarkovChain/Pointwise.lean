/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Coupling.Convergence
public import TauCeti.Probability.MarkovChain.Product.Basic
public import TauCeti.Probability.MarkovChain.Product.Limits
public import TauCeti.Probability.MarkovChain.Occupation.Bounds
public import TauCeti.Probability.MarkovChain.Occupation
public import TauCeti.Probability.Process.Occupation
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
public import TauCeti.Analysis.SpecificLimits.MovingAverage

/-!
# Pointwise decay at states with infinite mean return time

For an irreducible aperiodic countable-state chain, an infinite extended mean positive
return time at `y` implies that the time-`n` mass of `y` tends to zero from every initial
probability law. This includes null recurrent states and states with a positive chance
of never returning: the hypothesis uses an `ℝ≥0∞`-valued mean, with infinity on nonreturn.

The independent square chain gives two alternatives. Transience of `(y, y)` already
implies decay by summability of squared transition masses. In the recurrent case,
meeting-time coupling makes every fixed time shift asymptotically indistinguishable.
The uniform occupation bound and the occupation strong law then force pointwise decay.
The recurrent-square criterion is also exposed with a zero Cesàro return-mass hypothesis,
without countability or an aperiodicity assumption on the original kernel.

Only singleton convergence is asserted, not convergence in total variation to zero.
The infinite-mean decay theorem transfers to arbitrary realizations of the chain through
their path laws.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8,
  the independent-product and averaged-occupation proof of convergence.
-/

public section

open MeasureTheory ProbabilityTheory Filter TauCeti TauCeti.Probability
open scoped Topology ENNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsMarkovKernel κ]

/-- If the square chain is irreducible and recurrent, vanishing Cesàro return masses at `y`
force the singleton mass at `y` to vanish from every initial probability law. -/
theorem tendsto_pow_comp_real_singleton_of_parallelComp_isRecurrent
    [MeasurableEq α] [IsIrreducible Measure.count (κ ∥ₖ κ)]
    {z : α × α} (hz : (κ ∥ₖ κ).IsRecurrent z) {y : α}
    (hy : Tendsto (fun k : ℕ =>
      (∑ i ∈ Finset.range k, ((κ ^ (i + 1)) y).real {y}) / k) atTop (𝓝 0))
    (ν : Measure α) [IsProbabilityMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
  have hshift (i : ℕ) : Tendsto (fun n : ℕ =>
      ((κ ^ (n + i)) ∘ₘ ν).real {y} - ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (κ.tendsto_tvDist_pow_comp_pow_add_comp_of_parallelComp_isRecurrent hz ν i)
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact abs_measureReal_sub_le_tvDist (measurableSet_singleton y)
  have hb : Tendsto (fun k : ℕ =>
      (1 + ∑ i ∈ Finset.range k, ((κ ^ (i + 1)) y).real {y}) / k) atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).add hy
  exact tendsto_zero_of_nonneg_of_sum_range_add_div_le
    (fun _ => measureReal_nonneg) hshift hb
    (fun n k _ => κ.sum_range_pow_comp_real_singleton_div_le ν y n k)

/-- **Pointwise decay at an infinite-mean state.** For a countable-state irreducible
aperiodic Markov kernel, if the expected first positive return time to `y` is infinite,
then the time-`n` mass of `{y}` tends to zero from every initial probability law `ν`.
The mean assigns infinity to nonreturn, so no recurrence assumption is needed. -/
theorem tendsto_pow_comp_real_singleton_of_isAperiodic_of_meanReturnTime_eq_top
    [Countable α] [IsIrreducible Measure.count κ] (hκ : κ.IsAperiodic) {y : α}
    (hy : κ.meanReturnTime y = ⊤)
    (ν : Measure α) [IsProbabilityMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
  by_cases hr : (κ ∥ₖ κ).IsRecurrent (y, y)
  · let := hκ.isIrreducible_parallelComp hκ
    have hlim := HasLaw.tendsto_integral_visitCount_div_markovChainLaw_dirac
      (HasLaw.id (μ := markovChainLaw (Measure.dirac y) κ))
    apply κ.tendsto_pow_comp_real_singleton_of_parallelComp_isRecurrent hr _ ν
    simpa only [id_eq, integral_div, κ.integral_visitCount_succ_markovChainLaw_dirac,
      hy, ENNReal.inv_top, ENNReal.toReal_zero] using hlim
  · exact κ.tendsto_pow_comp_apply_singleton_of_parallelComp_return_lt_one ν
      (isTransient_iff_return_probability_lt_one.mp (isTransient_iff.mpr hr))

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

/-- On any realization of an irreducible aperiodic countable-state chain, the probability
of occupying an infinite-mean state tends to zero. -/
theorem tendsto_measureReal_apply_eq_of_isAperiodic_of_meanReturnTime_eq_top
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    [MeasurableSpace Ω] {κ : Kernel α α} [IsMarkovKernel κ]
    [Kernel.IsIrreducible Measure.count κ] {ν : Measure α} [IsProbabilityMeasure ν]
    {P : Measure Ω} {X : ℕ → Ω → α}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    (hκ : κ.IsAperiodic) {y : α}
    (hy : κ.meanReturnTime y = ⊤) :
    Tendsto (fun n : ℕ => P.real {ω | X n ω = y}) atTop (𝓝 0) := by
  have heq (n : ℕ) : P.real {ω | X n ω = y} = ((κ ^ n) ∘ₘ ν).real {y} :=
    (hX.eval_markovChainLaw ν κ n).measureReal_eq (measurableSet_singleton y)
  simp_rw [heq]
  exact κ.tendsto_pow_comp_real_singleton_of_isAperiodic_of_meanReturnTime_eq_top hκ hy ν

end ProbabilityTheory.HasLaw
