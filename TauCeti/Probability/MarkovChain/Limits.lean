/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Equilibrium
public import TauCeti.Probability.MarkovChain.Invariant
public import TauCeti.Probability.MarkovChain.Pointwise

/-!
# The return-mean formula for limiting transition probabilities

For an irreducible aperiodic chain, the time-`n` mass of each state `y` converges to
`(κ.meanReturnTime y)⁻¹.toReal`, from every initial probability law. The inverse is
taken in `ℝ≥0∞` before conversion to `ℝ`: null recurrence and transience both give
limit zero. Positive recurrence gives the singleton masses of the unique invariant
probability, by Kac's formula and total-variation convergence to equilibrium.

A probability limit in total variation exists exactly when some state is positive
recurrent. Thus singleton decay in the other two cases cannot be upgraded to
convergence in total variation to a probability measure. The singleton limit also
transfers to a realization on an arbitrary measurable sample space via its path law.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8,
  convergence to equilibrium and the return-mean formula.
-/

public section

open MeasureTheory ProbabilityTheory Filter TauCeti.Probability
open scoped Topology ENNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  {κ : Kernel α α} [IsMarkovKernel κ] [IsIrreducible Measure.count κ]

/-- **The limiting transition probability formula.** In an irreducible aperiodic chain,
the mass of a state tends to the reciprocal extended mean positive return time.
This includes infinite mean, in which case the limit is zero. -/
theorem tendsto_pow_comp_real_singleton (hκ : κ.IsAperiodic)
    (ν : Measure α) [IsProbabilityMeasure ν] (y : α) :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop
      (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  by_cases hy : κ.IsPositiveRecurrent y
  · obtain ⟨π, hπ, hπinv⟩ :=
      κ.exists_invariant_probability_iff_exists_isPositiveRecurrent.mpr ⟨y, hy⟩
    let := hπ
    have hlim : Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y} - π.real {y})
        atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by
        simpa only [Real.norm_eq_abs] using
          abs_measureReal_sub_le_tvDist (μ := (κ ^ n) ∘ₘ ν) (ν := π)
            (measurableSet_singleton y)) (hπinv.tendsto_tvDist_pow_comp hκ ν)
    simpa only [zero_add, sub_add_cancel, measureReal_def,
      hπinv.apply_singleton_eq_inv_meanReturnTime] using hlim.add_const (π.real {y})
  · have hm : κ.meanReturnTime y = ∞ := by
      simpa only [isPositiveRecurrent_iff, not_lt, top_le_iff] using hy
    have hraw : (∫⁻ x, (hittingAfter (fun n x => x n) {y} 1 x).recTopCoe ⊤
        (fun n => (n : ℝ≥0∞)) ∂markovChainLaw (Measure.dirac y) κ) = ⊤ := by
      calc
        _ = κ.meanReturnTime y := by
          rw [meanReturnTime_def]
          refine lintegral_congr fun x => ?_
          induction hittingAfter (fun n x => x n) {y} 1 x using WithTop.recTopCoe <;> rfl
        _ = ⊤ := hm
    simpa only [hm, ENNReal.inv_top, ENNReal.toReal_zero] using
      κ.tendsto_pow_comp_real_singleton_of_isAperiodic_of_lintegral_return_eq_top hκ hraw ν

/-- An irreducible aperiodic chain has a probability limit in total variation from
an initial probability law exactly when it has a positive recurrent state.
In the null recurrent and transient cases, singleton decay is not probability convergence. -/
theorem exists_tendsto_tvDist_pow_comp_iff (hκ : κ.IsAperiodic)
    (ν : Measure α) [IsProbabilityMeasure ν] :
    (∃ π : Measure α, IsProbabilityMeasure π ∧
      Tendsto (fun n : ℕ => tvDist ((κ ^ n) ∘ₘ ν) π) atTop (𝓝 0)) ↔
      ∃ y : α, κ.IsPositiveRecurrent y := by
  constructor
  · rintro ⟨π, hπ, hlim⟩
    let := hπ
    have := countable_of_isIrreducible_count (κ := κ)
    by_contra h
    have hzero : π = 0 := by
      apply Measure.ext_iff_singleton.mpr
      intro y
      have hm : κ.meanReturnTime y = ∞ := by
        have hy := not_exists.mp h y
        simpa only [isPositiveRecurrent_iff, not_lt, top_le_iff] using hy
      have hdecay : Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
        simpa only [hm, ENNReal.inv_top, ENNReal.toReal_zero] using
          tendsto_pow_comp_real_singleton hκ ν y
      have hsub : Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y} - π.real {y})
          atTop (𝓝 0) :=
        squeeze_zero_norm (fun n => by
          simpa only [Real.norm_eq_abs] using
            abs_measureReal_sub_le_tvDist (μ := (κ ^ n) ∘ₘ ν) (ν := π)
              (measurableSet_singleton y)) hlim
      have hz : π.real {y} = 0 := by
        have := tendsto_nhds_unique (hsub.add_const (π.real {y}))
          (by simpa only [sub_add_cancel] using hdecay)
        simpa only [zero_add] using this
      simpa [measureReal_def, ENNReal.toReal_eq_zero_iff, measure_ne_top] using hz
    have hone : π Set.univ = 1 := measure_univ
    simp [hzero] at hone
  · intro h
    obtain ⟨π, hπ, hπinv⟩ :=
      κ.exists_invariant_probability_iff_exists_isPositiveRecurrent.mpr h
    let := hπ
    exact ⟨π, hπ, hπinv.tendsto_tvDist_pow_comp hκ ν⟩

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

/-- The limiting state probabilities on any realization of an irreducible aperiodic
chain are the reciprocal extended mean return times, including zero at infinite mean. -/
theorem tendsto_measureReal_apply_eq_inv_meanReturnTime
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] {κ : Kernel α α} [IsMarkovKernel κ]
    [Kernel.IsIrreducible Measure.count κ] {ν : Measure α} [IsProbabilityMeasure ν]
    {P : Measure Ω} {X : ℕ → Ω → α}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    (hκ : κ.IsAperiodic) (y : α) :
    Tendsto (fun n : ℕ => P.real {ω | X n ω = y}) atTop
      (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  have heq (n : ℕ) : P.real {ω | X n ω = y} = ((κ ^ n) ∘ₘ ν).real {y} :=
    (hX.eval_markovChainLaw ν κ n).measureReal_eq (measurableSet_singleton y)
  simp_rw [heq]
  exact Kernel.tendsto_pow_comp_real_singleton hκ ν y

end ProbabilityTheory.HasLaw
