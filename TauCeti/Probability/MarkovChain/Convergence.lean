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
# The convergence theorem for irreducible aperiodic chains

A positive recurrent state supplies an invariant probability by normalizing its expected
occupation measure over one return cycle. For an irreducible aperiodic chain, this probability
attracts every initial probability in total variation.

The singleton limit has a uniform expression in all recurrence regimes: the mass at `y`
converges to `(κ.meanReturnTime y)⁻¹.toReal`. The inverse is taken before conversion to a real
number, so infinite mean gives zero. This includes both null recurrence and transience,
without asserting total-variation convergence to the zero measure in those cases.

Both conclusions transfer to arbitrary realizations through their path laws. No topology on
the sample space or separate choice of a stationary distribution is needed.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), Theorem 1.8.3.

The proofs combine the return-cycle construction and Kac formula in
`MarkovChain.Invariant` with the independent-square coupling and infinite-mean decay in
`MarkovChain.Equilibrium` and `MarkovChain.Pointwise`.
-/

public section

open MeasureTheory ProbabilityTheory Filter TauCeti.Probability
open scoped Topology ENNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  {κ : Kernel α α} [IsMarkovKernel κ] [IsIrreducible Measure.count κ]

/-- **Convergence to equilibrium from positive recurrence.** The normalized return-cycle
occupation measure at any positive recurrent state attracts every initial probability in
an irreducible aperiodic chain. -/
theorem IsPositiveRecurrent.tendsto_tvDist_pow_comp {x : α}
    (hx : κ.IsPositiveRecurrent x) (hκ : κ.IsAperiodic)
    (ν : Measure α) [IsProbabilityMeasure ν] :
    Tendsto (fun n : ℕ => tvDist ((κ ^ n) ∘ₘ ν)
      ((κ.meanReturnTime x)⁻¹ • κ.cycleOccupation x)) atTop (𝓝 0) := by
  let := hx.isProbabilityMeasure_inv_meanReturnTime_smul_cycleOccupation
  exact hx.invariant_inv_meanReturnTime_smul_cycleOccupation.tendsto_tvDist_pow_comp hκ ν

/-- **The singleton convergence theorem.** For an irreducible aperiodic chain, the mass of a
state converges to the reciprocal of its extended mean positive return time, from every
initial probability. Infinite return-time mean gives limit zero. -/
theorem tendsto_pow_comp_real_singleton_of_isAperiodic
    (κ : Kernel α α) [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    (hκ : κ.IsAperiodic) (ν : Measure α) [IsProbabilityMeasure ν] (y : α) :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop
      (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  by_cases hy : κ.meanReturnTime y = ⊤
  · have hmean : (∫⁻ ω, (hittingAfter (fun n ω => ω n) {y} 1 ω).recTopCoe ⊤
        (fun n => (n : ℝ≥0∞)) ∂markovChainLaw (Measure.dirac y) κ) = ⊤ := by
      calc
        _ = κ.meanReturnTime y := by
          rw [meanReturnTime_def]
          refine lintegral_congr fun ω => ?_
          induction hittingAfter (fun n ω => ω n) {y} 1 ω using WithTop.recTopCoe <;> rfl
        _ = ⊤ := hy
    simpa only [hy, ENNReal.inv_top, ENNReal.toReal_zero] using
      κ.tendsto_pow_comp_real_singleton_of_isAperiodic_of_lintegral_return_eq_top hκ hmean ν
  · have hpos : κ.IsPositiveRecurrent y :=
      (isPositiveRecurrent_iff κ y).mpr (lt_top_iff_ne_top.mpr hy)
    obtain ⟨π, ⟨hprob, hπ⟩, _⟩ := hpos.existsUnique_invariant_probability
    have hlim : Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y} - π.real {y})
        atTop (𝓝 0) := by
      apply squeeze_zero_norm (fun n => ?_) (hπ.tendsto_tvDist_pow_comp hκ ν)
      simpa only [Real.norm_eq_abs] using
        (abs_measureReal_sub_le_tvDist (μ := (κ ^ n) ∘ₘ ν) (ν := π)
          (measurableSet_singleton y))
    have hmass : π.real {y} = (κ.meanReturnTime y)⁻¹.toReal :=
      congrArg ENNReal.toReal (hπ.apply_singleton_eq_inv_meanReturnTime y)
    simpa only [sub_add_cancel, zero_add, hmass] using hlim.add_const (π.real {y})

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace Ω] {κ : Kernel α α} [IsMarkovKernel κ]
  [Kernel.IsIrreducible Measure.count κ] {ν : Measure α} [IsProbabilityMeasure ν]
  {P : Measure Ω} {X : ℕ → Ω → α}

/-- For any realization of an irreducible aperiodic chain with a positive recurrent state,
the coordinate laws converge in total variation to the normalized cycle occupation measure. -/
theorem tendsto_tvDist_map_of_isPositiveRecurrent
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    {x : α} (hx : κ.IsPositiveRecurrent x) (hκ : κ.IsAperiodic) :
    Tendsto (fun n : ℕ => tvDist (P.map (X n))
      ((κ.meanReturnTime x)⁻¹ • κ.cycleOccupation x)) atTop (𝓝 0) := by
  simpa only [(hX.eval_markovChainLaw ν κ _).map_eq] using hx.tendsto_tvDist_pow_comp hκ ν

/-- On any realization of an irreducible aperiodic chain, the probability of occupying `y`
converges to the reciprocal extended mean return time. This remains valid when that mean is
infinite, with zero limit. -/
theorem tendsto_measureReal_apply_eq_of_isAperiodic
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    (hκ : κ.IsAperiodic) (y : α) :
    Tendsto (fun n : ℕ => P.real {ω | X n ω = y}) atTop
      (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  have heq (n : ℕ) : P.real {ω | X n ω = y} = ((κ ^ n) ∘ₘ ν).real {y} :=
    (hX.eval_markovChainLaw ν κ n).measureReal_eq (measurableSet_singleton y)
  simp_rw [heq]
  exact κ.tendsto_pow_comp_real_singleton_of_isAperiodic hκ ν y

end ProbabilityTheory.HasLaw
