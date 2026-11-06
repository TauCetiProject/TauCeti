/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Visits
public import TauCeti.Probability.Kernel.Composition.ParallelComp
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Singleton decay from a transient independent square chain

The independent square kernel `κ ∥ₖ κ` turns the square of a singleton transition
probability into a singleton probability on the product space. If `(y, y)` is transient
for this kernel, the Green-function identity makes these squares summable under every
finite initial measure. Consequently the original singleton masses tend to zero, even
when `y` is recurrent for the original chain. In the recurrent-product case, recurrence of
`(y, y)` implies recurrence of `y`, since squared return probabilities are bounded by the
original return probabilities.

These are the product-chain alternatives used in proving convergence to equilibrium.
Neither irreducibility nor aperiodicity is required here. The limit is pointwise on
singletons; it is not total-variation convergence to the zero measure.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8,
  the independent-product argument for convergence of transition probabilities.
-/

public section

open MeasureTheory ProbabilityTheory Filter TauCeti.Probability

open scoped Topology

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsMarkovKernel κ]

/-- Recurrence of a state in an independent product chain implies recurrence of its
first coordinate. In particular this applies to diagonal states of the square chain. -/
theorem return_eq_one_of_parallelComp_return_eq_one
    {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    (η : Kernel β β) [IsMarkovKernel η] {y : α} {z : β}
    (hy : markovChainLaw (Measure.dirac (y, z)) (κ ∥ₖ η)
      {w | hittingAfter (fun n w => w n) {(y, z)} 1 w ≠ ⊤} = 1) :
    markovChainLaw (Measure.dirac y) κ
      {w | hittingAfter (fun n w => w n) {y} 1 w ≠ ⊤} = 1 := by
  apply (κ.tsum_pow_apply_singleton_self_eq_top_iff y).mp
  apply top_unique
  rw [← (κ ∥ₖ η).tsum_pow_apply_singleton_self_eq_top_iff (y, z)] at hy
  rw [← hy]
  exact tsum_le_tsum fun n => by
    rw [parallelComp_pow_apply_singleton]
    exact mul_le_of_le_one_right' prob_le_one

/-- If the diagonal state `(y, y)` is transient for the independent square chain,
then squared singleton masses are summable from every finite initial measure.
This does not require `y` to be transient for `κ`. -/
theorem summable_sq_pow_comp_apply_singleton_of_parallelComp_return_lt_one
    (ν : Measure α) [IsFiniteMeasure ν] {y : α}
    (hy : markovChainLaw (Measure.dirac (y, y)) (κ ∥ₖ κ)
      {w | hittingAfter (fun n w => w n) {(y, y)} 1 w ≠ ⊤} < 1) :
    Summable (fun n : ℕ => (((κ ^ n) ∘ₘ ν).real {y}) ^ 2) := by
  have hgreen : ∑' n : ℕ, (((κ ∥ₖ κ) ^ n) ∘ₘ (ν.prod ν)) {(y, y)} ≠ ⊤ := by
    rw [tsum_pow_comp_apply_singleton, tsum_pow_apply_singleton_self]
    exact ENNReal.mul_ne_top (measure_ne_top _ _)
      (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hy)))
  have hs := ENNReal.summable_toReal hgreen
  -- Each product marginal on the diagonal is the square of the original singleton mass.
  simpa only [parallelComp_pow, Measure.parallelComp_comp_prod,
    ← Set.singleton_prod_singleton, Measure.prod_prod, ENNReal.toReal_mul,
    Measure.real, pow_two] using hs

/-- Transience of `(y, y)` for the independent square chain forces the time-`n`
singleton mass at `y` to tend to zero under every finite initial measure. -/
theorem tendsto_pow_comp_apply_singleton_of_parallelComp_return_lt_one
    (ν : Measure α) [IsFiniteMeasure ν] {y : α}
    (hy : markovChainLaw (Measure.dirac (y, y)) (κ ∥ₖ κ)
      {w | hittingAfter (fun n w => w n) {(y, y)} 1 w ≠ ⊤} < 1) :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
  have hs := (κ.summable_sq_pow_comp_apply_singleton_of_parallelComp_return_lt_one
    ν hy).tendsto_atTop_zero
  simpa only [Function.comp_def, Real.sqrt_sq measureReal_nonneg, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hs

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

/-- The transient-product singleton limit transfers to any realization of the chain
on an arbitrary measurable sample space. -/
theorem tendsto_measureReal_apply_eq_of_parallelComp_return_lt_one
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace Ω]
    {κ : Kernel α α} [IsMarkovKernel κ] {ν : Measure α} [IsFiniteMeasure ν]
    {P : Measure Ω} {X : ℕ → Ω → α}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P) {y : α}
    (hy : markovChainLaw (Measure.dirac (y, y)) (κ ∥ₖ κ)
      {w | hittingAfter (fun n w => w n) {(y, y)} 1 w ≠ ⊤} < 1) :
    Tendsto (fun n : ℕ => P.real {ω | X n ω = y}) atTop (𝓝 0) := by
  have hn : ∀ n, P.real {ω | X n ω = y} = ((κ ^ n) ∘ₘ ν).real {y} := fun n =>
    (eval_markovChainLaw ν κ hX n).measureReal_eq (measurableSet_singleton y)
  simp_rw [hn]
  exact κ.tendsto_pow_comp_apply_singleton_of_parallelComp_return_lt_one ν hy

end ProbabilityTheory.HasLaw
