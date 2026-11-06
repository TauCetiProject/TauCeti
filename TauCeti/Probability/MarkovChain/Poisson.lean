/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.RandomWalk
public import TauCeti.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

/-!
# Discrete skeletons with Poisson increments

Sampling a nondecreasing counting process with stationary independent Poisson increments
on a fixed time grid gives an additive Markov chain: its transition from `i` is the law
of `i + Poisson(λΔ)`. The conclusion identifies the whole path law, not just marginals,
and holds on an arbitrary measurable sample space. The process starts at zero almost
surely; neither continuity nor nonexplosion is needed for this discrete-time assertion.

The transition powers add their rates. Zero rate gives the identity kernel, so the
zero-rate and zero-mesh cases are included without exponential waiting times.

See Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025, Chapter 6,
for the connection between Poisson processes and their discrete skeletons. The scalar
convolution identity is Mathlib's `poissonMeasure_conv_poissonMeasure`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti.Probability

open MeasureTheory.Measure

/-- Composing Poisson-increment steps adds their rates. -/
theorem additiveWalk_poissonMeasure_comp (r s : ℝ≥0) :
    additiveWalk (poissonMeasure s) ∘ₖ additiveWalk (poissonMeasure r) =
      additiveWalk (poissonMeasure (r + s)) := by
  rw [additiveWalk_comp, poissonMeasure_conv_poissonMeasure]

/-- The `n`-step kernel of the Poisson random walk has increment law `Poisson(nr)`. -/
theorem additiveWalk_poissonMeasure_pow (r : ℝ≥0) (n : ℕ) :
    additiveWalk (poissonMeasure r) ^ n = additiveWalk (poissonMeasure (n * r)) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul, poissonMeasure_zero, additiveWalk_dirac_zero]
    rfl
  | succ n ih =>
    rw [Kernel.pow_add, pow_one, ih, additiveWalk_poissonMeasure_comp]
    congr 2
    push_cast
    ring

/-- The fixed-grid counts of a nondecreasing process starting at zero with independent
Poisson increments have the homogeneous Markov-chain path law with transition
`i ↦ i + Poisson(λΔ)`. Monotonicity and the initial value are needed only almost surely.
Zero rate and a zero mesh are allowed. -/
theorem hasLaw_markovChainLaw_poissonSkeleton
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℝ≥0 → Ω → ℕ}
    (hN : ∀ t, Measurable (N t))
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t => N t ω))
    (hzero : ∀ᵐ ω ∂P, N 0 ω = 0)
    (hindep : HasIndepIncrements N P) (rate Δ : ℝ≥0)
    (hlaw : ∀ t, HasLaw (fun ω => N (t + Δ) ω - N t ω)
      (poissonMeasure (rate * Δ)) P) :
    HasLaw (fun ω (n : ℕ) => N ((n : ℝ≥0) * Δ) ω)
      (markovChainLaw (Measure.dirac 0) (poissonMeasure (rate * Δ)).additiveWalk) P := by
  let U (n : ℕ) (ω : Ω) := N (((n : ℝ≥0) + 1) * Δ) ω - N (n * Δ) ω
  have hU : ∀ n, Measurable (U n) := by intro n; fun_prop
  have hi : iIndepFun U P := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hindep.nat (t := fun n : ℕ => (n : ℝ≥0) * Δ)
        (fun i j hij => mul_le_mul_of_nonneg_right (by exact_mod_cast hij) zero_le)
  have hUlaw : ∀ n, HasLaw (U n) (poissonMeasure (rate * Δ)) P := by
    intro n
    simpa only [U, add_mul, one_mul] using hlaw (n * Δ)
  have hsum := hasLaw_markovChainLaw_partialSums hU hi hUlaw 0
  apply hsum.congr
  filter_upwards [hmono, hzero] with ω hm hz
  funext n
  have ht : Monotone (fun n : ℕ => N (n * Δ) ω) :=
    hm.comp (fun i j hij => mul_le_mul_of_nonneg_right (by exact_mod_cast hij) zero_le)
  simpa [U, hz] using (Finset.sum_range_tsub ht n).symm

end TauCeti.Probability
