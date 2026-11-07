/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Examples.IntegerWalk.Basic
public import TauCeti.Probability.MarkovChain.Recurrence
public import TauCeti.Analysis.SpecificLimits.CentralBinomial

/-!
# Recurrence of nearest-neighbor integer walks

The integer walk is recurrent exactly when its right-step probability is one half.
Every other parameter, including the deterministic endpoints, gives a transient walk.
For such a walk, from any finite initial law, almost every path visits each integer
only finitely often. This statement also holds for arbitrary realizations of the path law.

The diagonal Green function is the central-binomial series with parameter `p * (1 - p)`:
odd-time returns have zero mass. Its divergence criterion therefore gives recurrence
without assuming a return or hitting estimate. The symmetric case returns to its starting
state infinitely often almost surely; no finite-mean assertion about those returns is made.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.5–1.6.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TauCeti.Probability

/-- The diagonal Green function of integer walk is its even-time central-binomial series.
The term at zero counts the initial visit. -/
theorem integerWalk_tsum_pow_apply_self (p : unitInterval) (x : ℤ) :
    ∑' n : ℕ, (integerWalk p ^ n) x {x} =
      ∑' n : ℕ, (n.centralBinom : ℝ≥0∞) *
        ((unitInterval.toNNReal p * (1 - unitInterval.toNNReal p) : ℝ≥0) : ℝ≥0∞) ^ n := by
  rw [← tsum_even_add_odd (f := fun n : ℕ => (integerWalk p ^ n) x {x})
    CompleteLattice.summable CompleteLattice.summable]
  simp only [integerWalk_pow_odd_apply_self, tsum_zero, add_zero]
  apply tsum_congr
  intro n
  have hp : unitInterval.toNNReal p ≤ 1 := by exact_mod_cast p.2.2
  rw [integerWalk_pow_even_apply_self, ← ENNReal.ofReal_coe_nnreal]
  simp [NNReal.coe_sub hp, ← Nat.centralBinom_eq_two_mul_choose,
    ENNReal.ofReal_mul, ENNReal.ofReal_pow (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)),
    ← mul_pow, mul_assoc]

/-- An integer walk returns almost surely exactly for the symmetric step law.
This includes the deterministic parameters zero and one. -/
-- Simplify before the endpoint rules replace `integerWalk` by a deterministic kernel.
@[simp↓]
theorem integerWalk_isRecurrent_iff (p : unitInterval) (x : ℤ) :
    (integerWalk p).IsRecurrent x ↔ (p : ℝ) = 1 / 2 := by
  rw [Kernel.isRecurrent_iff_tsum_eq_top, integerWalk_tsum_pow_apply_self,
    NNReal.tsum_centralBinom_mul_mul_one_sub_pow_eq_top_iff (unitInterval.toNNReal p)
      (by exact_mod_cast p.2.2)]
  rw [← NNReal.coe_inj]
  simp only [unitInterval.coe_toNNReal, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]

/-- Every biased integer walk is transient, including the deterministic walks. -/
-- As for recurrence, preserve the walk-specific normal form at the endpoints.
@[simp↓]
theorem integerWalk_isTransient_iff (p : unitInterval) (x : ℤ) :
    (integerWalk p).IsTransient x ↔ (p : ℝ) ≠ 1 / 2 := by
  rw [Kernel.isTransient_iff, integerWalk_isRecurrent_iff]

/-- The symmetric walk returns to its initial state infinitely often almost surely. -/
theorem integerWalk_ae_infinite_setOf_eq (p : unitInterval) (hp : (p : ℝ) = 1 / 2)
    (x : ℤ) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac x) (integerWalk p), {n | ω n = x}.Infinite :=
  (integerWalk p).ae_infinite_setOf_eq_markovChainLaw_dirac
    (Kernel.isRecurrent_iff.mp ((integerWalk_isRecurrent_iff p x).mpr hp))

/-- From any finite initial measure, a biased integer walk visits every integer only
finitely often, on one common full-measure event. -/
theorem integerWalk_ae_forall_finite_setOf_eq (p : unitInterval)
    (hp : (p : ℝ) ≠ 1 / 2) (ν : Measure ℤ) [IsFiniteMeasure ν] :
    ∀ᵐ ω ∂markovChainLaw ν (integerWalk p), ∀ y : ℤ, {n | ω n = y}.Finite := by
  apply ae_all_iff.mpr
  intro y
  have h := Measure.markovChainLaw_setOf_infinite_setOf_eq_eq_zero ν (integerWalk p)
    (Kernel.isTransient_iff_return_probability_lt_one.mp
      ((integerWalk_isTransient_iff p y).mpr hp))
  simpa only [ae_iff, Set.Infinite] using h

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- Finiteness of visits for a biased integer walk transfers to any realization.
No topology or canonical construction of the sample space is required. -/
theorem integerWalk_ae_forall_finite_setOf_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ν : Measure ℤ} [IsFiniteMeasure ν] {p : unitInterval}
    {X : Ω → ℕ → ℤ} (hX : HasLaw X (markovChainLaw ν (integerWalk p)) P)
    (hp : (p : ℝ) ≠ 1 / 2) :
    ∀ᵐ ω ∂P, ∀ y : ℤ, {n | X ω n = y}.Finite := by
  have h := TauCeti.Probability.integerWalk_ae_forall_finite_setOf_eq p hp ν
  rw [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

end ProbabilityTheory.HasLaw
