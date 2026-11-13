/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Binomial.Basic
public import TauCeti.Probability.Kernel.Composition.Power
public import TauCeti.Probability.Process.MarkovChain

/-!
# Nearest-neighbor walks on the integers

`integerWalk p` moves from `x` to `x + 1` with probability `p` and to `x - 1` with
probability `1 - p`. Its time-`n` transition law is the image of the binomial law under
`k ↦ x + 2 * k - n`. Thus the binomial singleton formula computes all transition
probabilities, and states outside this lattice have zero mass. In particular a walk
cannot return at odd times, and its even-time return probabilities are central binomial
weights. The parameters zero and one give deterministic walks.

These computations concern transition laws, not recurrence classification.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §§1.1 and 1.6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

/-- The nearest-neighbor transition kernel on `ℤ`, with probability `p` of moving right. -/
def integerWalk (p : unitInterval) : Kernel ℤ ℤ :=
  Kernel.ofFunOfCountable fun x => bernoulliMeasure (x + 1) (x - 1) p

/-- A row of the integer walk is the two-point law of its two neighbors. -/
theorem integerWalk_apply (p : unitInterval) (x : ℤ) :
    integerWalk p x = bernoulliMeasure (x + 1) (x - 1) p := (rfl)

instance (p : unitInterval) : IsMarkovKernel (integerWalk p) :=
  ⟨fun x => by rw [integerWalk_apply]; infer_instance⟩

/-- The walk moves right with probability `p`. -/
@[simp]
theorem integerWalk_apply_add_one (p : unitInterval) (x : ℤ) :
    integerWalk p x {x + 1} = ENNReal.ofReal p := by
  rw [integerWalk_apply, bernoulliMeasure_apply_of_mem_of_notMem p
    (measurableSet_singleton _) (by simp) (by simp; omega)]
  exact ENNReal.ofReal_coe_nnreal.symm

/-- The walk moves left with probability `1 - p`. -/
@[simp]
theorem integerWalk_apply_sub_one (p : unitInterval) (x : ℤ) :
    integerWalk p x {x - 1} = ENNReal.ofReal (1 - (p : ℝ)) := by
  rw [integerWalk_apply, bernoulliMeasure_apply_of_notMem_of_mem p
    (measurableSet_singleton _) (by simp; omega) (by simp)]
  rw [← unitInterval.coe_symm_eq p,
    ← unitInterval.coe_toNNReal (unitInterval.symm p), ENNReal.ofReal_coe_nnreal]

/-- After `n` steps from `x`, the position is distributed as `x + 2 * B - n`,
where `B` has binomial law with parameters `n` and `p`. -/
theorem integerWalk_pow_apply (p : unitInterval) (n : ℕ) (x : ℤ) :
    (integerWalk p ^ n) x = (binomial n p).map (fun k : ℕ => x + 2 * (k : ℤ) - n) := by
  induction n generalizing x with
  | zero => simp [Kernel.one_def, Kernel.id_apply, binomial_zero]
  | succ n ih =>
    -- Chapman–Kolmogorov adds one Bernoulli step, just as convolution adds a binomial trial.
    rw [Nat.add_comm n 1, Kernel.pow_add, pow_one, Kernel.comp_apply, ih, Nat.add_comm 1 n]
    apply Measure.ext_of_lintegral
    intro f hf
    rw [Measure.lintegral_bind (integerWalk p).aemeasurable hf.aemeasurable,
      lintegral_map (by fun_prop) Measurable.of_discrete,
      ← binomial_conv_binomial n 1 p,
      lintegral_map hf Measurable.of_discrete,
      Measure.lintegral_conv Measurable.of_discrete]
    apply lintegral_congr
    intro k
    simp only [integerWalk_apply, binomial_one_eq_bernoulliMeasure,
      bernoulliMeasure_def, lintegral_add_measure, lintegral_smul_measure,
      lintegral_dirac, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    congr 2 <;> congr 1 <;> omega

/-- A transition to `x + 2 * k - n` has the binomial weight. This also covers `k > n`,
when the binomial coefficient vanishes. -/
theorem integerWalk_pow_apply_singleton (p : unitInterval) (n k : ℕ) (x : ℤ) :
    (integerWalk p ^ n) x {x + 2 * (k : ℤ) - n} =
      ENNReal.ofReal ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) := by
  rw [integerWalk_pow_apply, Measure.map_apply Measurable.of_discrete
    (measurableSet_singleton _)]
  have hpre : (fun j : ℕ => x + 2 * (j : ℤ) - n) ⁻¹' {x + 2 * (k : ℤ) - n} = {k} := by
    ext j
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  rw [hpre, binomial_singleton]

/-- A state not of the form `x + 2 * k - n`, with `0 ≤ k ≤ n`, has zero transition mass. -/
theorem integerWalk_pow_apply_singleton_eq_zero (p : unitInterval) (n : ℕ) (x y : ℤ)
    (hy : ¬ ∃ k : ℕ, k ≤ n ∧ y = x + 2 * (k : ℤ) - n) :
    (integerWalk p ^ n) x {y} = 0 := by
  rw [integerWalk_pow_apply, Measure.map_apply Measurable.of_discrete
    (measurableSet_singleton y)]
  apply measure_mono_null (t := {k : ℕ | n < k})
  · intro k hk
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hk
    exact lt_of_not_ge fun hkn => hy ⟨k, hkn, hk.symm⟩
  · have h := ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial n p))
    simpa only [ae_iff, Set.compl_ofPred, id_eq, not_le] using h

/-- The walk has zero probability of returning in an odd number of steps. -/
@[simp]
theorem integerWalk_pow_odd_apply_self (p : unitInterval) (n : ℕ) (x : ℤ) :
    (integerWalk p ^ (2 * n + 1)) x {x} = 0 := by
  apply integerWalk_pow_apply_singleton_eq_zero
  rintro ⟨k, _, hk⟩
  omega

/-- The even-time return probability is a central binomial weight. -/
theorem integerWalk_pow_even_apply_self (p : unitInterval) (n : ℕ) (x : ℤ) :
    (integerWalk p ^ (2 * n)) x {x} =
      ENNReal.ofReal (((2 * n).choose n : ℝ) * (p : ℝ) ^ n * (1 - (p : ℝ)) ^ n) := by
  have h := integerWalk_pow_apply_singleton p (2 * n) n x
  have hx : x + 2 * (n : ℤ) - (2 * n : ℕ) = x := by omega
  have hn : 2 * n - n = n := by omega
  simpa only [hx, hn] using h

/-- At probability zero, the walk always moves left. -/
@[simp]
theorem integerWalk_zero :
    integerWalk 0 = Kernel.deterministic (fun x : ℤ => x - 1) Measurable.of_discrete := by
  ext x : 1
  simp [integerWalk_apply, Kernel.deterministic_apply]

/-- At probability one, the walk always moves right. -/
@[simp]
theorem integerWalk_one :
    integerWalk 1 = Kernel.deterministic (fun x : ℤ => x + 1) Measurable.of_discrete := by
  ext x : 1
  simp [integerWalk_apply, Kernel.deterministic_apply]

/-- The binomial transition formula is the time-`n` marginal of the canonical path law. -/
theorem integerWalk_markovChainLaw_map_eval (p : unitInterval) (n : ℕ) (x : ℤ) :
    (markovChainLaw (Measure.dirac x) (integerWalk p)).map (fun ω => ω n) =
      (binomial n p).map (fun k : ℕ => x + 2 * (k : ℤ) - n) := by
  rw [Measure.markovChainLaw_map_eval, Measure.dirac_bind (Kernel.measurable _),
    integerWalk_pow_apply]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- On any probability realization of the integer walk, its time-`n` marginal is the
translated and rescaled binomial law. -/
theorem integerWalk_eval {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℤ} {p : unitInterval} {x : ℤ}
    (h : HasLaw (fun ω n => X n ω) (markovChainLaw (Measure.dirac x) (integerWalk p)) μ)
    (n : ℕ) : HasLaw (X n)
      ((binomial n p).map (fun k : ℕ => x + 2 * (k : ℤ) - n)) μ := by
  have hn := HasLaw.eval_markovChainLaw (Measure.dirac x) (integerWalk p) h n
  rwa [Measure.dirac_bind (Kernel.measurable _), integerWalk_pow_apply] at hn

end ProbabilityTheory.HasLaw
