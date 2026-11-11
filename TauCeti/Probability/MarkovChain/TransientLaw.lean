/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Visits
public import TauCeti.Probability.Distributions.Geometric.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# The geometric law of visits to a transient state

A chain started at `y` makes a geometrically distributed number of positive-time visits to `y`.
The parameter is the probability of never returning, and must be positive. Mathlib's
`geometricMeasure p` counts failures before the first success: here a failure is a return and a
success is the first nonreturn. Thus the total number of visits, including time zero, is one
plus this geometric variable.

We use `Set.ncard` for the positive-time visit count. It assigns zero to infinite sets; this
choice does not affect the law because visits to a transient state are almost surely finite.
The law is also transferred to processes on arbitrary sample spaces, using their path law.
No countability assumption on the state space or finite-mean return-time assumption is needed.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.5, Lemma 1.5.1.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.Probability Set
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (κ : Kernel α α) [IsMarkovKernel κ] (y : α) {p : unitInterval}

/-- The positive-time visit count has the geometric law with parameter equal to the
nonreturn probability. The case `p = 1`, where there are no returns, is included. -/
theorem hasLaw_ncard_setOf_succ_eq_geometricMeasure (hp : p ≠ 0)
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} = ENNReal.ofReal (1 - (p : ℝ))) :
    HasLaw (fun x : ℕ → α => {n | x (n + 1) = y}.ncard) (geometricMeasure p)
      (markovChainLaw (Measure.dirac y) κ) := by
  have hp0 : 0 < (p : ℝ) := unitInterval.coe_pos.mpr (unitInterval.pos_iff_ne_zero.mpr hp)
  have hρ : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} < 1 := by
    rw [hy]
    exact ENNReal.ofReal_lt_one.mpr (sub_lt_self 1 hp0)
  have hfin : ∀ᵐ x ∂markovChainLaw (Measure.dirac y) κ, {n | x n = y}.Finite := by
    rw [ae_iff]
    simpa only [Set.Infinite] using
      Measure.markovChainLaw_setOf_infinite_setOf_eq_eq_zero (Measure.dirac y) κ hρ
  have hm : Measurable (fun x : ℕ → α => {n | x (n + 1) = y}.ncard) :=
    measurable_ncard.comp (measurable_set_iff.mpr fun n =>
      ((measurableSet_singleton y).preimage (measurable_pi_apply (n + 1))).mem)
  refine ⟨hm.aemeasurable, Measure.ext_of_Ici _ _ fun k => ?_⟩
  rw [Measure.map_apply hm measurableSet_Ici]
  have hevent : {x : ℕ → α | k ≤ {n | x (n + 1) = y}.ncard} =ᵐ[
      markovChainLaw (Measure.dirac y) κ]
      {x | successiveVisit (fun n x => x n) y k x ≠ ⊤} := by
    filter_upwards [hfin, markovChainLaw_dirac_ae_apply_zero κ y] with x hx hx0
    simp only [successiveVisit_ne_top_iff_lt_ncard (X := fun n (x : ℕ → α) => x n) hx,
      ncard_setOf_eq_eq_ncard_setOf_succ_add_one hx hx0, Nat.lt_succ_iff]
  have htail : markovChainLaw (Measure.dirac y) κ
      {x | k ≤ {n | x (n + 1) = y}.ncard} = ENNReal.ofReal (1 - (p : ℝ)) ^ k := by
    rw [measure_congr hevent, markovChainLaw_dirac_setOf_successiveVisit_ne_top, hy]
  -- Membership in the preimage of an upper interval is the visit-count tail inequality.
  have hpre : (fun x : ℕ → α => {n | x (n + 1) = y}.ncard) ⁻¹' Ici k =
      {x | k ≤ {n | x (n + 1) = y}.ncard} := rfl
  rw [hpre, htail]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (measure_ne_top _ _)).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (sub_nonneg.mpr p.2.2)]
  exact (geometricMeasure_real_Ici hp k).symm

/-- The probability of exactly `k` positive-time visits to a transient starting state. -/
theorem markovChainLaw_setOf_ncard_setOf_succ_eq_eq (hp : p ≠ 0)
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} = ENNReal.ofReal (1 - (p : ℝ))) (k : ℕ) :
    markovChainLaw (Measure.dirac y) κ {x | {n | x (n + 1) = y}.ncard = k} =
      ENNReal.ofReal ((1 - (p : ℝ)) ^ k * p) := by
  have hlaw := κ.hasLaw_ncard_setOf_succ_eq_geometricMeasure y hp hy
  simpa only [Set.ofPred_eq_eq_singleton] using
    (hlaw.measure_eq (measurableSet_singleton k)).trans (geometricMeasure_singleton hp k)

/-- The positive-time visit count of a transient starting state is integrable. -/
theorem integrable_ncard_setOf_succ_eq (hp : p ≠ 0)
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} = ENNReal.ofReal (1 - (p : ℝ))) :
    Integrable (fun x : ℕ → α => ({n | x (n + 1) = y}.ncard : ℝ))
      (markovChainLaw (Measure.dirac y) κ) := by
  exact (κ.hasLaw_ncard_setOf_succ_eq_geometricMeasure y hp hy).integrable_fun_comp
    integrable_cast_geometricMeasure

/-- The expected positive-time visit count is the return probability divided by the
nonreturn probability. Integrability is supplied by `integrable_ncard_setOf_succ_eq`. -/
theorem integral_ncard_setOf_succ_eq (hp : p ≠ 0)
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} = ENNReal.ofReal (1 - (p : ℝ))) :
    ∫ x, ({n | x (n + 1) = y}.ncard : ℝ) ∂markovChainLaw (Measure.dirac y) κ =
      (1 - (p : ℝ)) / p := by
  have hlaw := (hasLaw_map (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).aemeasurable).fun_comp
    (κ.hasLaw_ncard_setOf_succ_eq_geometricMeasure y hp hy)
  exact integral_of_hasLaw_map_cast_geometricMeasure hlaw

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α]
  {P : Measure Ω} {X : ℕ → Ω → α} {κ : Kernel α α} [IsMarkovKernel κ]
  {y : α} {p : unitInterval}

/-- The geometric visit law depends only on the path law, not on the sample space. -/
theorem ncard_setOf_succ_eq_geometricMeasure (hX : HasLaw (fun ω n => X n ω)
    (markovChainLaw (Measure.dirac y) κ) P) (hp : p ≠ 0)
    (hy : markovChainLaw (Measure.dirac y) κ
      {x | hittingAfter (fun n x => x n) {y} 1 x ≠ ⊤} = ENNReal.ofReal (1 - (p : ℝ))) :
    HasLaw (fun ω => {n | X (n + 1) ω = y}.ncard) (geometricMeasure p) P := by
  exact (κ.hasLaw_ncard_setOf_succ_eq_geometricMeasure y hp hy).fun_comp hX

end ProbabilityTheory.HasLaw
