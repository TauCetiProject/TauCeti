/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Examples.HardCore.Basic
public import TauCeti.Probability.Distributions.HardCore
public import TauCeti.Probability.MarkovChain.Coupling.Convergence
public import TauCeti.Probability.MarkovChain.Product.Basic
public import TauCeti.Probability.Kernel.Matrix.Invariance

/-!
# Equilibrium of the hard-core sampling chain

The activity-weighted hard-core law satisfies detailed balance for single-site heat-bath
updates, including at activity zero. Consequently it is invariant. For positive activity,
the chain converges to this law in total variation from every initial probability law.
At activity one the limiting law is uniform on independent sets.

The convergence argument uses the finite irreducible square chain and meeting-time coupling;
it needs no bound on the partition function or return-time means.

## References

* Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025, Chapter 4
  (hard-core sampling).
* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8
  (coupling proof of convergence).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.HardCore

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Removing an occupied vertex balances the reverse accepted insertion. -/
private theorem delete_insert_balance (a : ℝ≥0) (I : State G) (v : V) (hi : v ∈ I.val) :
    G.hardCorePMF a I * ENNReal.ofReal (1 - activityProbability a) =
      G.hardCorePMF a (erase G I v) * ENNReal.ofReal (activityProbability a) := by
  have hw := G.hardCorePMF_single_site_balance a I (erase G I v) v
    (by ext w; simp)
  simp only [erase_val, Finset.notMem_erase, hi, ite_false, ite_true, mul_one] at hw
  have hp : ENNReal.ofReal (activityProbability a) = (a : ℝ≥0∞) / (1 + a) := by
    rw [coe_activityProbability, ENNReal.ofReal_div_of_pos (by positivity)]
    simp [ENNReal.ofReal_add, ENNReal.ofReal_coe_nnreal]
  have hq : ENNReal.ofReal (1 - activityProbability a) = (1 + (a : ℝ≥0∞))⁻¹ := by
    have h : (1 : ℝ) - activityProbability a = 1 / (1 + a) := by
      rw [coe_activityProbability]
      field_simp
      ring
    rw [h, ENNReal.ofReal_div_of_pos (by positivity)]
    simp [ENNReal.ofReal_add, ENNReal.ofReal_coe_nnreal]
  rw [hp, hq, hw]
  simp only [div_eq_mul_inv, mul_assoc]

variable [DecidableRel G.Adj]

/-- At one vertex, the two heat-bath outcomes satisfy detailed balance. -/
private theorem single_site_balance (a : ℝ≥0) (I J : State G) (v : V) :
    G.hardCorePMF a I *
        ((if occupy G I v = J then ENNReal.ofReal (activityProbability a) else 0) +
          if erase G I v = J then ENNReal.ofReal (1 - activityProbability a) else 0) =
      G.hardCorePMF a J *
        ((if occupy G J v = I then ENNReal.ofReal (activityProbability a) else 0) +
          if erase G J v = I then ENNReal.ofReal (1 - activityProbability a) else 0) := by
  by_cases hIJ : I = J
  · subst J
    rfl
  by_cases he : erase G I v = erase G J v
  · have hval : I.val.erase v = J.val.erase v := by
      simpa only [erase_val] using congrArg Subtype.val he
    by_cases hi : v ∈ I.val <;> by_cases hj : v ∈ J.val
    · exact (hIJ (Subtype.ext (Finset.erase_injOn' v hi hj hval))).elim
    · have hdel : erase G I v = J := by simpa only [erase_of_notMem G J hj] using he
      have hins : occupy G J v = I := by rw [← hdel, occupy_erase_of_mem G I hi]
      simpa only [occupy_of_mem G I hi, hdel, hins, erase_of_notMem G J hj,
        hIJ, Ne.symm hIJ, ite_false, ite_true, zero_add, add_zero] using
        (delete_insert_balance G a I v hi).trans (by rw [hdel])
    · have hdel : erase G J v = I := by simpa only [erase_of_notMem G I hi] using he.symm
      have hins : occupy G I v = J := by rw [← hdel, occupy_erase_of_mem G J hj]
      simpa only [occupy_of_mem G J hj, hdel, hins, erase_of_notMem G I hi,
        hIJ, Ne.symm hIJ, ite_false, ite_true, zero_add, add_zero] using
        ((delete_insert_balance G a J v hj).trans (by rw [hdel])).symm
    · exact (hIJ (by simpa only [erase_of_notMem G I hi, erase_of_notMem G J hj]
        using he)).elim
  · have hoIJ : occupy G I v ≠ J := fun h =>
      he (erase_eq_of_single_site_eq G I J v (Or.inl h))
    have hdIJ : erase G I v ≠ J := fun h =>
      he (erase_eq_of_single_site_eq G I J v (Or.inr h))
    have hoJI : occupy G J v ≠ I := fun h =>
      he (erase_eq_of_single_site_eq G J I v (Or.inl h)).symm
    have hdJI : erase G J v ≠ I := fun h =>
      he (erase_eq_of_single_site_eq G J I v (Or.inr h)).symm
    simp [hoIJ, hdIJ, hoJI, hdJI]

variable [Nonempty V]

/-- The Gibbs masses balance every transition of the hard-core heat bath, even at
zero activity and for blocked insertions. -/
theorem detailed_balance (a : ℝ≥0) (I J : State G) :
    G.hardCorePMF a I * kernel G (activityProbability a) I {J} =
      G.hardCorePMF a J * kernel G (activityProbability a) J {I} := by
  simp only [kernel_apply_singleton, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  simpa only [mul_left_comm] using
    congrArg ((Fintype.card V : ℝ≥0∞)⁻¹ * ·) (single_site_balance G a I J v)

/-- The hard-core heat-bath kernel is reversible for the activity-weighted law.
Positive activity is not needed for reversibility. -/
theorem isReversible (a : ℝ≥0) :
    (kernel G (activityProbability a)).IsReversible (G.hardCorePMF a).toMeasure := by
  apply (Kernel.isReversible_iff_isSymm_diagonal_mul _ _).mpr
  apply Matrix.IsSymm.ext_iff.mpr
  intro I J
  apply ENNReal.coe_injective
  simpa only [Matrix.diagonal_mul, ENNReal.coe_mul, Kernel.coe_toMatrix_apply,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] using
    detailed_balance G a J I

/-- The activity-weighted law is stationary for the hard-core heat bath. -/
theorem invariant (a : ℝ≥0) :
    (kernel G (activityProbability a)).Invariant (G.hardCorePMF a).toMeasure :=
  (isReversible G a).invariant

/-- For positive activity the hard-core chain converges in total variation to its Gibbs law
from every initial probability measure. -/
theorem tendsto_tvDist (a : ℝ≥0) (ha : 0 < a) (ν : Measure (State G))
    [IsProbabilityMeasure ν] :
    Tendsto (fun n : ℕ => tvDist
      (((kernel G (activityProbability a)) ^ n : Kernel (State G) (State G)) ∘ₘ ν)
      (G.hardCorePMF a).toMeasure) atTop (𝓝 0) := by
  have hp := (activityProbability_pos_iff a).mpr ha
  have hq := activityProbability_lt_one a
  let := isIrreducible G (activityProbability a) hp hq
  let := (isAperiodic G (activityProbability a) hp hq).isIrreducible_parallelComp
    (isAperiodic G (activityProbability a) hp hq)
  simpa only [((invariant G a).pow _).def] using
    (kernel G (activityProbability a)).tendsto_tvDist_pow_comp_of_parallelComp_isRecurrent
      (Kernel.isRecurrent_of_finite (κ := kernel G (activityProbability a) ∥ₖ
        kernel G (activityProbability a)) (empty G, empty G)) ν (G.hardCorePMF a).toMeasure

/-- At activity one the heat bath samples independent vertex sets uniformly in the limit. -/
theorem tendsto_tvDist_uniform (ν : Measure (State G)) [IsProbabilityMeasure ν] :
    Tendsto (fun n : ℕ => tvDist
      (((kernel G (activityProbability 1)) ^ n : Kernel (State G) (State G)) ∘ₘ ν)
      (Measure.uniformOfFinset (Finset.univ : Finset (State G)))) atTop (𝓝 0) := by
  have hμ : (G.hardCorePMF 1).toMeasure =
      Measure.uniformOfFinset (Finset.univ : Finset (State G)) := by
    -- The distribution API enumerates independent sets using classical decidability.
    convert G.hardCorePMF_one_toMeasure using 2
    ext I
    simp
  simpa only [hμ] using tendsto_tvDist G 1 zero_lt_one ν

end TauCeti.Probability.HardCore
