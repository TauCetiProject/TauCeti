/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MDP.Bellman
public import TauCeti.Probability.MDP.PolicyGradient.Value
public import TauCeti.Probability.Kernel.Matrix.Basic

/-!
# The state kernel of a stationary policy and the matrix form of its value

A randomized stationary policy `π : S → PMF A` in a Markov decision process `M` turns the
controlled transitions into a Markov chain on the states: from `s`, draw an action from `π s` and
then the next state from `M.trans s a`. Its transition kernel is `M.stationaryKernel π`, the
`Kernel.ofPMF` of the binds `(π s).bind (M.trans s)`, with mass `∑ a, π s a * M.trans s a s'`
at `s'`.

Integrating a bounded function against this kernel averages its expected next values over the
actions (`MDP.integral_stationaryKernel`), so the Bellman evaluation operator of `π` is the mean
reward of `π` plus `γ` times integration against the kernel
(`MDP.bellmanEval_apply_eq_meanReward_add_integral`). The real transition matrix of the kernel is
the transition matrix `M.transMatrix` of the weight table of `π`
(`MDP.transMatrix_toReal_eq_map_toMatrix`).

On a finite state space the evaluation operator is therefore the affine map `v ↦ r^π + γ P^π v`
(`MDP.coe_bellmanEval_eq_meanReward_add_mulVec`). For `γ < 1` the value of `π` is
`(1 - γ P^π)⁻¹ r^π`, the value `M.policyValue` of its weight table
(`MDP.coe_value_eq_policyValue`), so the matrix identities proved for weight tables, such as the
performance difference identity, apply to the values of stationary policies. Expanding the inverse
as a Neumann series gives `V^π = ∑ₖ γ ^ k (P^π) ^ k r^π` (`MDP.hasSum_value`).

## References

* M. L. Puterman, *Markov decision processes: discrete stochastic dynamic programming*, Wiley,
  1994, §6.1 and Theorem 6.1.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

namespace TauCeti.MDP

variable {S A : Type*} [MeasurableSpace S] (M : MDP S A)

section Countable

variable [Countable S] [MeasurableSingletonClass S]

/-- The state kernel of a randomized stationary policy `π`: from `s`, an action is drawn from
`π s` and the next state from `M.trans s a`. -/
def stationaryKernel (π : S → PMF A) : Kernel S S :=
  Kernel.ofPMF fun s ↦ (π s).bind (M.trans s)

/-- The state kernel of `π` is the `Kernel.ofPMF` of the binds `(π s).bind (M.trans s)`. -/
theorem stationaryKernel_def (π : S → PMF A) :
    M.stationaryKernel π = Kernel.ofPMF fun s ↦ (π s).bind (M.trans s) := (rfl)

instance (π : S → PMF A) : IsMarkovKernel (M.stationaryKernel π) := by
  rw [stationaryKernel_def]
  infer_instance

/-- The row of the state kernel at `s` is the measure of the bind `(π s).bind (M.trans s)`. -/
theorem stationaryKernel_apply (π : S → PMF A) (s : S) :
    M.stationaryKernel π s = ((π s).bind (M.trans s)).toMeasure := by
  rw [stationaryKernel_def, Kernel.ofPMF_apply]

/-- The state kernel of a deterministic policy `d` follows the transition law of the action
`d s`. -/
@[simp]
theorem stationaryKernel_ofDet (d : S → A) :
    M.stationaryKernel (ofDet d) = Kernel.ofPMF fun s ↦ M.trans s (d s) := by
  simp only [stationaryKernel_def, ofDet_apply, PMF.pure_bind]

variable [Fintype A]

/-- The state kernel moves from `s` to `s'` with probability `∑ a, π s a * M.trans s a s'`. -/
@[simp]
theorem stationaryKernel_apply_singleton (π : S → PMF A) (s s' : S) :
    M.stationaryKernel π s {s'} = ∑ a, π s a * M.trans s a s' := by
  rw [stationaryKernel_def, Kernel.ofPMF_apply_singleton, PMF.bind_apply, tsum_fintype]

/-- Integrating a bounded function against the state kernel of `π` averages its expected next
values over the actions drawn from `π s`. -/
theorem integral_stationaryKernel (π : S → PMF A) (v : BoundedFn S) (s : S) :
    ∫ s', v s' ∂(M.stationaryKernel π s) = ∑ a, (π s a).toReal * M.expect v s a := by
  have hv : Integrable v (M.stationaryKernel π s) :=
    Integrable.of_bound (measurable_of_countable v).aestronglyMeasurable ‖v‖
      (Filter.Eventually.of_forall fun t ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero v t)
  rw [stationaryKernel_apply, PMF.toMeasure_bind_eq_sum] at hv ⊢
  rw [integral_sum_measure hv, tsum_fintype]
  simp only [integral_smul_measure, smul_eq_mul, expect_eq_integral]

/-- The Bellman evaluation operator of `π` is its mean reward plus `γ` times the integral against
its state kernel: `T^π v s = r^π s + γ ∫ v ∂(κ^π s)`. -/
theorem bellmanEval_apply_eq_meanReward_add_integral (γ : ℝ≥0) (π : S → PMF A)
    (v : BoundedFn S) (s : S) :
    M.bellmanEval γ π v s =
      M.meanReward (fun s a ↦ (π s a).toReal) s + γ * ∫ s', v s' ∂(M.stationaryKernel π s) := by
  simp only [bellmanEval_apply, meanReward_apply, integral_stationaryKernel, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ ↦ by ring

/-- The transition matrix of the weight table of `π` is the real coercion of the transition matrix
of its state kernel. -/
theorem transMatrix_toReal_eq_map_toMatrix (π : S → PMF A) :
    M.transMatrix (fun s a ↦ (π s a).toReal) =
      (M.stationaryKernel π).toMatrix.map ((↑) : ℝ≥0 → ℝ) := by
  ext s s'
  simp [transMatrix_apply, Kernel.toMatrix_apply, ENNReal.coe_toNNReal_eq_toReal,
    ENNReal.toReal_sum, ENNReal.mul_ne_top, PMF.apply_ne_top]

omit [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] in
/-- The transition matrix of a deterministic policy `d` has the transition probabilities of the
action `d s` in the row `s`. -/
theorem transMatrix_ofDet (d : S → A) (s s' : S) :
    M.transMatrix (fun s a ↦ (ofDet d s a).toReal) s s' = (M.trans s (d s) s').toReal := by
  classical
  simp [PMF.pure_apply, apply_ite ENNReal.toReal, ite_mul]

end Countable

section Finite

variable [MeasurableSingletonClass S] [Fintype S] [Fintype A]

/-- On a finite state space, the Bellman evaluation operator of `π` is the affine map
`v ↦ r^π + γ P^π v`. -/
theorem coe_bellmanEval_eq_meanReward_add_mulVec (γ : ℝ≥0) (π : S → PMF A) (v : BoundedFn S) :
    ⇑(M.bellmanEval γ π v) = M.meanReward (fun s a ↦ (π s a).toReal) +
      (γ : ℝ) • (M.transMatrix (fun s a ↦ (π s a).toReal) *ᵥ ⇑v) := by
  ext s
  simp only [bellmanEval_apply, expect_eq_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    meanReward_apply, mulVec, dotProduct, transMatrix_apply, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

variable [DecidableEq S]

/-- **The value as a resolvent.** On a finite state space and for `γ < 1`, the value of a
randomized stationary policy `π` is `V^π = (1 - γ P^π)⁻¹ r^π`, the value `M.policyValue` of the
weight table of `π`. -/
theorem coe_value_eq_policyValue {γ : ℝ≥0} (hγ : γ < 1) (π : S → PMF A) :
    ⇑(M.value γ π) = M.policyValue γ (fun s a ↦ (π s a).toReal) := by
  set w : BoundedFn S := ⟨M.policyValue γ (fun s a ↦ (π s a).toReal), Memℓp.all (p := ∞) _⟩
  -- Mathlib has no simp lemma for the coercion of an `lp` element built with the constructor.
  have hw' : ⇑w = M.policyValue γ (fun s a ↦ (π s a).toReal) := rfl
  have hw : M.bellmanEval γ π w = w := by
    refine lp.ext ?_
    rw [coe_bellmanEval_eq_meanReward_add_mulVec, hw']
    exact (policyValue_eq_meanReward_add hγ (isPolicy_toReal π)).symm
  rw [← (M.bellmanEval_eq_self_iff hγ π).1 hw, hw']

/-- On a finite state space and for `γ < 1`, the value of `π` is the sum of its discounted mean
rewards after `k` steps: `V^π = ∑ₖ γ ^ k (P^π) ^ k r^π`. -/
theorem hasSum_value {γ : ℝ≥0} (hγ : γ < 1) (π : S → PMF A) :
    HasSum (fun k ↦ (γ : ℝ) ^ k • (M.transMatrix (fun s a ↦ (π s a).toReal) ^ k *ᵥ
      M.meanReward (fun s a ↦ (π s a).toReal))) ⇑(M.value γ π) :=
  M.coe_value_eq_policyValue hγ π ▸ hasSum_policyValue hγ (isPolicy_toReal π)

end Finite

end TauCeti.MDP
