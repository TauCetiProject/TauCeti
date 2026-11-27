/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Stochastic
public import TauCeti.Probability.MDP.Basic
import TauCeti.Algebra.Ring.Invertible
import TauCeti.Analysis.Matrix.Stochastic
import TauCeti.Probability.ProbabilityMassFunction.Finite

/-!
# Values of weight tables in a finite discounted Markov decision process

On a finite Markov decision process `M`, a *weight table* is any `π : S → A → ℝ`; it is a
*policy* (`MDP.IsPolicy`) when each row `π s` is a probability vector on the actions. Policy
gradient methods differentiate values with respect to the entries of `π`, so the values are
defined here for every weight table, by linear algebra in `Matrix S S ℝ`:

* `MDP.transMatrix π`, the state transition matrix `P^π s s' = ∑ a, π s a * trans s a s'`, and
  `MDP.meanReward π`, the mean reward `r^π s = ∑ a, π s a * reward s a`;
* `MDP.policyValue γ π`, the value `V^π = (1 - γ P^π)⁻¹ r^π`, where the inverse is
  `Ring.inverse` (and so is `0` when `1 - γ P^π` is singular);
* `MDP.policyQ γ π`, the Q-function `Q^π s a = reward s a + γ ∑ s', trans s a s' * V^π s'`, and
  `MDP.advantage γ π`, the advantage `A^π s a = Q^π s a - V^π s`;
* `MDP.visitation γ μ π`, the discounted state-visitation row vector
  `d^π_μ = (1 - γ) μ (1 - γ P^π)⁻¹` of a weight vector `μ` on the states;
* `MDP.objective γ μ π`, the averaged value `V^π(μ) = ∑ s, μ s * V^π s`.

At a policy and for a discount `γ < 1`, the matrix `P^π` is row stochastic, so `1 - γ P^π` is
invertible and its inverse has nonnegative entries
(`Matrix.isUnit_one_sub_smul_of_mem_rowStochastic` and `Matrix.ringInverse_one_sub_smul_nonneg`).
This gives the identities used to study policy gradients.

## Main results

* `MDP.policyValue_eq_meanReward_add`: the evaluation equation `V^π = r^π + γ P^π V^π`,
  `MDP.hasSum_policyValue`: its Neumann series `V^π = ∑ₖ γ ^ k (P^π) ^ k r^π`, and
  `MDP.sum_mul_advantage_eq_zero`: the advantage has `π`-mean zero at every state.
* `MDP.visitation_nonneg`, `MDP.sum_visitation`, `MDP.smul_le_visitation`: for `μ ≥ 0` the
  visitation vector is nonnegative, has total mass `∑ s, μ s` (for every `μ`), and dominates
  `(1 - γ) μ`.
* `MDP.objective_sub_objective`: the **performance difference identity**
  `V^{π'}(ρ) - V^π(ρ) = (1 - γ)⁻¹ ∑ s, d^{π'}_ρ s ∑ a, π' s a * A^π s a` for a policy `π'`, an
  arbitrary weight table `π` and an arbitrary weight vector `ρ`.

## References

* S. M. Kakade and J. Langford, *Approximately optimal approximate reinforcement learning*,
  ICML 2002, Lemma 6.1 (the performance difference lemma).
* A. Agarwal, S. M. Kakade, J. D. Lee and G. Mahajan, *On the theory of policy gradient methods:
  optimality, approximation, and distribution shift*, J. Mach. Learn. Res. **22** (2021), no. 98,
  Section 3, equation (4) and Lemma 2.
-/

public section

noncomputable section

open Matrix
open scoped ENNReal NNReal

namespace TauCeti.MDP

variable {S A : Type*}

/-- A weight table `π : S → A → ℝ` is a policy when each row `π s` is a probability vector. -/
structure IsPolicy [Fintype A] (π : S → A → ℝ) : Prop where
  /-- The weights of a policy are nonnegative. -/
  nonneg : ∀ s a, 0 ≤ π s a
  /-- The weights of a policy sum to one at every state. -/
  sum_eq_one : ∀ s, ∑ a, π s a = 1

/-- A randomized stationary policy `p : S → PMF A` gives the policy `fun s a ↦ (p s a).toReal`. -/
theorem isPolicy_toReal [Fintype A] (p : S → PMF A) : IsPolicy fun s a ↦ (p s a).toReal where
  nonneg _ _ := ENNReal.toReal_nonneg
  sum_eq_one s := (p s).sum_toReal_eq_one

variable [Fintype A] (M : MDP S A)

/-! ### Definitions -/

/-- The state transition matrix `P^π s s' = ∑ a, π s a * trans s a s'` of a weight table. -/
def transMatrix (π : S → A → ℝ) : Matrix S S ℝ :=
  Matrix.of fun s s' ↦ ∑ a, π s a * (M.trans s a s').toReal

/-- The entries of the transition matrix of a weight table. -/
@[simp]
theorem transMatrix_apply (π : S → A → ℝ) (s s' : S) :
    M.transMatrix π s s' = ∑ a, π s a * (M.trans s a s').toReal := (rfl)

/-- The mean reward `r^π s = ∑ a, π s a * reward s a` of a weight table. -/
def meanReward (π : S → A → ℝ) : S → ℝ :=
  fun s ↦ ∑ a, π s a * M.reward s a

/-- The mean reward of a weight table at a state. -/
@[simp]
theorem meanReward_apply (π : S → A → ℝ) (s : S) :
    M.meanReward π s = ∑ a, π s a * M.reward s a := (rfl)

variable [Fintype S] [DecidableEq S]

/-- The value `V^π = (1 - γ P^π)⁻¹ r^π` of a weight table, with `Ring.inverse` as the inverse. At
a policy and for `γ < 1` it solves the evaluation equation `V = r^π + γ P^π V`
(`MDP.policyValue_eq_meanReward_add`). -/
def policyValue (γ : ℝ≥0) (π : S → A → ℝ) : S → ℝ :=
  Ring.inverse (1 - (γ : ℝ) • M.transMatrix π) *ᵥ M.meanReward π

/-- The value of a weight table, unfolded. -/
theorem policyValue_def (γ : ℝ≥0) (π : S → A → ℝ) :
    M.policyValue γ π = Ring.inverse (1 - (γ : ℝ) • M.transMatrix π) *ᵥ M.meanReward π := (rfl)

/-- The Q-function `Q^π s a = reward s a + γ ∑ s', trans s a s' * V^π s'` of a weight table. -/
def policyQ (γ : ℝ≥0) (π : S → A → ℝ) : S → A → ℝ :=
  fun s a ↦ M.reward s a + γ * ∑ s', (M.trans s a s').toReal * M.policyValue γ π s'

/-- The Q-function of a weight table at a state-action pair, unfolded. -/
theorem policyQ_apply (γ : ℝ≥0) (π : S → A → ℝ) (s : S) (a : A) :
    M.policyQ γ π s a =
      M.reward s a + γ * ∑ s', (M.trans s a s').toReal * M.policyValue γ π s' := (rfl)

/-- The advantage `A^π s a = Q^π s a - V^π s` of a weight table. -/
def advantage (γ : ℝ≥0) (π : S → A → ℝ) : S → A → ℝ :=
  fun s a ↦ M.policyQ γ π s a - M.policyValue γ π s

/-- The advantage of a weight table at a state-action pair, unfolded. -/
theorem advantage_apply (γ : ℝ≥0) (π : S → A → ℝ) (s : S) (a : A) :
    M.advantage γ π s a = M.policyQ γ π s a - M.policyValue γ π s := (rfl)

/-- The discounted state-visitation row vector `d^π_μ = (1 - γ) μ (1 - γ P^π)⁻¹` of a weight
vector `μ` on the states, with `Ring.inverse` as the inverse. -/
def visitation (γ : ℝ≥0) (μ : S → ℝ) (π : S → A → ℝ) : S → ℝ :=
  (1 - (γ : ℝ)) • (μ ᵥ* Ring.inverse (1 - (γ : ℝ) • M.transMatrix π))

/-- The visitation vector of a weight table, unfolded. -/
theorem visitation_def (γ : ℝ≥0) (μ : S → ℝ) (π : S → A → ℝ) :
    M.visitation γ μ π = (1 - (γ : ℝ)) • (μ ᵥ* Ring.inverse (1 - (γ : ℝ) • M.transMatrix π)) :=
  (rfl)

/-- The value `V^π(μ) = ∑ s, μ s * V^π s` of a weight table averaged over a weight vector `μ`. -/
def objective (γ : ℝ≥0) (μ : S → ℝ) (π : S → A → ℝ) : ℝ :=
  ∑ s, μ s * M.policyValue γ π s

/-- The averaged value of a weight table, unfolded. -/
theorem objective_def (γ : ℝ≥0) (μ : S → ℝ) (π : S → A → ℝ) :
    M.objective γ μ π = ∑ s, μ s * M.policyValue γ π s := (rfl)

/-! ### Identities for every weight table -/

/-- Averaging the Q-function of `π` against another weight table `π'` gives the one-step return
`r^{π'} + γ P^{π'} V^π`. -/
theorem sum_mul_policyQ (γ : ℝ≥0) (π' π : S → A → ℝ) (s : S) :
    ∑ a, π' s a * M.policyQ γ π s a =
      M.meanReward π' s + γ * (M.transMatrix π' *ᵥ M.policyValue γ π) s := by
  simp only [policyQ_apply, meanReward_apply, mulVec, dotProduct, transMatrix_apply, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-! ### Identities at policies -/

variable {M}

/-- The transition matrix of a policy is row stochastic. -/
theorem transMatrix_mem_rowStochastic {π : S → A → ℝ} (hπ : IsPolicy π) :
    M.transMatrix π ∈ rowStochastic ℝ S := by
  refine mem_rowStochastic_iff_sum.2 ⟨fun s s' ↦ ?_, fun s ↦ ?_⟩
  · rw [transMatrix_apply]
    exact Finset.sum_nonneg fun a _ ↦ mul_nonneg (hπ.nonneg s a) ENNReal.toReal_nonneg
  · simp only [transMatrix_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, PMF.sum_toReal_eq_one, mul_one, hπ.sum_eq_one]

variable {γ : ℝ≥0} {π : S → A → ℝ}

/-- At a policy and for `γ < 1`, the matrix `1 - γ P^π` is invertible. -/
theorem isUnit_one_sub_smul_transMatrix (hγ : γ < 1) (hπ : IsPolicy π) :
    IsUnit (1 - (γ : ℝ) • M.transMatrix π) :=
  isUnit_one_sub_smul_of_mem_rowStochastic (transMatrix_mem_rowStochastic hπ) γ.coe_nonneg
    (by exact_mod_cast hγ)

/-- At a policy and for `γ < 1`, the value solves the linear system `(1 - γ P^π) V^π = r^π`. -/
theorem one_sub_smul_transMatrix_mulVec_policyValue (hγ : γ < 1) (hπ : IsPolicy π) :
    (1 - (γ : ℝ) • M.transMatrix π) *ᵥ M.policyValue γ π = M.meanReward π := by
  rw [policyValue_def, mulVec_mulVec, Ring.mul_inverse_cancel _
    (isUnit_one_sub_smul_transMatrix hγ hπ), one_mulVec]

/-- The **evaluation equation**: at a policy and for `γ < 1`, `V^π = r^π + γ P^π V^π`. -/
theorem policyValue_eq_meanReward_add (hγ : γ < 1) (hπ : IsPolicy π) :
    M.policyValue γ π = M.meanReward π + (γ : ℝ) • (M.transMatrix π *ᵥ M.policyValue γ π) := by
  conv_lhs =>
    rw [policyValue_def, Ring.inverse_one_sub_eq (isUnit_one_sub_smul_transMatrix hγ hπ)]
  rw [add_mulVec, one_mulVec, smul_mul_assoc, smul_mulVec, ← mulVec_mulVec, ← policyValue_def]

/-- At a policy and for `γ < 1`, the value is the sum of the discounted mean rewards after `k`
steps, the Neumann series `V^π = ∑ₖ γ ^ k (P^π) ^ k r^π`. -/
theorem hasSum_policyValue (hγ : γ < 1) (hπ : IsPolicy π) :
    HasSum (fun k ↦ (γ : ℝ) ^ k • (M.transMatrix π ^ k *ᵥ M.meanReward π))
      (M.policyValue γ π) := by
  have hγ' : |(γ : ℝ)| < 1 := by
    rw [abs_of_nonneg γ.coe_nonneg]
    exact_mod_cast hγ
  have h := (hasSum_pow_smul_of_mem_rowStochastic
    (transMatrix_mem_rowStochastic (M := M) hπ) hγ').map (mulVec.addMonoidHomLeft (M.meanReward π))
    (continuous_id.matrix_mulVec continuous_const)
  rw [policyValue_def]
  convert h using 1
  · ext k s
    simp only [Function.comp_apply, mulVec.addMonoidHomLeft_apply, smul_pow, smul_mulVec]
  · ext s
    simp only [mulVec.addMonoidHomLeft_apply]

/-- At a policy and for `γ < 1`, the `π`-mean of the Q-function is the value. -/
theorem sum_mul_policyQ_eq_policyValue (hγ : γ < 1) (hπ : IsPolicy π) (s : S) :
    ∑ a, π s a * M.policyQ γ π s a = M.policyValue γ π s := by
  have h := congrFun (policyValue_eq_meanReward_add (M := M) hγ hπ) s
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [M.sum_mul_policyQ, h]

/-- At a policy and for `γ < 1`, the advantage has `π`-mean zero at every state. -/
theorem sum_mul_advantage_eq_zero (hγ : γ < 1) (hπ : IsPolicy π) (s : S) :
    ∑ a, π s a * M.advantage γ π s a = 0 := by
  simp only [advantage_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hπ.sum_eq_one, one_mul, sum_mul_policyQ_eq_policyValue hγ hπ, sub_self]

/-- At a policy and for `γ < 1`, the visitation vector of a nonnegative weight vector is
nonnegative. -/
theorem visitation_nonneg (hγ : γ < 1) (hπ : IsPolicy π) {μ : S → ℝ} (hμ : 0 ≤ μ) :
    0 ≤ M.visitation γ μ π := fun s' ↦ by
  have hP := transMatrix_mem_rowStochastic (M := M) hπ
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  rw [visitation_def, Pi.smul_apply, smul_eq_mul]
  simp only [vecMul, dotProduct]
  refine mul_nonneg (sub_nonneg.2 hγ'.le) (Finset.sum_nonneg fun s _ ↦ ?_)
  exact mul_nonneg (hμ s) (ringInverse_one_sub_smul_nonneg hP γ.coe_nonneg hγ' s s')

/-- At a policy and for `γ < 1`, the visitation vector has the total mass of the weight vector. -/
theorem sum_visitation (hγ : γ < 1) (hπ : IsPolicy π) (μ : S → ℝ) :
    ∑ s, M.visitation γ μ π s = ∑ s, μ s := by
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  rw [← dotProduct_one, visitation_def, smul_dotProduct, ← dotProduct_mulVec,
    ringInverse_one_sub_smul_mulVec_one (transMatrix_mem_rowStochastic hπ) γ.coe_nonneg hγ',
    dotProduct_smul, smul_smul, mul_inv_cancel₀ (sub_ne_zero.2 hγ'.ne'), one_smul,
    dotProduct_one]

/-- At a policy and for `γ < 1`, the visitation vector of a nonnegative weight vector `μ`
dominates `(1 - γ) μ`: the term of time `0` already contributes `(1 - γ) μ`. -/
theorem smul_le_visitation (hγ : γ < 1) (hπ : IsPolicy π) {μ : S → ℝ} (hμ : 0 ≤ μ) :
    (1 - (γ : ℝ)) • μ ≤ M.visitation γ μ π := by
  rw [visitation_def]
  set P := M.transMatrix π
  set N := Ring.inverse (1 - (γ : ℝ) • P)
  have hP : P ∈ rowStochastic ℝ S := transMatrix_mem_rowStochastic hπ
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  -- The resolvent satisfies `N = 1 + γ P N`, and `P N` has nonnegative entries.
  have hN : N = 1 + (γ : ℝ) • (P * N) := by
    rw [← smul_mul_assoc]
    exact Ring.inverse_one_sub_eq (isUnit_one_sub_smul_transMatrix hγ hπ)
  have hPN := mul_ringInverse_one_sub_smul_nonneg hP γ.coe_nonneg hγ'
  intro s
  have hsum : 0 ≤ (μ ᵥ* (P * N)) s := by
    simp only [vecMul, dotProduct]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hμ i) (hPN i s)
  have hγ₀ : (0 : ℝ) ≤ γ := γ.coe_nonneg
  rw [hN, vecMul_add, vecMul_one, vecMul_smul]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  nlinarith [mul_nonneg (sub_nonneg.2 hγ'.le) (mul_nonneg hγ₀ hsum)]

/-- At a policy `π'` and for `γ < 1`, the difference of the values of `π'` and of an arbitrary
weight table `π` is the resolvent of `π'` applied to the `π'`-mean of the advantage of `π`. -/
theorem policyValue_sub_policyValue (hγ : γ < 1) {π' : S → A → ℝ} (hπ' : IsPolicy π')
    (π : S → A → ℝ) :
    M.policyValue γ π' - M.policyValue γ π =
      Ring.inverse (1 - (γ : ℝ) • M.transMatrix π') *ᵥ
        fun s ↦ ∑ a, π' s a * M.advantage γ π s a := by
  have hu := isUnit_one_sub_smul_transMatrix (M := M) hγ hπ'
  -- The `π'`-mean of the advantage of `π` is `(1 - γ P^{π'}) (V^{π'} - V^π)`.
  have hg : (fun s ↦ ∑ a, π' s a * M.advantage γ π s a) =
      (1 - (γ : ℝ) • M.transMatrix π') *ᵥ (M.policyValue γ π' - M.policyValue γ π) := by
    rw [mulVec_sub, one_sub_smul_transMatrix_mulVec_policyValue hγ hπ', sub_mulVec, one_mulVec,
      smul_mulVec]
    ext s
    simp only [advantage_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hπ'.sum_eq_one, one_mul, M.sum_mul_policyQ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hg, mulVec_mulVec, Ring.inverse_mul_cancel _ hu, one_mulVec]

/-- The **performance difference identity**: at a policy `π'` and for `γ < 1`, for every weight
table `π` and every weight vector `ρ`,
`V^{π'}(ρ) - V^π(ρ) = (1 - γ)⁻¹ ∑ s, d^{π'}_ρ s ∑ a, π' s a * A^π s a`. -/
theorem objective_sub_objective (hγ : γ < 1) {π' : S → A → ℝ} (hπ' : IsPolicy π')
    (π : S → A → ℝ) (ρ : S → ℝ) :
    M.objective γ ρ π' - M.objective γ ρ π =
      (1 - (γ : ℝ))⁻¹ * ∑ s, M.visitation γ ρ π' s * ∑ a, π' s a * M.advantage γ π s a := by
  have hγ' : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hγ.ne')
  have h := congrArg (ρ ⬝ᵥ ·) (policyValue_sub_policyValue (M := M) hγ hπ' π)
  rw [dotProduct_sub, dotProduct_mulVec] at h
  simp only [dotProduct] at h
  simp only [objective_def, visitation_def, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum]
  rw [← mul_assoc, inv_mul_cancel₀ hγ', one_mul]
  exact h

end TauCeti.MDP
