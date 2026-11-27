/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MDP.Basic
public import TauCeti.Probability.MDP.Trajectory
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Returns of a history-dependent policy

The discounted path return sums the rewards of a state-action trajectory. The finite path
return sums the first `N` rewards and adds a discounted terminal value at the state at time
`N`. Integrating these functions against `HistoryPolicy.trajLaw` gives the corresponding
expected returns.

The finite return is defined for any nonnegative discount. For a discount below one,
`MDP.abs_expectedReturn_sub_finiteReturn_le` bounds the error of truncating the infinite
return by a geometric tail, uniformly over policies and initial states.

## References

* M. L. Puterman, *Markov Decision Processes* (1994), §§4.1 and 5.3.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti.MDP

variable {S A : Type*} (M : MDP S A) {γ : ℝ≥0}

/-- The infinite discounted reward along a state-action path. -/
def discountedPathReturn (γ : ℝ≥0) (x : ℕ → S × A) : ℝ :=
  ∑' n, (γ : ℝ) ^ n * M.reward (x n).1 (x n).2

/-- The path return is the series of discounted rewards. -/
theorem discountedPathReturn_eq_tsum (x : ℕ → S × A) :
    M.discountedPathReturn γ x = ∑' n, (γ : ℝ) ^ n * M.reward (x n).1 (x n).2 := (rfl)

/-- The first `N` discounted rewards and the discounted terminal value at time `N`. -/
def finitePathReturn (γ : ℝ≥0) (N : ℕ) (g : BoundedFn S) (x : ℕ → S × A) : ℝ :=
  (∑ n ∈ Finset.range N, (γ : ℝ) ^ n * M.reward (x n).1 (x n).2) +
    (γ : ℝ) ^ N * g (x N).1

/-- The finite path return adds the discounted terminal value to the finite reward sum. -/
theorem finitePathReturn_eq_sum (N : ℕ) (g : BoundedFn S) (x : ℕ → S × A) :
    M.finitePathReturn γ N g x =
      (∑ n ∈ Finset.range N, (γ : ℝ) ^ n * M.reward (x n).1 (x n).2) +
        (γ : ℝ) ^ N * g (x N).1 := (rfl)

/-- At horizon zero the path return consists of the terminal value at the initial state. -/
@[simp]
theorem finitePathReturn_zero (g : BoundedFn S) (x : ℕ → S × A) :
    M.finitePathReturn γ 0 g x = g (x 0).1 := by
  simp [finitePathReturn]

/-- Splitting off the first reward gives the finite return on the path from time one. -/
theorem finitePathReturn_succ (N : ℕ) (g : BoundedFn S) (x : ℕ → S × A) :
    M.finitePathReturn γ (N + 1) g x =
      M.reward (x 0).1 (x 0).2 + (γ : ℝ) * M.finitePathReturn γ N g (fun n ↦ x (n + 1)) := by
  simp only [finitePathReturn_eq_sum, Finset.sum_range_succ', pow_zero, one_mul, pow_succ',
    mul_add, Finset.mul_sum, mul_assoc]
  ac_rfl

private theorem norm_discounted_reward_le (x : ℕ → S × A) (n : ℕ) :
    ‖(γ : ℝ) ^ n * M.reward (x n).1 (x n).2‖ ≤ (γ : ℝ) ^ n * M.rewardBound := by
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg γ.coe_nonneg _), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (M.abs_reward_le _ _) (pow_nonneg γ.coe_nonneg _)

/-- Below discount one, the rewards of every path are absolutely summable after discounting. -/
theorem summable_norm_discounted_reward (hγ : γ < 1) (x : ℕ → S × A) :
    Summable (fun n ↦ ‖(γ : ℝ) ^ n * M.reward (x n).1 (x n).2‖) :=
  ((summable_geometric_of_lt_one γ.coe_nonneg (NNReal.coe_lt_coe.mpr hγ)).mul_right
    M.rewardBound).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (M.norm_discounted_reward_le x)

/-- The absolute infinite return along any path is bounded by the discounted reward bound. -/
theorem abs_discountedPathReturn_le (hγ : γ < 1) (x : ℕ → S × A) :
    |M.discountedPathReturn γ x| ≤ M.rewardBound / (1 - (γ : ℝ)) := by
  rw [discountedPathReturn, ← Real.norm_eq_abs, div_eq_inv_mul]
  exact tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one γ.coe_nonneg (NNReal.coe_lt_coe.mpr hγ)).mul_right _)
    (M.norm_discounted_reward_le x)

/-- The finite return is bounded by the sum of the discounted reward bounds and the
discounted sup norm of the terminal value. -/
theorem abs_finitePathReturn_le (N : ℕ) (g : BoundedFn S) (x : ℕ → S × A) :
    |M.finitePathReturn γ N g x| ≤
      (∑ n ∈ Finset.range N, (γ : ℝ) ^ n * M.rewardBound) + (γ : ℝ) ^ N * ‖g‖ := by
  rw [finitePathReturn, ← Real.norm_eq_abs]
  refine (norm_add_le _ _).trans (add_le_add (norm_sum_le_of_le _ fun n _ ↦
    M.norm_discounted_reward_le x n) ?_)
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg γ.coe_nonneg _)]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero g _) (by positivity)

/-- Beyond horizon `N`, the remaining discounted reward is the return on the shifted path
multiplied by the discount for reaching time `N`. -/
theorem discountedPathReturn_sub_finitePathReturn_zero (hγ : γ < 1) (N : ℕ)
    (x : ℕ → S × A) :
    M.discountedPathReturn γ x - M.finitePathReturn γ N 0 x =
      (γ : ℝ) ^ N * M.discountedPathReturn γ (fun n ↦ x (n + N)) := by
  have hs := (M.summable_norm_discounted_reward hγ x).of_norm
  simp only [discountedPathReturn, finitePathReturn, lp.coeFn_zero, Pi.zero_apply, mul_zero,
    add_zero]
  rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [pow_add]
  ring

/-- The discounted path return is the initial reward plus the discounted return from time one. -/
theorem discountedPathReturn_eq_reward_add (hγ : γ < 1) (x : ℕ → S × A) :
    M.discountedPathReturn γ x =
      M.reward (x 0).1 (x 0).2 + (γ : ℝ) * M.discountedPathReturn γ (fun n ↦ x (n + 1)) := by
  have h := M.discountedPathReturn_sub_finitePathReturn_zero hγ 1 x
  simpa [finitePathReturn_succ, add_comm] using (sub_eq_iff_eq_add.mp h)

/-- Truncating a path after its first `N` rewards costs at most the geometric tail bound. -/
theorem abs_discountedPathReturn_sub_finitePathReturn_le (hγ : γ < 1) (N : ℕ)
    (x : ℕ → S × A) :
    |M.discountedPathReturn γ x - M.finitePathReturn γ N 0 x| ≤
      (γ : ℝ) ^ N * M.rewardBound / (1 - (γ : ℝ)) := by
  rw [M.discountedPathReturn_sub_finitePathReturn_zero hγ, abs_mul, abs_of_nonneg (by positivity),
    mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (M.abs_discountedPathReturn_le hγ _) (by positivity)

section Measurable

variable [MeasurableSpace S] [MeasurableSpace A] [Countable S] [Countable A]
  [MeasurableSingletonClass S] [MeasurableSingletonClass A]

private theorem measurable_discounted_reward (n : ℕ) :
    Measurable (fun x : ℕ → S × A ↦ (γ : ℝ) ^ n * M.reward (x n).1 (x n).2) :=
  measurable_const.mul ((measurable_of_countable (Function.uncurry M.reward)).comp
    (measurable_pi_apply n))

/-- The discounted return is a measurable function of the path. -/
@[fun_prop]
theorem measurable_discountedPathReturn : Measurable (M.discountedPathReturn γ) :=
  Measurable.tsum (M.measurable_discounted_reward (γ := γ))

/-- The finite return with a bounded terminal value is measurable. -/
@[fun_prop]
theorem measurable_finitePathReturn (N : ℕ) (g : BoundedFn S) :
    Measurable (M.finitePathReturn γ N g) := by
  unfold finitePathReturn
  exact (Finset.measurable_sum _ fun n _ ↦ M.measurable_discounted_reward n).add
    (measurable_const.mul ((measurable_of_countable g).comp
      (measurable_fst.comp (measurable_pi_apply N))))

/-- The expected infinite discounted reward under a history-dependent policy. -/
def expectedReturn (γ : ℝ≥0) (π : HistoryPolicy S A) (s : S) : ℝ :=
  ∫ x, M.discountedPathReturn γ x ∂π.trajLaw M.transKernel s

/-- The expected finite discounted reward, including the terminal value at time `N`. -/
def finiteReturn (γ : ℝ≥0) (N : ℕ) (g : BoundedFn S) (π : HistoryPolicy S A) (s : S) : ℝ :=
  ∫ x, M.finitePathReturn γ N g x ∂π.trajLaw M.transKernel s

/-- The infinite return is obtained by integrating the discounted path return. -/
theorem expectedReturn_eq_integral (π : HistoryPolicy S A) (s : S) :
    M.expectedReturn γ π s = ∫ x, M.discountedPathReturn γ x ∂π.trajLaw M.transKernel s := (rfl)

/-- The finite return is obtained by integrating the finite path return. -/
theorem finiteReturn_eq_integral (N : ℕ) (g : BoundedFn S) (π : HistoryPolicy S A) (s : S) :
    M.finiteReturn γ N g π s = ∫ x, M.finitePathReturn γ N g x ∂π.trajLaw M.transKernel s := (rfl)

/-- With discount below one, the discounted path return is integrable under any finite law. -/
theorem integrable_discountedPathReturn (hγ : γ < 1) (μ : Measure (ℕ → S × A))
    [IsFiniteMeasure μ] : Integrable (M.discountedPathReturn γ) μ :=
  Integrable.of_bound M.measurable_discountedPathReturn.aestronglyMeasurable _
    (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using M.abs_discountedPathReturn_le hγ x)

/-- The finite path return is integrable under any finite law and any nonnegative discount. -/
theorem integrable_finitePathReturn (N : ℕ) (g : BoundedFn S) (μ : Measure (ℕ → S × A))
    [IsFiniteMeasure μ] : Integrable (M.finitePathReturn γ N g) μ :=
  Integrable.of_bound (M.measurable_finitePathReturn N g).aestronglyMeasurable _
    (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using M.abs_finitePathReturn_le N g x)

/-- At horizon zero the expected return equals the terminal value at the starting state. -/
@[simp]
theorem finiteReturn_zero (g : BoundedFn S) (π : HistoryPolicy S A) (s : S) :
    M.finiteReturn γ 0 g π s = g s := by
  rw [finiteReturn_eq_integral]
  exact integral_eq_const (by
    filter_upwards [π.trajLaw_ae_state_zero M.transKernel s] with x hx
    rw [finitePathReturn_zero, hx])

/-- The expected discounted return is uniformly bounded over all policies and initial states. -/
theorem abs_expectedReturn_le (hγ : γ < 1) (π : HistoryPolicy S A) (s : S) :
    |M.expectedReturn γ π s| ≤ M.rewardBound / (1 - (γ : ℝ)) := by
  rw [expectedReturn_eq_integral, ← Real.norm_eq_abs]
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := π.trajLaw M.transKernel s)
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using
        M.abs_discountedPathReturn_le hγ x))

/-- Replacing the infinite return by the first `N` rewards incurs at most the geometric tail
bound, for any history-dependent randomized policy. -/
theorem abs_expectedReturn_sub_finiteReturn_le (hγ : γ < 1) (N : ℕ)
    (π : HistoryPolicy S A) (s : S) :
    |M.expectedReturn γ π s - M.finiteReturn γ N 0 π s| ≤
      (γ : ℝ) ^ N * M.rewardBound / (1 - (γ : ℝ)) := by
  rw [expectedReturn_eq_integral, finiteReturn_eq_integral,
    ← integral_sub (M.integrable_discountedPathReturn hγ _) (M.integrable_finitePathReturn N 0 _),
    ← Real.norm_eq_abs]
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := π.trajLaw M.transKernel s)
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using
        M.abs_discountedPathReturn_sub_finitePathReturn_le hγ N x))

end Measurable

end TauCeti.MDP
