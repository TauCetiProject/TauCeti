/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MDP.Basic
public import TauCeti.Probability.MDP.Trajectory
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Discounted returns of a Markov decision process

A state-action path `ω : ℕ → S × A` of an MDP collects the discounted rewards
`γ ^ n * reward (ω n).1 (ω n).2`. Its **discounted return** `MDP.pathReturn` is their sum,
and its **`N`-step return** `MDP.finitePathReturn` with terminal value `g` adds the first `N`
discounted rewards and `γ ^ N * g (ω N).1`. For `γ < 1` and rewards bounded by `R`, the
discounted return is bounded by `R / (1 - γ)` and differs from the `N`-step return with terminal
value `0` by at most `γ ^ N * R / (1 - γ)`, path by path.

The controlled transition kernel `MDP.transKernel` draws the next state from `trans s a`. With
it, every history-dependent policy `π` and initial state `s` give the trajectory law
`π.trajLaw M.transKernel s` on paths. The **expected discounted return**
`MDP.expectedReturn M γ π s` and the **`N`-step return** `MDP.finiteReturn M γ N g π s` are the
integrals of the two path returns against this law. The path estimates integrate to the bound
`|expectedReturn| ≤ R / (1 - γ)` and to the tail bound
`|expectedReturn - finiteReturn N 0| ≤ γ ^ N * R / (1 - γ)`, so the `N`-step returns converge to
the expected discounted return. The one-step recursion `MDP.finitePathReturn_succ` splits off the
first reward, as backward induction does.

When every transition is deterministic, `trans s a = pure (f s a)`, the trajectory law follows
the transitions almost surely. If moreover `f` and the reward ignore the action, every policy has
the same `N`-step return, computed along the orbit `f^[n] s`.

## Main results

* `MDP.abs_pathReturn_sub_finitePathReturn_le`: the pathwise tail bound.
* `MDP.pathReturn_sub_finitePathReturn_zero`: the exact discounted return of the shifted path.
* `MDP.abs_expectedReturn_le`: the expected discounted return is bounded by `R / (1 - γ)`.
* `MDP.abs_expectedReturn_sub_finiteReturn_le`: the tail bound for expected returns, and
  `MDP.tendsto_finiteReturn`: the `N`-step returns converge to the expected discounted return.
* `MDP.finiteReturn_zero`: the `0`-step return is the terminal value at the initial state.
* `MDP.expectedReturn_zero_discount`: at discount `0` the expected return is the mean reward of
  the first action.
* `MDP.finiteReturn_eq_of_trans_eq_pure`: the `N`-step return along deterministic,
  action-independent transitions.

## References

* M. L. Puterman, *Markov decision processes: discrete stochastic dynamic programming*, Wiley,
  1994, Sections 2.1.6 and 5.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal ENNReal

namespace TauCeti.MDP

variable {S A : Type*} (M : MDP S A)

/-! ### Returns along a path -/

section Path

/-- The discounted return `∑' n, γ ^ n * reward (ω n).1 (ω n).2` of a state-action path `ω`. -/
def pathReturn (γ : ℝ≥0) (ω : ℕ → S × A) : ℝ :=
  ∑' n, (γ : ℝ) ^ n * M.reward (ω n).1 (ω n).2

/-- The defining formula of `pathReturn`. -/
theorem pathReturn_def (γ : ℝ≥0) (ω : ℕ → S × A) :
    M.pathReturn γ ω = ∑' n, (γ : ℝ) ^ n * M.reward (ω n).1 (ω n).2 := (rfl)

/-- The `N`-step discounted return of a state-action path `ω` with terminal value `g`: the first
`N` discounted rewards plus `γ ^ N * g (ω N).1`. -/
def finitePathReturn (γ : ℝ≥0) (N : ℕ) (g : S → ℝ) (ω : ℕ → S × A) : ℝ :=
  ∑ n ∈ range N, (γ : ℝ) ^ n * M.reward (ω n).1 (ω n).2 + (γ : ℝ) ^ N * g (ω N).1

/-- The defining formula of `finitePathReturn`. -/
theorem finitePathReturn_def (γ : ℝ≥0) (N : ℕ) (g : S → ℝ) (ω : ℕ → S × A) :
    M.finitePathReturn γ N g ω =
      ∑ n ∈ range N, (γ : ℝ) ^ n * M.reward (ω n).1 (ω n).2 + (γ : ℝ) ^ N * g (ω N).1 := (rfl)

/-- The `0`-step return of a path is the terminal value at its initial state. -/
@[simp]
theorem finitePathReturn_zero (γ : ℝ≥0) (g : S → ℝ) (ω : ℕ → S × A) :
    M.finitePathReturn γ 0 g ω = g (ω 0).1 := by
  simp [finitePathReturn_def]

/-- The `(N + 1)`-step return of a path is its first reward plus `γ` times the `N`-step return of
the shifted path. -/
theorem finitePathReturn_succ (γ : ℝ≥0) (N : ℕ) (g : S → ℝ) (ω : ℕ → S × A) :
    M.finitePathReturn γ (N + 1) g ω =
      M.reward (ω 0).1 (ω 0).2 + γ * M.finitePathReturn γ N g (fun n ↦ ω (n + 1)) := by
  simp only [finitePathReturn_def, sum_range_succ', pow_succ', mul_add, mul_sum, mul_assoc]
  ring

private theorem norm_discount_mul_reward_le (γ : ℝ≥0) (ω : ℕ → S × A) (n : ℕ) :
    ‖(γ : ℝ) ^ n * M.reward (ω n).1 (ω n).2‖ ≤ (γ : ℝ) ^ n * M.rewardBound := by
  rw [norm_mul, norm_pow, Real.norm_of_nonneg γ.coe_nonneg, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (M.abs_reward_le _ _) (pow_nonneg γ.coe_nonneg _)

/-- The discounted rewards along a path are absolutely summable when `γ < 1`. -/
theorem summable_norm_discount_mul_reward {γ : ℝ≥0} (hγ : γ < 1) (ω : ℕ → S × A) :
    Summable fun n ↦ ‖(γ : ℝ) ^ n * M.reward (ω n).1 (ω n).2‖ :=
  ((summable_geometric_of_lt_one γ.coe_nonneg hγ).mul_right M.rewardBound).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (M.norm_discount_mul_reward_le γ ω)

/-- The discounted rewards along a path are summable when `γ < 1`. -/
theorem summable_discount_mul_reward {γ : ℝ≥0} (hγ : γ < 1) (ω : ℕ → S × A) :
    Summable fun n ↦ (γ : ℝ) ^ n * M.reward (ω n).1 (ω n).2 :=
  (M.summable_norm_discount_mul_reward hγ ω).of_norm

/-- For `γ < 1` the discounted return of a path is its first reward plus `γ` times the discounted
return of the shifted path. -/
theorem pathReturn_eq_add {γ : ℝ≥0} (hγ : γ < 1) (ω : ℕ → S × A) :
    M.pathReturn γ ω = M.reward (ω 0).1 (ω 0).2 + γ * M.pathReturn γ (fun n ↦ ω (n + 1)) := by
  rw [pathReturn_def, (M.summable_discount_mul_reward hγ ω).tsum_eq_zero_add, pathReturn_def,
    ← tsum_mul_left]
  simp only [pow_zero, one_mul, pow_succ', mul_assoc]

/-- After the first `N` rewards, the remaining return is the return on the shifted path
discounted by `γ ^ N`. -/
theorem pathReturn_sub_finitePathReturn_zero {γ : ℝ≥0} (hγ : γ < 1) (N : ℕ)
    (ω : ℕ → S × A) :
    M.pathReturn γ ω - M.finitePathReturn γ N 0 ω =
      (γ : ℝ) ^ N * M.pathReturn γ (fun n ↦ ω (n + N)) := by
  simp only [pathReturn_def, finitePathReturn_def, Pi.zero_apply, mul_zero, add_zero]
  rw [← (M.summable_discount_mul_reward hγ ω).sum_add_tsum_nat_add N, add_sub_cancel_left,
    ← tsum_mul_left]
  congr 1
  funext n
  rw [pow_add]
  ring

/-- For `γ < 1` the discounted return of a path is bounded by `rewardBound / (1 - γ)`. -/
theorem abs_pathReturn_le {γ : ℝ≥0} (hγ : γ < 1) (ω : ℕ → S × A) :
    |M.pathReturn γ ω| ≤ M.rewardBound / (1 - γ) := by
  rw [pathReturn_def, ← Real.norm_eq_abs, div_eq_inv_mul]
  exact tsum_of_norm_bounded ((hasSum_geometric_of_lt_one γ.coe_nonneg hγ).mul_right _)
    (M.norm_discount_mul_reward_le γ ω)

/-- **The pathwise tail bound.** For `γ < 1` the discounted return of a path differs from its
`N`-step return with terminal value `0` by at most `γ ^ N * rewardBound / (1 - γ)`. -/
theorem abs_pathReturn_sub_finitePathReturn_le {γ : ℝ≥0} (hγ : γ < 1) (N : ℕ)
    (ω : ℕ → S × A) :
    |M.pathReturn γ ω - M.finitePathReturn γ N 0 ω| ≤ γ ^ N * M.rewardBound / (1 - γ) := by
  rw [M.pathReturn_sub_finitePathReturn_zero hγ, abs_mul,
    abs_of_nonneg (pow_nonneg γ.coe_nonneg _), mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (M.abs_pathReturn_le hγ _) (pow_nonneg γ.coe_nonneg _)

/-- The `N`-step return of a path with a terminal value bounded by `C` is bounded by
`∑ n < N, γ ^ n * rewardBound + γ ^ N * C`. -/
theorem abs_finitePathReturn_le (γ : ℝ≥0) (N : ℕ) {g : S → ℝ} {C : ℝ} (hg : ∀ s, |g s| ≤ C)
    (ω : ℕ → S × A) :
    |M.finitePathReturn γ N g ω| ≤
      ∑ n ∈ range N, (γ : ℝ) ^ n * M.rewardBound + (γ : ℝ) ^ N * C := by
  rw [finitePathReturn_def]
  refine (abs_add_le _ _).trans (add_le_add ((abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun n _ ↦ ?_)) ?_)
  · rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (M.abs_reward_le _ _) (by positivity)
  · rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hg _) (by positivity)

variable [MeasurableSpace S] [MeasurableSpace A] [Countable S] [MeasurableSingletonClass S]
  [Countable A] [MeasurableSingletonClass A]

/-- The reward at time `n` is a measurable function of the path. -/
private theorem measurable_reward_eval (n : ℕ) :
    Measurable fun ω : ℕ → S × A ↦ M.reward (ω n).1 (ω n).2 :=
  (measurable_of_countable fun sa : S × A ↦ M.reward sa.1 sa.2).comp (measurable_pi_apply n)

/-- The `N`-step return is a measurable function of the path. -/
@[fun_prop]
theorem measurable_finitePathReturn (γ : ℝ≥0) (N : ℕ) (g : S → ℝ) :
    Measurable (M.finitePathReturn γ N g) := by
  have hg : Measurable fun ω : ℕ → S × A ↦ g (ω N).1 :=
    (measurable_of_countable g).comp (measurable_fst.comp (measurable_pi_apply N))
  exact (Finset.measurable_sum _ fun n _ ↦ (M.measurable_reward_eval n).const_mul _).add
    (hg.const_mul _)

/-- The discounted return is a measurable function of the path for every discount. -/
@[fun_prop]
theorem measurable_pathReturn (γ : ℝ≥0) : Measurable (M.pathReturn γ) :=
  Measurable.tsum fun n ↦ (M.measurable_reward_eval n).const_mul _

/-- For `γ < 1` the discounted return is integrable for every finite measure on paths. -/
theorem integrable_pathReturn {γ : ℝ≥0} (hγ : γ < 1) (μ : Measure (ℕ → S × A))
    [IsFiniteMeasure μ] : Integrable (M.pathReturn γ) μ :=
  Integrable.of_bound (M.measurable_pathReturn γ).aestronglyMeasurable _
    (Eventually.of_forall fun ω ↦ (Real.norm_eq_abs _).trans_le (M.abs_pathReturn_le hγ ω))

/-- The `N`-step return with a bounded terminal value is integrable for every finite measure on
paths. -/
theorem integrable_finitePathReturn (γ : ℝ≥0) (N : ℕ) {g : S → ℝ} {C : ℝ}
    (hg : ∀ s, |g s| ≤ C) (μ : Measure (ℕ → S × A)) [IsFiniteMeasure μ] :
    Integrable (M.finitePathReturn γ N g) μ :=
  Integrable.of_bound (M.measurable_finitePathReturn γ N g).aestronglyMeasurable _
    (Eventually.of_forall fun ω ↦
      (Real.norm_eq_abs _).trans_le (M.abs_finitePathReturn_le γ N hg ω))

end Path

/-! ### Expected returns under a policy -/

variable [MeasurableSpace S] [MeasurableSpace A] [Countable S] [MeasurableSingletonClass S]
  [Countable A] [MeasurableSingletonClass A]

/-- The controlled transition kernel, drawing the next state from `trans s a` at the
state-action pair `(s, a)`. -/
def transKernel : Kernel (S × A) S :=
  Kernel.ofPMF fun sa ↦ M.trans sa.1 sa.2

/-- The row of the transition kernel at `sa = (s, a)` is the measure of `trans s a`. -/
theorem transKernel_apply (sa : S × A) : M.transKernel sa = (M.trans sa.1 sa.2).toMeasure :=
  Kernel.ofPMF_apply _ sa

/-- The transition kernel moves from `(s, a)` to `t` with probability `trans s a t`. -/
@[simp]
theorem transKernel_apply_singleton (s : S) (a : A) (t : S) :
    M.transKernel (s, a) {t} = M.trans s a t :=
  Kernel.ofPMF_apply_singleton _ (s, a) t

instance : IsMarkovKernel M.transKernel :=
  inferInstanceAs (IsMarkovKernel (Kernel.ofPMF _))

/-- The expected discounted return of the history-dependent policy `π` from the state `s`: the
integral of the discounted return against the trajectory law. -/
def expectedReturn (γ : ℝ≥0) (π : HistoryPolicy S A) (s : S) : ℝ :=
  ∫ ω, M.pathReturn γ ω ∂(π.trajLaw M.transKernel s)

/-- The defining formula of `expectedReturn`. -/
theorem expectedReturn_def (γ : ℝ≥0) (π : HistoryPolicy S A) (s : S) :
    M.expectedReturn γ π s = ∫ ω, M.pathReturn γ ω ∂(π.trajLaw M.transKernel s) := (rfl)

/-- The `N`-step return with terminal value `g` of the history-dependent policy `π` from the
state `s`: the integral of the `N`-step path return against the trajectory law. -/
def finiteReturn (γ : ℝ≥0) (N : ℕ) (g : S → ℝ) (π : HistoryPolicy S A) (s : S) : ℝ :=
  ∫ ω, M.finitePathReturn γ N g ω ∂(π.trajLaw M.transKernel s)

/-- The defining formula of `finiteReturn`. -/
theorem finiteReturn_def (γ : ℝ≥0) (N : ℕ) (g : S → ℝ) (π : HistoryPolicy S A) (s : S) :
    M.finiteReturn γ N g π s = ∫ ω, M.finitePathReturn γ N g ω ∂(π.trajLaw M.transKernel s) :=
  (rfl)

variable (π : HistoryPolicy S A) (s : S)

/-- For `γ < 1` the expected discounted return is bounded by `rewardBound / (1 - γ)`. -/
theorem abs_expectedReturn_le {γ : ℝ≥0} (hγ : γ < 1) :
    |M.expectedReturn γ π s| ≤ M.rewardBound / (1 - γ) := by
  simpa [expectedReturn_def] using norm_integral_le_of_norm_le_const
    (μ := π.trajLaw M.transKernel s) (Eventually.of_forall fun ω ↦
      (Real.norm_eq_abs _).trans_le (M.abs_pathReturn_le hγ ω))

/-- The `N`-step return with a terminal value bounded by `C` is bounded by
`∑ n < N, γ ^ n * rewardBound + γ ^ N * C`. -/
theorem abs_finiteReturn_le (γ : ℝ≥0) (N : ℕ) {g : S → ℝ} {C : ℝ} (hg : ∀ s, |g s| ≤ C) :
    |M.finiteReturn γ N g π s| ≤
      ∑ n ∈ range N, (γ : ℝ) ^ n * M.rewardBound + (γ : ℝ) ^ N * C := by
  simpa [finiteReturn_def] using norm_integral_le_of_norm_le_const
    (μ := π.trajLaw M.transKernel s) (Eventually.of_forall fun ω ↦
      (Real.norm_eq_abs _).trans_le (M.abs_finitePathReturn_le γ N hg ω))

/-- **The tail bound.** For `γ < 1` the expected discounted return differs from the `N`-step
return with terminal value `0` by at most `γ ^ N * rewardBound / (1 - γ)`. -/
theorem abs_expectedReturn_sub_finiteReturn_le {γ : ℝ≥0} (hγ : γ < 1) (N : ℕ) :
    |M.expectedReturn γ π s - M.finiteReturn γ N 0 π s| ≤
      γ ^ N * M.rewardBound / (1 - γ) := by
  have h0 : ∀ s : S, |(0 : S → ℝ) s| ≤ 0 := fun _ ↦ by simp
  rw [expectedReturn_def, finiteReturn_def, ← integral_sub (M.integrable_pathReturn hγ _)
    (M.integrable_finitePathReturn γ N h0 _)]
  simpa using norm_integral_le_of_norm_le_const (μ := π.trajLaw M.transKernel s)
    (Eventually.of_forall fun ω ↦
      (Real.norm_eq_abs _).trans_le (M.abs_pathReturn_sub_finitePathReturn_le hγ N ω))

/-- For `γ < 1` the `N`-step returns with terminal value `0` converge to the expected discounted
return as `N → ∞`. -/
theorem tendsto_finiteReturn {γ : ℝ≥0} (hγ : γ < 1) :
    Tendsto (fun N ↦ M.finiteReturn γ N 0 π s) atTop (𝓝 (M.expectedReturn γ π s)) := by
  have hlim : Tendsto (fun N : ℕ ↦ (γ : ℝ) ^ N * M.rewardBound / (1 - γ)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one γ.coe_nonneg hγ).mul_const
      M.rewardBound).div_const (1 - (γ : ℝ))
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg) (fun N ↦ ?_) hlim)
  rw [Real.dist_eq, abs_sub_comm]
  exact M.abs_expectedReturn_sub_finiteReturn_le π s hγ N

/-- The `0`-step return is the terminal value at the initial state. -/
@[simp]
theorem finiteReturn_zero (γ : ℝ≥0) (g : S → ℝ) : M.finiteReturn γ 0 g π s = g s := by
  rw [finiteReturn_def, integral_congr_ae ((π.trajLaw_ae_state_zero M.transKernel s).mono
    fun ω hω ↦ by rw [finitePathReturn_zero, hω])]
  simp

/-- At discount `0` the expected return is the mean reward of the first action, drawn from
`π.first s`. -/
theorem expectedReturn_zero_discount :
    M.expectedReturn 0 π s = ∫ a, M.reward s a ∂(π.first s) := by
  have hpath (ω : ℕ → S × A) : M.pathReturn 0 ω = M.reward (ω 0).1 (ω 0).2 := by
    rw [pathReturn_def, tsum_eq_single 0 fun n hn ↦ by simp [hn]]
    simp
  have hmeas : Measurable fun sa : S × A ↦ M.reward sa.1 sa.2 := measurable_of_countable _
  have hint : Integrable (fun sa : S × A ↦ M.reward sa.1 sa.2)
      (Measure.dirac s ⊗ₘ π.first) :=
    Integrable.of_bound hmeas.aestronglyMeasurable M.rewardBound
      (Eventually.of_forall fun sa ↦ (Real.norm_eq_abs _).trans_le (M.abs_reward_le _ _))
  simp_rw [expectedReturn_def, hpath]
  rw [← integral_map (φ := fun ω : ℕ → S × A ↦ ω 0) (measurable_pi_apply 0).aemeasurable
      (f := fun sa : S × A ↦ M.reward sa.1 sa.2) hmeas.aestronglyMeasurable,
    HistoryPolicy.trajLaw_map_eval_zero, Measure.integral_compProd hint, integral_dirac]

/-! ### Deterministic transitions -/

/-- Under deterministic transitions `trans s a = pure (f s a)`, the state at time `n + 1` is
almost surely `f` of the state-action pair at time `n`. -/
theorem trajLaw_ae_state_succ_of_trans_eq_pure {f : S → A → S}
    (htrans : ∀ s a, M.trans s a = PMF.pure (f s a)) :
    ∀ᵐ ω ∂π.trajLaw M.transKernel s, ∀ n, (ω (n + 1)).1 = f (ω n).1 (ω n).2 := by
  refine ae_all_iff.2 fun n ↦ ?_
  have hmeas : Measurable fun x : ℕ → S × A ↦ (x n, (x (n + 1)).1) := by fun_prop
  have hstep : ∀ᵐ p ∂((π.trajLaw M.transKernel s).map (fun x ↦ x n) ⊗ₘ M.transKernel),
      p.2 = f p.1.1 p.1.2 :=
    Kernel.ae_compProd_ofPMF_of_eq_pure fun sa : S × A ↦ htrans sa.1 sa.2
  rw [← π.trajLaw_map_eval_state_succ M.transKernel s n] at hstep
  exact ae_of_ae_map hmeas.aemeasurable hstep

/-- Under deterministic transitions `trans s a = pure (f s)` that ignore the action, the state at
time `n` is almost surely `f^[n] s`. -/
theorem trajLaw_ae_state_eq_iterate {f : S → S} (htrans : ∀ s a, M.trans s a = PMF.pure (f s)) :
    ∀ᵐ ω ∂π.trajLaw M.transKernel s, ∀ n, (ω n).1 = f^[n] s := by
  filter_upwards [π.trajLaw_ae_state_zero M.transKernel s,
    M.trajLaw_ae_state_succ_of_trans_eq_pure π s (f := fun s _ ↦ f s) htrans] with ω h0 hsucc n
  induction n with
  | zero => exact h0
  | succ n ih => rw [hsucc, ih, Function.iterate_succ_apply']

/-- Under deterministic action-independent transitions `trans s a = pure (f s)` and an
action-independent reward `r`, every policy has `N`-step return
`∑ n < N, γ ^ n * r (f^[n] s) + γ ^ N * g (f^[N] s)`. -/
theorem finiteReturn_eq_of_trans_eq_pure {f : S → S}
    (htrans : ∀ s a, M.trans s a = PMF.pure (f s)) {r : S → ℝ} (hr : ∀ s a, M.reward s a = r s)
    (γ : ℝ≥0) (N : ℕ) (g : S → ℝ) :
    M.finiteReturn γ N g π s =
      ∑ n ∈ range N, (γ : ℝ) ^ n * r (f^[n] s) + (γ : ℝ) ^ N * g (f^[N] s) := by
  have h : M.finitePathReturn γ N g =ᵐ[π.trajLaw M.transKernel s] fun _ ↦
      ∑ n ∈ range N, (γ : ℝ) ^ n * r (f^[n] s) + (γ : ℝ) ^ N * g (f^[N] s) :=
    (M.trajLaw_ae_state_eq_iterate π s htrans).mono fun ω hω ↦ by
      simp only [finitePathReturn_def, hr, hω]
  rw [finiteReturn_def, integral_congr_ae h, integral_const]
  simp

end TauCeti.MDP

