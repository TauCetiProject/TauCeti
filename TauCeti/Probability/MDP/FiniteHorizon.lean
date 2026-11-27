/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MDP.Bellman
public import TauCeti.Probability.MDP.Return
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Finite-horizon dynamic programming by backward induction

For a Markov decision process with finitely many actions, a discount `γ` and a bounded terminal
value `g`, the iterates `T^N g` of the Bellman optimality operator `T = M.bellman γ` solve the
`N`-step problem: no history-dependent randomized policy has an `N`-step return
`M.finiteReturn γ N g π s` above `T^N g s`, and a deterministic Markov policy that at each time
`n < N` is greedy for `T^(N - n - 1) g` attains `T^N g s` from every state. Since every function
on the states has a greedy action, such a policy exists, and `T^N g s` is the largest `N`-step
return. The discount factor is arbitrary: `γ ≥ 1` is allowed.

The proof compares the return with a sequence of bounded value functions `v 0, …, v N` through
their **Bellman residuals** `reward s a + γ * M.expect (v (n + 1)) s a - v n s`. Along every
path the `N`-step return with terminal value `v N` telescopes into `v 0` at the initial state
plus the discounted residuals of the actual transitions
(`MDP.finitePathReturn_eq_add_sum`). Under a trajectory law the next state has conditional law
`trans sₙ aₙ` given the past, so the value at the next state integrates to the expected next value
(`MDP.integral_state_succ_eq_integral_expect`), and the `N`-step return of any policy is
`v 0 s` plus the discounted integrals of the residuals (`MDP.finiteReturn_eq_add_sum_integral`).
For `v n = T^(N - n) g` every residual is nonpositive, and it vanishes at greedy actions.

## Main results

* `MDP.finiteReturn_eq_add_sum_integral`: the residual decomposition of the `N`-step return.
* `MDP.finiteReturn_le_bellman_iterate`: every history-dependent policy has `N`-step return at
  most `T^N g s`.
* `MDP.finiteReturn_ofMarkov_ofDet_eq_bellman_iterate`: a deterministic Markov policy greedy for
  `T^(N - n - 1) g` at each time `n < N` attains `T^N g s`.
* `MDP.isGreatest_finiteReturn`, `MDP.iSup_finiteReturn`: `T^N g s` is the largest `N`-step
  return.

## References

* M. L. Puterman, *Markov decision processes: discrete stochastic dynamic programming*, Wiley,
  1994, Theorem 4.5.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped NNReal ENNReal

namespace TauCeti.MDP

variable {S A : Type*} (M : MDP S A)

/-- **Telescoping along a path.** For every sequence of value functions `v`, the `N`-step return
of a path with terminal value `v N` is `v 0` at the initial state plus the discounted Bellman
residuals `reward sₙ aₙ + γ * v (n + 1) sₙ₊₁ - v n sₙ` of its transitions. -/
theorem finitePathReturn_eq_add_sum (γ : ℝ≥0) (N : ℕ) (v : ℕ → S → ℝ) (ω : ℕ → S × A) :
    M.finitePathReturn γ N (v N) ω = v 0 (ω 0).1 + ∑ n ∈ range N, (γ : ℝ) ^ n *
      (M.reward (ω n).1 (ω n).2 + γ * v (n + 1) (ω (n + 1)).1 - v n (ω n).1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ← add_assoc, ← ih]
    simp only [finitePathReturn_def, sum_range_succ, pow_succ]
    ring

variable [MeasurableSpace S] [MeasurableSpace A] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSingletonClass A]

section Residual

variable [Countable A]

/-- Under the trajectory law of any history-dependent policy, the value of a bounded function at
the state at time `n + 1` integrates to the expected next value of the pair at time `n`: given the
past, the next state is drawn from `trans sₙ aₙ`. -/
theorem integral_state_succ_eq_integral_expect (π : HistoryPolicy S A) (s : S) (n : ℕ)
    (v : BoundedFn S) :
    ∫ ω, v (ω (n + 1)).1 ∂(π.trajLaw M.transKernel s) =
      ∫ ω, M.expect v (ω n).1 (ω n).2 ∂(π.trajLaw M.transKernel s) := by
  set μ := π.trajLaw M.transKernel s
  have hv : Measurable (v : S → ℝ) := measurable_of_countable _
  have hint : Integrable (fun p : (S × A) × S ↦ v p.2)
      (μ.map (fun x ↦ x n) ⊗ₘ M.transKernel) :=
    Integrable.of_bound (hv.comp measurable_snd).aestronglyMeasurable ‖v‖
      (Eventually.of_forall fun p ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero v p.2)
  have hmeas : Measurable fun x : ℕ → S × A ↦ (x n, (x (n + 1)).1) := by fun_prop
  calc ∫ ω, v (ω (n + 1)).1 ∂μ
      = ∫ p, v p.2 ∂(μ.map fun x ↦ (x n, (x (n + 1)).1)) :=
        (integral_map hmeas.aemeasurable (hv.comp measurable_snd).aestronglyMeasurable).symm
    _ = ∫ p, v p.2 ∂(μ.map (fun x ↦ x n) ⊗ₘ M.transKernel) := by
        rw [π.trajLaw_map_eval_state_succ]
    _ = ∫ x, M.expect v x.1 x.2 ∂(μ.map fun x ↦ x n) := by
        rw [Measure.integral_compProd hint]
        simp only [transKernel_apply, expect_eq_integral]
    _ = ∫ ω, M.expect v (ω n).1 (ω n).2 ∂μ :=
        integral_map (measurable_pi_apply n).aemeasurable
          (measurable_of_countable fun x : S × A ↦ M.expect v x.1 x.2).aestronglyMeasurable

/-- **The residual decomposition of the `N`-step return.** For every history-dependent policy `π`
and every sequence `v` of bounded value functions, the `N`-step return with terminal value `v N`
is `v 0 s` plus the discounted integrals of the Bellman residuals
`reward s a + γ * M.expect (v (n + 1)) s a - v n s` at the pairs visited at times `n < N`. -/
theorem finiteReturn_eq_add_sum_integral (γ : ℝ≥0) (N : ℕ) (v : ℕ → BoundedFn S)
    (π : HistoryPolicy S A) (s : S) :
    M.finiteReturn γ N (v N) π s = v 0 s + ∑ n ∈ range N, (γ : ℝ) ^ n *
      ∫ ω, M.reward (ω n).1 (ω n).2 + γ * M.expect (v (n + 1)) (ω n).1 (ω n).2 - v n (ω n).1
        ∂(π.trajLaw M.transKernel s) := by
  set μ := π.trajLaw M.transKernel s
  -- Every bounded function of the pair at a fixed time is integrable.
  have hb (n : ℕ) {f : S × A → ℝ} {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) :
      Integrable (fun ω : ℕ → S × A ↦ f (ω n)) μ :=
    Integrable.of_bound
      ((measurable_of_countable f).comp (measurable_pi_apply n)).aestronglyMeasurable C
      (Eventually.of_forall fun _ ↦ hf _)
  have hr (n : ℕ) : Integrable (fun ω : ℕ → S × A ↦ M.reward (ω n).1 (ω n).2) μ :=
    hb n (f := fun x ↦ M.reward x.1 x.2) fun x ↦ (Real.norm_eq_abs _).trans_le (M.abs_reward_le _ _)
  have hv (n k : ℕ) : Integrable (fun ω : ℕ → S × A ↦ v k (ω n).1) μ :=
    hb n (f := fun x ↦ v k x.1) fun x ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero (v k) x.1
  have he (n k : ℕ) : Integrable (fun ω : ℕ → S × A ↦ M.expect (v k) (ω n).1 (ω n).2) μ :=
    hb n (f := fun x ↦ M.expect (v k) x.1 x.2) fun x ↦
      (Real.norm_eq_abs _).trans_le (M.abs_expect_le _ _ _)
  -- Each residual of the actual transition integrates to the residual with the expected next
  -- value.
  have hstep (n : ℕ) : ∫ ω, (M.reward (ω n).1 (ω n).2 + γ * v (n + 1) (ω (n + 1)).1 -
      v n (ω n).1) ∂μ = ∫ ω, (M.reward (ω n).1 (ω n).2 +
        γ * M.expect (v (n + 1)) (ω n).1 (ω n).2 - v n (ω n).1) ∂μ := by
    have h₁ : Integrable (fun ω : ℕ → S × A ↦
        M.reward (ω n).1 (ω n).2 + γ * v (n + 1) (ω (n + 1)).1) μ :=
      (hr n).add ((hv (n + 1) (n + 1)).const_mul _)
    have h₂ : Integrable (fun ω : ℕ → S × A ↦
        M.reward (ω n).1 (ω n).2 + γ * M.expect (v (n + 1)) (ω n).1 (ω n).2) μ :=
      (hr n).add ((he n (n + 1)).const_mul _)
    rw [integral_sub h₁ (hv n n), integral_sub h₂ (hv n n),
      integral_add (hr n) ((hv (n + 1) (n + 1)).const_mul _),
      integral_add (hr n) ((he n (n + 1)).const_mul _), integral_const_mul, integral_const_mul,
      M.integral_state_succ_eq_integral_expect π s n]
  have hres (n : ℕ) : Integrable (fun ω : ℕ → S × A ↦ (γ : ℝ) ^ n *
      (M.reward (ω n).1 (ω n).2 + γ * v (n + 1) (ω (n + 1)).1 - v n (ω n).1)) μ :=
    (((hr n).add ((hv (n + 1) (n + 1)).const_mul _)).sub (hv n n)).const_mul _
  have h0 : ∫ ω, v 0 (ω 0).1 ∂μ = v 0 s := by
    rw [integral_congr_ae ((π.trajLaw_ae_state_zero M.transKernel s).mono fun ω hω ↦
      congrArg (v 0) hω)]
    simp
  rw [finiteReturn_def]
  simp_rw [M.finitePathReturn_eq_add_sum γ N (fun n ↦ v n)]
  rw [integral_add (hv 0 0) (integrable_finsetSum _ fun n _ ↦ hres n), h0,
    integral_finsetSum _ fun n _ ↦ hres n]
  simp_rw [integral_const_mul, hstep]

end Residual

variable [Finite A] [Nonempty A]

omit [MeasurableSpace A] [Countable S] [MeasurableSingletonClass S]
  [MeasurableSingletonClass A] in
/-- The value functions `T^(N - n) g` of backward induction have nonpositive Bellman residuals at
every time `n < N` and every state-action pair. -/
private theorem reward_add_expect_bellman_iterate_le (γ : ℝ≥0) {N n : ℕ} (hn : n < N)
    (g : BoundedFn S) (s : S) (a : A) :
    M.reward s a + γ * M.expect ((M.bellman γ)^[N - (n + 1)] g) s a ≤
      (M.bellman γ)^[N - n] g s := by
  rw [show N - n = N - (n + 1) + 1 by omega, Function.iterate_succ_apply']
  exact M.le_bellman γ _ s a

/-- **Backward induction, upper bound.** For every discount `γ` (also `γ ≥ 1`), every bounded
terminal value `g` and every history-dependent randomized policy `π`, the `N`-step return is at
most `T^N g s`, where `T = M.bellman γ`. -/
theorem finiteReturn_le_bellman_iterate (γ : ℝ≥0) (N : ℕ) (g : BoundedFn S)
    (π : HistoryPolicy S A) (s : S) :
    M.finiteReturn γ N g π s ≤ (M.bellman γ)^[N] g s := by
  have h := M.finiteReturn_eq_add_sum_integral γ N (fun n ↦ (M.bellman γ)^[N - n] g) π s
  simp only [Nat.sub_self, Function.iterate_zero_apply, Nat.sub_zero] at h
  rw [h, add_le_iff_nonpos_right]
  refine sum_nonpos fun n hn ↦ mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_
  refine integral_nonpos fun ω ↦ sub_nonpos.2 ?_
  exact M.reward_add_expect_bellman_iterate_le γ (mem_range.1 hn) g _ _

/-- **Backward induction, attainment.** If the deterministic Markov policy `d` is greedy for
`T^(N - n - 1) g` at every time `n < N`, where `T = M.bellman γ`, then
`ofMarkov (fun n ↦ ofDet (d n))` has `N`-step return `T^N g s` from every state `s`. -/
theorem finiteReturn_ofMarkov_ofDet_eq_bellman_iterate {γ : ℝ≥0} {N : ℕ} {g : BoundedFn S}
    {d : ℕ → S → A} (hd : ∀ n < N, M.IsGreedy γ ((M.bellman γ)^[N - n - 1] g) (d n)) (s : S) :
    M.finiteReturn γ N g (HistoryPolicy.ofMarkov fun n ↦ ofDet (d n)) s =
      (M.bellman γ)^[N] g s := by
  have h := M.finiteReturn_eq_add_sum_integral γ N (fun n ↦ (M.bellman γ)^[N - n] g)
    (HistoryPolicy.ofMarkov fun n ↦ ofDet (d n)) s
  simp only [Nat.sub_self, Function.iterate_zero_apply, Nat.sub_zero] at h
  rw [h, add_eq_left]
  refine sum_eq_zero fun n hn ↦ ?_
  have hn : n < N := mem_range.1 hn
  -- Along almost every path, the action at time `n` is greedy, so the residual vanishes.
  refine mul_eq_zero_of_right _ (integral_eq_zero_of_ae
    ((HistoryPolicy.trajLaw_ofMarkov_ae_action_eq M.transKernel s
      fun n s ↦ ofDet_apply (d n) s).mono fun ω hω ↦ ?_))
  have hg := (M.isGreedy_iff_eq_bellman γ _ (d n)).1 (hd n hn) (ω n).1
  rw [Nat.sub_sub, ← Function.iterate_succ_apply' (M.bellman γ),
    show (N - (n + 1)).succ = N - n by omega] at hg
  dsimp only
  rw [Pi.zero_apply, hω n, sub_eq_zero, hg]

/-- For every discount `γ`, horizon `N` and bounded terminal value `g`, some deterministic Markov
policy attains the `N`-step return `T^N g s` from every state `s`, where `T = M.bellman γ`. -/
theorem exists_finiteReturn_ofMarkov_ofDet_eq_bellman_iterate (γ : ℝ≥0) (N : ℕ)
    (g : BoundedFn S) : ∃ d : ℕ → S → A, ∀ s,
      M.finiteReturn γ N g (HistoryPolicy.ofMarkov fun n ↦ ofDet (d n)) s =
        (M.bellman γ)^[N] g s := by
  choose d hd using fun n ↦ M.exists_isGreedy γ ((M.bellman γ)^[N - n - 1] g)
  exact ⟨d, M.finiteReturn_ofMarkov_ofDet_eq_bellman_iterate fun n _ ↦ hd n⟩

/-- **Backward induction.** For every discount `γ`, horizon `N`, bounded terminal value `g` and
state `s`, the value `T^N g s` is the largest `N`-step return of a history-dependent randomized
policy, where `T = M.bellman γ`. -/
theorem isGreatest_finiteReturn (γ : ℝ≥0) (N : ℕ) (g : BoundedFn S) (s : S) :
    IsGreatest (Set.range fun π : HistoryPolicy S A ↦ M.finiteReturn γ N g π s)
      ((M.bellman γ)^[N] g s) := by
  obtain ⟨d, hd⟩ := M.exists_finiteReturn_ofMarkov_ofDet_eq_bellman_iterate γ N g
  exact ⟨⟨_, hd s⟩, Set.forall_mem_range.2 fun π ↦ M.finiteReturn_le_bellman_iterate γ N g π s⟩

/-- The supremum of the `N`-step returns over history-dependent randomized policies is
`T^N g s`, where `T = M.bellman γ`. -/
theorem iSup_finiteReturn (γ : ℝ≥0) (N : ℕ) (g : BoundedFn S) (s : S) :
    ⨆ π : HistoryPolicy S A, M.finiteReturn γ N g π s = (M.bellman γ)^[N] g s := by
  rw [← sSup_range]
  exact (M.isGreatest_finiteReturn γ N g s).csSup_eq

end TauCeti.MDP
