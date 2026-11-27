/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MDP.Bellman
public import TauCeti.Probability.MDP.Return
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Order.SuccPred.Nat

/-!
# Checks for discounted returns of a Markov decision process

A constant reward `c` has expected discounted return `c / (1 - γ)` and `N`-step return
`c * (1 - γ ^ N) / (1 - γ)` under every policy, the `0`-step return is the terminal value at the
initial state, and at discount `0` the expected return is the mean first reward
`∑ a, π.first s {a} * reward s a`.

Along the shift `n ↦ n + 1` on `ℕ` with one action, the state at time `n` is `s + n` and the
`N`-step return is `∑ n < N, γ ^ n * reward (s + n) + γ ^ N * g (s + N)`; two alternating states
give the analogous sum along `not^[n] s`. With `S = A` and `trans s a = pure a`, under the
deterministic Markov policy `d` the state at time `n + 1` is the action at time `n`, and the
action at time `n + 1` is `d (n + 1)` of that state, not `d n`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped NNReal ENNReal

namespace TauCeti.Examples.MDPReturn

open TauCeti TauCeti.MDP

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Countable S]
  [MeasurableSingletonClass S] [Countable A] [MeasurableSingletonClass A]
  (M : MDP S A) (π : HistoryPolicy S A) (s : S)

/-! ### Constant rewards, zero horizon and zero discount -/

/-- A constant reward `c` has expected discounted return `c / (1 - γ)`. -/
example {c : ℝ} (hc : ∀ s a, M.reward s a = c) {γ : ℝ≥0} (hγ : γ < 1) :
    M.expectedReturn γ π s = c / (1 - γ) := by
  have h (ω : ℕ → S × A) : M.pathReturn γ ω = c / (1 - γ) := by
    simp only [pathReturn_def, hc, tsum_mul_right,
      tsum_geometric_of_lt_one γ.coe_nonneg hγ, div_eq_inv_mul]
  simp [expectedReturn_def, h]

/-- A constant reward `c` has `N`-step return `c * (1 - γ ^ N) / (1 - γ)` with terminal
value `0`. -/
example {c : ℝ} (hc : ∀ s a, M.reward s a = c) {γ : ℝ≥0} (hγ : γ < 1) (N : ℕ) :
    M.finiteReturn γ N 0 π s = c * (1 - γ ^ N) / (1 - γ) := by
  have hγ' : (γ : ℝ) ≠ 1 := (NNReal.coe_lt_one.2 hγ).ne
  have h (ω : ℕ → S × A) : M.finitePathReturn γ N 0 ω = c * (1 - γ ^ N) / (1 - γ) := by
    rw [finitePathReturn_def]
    simp only [hc, Pi.zero_apply, mul_zero, add_zero, ← sum_mul, geom_sum_eq hγ']
    field_simp [sub_ne_zero.2 hγ', sub_ne_zero.2 hγ'.symm]
    ring
  simp [finiteReturn_def, h]

/-- The `0`-step return is the terminal value at the initial state. -/
example (γ : ℝ≥0) (g : S → ℝ) : M.finiteReturn γ 0 g π s = g s := by simp

/-- At `N = 0` the tail bound is the bound on the expected discounted return. -/
example {γ : ℝ≥0} (hγ : γ < 1) : |M.expectedReturn γ π s| ≤ M.rewardBound / (1 - γ) := by
  simpa using M.abs_expectedReturn_sub_finiteReturn_le π s hγ 0

/-- At discount `0` the expected return is the mean reward of the first action. -/
example [Fintype A] :
    M.expectedReturn 0 π s = ∑ a, (π.first s).real {a} * M.reward s a := by
  rw [expectedReturn_zero_discount, integral_fintype (Integrable.of_finite)]
  simp

/-! ### Deterministic transitions -/

/-- The shift `n ↦ n + 1` on `ℕ` with one action: the state at time `n` is `s + n`. -/
example (M : MDP ℕ Unit) (π : HistoryPolicy ℕ Unit) (s : ℕ)
    (htrans : ∀ n a, M.trans n a = PMF.pure (n + 1)) (γ : ℝ≥0) (N : ℕ) (g : ℕ → ℝ) :
    M.finiteReturn γ N g π s =
      ∑ n ∈ range N, (γ : ℝ) ^ n * M.reward (s + n) () + (γ : ℝ) ^ N * g (s + N) := by
  rw [finiteReturn_eq_of_trans_eq_pure M π s (f := Nat.succ) htrans (r := fun n ↦ M.reward n ())
    (fun _ _ ↦ rfl)]
  simp only [Nat.succ_iterate]

/-- Two states alternating deterministically with one action: the state at time `n` is
`not^[n] s`. -/
example (M : MDP Bool Unit) (π : HistoryPolicy Bool Unit) (s : Bool)
    (htrans : ∀ b a, M.trans b a = PMF.pure (!b)) (γ : ℝ≥0) (N : ℕ) (g : Bool → ℝ) :
    M.finiteReturn γ N g π s =
      ∑ n ∈ range N, (γ : ℝ) ^ n * M.reward (not^[n] s) () + (γ : ℝ) ^ N * g (not^[N] s) :=
  finiteReturn_eq_of_trans_eq_pure M π s htrans (r := fun b ↦ M.reward b ()) (fun _ _ ↦ rfl) γ N g

/-- With `S = A` and `trans s a = pure a`, under the deterministic Markov policy `d` the state at
time `n + 1` is the action at time `n`, and the action at time `n + 1` is `d (n + 1)` of that
state. -/
example (M : MDP Bool Bool) (htrans : ∀ s a, M.trans s a = PMF.pure a) (d : ℕ → Bool → Bool)
    (s : Bool) (n : ℕ) :
    ∀ᵐ ω ∂(HistoryPolicy.ofMarkov fun k ↦ ofDet (d k)).trajLaw M.transKernel s,
      (ω (n + 1)).1 = (ω n).2 ∧ (ω (n + 1)).2 = d (n + 1) (ω (n + 1)).1 := by
  set μ := (HistoryPolicy.ofMarkov fun k ↦ ofDet (d k)).trajLaw M.transKernel s
  have haction : ∀ᵐ ω ∂μ, (ω (n + 1)).2 = d (n + 1) (ω (n + 1)).1 := by
    have h : ∀ᵐ p ∂(μ.map (fun x ↦ (x (n + 1)).1) ⊗ₘ Kernel.ofPMF (ofDet (d (n + 1)))),
        p.2 = d (n + 1) p.1 :=
      Kernel.ae_compProd_ofPMF_of_eq_pure (ofDet_apply (d (n + 1)))
    rw [← HistoryPolicy.trajLaw_ofMarkov_map_eval_succ] at h
    exact ae_of_ae_map (measurable_pi_apply _).aemeasurable h
  filter_upwards [M.trajLaw_ae_state_succ_of_trans_eq_pure _ s (f := fun _ a ↦ a) htrans,
    haction] with ω h1 h2
  exact ⟨h1 n, h2⟩

end TauCeti.Examples.MDPReturn
