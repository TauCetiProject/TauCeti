/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.MarkovChain.Examples.Absorbing
public import TauCeti.Probability.Process.StoppedValue

/-!
# The last visit in an absorbing two-state chain

In the absorbing chain started at `false`, the last visit to `false` is finite almost surely
if absorption has positive probability. Its survival probabilities are powers of the
one-step probability of remaining at `false`. The whole path from the last visit is almost
surely the path that starts at `false` and moves immediately and permanently to `true`.

This gives a counterexample to extending the strong Markov property to arbitrary measurable
times. The last visit cannot be detected from the history at that time. When the chain can
stay at `false` with positive probability, the future at the last visit has a different law
from a fresh chain started at its state.

See Vincent Tassion, *Applied Stochastic Processes* (2025), §2.3, Theorem 2.6, for the
strong Markov property at stopping times.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace TauCeti.Probability

/-- The last index where a Boolean path is `false`, with value `⊤` for infinitely many such
indices. The supremum is zero if there is no visit. -/
noncomputable def lastVisitFalse (ω : ℕ → Bool) : WithTop ℕ :=
  ⨆ n : ℕ, if ω n = false then (n : WithTop ℕ) else 0

/-- The last visit is at most `n` exactly when the path is `true` at every later time. -/
theorem lastVisitFalse_le_iff (ω : ℕ → Bool) (n : ℕ) :
    lastVisitFalse ω ≤ (n : WithTop ℕ) ↔ ∀ k > n, ω k = true := by
  rw [lastVisitFalse, iSup_le_iff]
  constructor
  · intro h k hk
    cases hω : ω k with
    | true => rfl
    | false =>
      have hle : (k : WithTop ℕ) ≤ (n : WithTop ℕ) := by simpa [hω] using h k
      exact (hk.not_ge (WithTop.coe_le_coe.mp hle)).elim
  · intro h k
    by_cases hω : ω k = false
    · have hle : k ≤ n := le_of_not_gt fun hk => Bool.false_ne_true (hω.symm.trans (h k hk))
      simp only [hω, ite_true]
      exact (WithTop.coe_le_coe.mpr hle : (k : WithTop ℕ) ≤ (n : WithTop ℕ))
    · simp [hω]

/-- On nondecreasing paths, the last visit is at most `n` exactly when the next state is
`true`. -/
theorem lastVisitFalse_le_iff_of_monotone {ω : ℕ → Bool} (hω : Monotone ω) (n : ℕ) :
    lastVisitFalse ω ≤ (n : WithTop ℕ) ↔ ω (n + 1) = true := by
  rw [lastVisitFalse_le_iff]
  refine ⟨fun h => h _ (Nat.lt_succ_self _), fun h k hk => ?_⟩
  have hle := hω (Nat.succ_le_of_lt hk)
  rw [h] at hle
  exact top_le_iff.mp hle

/-- The last visit is measurable on the entire path space. -/
@[fun_prop]
theorem measurable_lastVisitFalse : Measurable lastVisitFalse := by
  apply Measurable.iSup
  intro n
  exact measurable_const.piecewise ((measurable_pi_apply (X := fun _ : ℕ => Bool) n)
    (measurableSet_singleton false)) measurable_const

/-- The last visit to `false` is not a stopping time for the canonical path filtration.
Paths first entering `true` at times one and two have the same time-zero history. -/
theorem not_isStoppingTime_lastVisitFalse :
    ¬ IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => Bool)) lastVisitFalse := by
  intro h
  have hEvent := h.measurableSet_le 0
  rw [Filtration.piLE_eq_comap_prefix] at hEvent
  obtain ⟨A, _, hA⟩ := hEvent
  let x : ℕ → Bool := fun k => decide (0 < k)
  let y : ℕ → Bool := fun k => decide (1 < k)
  have hprefix : (fun i : Fin 1 => x i.val) = fun i : Fin 1 => y i.val := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  have hx := (Set.ext_iff.mp hA x).mpr
    ((lastVisitFalse_le_iff x 0).2 fun k hk => decide_eq_true hk)
  have hy : (fun i : Fin 1 => y i.val) ∈ A := by
    exact hprefix ▸ hx
  have := (lastVisitFalse_le_iff y 0).1 ((Set.ext_iff.mp hA y).mp hy) 1 (by decide)
  simp [y] at this

variable (p : unitInterval)

/-- Surviving past time `n` for the last-visit time is the same as being unabsorbed at
time `n + 1`. -/
theorem measure_lt_lastVisitFalse_absorbingChain (n : ℕ) :
    markovChainLaw (Measure.dirac false) (absorbingChain p)
        {ω | (n : WithTop ℕ) < lastVisitFalse ω} =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1) := by
  calc
    _ = markovChainLaw (Measure.dirac false) (absorbingChain p) {ω | ω (n + 1) = false} := by
      apply measure_congr
      filter_upwards [ae_monotone_absorbingChain p (Measure.dirac false)] with ω hω
      simp [lt_iff_not_ge, lastVisitFalse_le_iff_of_monotone hω]
    _ = _ := by
      rw [Measure.markovChainLaw_setOf_apply_eq_comp,
        Measure.dirac_bind (absorbingChain p ^ (n + 1)).measurable]
      exact absorbingChain_pow_false_false p (n + 1)

/-- Positive absorption probability makes the last visit finite almost surely. -/
theorem ae_lastVisitFalse_ne_top_absorbingChain (hp : p < 1) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac false) (absorbingChain p), lastVisitFalse ω ≠ ⊤ := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  apply le_antisymm _ bot_le
  have hp' : (unitInterval.toNNReal p : ℝ≥0∞) < 1 := by exact_mod_cast hp
  have hlim : Tendsto (fun n : ℕ => (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1))
      atTop (𝓝 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hp').comp (tendsto_add_atTop_nat 1)
  refine ge_of_tendsto' hlim fun n => ?_
  rw [← measure_lt_lastVisitFalse_absorbingChain]
  refine measure_mono fun ω hω => Set.mem_ofPred_eq.mpr ?_
  rw [Set.mem_ofPred_eq.mp hω]
  exact WithTop.coe_lt_top n

/-- The future from the last visit has the law of the path that moves from `false` to
`true` at its first step and stays there. -/
theorem hasLaw_stoppedValue_processShift_lastVisitFalse (hp : p < 1) :
    HasLaw (stoppedValue (processShift (fun n (ω : ℕ → Bool) => ω n)) lastVisitFalse)
      (Measure.dirac (fun k : ℕ => decide (0 < k)))
      (markovChainLaw (Measure.dirac false) (absorbingChain p)) := by
  have hstart : ∀ᵐ ω ∂markovChainLaw (Measure.dirac false) (absorbingChain p), ω 0 = false :=
    markovChainLaw_dirac_ae_apply_zero (absorbingChain p) false
  apply hasLaw_dirac_of_ae_eq
  filter_upwards [hstart, ae_monotone_absorbingChain p (Measure.dirac false),
    ae_lastVisitFalse_ne_top_absorbingChain p hp] with ω h₀ hω hfin
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [stoppedValue_of_eq hn.symm]
  funext k
  rw [processShift_apply]
  cases k with
  | zero =>
    simp only [Nat.add_zero, Nat.lt_irrefl, decide_false]
    cases n with
    | zero => exact h₀
    | succ n =>
      by_contra hn'
      have hle := (lastVisitFalse_le_iff_of_monotone hω n).2
        (Bool.eq_true_of_not_eq_false hn')
      rw [← hn] at hle
      exact (Nat.not_succ_le_self n) (WithTop.coe_le_coe.mp hle)
  | succ k =>
    have hnext := (lastVisitFalse_le_iff_of_monotone hω n).1 (hn.ge)
    have hlater : n + 1 ≤ n + (k + 1) := by omega
    have hle := hω hlater
    rw [hnext] at hle
    simpa only [Nat.zero_lt_succ, decide_true, top_eq_true] using top_le_iff.mp hle

/-- When the probability of staying at `false` is positive, the future at the almost surely
finite last visit differs from the law of the chain started at the stopped state. -/
theorem not_hasLaw_stoppedValue_processShift_lastVisitFalse (hpos : 0 < p) (hp : p < 1) :
    ¬ HasLaw (stoppedValue (processShift (fun n (ω : ℕ → Bool) => ω n)) lastVisitFalse)
      (markovChainLaw (Measure.dirac false) (absorbingChain p))
      (markovChainLaw (Measure.dirac false) (absorbingChain p)) := by
  intro h
  have heq := h.map_eq.symm.trans (hasLaw_stoppedValue_processShift_lastVisitFalse p hp).map_eq
  have hmass := congrArg (fun μ : Measure (ℕ → Bool) => μ {ω | ω 1 = false}) heq
  have hB : MeasurableSet {ω : ℕ → Bool | ω 1 = false} :=
    measurableSet_eq_fun (measurable_pi_apply 1) measurable_const
  have hleave : (fun k : ℕ => decide (0 < k)) ∉ {ω : ℕ → Bool | ω 1 = false} := by simp
  rw [Measure.markovChainLaw_setOf_apply_eq_comp,
    Measure.dirac_bind (absorbingChain p ^ 1).measurable,
    absorbingChain_pow_false_false, pow_one, Measure.dirac_apply' _ hB,
    Set.indicator_of_notMem hleave] at hmass
  exact (ne_of_gt (by exact_mod_cast hpos : 0 < (unitInterval.toNNReal p : ℝ≥0∞))) hmass

end TauCeti.Probability
