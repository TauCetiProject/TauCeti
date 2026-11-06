/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.Process.HittingTime
public import TauCeti.Probability.Kernel.Composition.Power
public import TauCeti.Probability.Kernel.PMF
public import TauCeti.Probability.MarkovChain.MarkovProperty

/-!
# An absorbing two-state chain

The state `true` is absorbing, while `false` stays put with probability `p` and moves to
`true` with probability `1 - p`. The transition powers are explicit: the chance of still
being at `false` after `n` steps, starting there, is `p ^ n`.

This example also distinguishes entrance at time zero from positive-time return. Starting
at `false`, a missed first return is permanent, so any positive chance of absorption makes
the extended mean return time infinite. Starting at the absorbing state, entrance is at
zero and return is at one.

See J. R. Norris, *Markov Chains* (1997), §§1.1 and 1.3, for finite-state chains and
absorption.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

/-- A two-state chain with absorbing state `true` and probability `p` of staying at `false`. -/
def absorbingChain (p : unitInterval) : Kernel Bool Bool :=
  Kernel.ofFunOfCountable fun b => if b then Measure.dirac true else bernoulliMeasure false true p

@[simp] theorem absorbingChain_false (p : unitInterval) :
    absorbingChain p false = bernoulliMeasure false true p := (rfl)

@[simp] theorem absorbingChain_true (p : unitInterval) :
    absorbingChain p true = Measure.dirac true := (rfl)

instance (p : unitInterval) : IsMarkovKernel (absorbingChain p) :=
  ⟨fun b => by cases b <;> simp only [absorbingChain_false, absorbingChain_true] <;> infer_instance⟩

/-- The absorbing state remains there at every time. -/
@[simp] theorem absorbingChain_pow_true (p : unitInterval) (n : ℕ) :
    (absorbingChain p ^ n) true = Measure.dirac true := by
  induction n with
  | zero => rw [pow_zero, Kernel.one_def, Kernel.id_apply]
  | succ n ih =>
    rw [Nat.add_comm n 1, Kernel.pow_add _ 1 n, pow_one, Kernel.comp_apply, ih,
      Measure.dirac_bind (absorbingChain p).measurable, absorbingChain_true]

/-- The probability of remaining at `false` is the geometric survival probability. -/
@[simp] theorem absorbingChain_pow_false_false (p : unitInterval) (n : ℕ) :
    (absorbingChain p ^ n) false {false} = (unitInterval.toNNReal p : ℝ≥0∞) ^ n := by
  induction n with
  | zero => rw [pow_zero, Kernel.one_def, Kernel.id_apply]; simp
  | succ n ih =>
    rw [Kernel.pow_add_apply_singleton _ n 1]
    simp [ih, pow_succ]

/-- The full law started at `false`, including time zero and both endpoints of `p`. -/
theorem absorbingChain_pow_false (p : unitInterval) (n : ℕ) :
    (absorbingChain p ^ n) false = bernoulliMeasure false true (p ^ n) := by
  have hfalse : (absorbingChain p ^ n) false {false} =
      bernoulliMeasure false true (p ^ n) {false} := by
    simp only [absorbingChain_pow_false_false, MeasurableSpace.measurableSet_top,
      Set.mem_singleton_iff, Bool.true_eq_false, not_false_eq_true,
      bernoulliMeasure_apply_of_mem_of_notMem]
    rw [← ENNReal.coe_pow]
    congr 1
  apply Measure.ext_iff_singleton.mpr
  intro b
  cases b with
  | false => exact hfalse
  | true =>
    have hc : ({false} : Set Bool)ᶜ = {true} := by ext b; cases b <;> simp
    rw [← hc, measure_compl (measurableSet_singleton _) (measure_ne_top _ _),
      measure_compl (measurableSet_singleton _) (measure_ne_top _ _), hfalse,
      measure_univ, measure_univ]

/-- The point mass at the absorbing state is stationary. -/
theorem absorbingChain_invariant_dirac (p : unitInterval) :
    (absorbingChain p).Invariant (Measure.dirac true) := by
  rw [Kernel.Invariant, Measure.dirac_bind (absorbingChain p).measurable, absorbingChain_true]

/-- The time-`n` law of the coordinate process agrees with the elementary survival law. -/
theorem absorbingChain_map_eval (p : unitInterval) (n : ℕ) :
    (markovChainLaw (Measure.dirac false) (absorbingChain p)).map (fun ω => ω n) =
      bernoulliMeasure false true (p ^ n) := by
  rw [Measure.markovChainLaw_map_eval]
  rw [Measure.dirac_bind (absorbingChain p ^ n).measurable, absorbingChain_pow_false]

/-- Almost every path is nondecreasing: once absorbed, the chain never leaves `true`. -/
theorem ae_monotone_absorbingChain (p : unitInterval) (ν : Measure Bool) [SFinite ν] :
    ∀ᵐ ω ∂markovChainLaw ν (absorbingChain p), Monotone ω := by
  have hstep : ∀ n, ∀ᵐ ω ∂markovChainLaw ν (absorbingChain p), ω n ≤ ω (n + 1) := by
    intro n
    have hpair : Measurable (fun ω : ℕ → Bool => (ω n, ω (n + 1))) := by fun_prop
    rw [← ae_map_iff hpair.aemeasurable
      (p := fun b : Bool × Bool => b.1 ≤ b.2) (Set.toFinite _).measurableSet,
      markovChainLaw_map_pair_succ]
    apply (Measure.ae_compProd_iff (Set.toFinite _).measurableSet).2
    apply ae_of_all
    intro b
    cases b <;> simp
  filter_upwards [ae_all_iff.2 hstep] with ω hω
  exact monotone_nat_of_le_succ hω

/-- A return to `false` is either immediate or never occurs. -/
theorem ae_hittingAfter_false_absorbingChain (p : unitInterval) (ν : Measure Bool) [SFinite ν] :
    ∀ᵐ ω ∂markovChainLaw ν (absorbingChain p),
      hittingAfter (fun n ω => ω n) {false} 1 ω =
        if ω 1 = false then 1 else ⊤ := by
  filter_upwards [ae_monotone_absorbingChain p ν] with ω hω
  split_ifs with h
  · exact le_antisymm (hittingAfter_le_of_mem le_rfl h) (le_hittingAfter ω)
  · rw [hittingAfter_eq_top_iff]
    intro j hj
    have hm := hω hj
    cases h₁ : ω 1 <;> cases hⱼ : ω j <;>
      simp_all only [Set.mem_singleton_iff, Bool.true_eq_false, not_false_eq_true,
        not_true_eq_false]
    exact (by decide : ¬ ((true : Bool) ≤ false)) hm

/-- The probability of returning to `false` is its one-step survival probability.
In contrast, entrance at time zero has probability one. -/
theorem absorbingChain_return_probability (p : unitInterval) :
    markovChainLaw (Measure.dirac false) (absorbingChain p)
      {ω | hittingAfter (fun n ω => ω n) {false} 1 ω ≠ ⊤} = unitInterval.toNNReal p := by
  calc
    _ = markovChainLaw (Measure.dirac false) (absorbingChain p) {ω | ω 1 = false} := by
      apply measure_congr
      filter_upwards [ae_hittingAfter_false_absorbingChain p (Measure.dirac false)] with ω hω
      simp [hω]
    _ = _ := by
      rw [Measure.markovChainLaw_setOf_apply_eq_comp,
        Measure.dirac_bind (absorbingChain p ^ 1).measurable]
      simp

/-- Missing a return with positive probability makes the extended mean return time infinite.
In particular this remains true when the absorption probability is arbitrarily small. -/
theorem lintegral_return_absorbingChain (p : unitInterval) (hp : p < 1) :
    ∫⁻ ω, ENat.toENNReal (hittingAfter (fun n (ω : ℕ → Bool) => ω n) {false} 1 ω)
      ∂markovChainLaw (Measure.dirac false) (absorbingChain p) = ⊤ := by
  have hm : Measurable (hittingAfter (fun n (ω : ℕ → Bool) => ω n) {false} 1) :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (f := Filtration.piLE (X := fun _ : ℕ => Bool)) (measurableSet_singleton false)).measurable'
  have hf : AEMeasurable (fun ω : ℕ → Bool =>
      ENat.toENNReal (hittingAfter (fun n ω => ω n) {false} 1 ω))
      (markovChainLaw (Measure.dirac false) (absorbingChain p)) :=
    ((measurable_of_countable (fun t : WithTop ℕ => ENat.toENNReal t)).comp hm).aemeasurable
  apply lintegral_eq_top_of_measure_eq_top_ne_zero hf
  -- The hitting time uses the Borel space on WithTop ℕ, not ENat's measurable-space instance.
  have he : {ω : ℕ → Bool | ENat.toENNReal
      (hittingAfter (fun n ω => ω n) {false} 1 ω) = ⊤} =
      {ω | hittingAfter (fun n ω => ω n) {false} 1 ω = ⊤} :=
    Set.ext fun _ => ENat.toENNReal_eq_top
  rw [he]
  have hset : {ω : ℕ → Bool | hittingAfter (fun n ω => ω n) {false} 1 ω = ⊤} =
      {ω | hittingAfter (fun n ω => ω n) {false} 1 ω ≠ ⊤}ᶜ := by ext; simp
  have hs : MeasurableSet {ω : ℕ → Bool |
      hittingAfter (fun n ω => ω n) {false} 1 ω ≠ ⊤} := by
    simpa only [Set.preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using
      (measurableSet_singleton ⊤).compl.preimage hm
  rw [hset, measure_compl hs (measure_ne_top _ _), measure_univ,
    absorbingChain_return_probability]
  apply ne_of_gt
  exact tsub_pos_of_lt (by exact_mod_cast hp)

/-- At the absorbing state entrance is at time zero and positive-time return is at time one. -/
theorem ae_hittingAfter_true_absorbingChain (p : unitInterval) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac true) (absorbingChain p),
      hittingAfter (fun n ω => ω n) {true} 0 ω = 0 ∧
      hittingAfter (fun n ω => ω n) {true} 1 ω = 1 := by
  have h : ∀ n, ∀ᵐ ω ∂markovChainLaw (Measure.dirac true) (absorbingChain p), ω n = true := by
    intro n
    have heval : Measurable (fun ω : ℕ → Bool => ω n) := measurable_pi_apply n
    apply (ae_map_iff heval.aemeasurable
      (p := fun b : Bool => b = true) (measurableSet_singleton true)).1
    rw [Measure.markovChainLaw_map_eval, Measure.dirac_bind (absorbingChain p ^ n).measurable,
      absorbingChain_pow_true]
    simp
  filter_upwards [h 0, h 1] with ω h₀ h₁
  exact ⟨le_antisymm (hittingAfter_le_of_mem le_rfl h₀) (le_hittingAfter ω),
    le_antisymm (hittingAfter_le_of_mem le_rfl h₁) (le_hittingAfter ω)⟩

end TauCeti.Probability
