/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import TauCeti.MeasureTheory.Measure.GiryMonad
public import TauCeti.Probability.Kernel.Composition.Power
public import TauCeti.Probability.Kernel.Reachability
public import TauCeti.Probability.MarkovChain.Visits

/-!
# Mean return times, cycle occupation measures, and Kac's theorem

Let `κ : Kernel α α` be a Markov transition kernel, write `ℙ_x = markovChainLaw (dirac x) κ` for the
path law of the chain started at `x`, and write `T_x⁺ = hittingAfter (fun n w => w n) {x} 1` for the
first positive return time to `x`.

* The *mean return time* `κ.meanReturn x` is the extended expectation `𝔼_x[T_x⁺]` in `ℝ≥0∞`,
  assigning `∞` to paths that never return. A state `x` is *positive recurrent*
  (`κ.IsPositiveRecurrent x`) when `κ.meanReturn x < ∞`; since positive nonreturn probability forces
  `κ.meanReturn x = ∞`, positive recurrence implies almost-sure return.
* The *cycle occupation measure* `κ.cycleOccupation x` sums the laws of `X_n` restricted to the
  events `{n < T_x⁺}` before the first positive return to `x`. It assigns mass `1` to `{x}` and
  total mass `κ.meanReturn x` to `Set.univ`, and satisfies the exact one-step balance
  `κ ∘ₘ κ.cycleOccupation x = ℙ_x(T_x⁺ ≠ ⊤) • dirac x + (κ.cycleOccupation x).restrict {x}ᶜ`.
  In particular, `κ.cycleOccupation x` is always superharmonic (`κ ∘ₘ μ ≤ μ`), and is `κ`-invariant
  whenever `x` returns almost surely.
* Conversely, `κ.cycleOccupation x` is the minimal subinvariant measure normalized at `x`: every
  measure `μ` with `κ ∘ₘ μ ≤ μ` satisfies `μ {x} • κ.cycleOccupation x ≤ μ`, hence
  `μ {x} * κ.meanReturn x ≤ μ Set.univ`. Consequently any finite `κ`-invariant measure vanishes on
  states that are not positive recurrent, and positive recurrence is inherited along reachability
  (`IsPositiveRecurrent.of_reaches`).
* On a countable state space with measurable singletons, if `κ` is irreducible with respect to
  counting measure (`[IsIrreducible Measure.count κ]`), every `κ`-invariant measure `μ` finite at an
  almost surely returning state `x` equals `μ {x} • κ.cycleOccupation x`. An invariant probability
  measure therefore exists if and only if some (equivalently, every) state is positive recurrent; it
  is unique, equals `(κ.meanReturn x)⁻¹ • κ.cycleOccupation x`, and satisfies Kac's formula
  `π {x} = (κ.meanReturn x)⁻¹` with no aperiodicity assumption. In particular, every finite
  nonempty irreducible chain is positive recurrent and admits a unique invariant probability
  measure.

As checks on the definitions, for a deterministic kernel `deterministic f hf` the mean return time
of `x` is `Function.minimalPeriod f x` on `Function.periodicPts f` and `∞` off it; for a constant
point-mass kernel `const α (dirac a)` the mean return time is `1` at `a` and `∞` away from `a`,
distinguishing positive return times from time-zero entrance.

## Main definitions

* `ProbabilityTheory.Kernel.meanReturn`: the mean first positive return time `𝔼_x[T_x⁺]` in `ℝ≥0∞`.
* `ProbabilityTheory.Kernel.IsPositiveRecurrent`: finiteness of the mean return time.
* `ProbabilityTheory.Kernel.cycleOccupation`: expected occupation measure in one return cycle.

## Main statements

* `ProbabilityTheory.Kernel.comp_cycleOccupation_eq` and
  `ProbabilityTheory.Kernel.invariant_cycleOccupation`: one-step balance and invariance of the cycle
  occupation measure when `x` returns almost surely.
* `ProbabilityTheory.Kernel.smul_cycleOccupation_le_of_comp_le` and
  `ProbabilityTheory.Kernel.Invariant.smul_cycleOccupation_le`: minimality of `cycleOccupation`
  among subinvariant and invariant measures.
* `ProbabilityTheory.Kernel.IsPositiveRecurrent.of_reaches` and
  `ProbabilityTheory.Kernel.Communicates.isPositiveRecurrent_iff`: positive recurrence propagates
  to reachable states.
* `ProbabilityTheory.Kernel.Invariant.eq_smul_cycleOccupation`: uniqueness up to scaling of
  invariant measures on countable irreducible chains.
* `ProbabilityTheory.Kernel.Invariant.apply_singleton_eq_inv_meanReturn`: Kac's formula
  `π {x} = (κ.meanReturn x)⁻¹`.
* `ProbabilityTheory.Kernel.exists_invariant_probability_iff_forall_isPositiveRecurrent`,
  `ProbabilityTheory.Kernel.exists_invariant_probability_iff_exists_isPositiveRecurrent`, and
  `ProbabilityTheory.Kernel.IsPositiveRecurrent.existsUnique_invariant_probability`: existence and
  uniqueness of invariant probability measures on countable irreducible chains.
* `ProbabilityTheory.Kernel.isPositiveRecurrent_of_finite` and
  `ProbabilityTheory.Kernel.existsUnique_invariant_probability`: every finite nonempty irreducible
  chain is positive recurrent and has a unique invariant probability measure.
* `ProbabilityTheory.Kernel.meanReturn_deterministic` and
  `ProbabilityTheory.Kernel.meanReturn_const_dirac`: deterministic and constant-kernel evaluations.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.7 (Theorems 1.7.5, 1.7.6, and
  1.7.7).
* Olav Kallenberg, *Foundations of Modern Probability*, 2nd edition, Springer, 2002, Theorem 8.6.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.Probability

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α]

/-! ### Mean return time and positive recurrence -/

/-- **The mean return time of a state** under a Markov kernel `κ`: the expected first positive
return time `hittingAfter (fun n w => w n) {x} 1` under `markovChainLaw (Measure.dirac x) κ`,
valued in `ℝ≥0∞` so that nonreturn contributes `∞`. -/
noncomputable def meanReturn (κ : Kernel α α) [IsMarkovKernel κ] (x : α) : ℝ≥0∞ :=
  ∫⁻ w, (hittingAfter (fun n w => w n) {x} 1 w).recTopCoe ⊤ Nat.cast
    ∂markovChainLaw (Measure.dirac x) κ

/-- Defining equation for `Kernel.meanReturn`. -/
theorem meanReturn_def (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    κ.meanReturn x =
      ∫⁻ w, (hittingAfter (fun n w => w n) {x} 1 w).recTopCoe ⊤ Nat.cast
        ∂markovChainLaw (Measure.dirac x) κ := (rfl)

/-- Congruence in the kernel argument of `Kernel.meanReturn`. -/
theorem meanReturn_congr {κ η : Kernel α α} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : κ = η) (x : α) :
    κ.meanReturn x = η.meanReturn x := by
  subst h
  rfl

/-- Restatement of `Kernel.meanReturn` using `WithTop.untop`. -/
theorem meanReturn_eq_lintegral_dite (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    κ.meanReturn x =
      ∫⁻ w, (if h : hittingAfter (fun (n : ℕ) w => w n) {x} 1 w = ⊤ then ⊤
        else ((hittingAfter (fun (n : ℕ) w => w n) {x} 1 w).untop h : ℝ≥0∞))
        ∂markovChainLaw (Measure.dirac x) κ := by
  rw [meanReturn_def]
  refine lintegral_congr fun w => ?_
  induction hittingAfter (fun (n : ℕ) (w : ℕ → α) => w n) {x} 1 w using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    rw [dite_eq_right WithTop.coe_ne_top]
    rfl

/-- Every first positive return occurs at time `1` or later, so the mean return time is at least
`1`. -/
theorem one_le_meanReturn (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    1 ≤ κ.meanReturn x := by
  rw [meanReturn_def]
  have hle : ∀ w : ℕ → α,
      (1 : ℝ≥0∞) ≤ (hittingAfter (fun n w => w n) {x} 1 w).recTopCoe ⊤ Nat.cast := fun w => by
    have h1 : (1 : WithTop ℕ) ≤ hittingAfter (fun n w => w n) {x} 1 w := le_hittingAfter w
    induction h : hittingAfter (fun (n : ℕ) (w : ℕ → α) => w n) {x} 1 w using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      rw [h, ← Nat.cast_one] at h1
      rw [WithTop.recTopCoe_coe]
      exact Nat.one_le_cast.mpr (WithTop.coe_le_coe.mp h1)
  calc
    (1 : ℝ≥0∞) = ∫⁻ _, (1 : ℝ≥0∞) ∂markovChainLaw (Measure.dirac x) κ := by simp
    _ ≤ ∫⁻ w, (hittingAfter (fun n w => w n) {x} 1 w).recTopCoe ⊤ Nat.cast
          ∂markovChainLaw (Measure.dirac x) κ := lintegral_mono hle

/-- The mean return time of any state is strictly positive. -/
theorem meanReturn_pos (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    0 < κ.meanReturn x :=
  zero_lt_one.trans_le (κ.one_le_meanReturn x)

/-- The mean return time of any state is nonzero. -/
theorem meanReturn_ne_zero (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    κ.meanReturn x ≠ 0 :=
  (κ.meanReturn_pos x).ne'

/-- A state `x` is **positive recurrent** under `κ` when its mean return time is finite. -/
def IsPositiveRecurrent (κ : Kernel α α) [IsMarkovKernel κ] (x : α) : Prop :=
  κ.meanReturn x < ⊤

/-- Defining equivalence for `Kernel.IsPositiveRecurrent`. -/
theorem isPositiveRecurrent_iff (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    κ.IsPositiveRecurrent x ↔ κ.meanReturn x < ⊤ := (Iff.rfl)

/-- Congruence in the kernel argument of `Kernel.IsPositiveRecurrent`. -/
theorem isPositiveRecurrent_congr {κ η : Kernel α α} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : κ = η) (x : α) :
    κ.IsPositiveRecurrent x ↔ η.IsPositiveRecurrent x := by
  subst h
  rfl

/-- Elimination of `Kernel.IsPositiveRecurrent` to `κ.meanReturn x < ⊤`. -/
theorem IsPositiveRecurrent.meanReturn_lt_top {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsPositiveRecurrent x) : κ.meanReturn x < ⊤ :=
  hx

/-- Elimination of `Kernel.IsPositiveRecurrent` to `κ.meanReturn x ≠ ⊤`. -/
theorem IsPositiveRecurrent.meanReturn_ne_top {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsPositiveRecurrent x) : κ.meanReturn x ≠ ⊤ :=
  hx.meanReturn_lt_top.ne

/-- The pre-return event `{n < T_x⁺}` belongs to the history σ-algebra `Filtration.piLE n`. -/
private theorem measurableSet_lt_hittingAfter [MeasurableSingletonClass α] (x : α) (n : ℕ) :
    MeasurableSet[Filtration.piLE n]
      {w : ℕ → α | (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w} := by
  have hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α))
      (hittingAfter (fun k (w : ℕ → α) => w k) {x} 1) :=
    Filtration.adapted_piLE.isStoppingTime_hittingAfter (measurableSet_singleton x)
  have heq : {w : ℕ → α | (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w} =
      {w : ℕ → α | hittingAfter (fun k w => w k) {x} 1 w ≤ (n : WithTop ℕ)}ᶜ := by
    ext w
    simp
  rw [heq]
  exact (hτ n).compl

/-- **Tail-sum formula for the mean return time.** -/
theorem meanReturn_eq_tsum [MeasurableSingletonClass α] (κ : Kernel α α) [IsMarkovKernel κ]
    (x : α) :
    κ.meanReturn x =
      ∑' n : ℕ, markovChainLaw (Measure.dirac x) κ
        {w | (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w} :=
  lintegral_withTop_nat_eq_tsum _ fun n =>
    Filtration.le _ n _ (measurableSet_lt_hittingAfter x n)

/-- **Nonreturn with positive probability forces infinite mean return time.** -/
theorem meanReturn_eq_top_of_markovChainLaw_lt_one [MeasurableSingletonClass α] (κ : Kernel α α)
    [IsMarkovKernel κ] {x : α}
    (hx : markovChainLaw (Measure.dirac x) κ
      {w | hittingAfter (fun n w => w n) {x} 1 w ≠ ⊤} < 1) :
    κ.meanReturn x = ⊤ := by
  set P := markovChainLaw (Measure.dirac x) κ
  set τ := hittingAfter (fun n (w : ℕ → α) => w n) {x} 1
  have hτ : Measurable τ :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (f := Filtration.piLE (X := fun _ : ℕ => α)) (measurableSet_singleton x)).measurable'
  have hA : MeasurableSet {w | τ w = ⊤} := (measurableSet_singleton ⊤).preimage hτ
  have hne : P {w | τ w = ⊤} ≠ 0 := fun h0 =>
    hx.ne (by simpa [Set.compl_def] using (prob_compl_eq_one_iff hA).2 h0)
  have hle : ∫⁻ w in {w | τ w = ⊤}, (τ w).recTopCoe ⊤ Nat.cast ∂P ≤ κ.meanReturn x :=
    setLIntegral_le_lintegral _ _
  have htop : ∫⁻ w in {w | τ w = ⊤}, (τ w).recTopCoe ⊤ Nat.cast ∂P = ⊤ := by
    have hcongr : ∫⁻ w in {w | τ w = ⊤}, (τ w).recTopCoe ⊤ Nat.cast ∂P =
        ∫⁻ _ in {w | τ w = ⊤}, (⊤ : ℝ≥0∞) ∂P :=
      setLIntegral_congr_fun hA fun w (hw : τ w = ⊤) => by simp [hw]
    rw [hcongr, MeasureTheory.setLIntegral_const, ENNReal.top_mul hne]
  exact top_unique (htop ▸ hle)

/-- A positive recurrent state is returned to with probability one. -/
theorem IsPositiveRecurrent.markovChainLaw_hittingAfter_ne_top [MeasurableSingletonClass α]
    {κ : Kernel α α} [IsMarkovKernel κ] {x : α} (hx : κ.IsPositiveRecurrent x) :
    markovChainLaw (Measure.dirac x) κ {w | hittingAfter (fun n w => w n) {x} 1 w ≠ ⊤} = 1 :=
  le_antisymm prob_le_one <| le_of_not_gt fun hlt =>
    hx.meanReturn_ne_top (κ.meanReturn_eq_top_of_markovChainLaw_lt_one hlt)

/-- Started at a positive recurrent state `x`, the chain returns to `x` almost surely. -/
theorem IsPositiveRecurrent.ae_hittingAfter_ne_top [MeasurableSingletonClass α]
    {κ : Kernel α α} [IsMarkovKernel κ] {x : α} (hx : κ.IsPositiveRecurrent x) :
    ∀ᵐ w ∂markovChainLaw (Measure.dirac x) κ, hittingAfter (fun n w => w n) {x} 1 w ≠ ⊤ := by
  have hτ : Measurable (hittingAfter (fun n (w : ℕ → α) => w n) {x} 1) :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (f := Filtration.piLE (X := fun _ : ℕ => α)) (measurableSet_singleton x)).measurable'
  have hA : MeasurableSet {w : ℕ → α | hittingAfter (fun n w => w n) {x} 1 w = ⊤} :=
    (measurableSet_singleton ⊤).preimage hτ
  rw [ae_iff]
  simpa [Set.compl_def] using (prob_compl_eq_one_iff hA).1 hx.markovChainLaw_hittingAfter_ne_top

/-- A positive recurrent state has divergent Green function `∑' n, (κ ^ n) x {x} = ∞`. -/
theorem IsPositiveRecurrent.tsum_pow_apply_singleton_self_eq_top [MeasurableSingletonClass α]
    {κ : Kernel α α} [IsMarkovKernel κ] {x : α} (hx : κ.IsPositiveRecurrent x) :
    ∑' n : ℕ, (κ ^ n) x {x} = ∞ :=
  (κ.tsum_pow_apply_singleton_self_eq_top_iff x).mpr hx.markovChainLaw_hittingAfter_ne_top

/-! ### Expected occupation in one return cycle -/

/-- The time-`n` pre-return occupation measure of the chain started at `x`: the law of `X_n`
restricted to `{n < T_x⁺}`. -/
private noncomputable def cycleStep (κ : Kernel α α) [IsMarkovKernel κ] (x : α) (n : ℕ) :
    Measure α :=
  ((markovChainLaw (Measure.dirac x) κ).restrict
    {w | (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w}).map fun w => w n

/-- **Expected occupation measure in one return cycle** started at `x`: for a measurable set `s`,
`κ.cycleOccupation x s` is the expected number of times `n < T_x⁺` before the first positive return
to `x` at which the chain started at `x` visits `s`. -/
noncomputable def cycleOccupation (κ : Kernel α α) [IsMarkovKernel κ] (x : α) : Measure α :=
  Measure.sum fun n : ℕ =>
    ((markovChainLaw (Measure.dirac x) κ).restrict
      {w | (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w}).map fun w => w n

/-- Defining equation for `Kernel.cycleOccupation`. -/
theorem cycleOccupation_def (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    κ.cycleOccupation x =
      Measure.sum fun n : ℕ =>
        ((markovChainLaw (Measure.dirac x) κ).restrict
          {w | (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w}).map fun w => w n := (rfl)

/-- Congruence in the kernel argument of `Kernel.cycleOccupation`. -/
theorem cycleOccupation_congr {κ η : Kernel α α} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : κ = η) (x : α) :
    κ.cycleOccupation x = η.cycleOccupation x := by
  subst h
  rfl

/-- On any measurable set `s`, `κ.cycleOccupation x s` sums the pre-return visit probabilities
`ℙ_x(X_n ∈ s ∧ n < T_x⁺)`. -/
theorem cycleOccupation_apply (κ : Kernel α α) [IsMarkovKernel κ] (x : α) {s : Set α}
    (hs : MeasurableSet s) :
    κ.cycleOccupation x s =
      ∑' n : ℕ, markovChainLaw (Measure.dirac x) κ
        {w | w n ∈ s ∧ (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w} := by
  rw [cycleOccupation_def, Measure.sum_apply _ hs]
  refine tsum_congr fun n => ?_
  rw [Measure.map_apply (measurable_pi_apply n) hs,
    Measure.restrict_apply (hs.preimage (measurable_pi_apply n))]
  rfl

/-- Singleton evaluation of `Kernel.cycleOccupation`. -/
theorem cycleOccupation_apply_singleton [MeasurableSingletonClass α] (κ : Kernel α α)
    [IsMarkovKernel κ] (x y : α) :
    κ.cycleOccupation x {y} =
      ∑' n : ℕ, markovChainLaw (Measure.dirac x) κ
        {w | w n = y ∧ (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w} := by
  simpa using κ.cycleOccupation_apply x (measurableSet_singleton y)

/-- Integrating a measurable nonnegative function against `κ.cycleOccupation x` computes its
expected sum over one return cycle `{n < T_x⁺}`. -/
theorem lintegral_cycleOccupation [MeasurableSingletonClass α] (κ : Kernel α α) [IsMarkovKernel κ]
    (x : α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂κ.cycleOccupation x =
      ∫⁻ w, ∑' n : ℕ,
        {w | (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w}.indicator
          (fun w => f (w n)) w
        ∂markovChainLaw (Measure.dirac x) κ := by
  have hE : ∀ n : ℕ, MeasurableSet
      {w : ℕ → α | (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w} :=
    fun n => Filtration.le _ n _ (measurableSet_lt_hittingAfter x n)
  have hfm : ∀ n : ℕ, AEMeasurable
      ({w : ℕ → α | (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w}.indicator
        fun w => f (w n))
      (markovChainLaw (Measure.dirac x) κ) :=
    fun n => ((hf.comp (measurable_pi_apply n)).indicator (hE n)).aemeasurable
  rw [cycleOccupation_def, lintegral_sum_measure, lintegral_tsum hfm]
  refine tsum_congr fun n => ?_
  rw [MeasureTheory.lintegral_map hf (measurable_pi_apply n), lintegral_indicator (hE n)]

/-- The total mass of the cycle occupation measure is the mean return time. -/
@[simp]
theorem cycleOccupation_univ [MeasurableSingletonClass α] (κ : Kernel α α) [IsMarkovKernel κ]
    (x : α) :
    κ.cycleOccupation x Set.univ = κ.meanReturn x := by
  rw [cycleOccupation_apply _ _ .univ, meanReturn_eq_tsum]
  simp

private theorem cycleStep_zero (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    cycleStep κ x 0 = Measure.dirac x := by
  have hu : {w : ℕ → α | (0 : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w} = Set.univ :=
    Set.eq_univ_of_forall fun w =>
      (by decide : (0 : WithTop ℕ) < 1).trans_le (le_hittingAfter w)
  simp [cycleStep, hu]

private theorem cycleStep_succ_singleton_self [MeasurableSingletonClass α] (κ : Kernel α α)
    [IsMarkovKernel κ] (x : α) (n : ℕ) :
    cycleStep κ x (n + 1) {x} = 0 := by
  rw [cycleStep, Measure.map_apply (measurable_pi_apply (n + 1)) (measurableSet_singleton x),
    Measure.restrict_apply ((measurableSet_singleton x).preimage (measurable_pi_apply (n + 1)))]
  refine measure_mono_null (fun w hw => ?_) measure_empty
  have hle : hittingAfter (fun (k : ℕ) w => w k) {x} 1 w ≤ ((n + 1 : ℕ) : WithTop ℕ) :=
    hittingAfter_le_of_mem (Nat.le_add_left 1 n) hw.1
  exact False.elim (hw.2.trans_le hle).false

/-- Before its first positive return to `x`, the chain visits `x` once, at time `0`. -/
@[simp]
theorem cycleOccupation_singleton_self [MeasurableSingletonClass α] (κ : Kernel α α)
    [IsMarkovKernel κ] (x : α) :
    κ.cycleOccupation x {x} = 1 := by
  have hsum : κ.cycleOccupation x {x} = ∑' n : ℕ, cycleStep κ x n {x} :=
    Measure.sum_apply _ (measurableSet_singleton x)
  rw [hsum, tsum_eq_zero_add' CompleteLattice.summable, cycleStep_zero]
  simp [cycleStep_succ_singleton_self]

/-- Decomposing `κ.cycleOccupation x` at `{x}` and `{x}ᶜ` splits off the unit mass at `x`. -/
theorem cycleOccupation_eq_dirac_add_restrict_compl [MeasurableSingletonClass α] (κ : Kernel α α)
    [IsMarkovKernel κ] (x : α) :
    κ.cycleOccupation x = Measure.dirac x + (κ.cycleOccupation x).restrict {x}ᶜ := by
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (measurableSet_singleton x)
    (μ := κ.cycleOccupation x)]
  rw [Measure.restrict_singleton, cycleOccupation_singleton_self, one_smul]

/-- Pushing `cycleStep κ x n` forward by one `κ`-step yields the law of `X_{n + 1}` on `{n < T_x⁺}`,
by the Markov property at the fixed time `n`. -/
private theorem comp_cycleStep [MeasurableSingletonClass α] (κ : Kernel α α) [IsMarkovKernel κ]
    (x : α) (n : ℕ) :
    κ ∘ₘ cycleStep κ x n =
      ((markovChainLaw (Measure.dirac x) κ).restrict
        {w | (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w}).map fun w => w (n + 1) := by
  have hEn := measurableSet_lt_hittingAfter x n
  rw [Filtration.piLE_eq_comap_prefix] at hEn
  obtain ⟨A, hA, hAE⟩ := hEn
  have hshift := Measure.markovChainLaw_restrict_map_shift_iterate (Measure.dirac x) κ n hA
  rw [hAE] at hshift
  have heval := congrArg (fun μ : Measure (ℕ → α) => μ.map fun u => u 1) hshift
  rw [Measure.map_map (measurable_pi_apply 1) (measurable_shift_iterate n),
    Measure.markovChainLaw_map_eval, pow_one] at heval
  simpa [cycleStep, Function.comp_def, shift_iterate_apply, Nat.add_comm 1 n] using heval.symm

/-- Splitting `{n < T_x⁺}` into `{n + 1 < T_x⁺}` and `{T_x⁺ = n + 1}` decomposes one `κ`-step from
`cycleStep κ x n` into `cycleStep κ x (n + 1)` plus the return mass at `x`. -/
private theorem comp_cycleStep_eq [MeasurableSingletonClass α] (κ : Kernel α α) [IsMarkovKernel κ]
    (x : α) (n : ℕ) :
    κ ∘ₘ cycleStep κ x n =
      cycleStep κ x (n + 1) +
        markovChainLaw (Measure.dirac x) κ
          {w | hittingAfter (fun k w => w k) {x} 1 w = ((n + 1 : ℕ) : WithTop ℕ)} •
            Measure.dirac x := by
  set P := markovChainLaw (Measure.dirac x) κ
  set τ := hittingAfter (fun k (w : ℕ → α) => w k) {x} 1
  have hτ : Measurable τ :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (f := Filtration.piLE (X := fun _ : ℕ => α)) (measurableSet_singleton x)).measurable'
  set E₁ : Set (ℕ → α) := {w | ((n + 1 : ℕ) : WithTop ℕ) < τ w}
  set F : Set (ℕ → α) := {w | τ w = ((n + 1 : ℕ) : WithTop ℕ)}
  have hF : MeasurableSet F := (measurableSet_singleton _).preimage hτ
  have hdisj : Disjoint E₁ F :=
    Set.disjoint_left.2 fun w (hw₁ : ((n + 1 : ℕ) : WithTop ℕ) < τ w)
      (hw₂ : τ w = ((n + 1 : ℕ) : WithTop ℕ)) => (hw₂ ▸ hw₁).false
  have hunion : {w | (n : WithTop ℕ) < τ w} = E₁ ∪ F := by
    ext w
    simp only [E₁, F, Set.mem_union, Set.mem_ofPred_eq]
    induction τ w using WithTop.recTopCoe with
    | top => exact ⟨fun _ => Or.inl (WithTop.coe_lt_top _), fun _ => WithTop.coe_lt_top _⟩
    | coe m =>
      have hlt₁ : (n : WithTop ℕ) < WithTop.some m ↔ n < m := WithTop.coe_lt_coe
      have hlt₂ : ((n + 1 : ℕ) : WithTop ℕ) < WithTop.some m ↔ n + 1 < m := WithTop.coe_lt_coe
      have heq : WithTop.some m = ((n + 1 : ℕ) : WithTop ℕ) ↔ m = n + 1 := WithTop.coe_inj
      rw [hlt₁, hlt₂, heq]
      omega
  have hFx : ∀ w ∈ F, w (n + 1) = x := fun w (hw : τ w = ((n + 1 : ℕ) : WithTop ℕ)) => by
    have hne : τ w ≠ ⊤ := by
      rw [hw]
      exact WithTop.coe_ne_top
    have hmem : w (τ w).untopA ∈ ({x} : Set α) := hittingAfter_mem_set_of_ne_top hne
    rw [hw, Set.mem_singleton_iff] at hmem
    exact hmem
  rw [comp_cycleStep, hunion, Measure.restrict_union hdisj hF,
    Measure.map_add _ _ (measurable_pi_apply (n + 1)),
    Measure.map_congr (ae_restrict_of_forall_mem hF hFx), Measure.map_const,
    Measure.restrict_apply_univ]
  rfl

/-- Away from `x`, pushing `cycleStep κ x n` forward by `κ` gives `cycleStep κ x (n + 1)`. -/
private theorem restrict_compl_singleton_comp_cycleStep [MeasurableSingletonClass α]
    (κ : Kernel α α) [IsMarkovKernel κ] (x : α) (n : ℕ) :
    (κ ∘ₘ cycleStep κ x n).restrict {x}ᶜ = cycleStep κ x (n + 1) := by
  have hdirac : (Measure.dirac x).restrict ({x}ᶜ : Set α) = 0 :=
    Measure.restrict_eq_zero.2 (by simp)
  have hself : (cycleStep κ x (n + 1)).restrict {x}ᶜ = cycleStep κ x (n + 1) := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    simpa using cycleStep_succ_singleton_self κ x n
  rw [comp_cycleStep_eq, Measure.restrict_add, Measure.restrict_smul, hdirac, smul_zero, add_zero,
    hself]

private theorem sum_cycleStep_succ_eq_restrict_compl [MeasurableSingletonClass α] (κ : Kernel α α)
    [IsMarkovKernel κ] (x : α) :
    Measure.sum (fun n : ℕ => cycleStep κ x (n + 1)) =
      (κ.cycleOccupation x).restrict {x}ᶜ := by
  ext s hs
  have h0 : (cycleStep κ x 0).restrict ({x}ᶜ : Set α) = 0 := by
    rw [cycleStep_zero]
    exact Measure.restrict_eq_zero.2 (by simp)
  have hsucc : ∀ n : ℕ, (cycleStep κ x (n + 1)).restrict {x}ᶜ = cycleStep κ x (n + 1) := fun n => by
    rw [← restrict_compl_singleton_comp_cycleStep,
      Measure.restrict_restrict (measurableSet_singleton x).compl, Set.inter_self]
  have hrestr : (κ.cycleOccupation x).restrict {x}ᶜ =
      Measure.sum fun n : ℕ => (cycleStep κ x n).restrict {x}ᶜ :=
    Measure.restrict_sum_of_countable _ _
  rw [hrestr, Measure.sum_apply _ hs, Measure.sum_apply _ hs, eq_comm,
    tsum_eq_zero_add' CompleteLattice.summable, h0]
  simp [hsucc]

/-- **One-step balance for the cycle occupation measure.** Pushing `κ.cycleOccupation x` forward by
one step of `κ` replaces the initial unit mass at `x` by the return probability `ℙ_x(T_x⁺ ≠ ⊤)` at
`x`, while preserving the occupation measure on `{x}ᶜ`. -/
theorem comp_cycleOccupation_eq [MeasurableSingletonClass α] (κ : Kernel α α) [IsMarkovKernel κ]
    (x : α) :
    κ ∘ₘ κ.cycleOccupation x =
      markovChainLaw (Measure.dirac x) κ
        {w | hittingAfter (fun k w => w k) {x} 1 w ≠ ⊤} • Measure.dirac x +
        (κ.cycleOccupation x).restrict {x}ᶜ := by
  set P := markovChainLaw (Measure.dirac x) κ
  set τ := hittingAfter (fun k (w : ℕ → α) => w k) {x} 1
  have hτ : Measurable τ :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (f := Filtration.piLE (X := fun _ : ℕ => α)) (measurableSet_singleton x)).measurable'
  set F : ℕ → Set (ℕ → α) := fun n => {w | τ w = ((n + 1 : ℕ) : WithTop ℕ)}
  have hFm : ∀ n, MeasurableSet (F n) := fun n => (measurableSet_singleton _).preimage hτ
  have hdisj : Pairwise (Function.onFun Disjoint F) := fun m n hmn =>
    Set.disjoint_left.2 fun w (hm : τ w = ((m + 1 : ℕ) : WithTop ℕ))
      (hn : τ w = ((n + 1 : ℕ) : WithTop ℕ)) =>
      hmn (Nat.succ.inj (WithTop.coe_injective (hm.symm.trans hn)))
  have hiUnion : {w | τ w ≠ ⊤} = ⋃ n : ℕ, F n := by
    ext w
    simp only [F, Set.mem_ofPred_eq, Set.mem_iUnion]
    have h1 : (1 : WithTop ℕ) ≤ τ w := le_hittingAfter w
    induction h : τ w using WithTop.recTopCoe with
    | top =>
      exact ⟨fun hne => (hne rfl).elim, fun ⟨_, hn⟩ => False.elim (WithTop.coe_ne_top hn.symm)⟩
    | coe k =>
      rw [h, ← Nat.cast_one] at h1
      have hk : 1 ≤ k := WithTop.coe_le_coe.mp h1
      exact ⟨fun _ => ⟨k - 1, congrArg Nat.cast (Nat.sub_add_cancel hk).symm⟩,
        fun _ => WithTop.coe_ne_top⟩
  have hbind : κ ∘ₘ κ.cycleOccupation x = Measure.sum fun n : ℕ => κ ∘ₘ cycleStep κ x n :=
    Measure.bind_sum _ _ κ.aemeasurable
  ext s hs
  rw [hbind, Measure.sum_apply _ hs]
  simp_rw [comp_cycleStep_eq, add_apply, smul_apply, smul_eq_mul]
  rw [tsum_add, ENNReal.tsum_mul_right, ← measure_iUnion hdisj hFm, ← hiUnion,
    ← Measure.sum_apply _ hs, sum_cycleStep_succ_eq_restrict_compl, add_comm]

/-- The cycle occupation measure is superharmonic (`κ ∘ₘ μ ≤ μ`) at every state, recurrent or
transient. -/
theorem comp_cycleOccupation_le [MeasurableSingletonClass α] (κ : Kernel α α) [IsMarkovKernel κ]
    (x : α) :
    κ ∘ₘ κ.cycleOccupation x ≤ κ.cycleOccupation x := by
  rw [comp_cycleOccupation_eq]
  conv_rhs => rw [cycleOccupation_eq_dirac_add_restrict_compl κ x]
  refine add_le_add (Measure.le_iff.2 fun s _ => ?_) le_rfl
  simp only [smul_apply, smul_eq_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right prob_le_one zero_le

/-- **Invariance of the cycle occupation measure.** Whenever the chain started at `x` returns to `x`
with probability one, `κ.cycleOccupation x` is `κ`-invariant. -/
theorem invariant_cycleOccupation [MeasurableSingletonClass α] (κ : Kernel α α) [IsMarkovKernel κ]
    {x : α}
    (hx : markovChainLaw (Measure.dirac x) κ {w | hittingAfter (fun k w => w k) {x} 1 w ≠ ⊤} = 1) :
    κ.Invariant (κ.cycleOccupation x) := by
  rw [Invariant, comp_cycleOccupation_eq, hx, one_smul,
    ← cycleOccupation_eq_dirac_add_restrict_compl]

/-- If `x` is positive recurrent, `κ.cycleOccupation x` is a finite measure. -/
theorem IsPositiveRecurrent.isFiniteMeasure_cycleOccupation [MeasurableSingletonClass α]
    {κ : Kernel α α} [IsMarkovKernel κ] {x : α} (hx : κ.IsPositiveRecurrent x) :
    IsFiniteMeasure (κ.cycleOccupation x) :=
  ⟨by rw [cycleOccupation_univ]; exact hx.meanReturn_lt_top⟩

/-- If `x` is positive recurrent, `κ.cycleOccupation x` is `κ`-invariant. -/
theorem IsPositiveRecurrent.invariant_cycleOccupation [MeasurableSingletonClass α]
    {κ : Kernel α α} [IsMarkovKernel κ] {x : α} (hx : κ.IsPositiveRecurrent x) :
    κ.Invariant (κ.cycleOccupation x) :=
  Kernel.invariant_cycleOccupation κ hx.markovChainLaw_hittingAfter_ne_top

/-- If `x` is positive recurrent, normalizing `κ.cycleOccupation x` by `(κ.meanReturn x)⁻¹` yields
a probability measure. -/
theorem IsPositiveRecurrent.isProbabilityMeasure_inv_meanReturn_smul_cycleOccupation
    [MeasurableSingletonClass α] {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsPositiveRecurrent x) :
    IsProbabilityMeasure ((κ.meanReturn x)⁻¹ • κ.cycleOccupation x) :=
  ⟨by
    rw [smul_apply, cycleOccupation_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel (κ.meanReturn_ne_zero x) hx.meanReturn_ne_top]⟩

/-- If `x` is positive recurrent, `(κ.meanReturn x)⁻¹ • κ.cycleOccupation x` is `κ`-invariant. -/
theorem IsPositiveRecurrent.invariant_inv_meanReturn_smul_cycleOccupation
    [MeasurableSingletonClass α] {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsPositiveRecurrent x) :
    κ.Invariant ((κ.meanReturn x)⁻¹ • κ.cycleOccupation x) :=
  hx.invariant_cycleOccupation.smul _

/-- If `x` returns almost surely and reaches `y`, the cycle occupation measure at `x` gives
positive mass to `{y}`. -/
theorem cycleOccupation_singleton_pos_of_reaches [MeasurableSingletonClass α] (κ : Kernel α α)
    [IsMarkovKernel κ] {x y : α}
    (hx : markovChainLaw (Measure.dirac x) κ {w | hittingAfter (fun k w => w k) {x} 1 w ≠ ⊤} = 1)
    (hxy : κ.Reaches x y) :
    0 < κ.cycleOccupation x {y} := by
  obtain ⟨n, hn⟩ := (reaches_def x y).mp hxy
  have hinv := ((invariant_cycleOccupation κ hx).pow n).def
  have hle := Measure.singleton_mul_apply_le_bind_apply (κ.cycleOccupation x) (κ ^ n).measurable x
    (measurableSet_singleton y)
  rw [cycleOccupation_singleton_self, one_mul, hinv] at hle
  exact hn.trans_le hle

/-- If `x` returns almost surely and is reachable from `y`, the cycle occupation measure at `x`
assigns finite mass to `{y}`. -/
theorem cycleOccupation_singleton_lt_top_of_reaches [MeasurableSingletonClass α] (κ : Kernel α α)
    [IsMarkovKernel κ] {x y : α}
    (hx : markovChainLaw (Measure.dirac x) κ {w | hittingAfter (fun k w => w k) {x} 1 w ≠ ⊤} = 1)
    (hyx : κ.Reaches y x) :
    κ.cycleOccupation x {y} < ⊤ := by
  obtain ⟨n, hn⟩ := (reaches_def y x).mp hyx
  have hinv := ((invariant_cycleOccupation κ hx).pow n).def
  have hle := Measure.singleton_mul_apply_le_bind_apply (κ.cycleOccupation x) (κ ^ n).measurable y
    (measurableSet_singleton x)
  rw [hinv, cycleOccupation_singleton_self] at hle
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  rw [htop, ENNReal.top_mul hn.ne'] at hle
  exact not_top_lt (hle.trans_lt ENNReal.one_lt_top)

/-! ### Minimality of `cycleOccupation` and propagation of positive recurrence -/

/-- **Minimality of the cycle occupation measure.** Every subinvariant measure `μ` (`κ ∘ₘ μ ≤ μ`)
dominates `μ {x} • κ.cycleOccupation x`. -/
theorem smul_cycleOccupation_le_of_comp_le [MeasurableSingletonClass α] {κ : Kernel α α}
    [IsMarkovKernel κ] {μ : Measure α} (hμ : κ ∘ₘ μ ≤ μ) (x : α) :
    μ {x} • κ.cycleOccupation x ≤ μ := by
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, μ {x} • cycleStep κ x n ≤ μ := fun N => by
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact Measure.le_iff.2 fun _ _ => zero_le
    | succ N ih =>
      have hbind : ∑ n ∈ Finset.range N, μ {x} • (κ ∘ₘ cycleStep κ x n) ≤ μ := by
        simpa only [Measure.bind_finset_sum _ _ κ.aemeasurable, Measure.comp_smul] using
          (Measure.bind_mono_left κ.aemeasurable ih).trans hμ
      have hcompl : ∑ n ∈ Finset.range N, μ {x} • cycleStep κ x (n + 1) ≤ μ.restrict {x}ᶜ := by
        refine Measure.le_iff.2 fun s hs => ?_
        have hstep := hbind (s ∩ {x}ᶜ)
        simpa [sum_apply, smul_apply, ← restrict_compl_singleton_comp_cycleStep,
          Measure.restrict_apply hs] using hstep
      rw [Finset.sum_range_succ', add_comm, cycleStep_zero, ← Measure.restrict_singleton]
      conv_rhs => rw [← Measure.restrict_add_restrict_compl (measurableSet_singleton x) (μ := μ)]
      exact add_le_add le_rfl hcompl
  refine Measure.le_iff.2 fun s hs => ?_
  have hsum : κ.cycleOccupation x = Measure.sum (cycleStep κ x) := rfl
  rw [smul_apply, hsum, Measure.sum_apply _ hs, smul_eq_mul, ← ENNReal.tsum_mul_left,
    ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  have hN := (hpartial N) s
  simp only [sum_apply, smul_apply, smul_eq_mul] at hN
  exact hN

/-- Every `κ`-invariant measure `μ` dominates `μ {x} • κ.cycleOccupation x`. -/
theorem Invariant.smul_cycleOccupation_le [MeasurableSingletonClass α] {κ : Kernel α α}
    [IsMarkovKernel κ] {μ : Measure α} (hμ : κ.Invariant μ) (x : α) :
    μ {x} • κ.cycleOccupation x ≤ μ :=
  smul_cycleOccupation_le_of_comp_le hμ.def.le x

/-- For any `κ`-invariant measure `μ` and state `x`, `μ {x} * κ.meanReturn x ≤ μ Set.univ`. -/
theorem Invariant.apply_singleton_mul_meanReturn_le [MeasurableSingletonClass α] {κ : Kernel α α}
    [IsMarkovKernel κ] {μ : Measure α} (hμ : κ.Invariant μ) (x : α) :
    μ {x} * κ.meanReturn x ≤ μ Set.univ := by
  simpa [smul_apply, smul_eq_mul] using (hμ.smul_cycleOccupation_le x) Set.univ

/-- Any finite `κ`-invariant measure assigns mass zero to states that are not positive recurrent. -/
theorem Invariant.apply_singleton_eq_zero_of_not_isPositiveRecurrent [MeasurableSingletonClass α]
    {κ : Kernel α α} [IsMarkovKernel κ] {μ : Measure α} [IsFiniteMeasure μ] (hμ : κ.Invariant μ)
    {x : α} (hx : ¬ κ.IsPositiveRecurrent x) :
    μ {x} = 0 := by
  have htop : κ.meanReturn x = ⊤ := top_unique (not_lt.mp hx)
  by_contra hne
  have hle := hμ.apply_singleton_mul_meanReturn_le x
  rw [htop, ENNReal.mul_top hne] at hle
  exact (measure_lt_top μ Set.univ).not_ge hle

/-- If a finite `κ`-invariant measure assigns positive mass to `{x}`, then `x` is positive
recurrent. -/
theorem Invariant.isPositiveRecurrent_of_apply_singleton_pos [MeasurableSingletonClass α]
    {κ : Kernel α α} [IsMarkovKernel κ] {μ : Measure α} [IsFiniteMeasure μ] (hμ : κ.Invariant μ)
    {x : α} (hx : 0 < μ {x}) :
    κ.IsPositiveRecurrent x :=
  by_contra fun hnot => hx.ne' (hμ.apply_singleton_eq_zero_of_not_isPositiveRecurrent hnot)

/-- Positive mass of an invariant measure propagates along reachable transitions. -/
theorem Invariant.apply_singleton_pos_of_reaches [MeasurableSingletonClass α] {κ : Kernel α α}
    {μ : Measure α} (hμ : κ.Invariant μ) {x y : α} (hx : 0 < μ {x}) (hxy : κ.Reaches x y) :
    0 < μ {y} := by
  obtain ⟨n, hn⟩ := (reaches_def x y).mp hxy
  have hle := Measure.singleton_mul_apply_le_bind_apply μ (κ ^ n).measurable x
    (measurableSet_singleton y)
  rw [(hμ.pow n).def] at hle
  exact (ENNReal.mul_pos hx.ne' hn.ne').trans_le hle

/-- **Positive recurrence is inherited by reachable states.** If `x` is positive recurrent and
reaches `y`, then `y` is positive recurrent. -/
theorem IsPositiveRecurrent.of_reaches [MeasurableSingletonClass α] {κ : Kernel α α}
    [IsMarkovKernel κ] {x y : α} (hx : κ.IsPositiveRecurrent x) (hxy : κ.Reaches x y) :
    κ.IsPositiveRecurrent y := by
  have := hx.isFiniteMeasure_cycleOccupation
  exact hx.invariant_cycleOccupation.isPositiveRecurrent_of_apply_singleton_pos
    (cycleOccupation_singleton_pos_of_reaches κ hx.markovChainLaw_hittingAfter_ne_top hxy)

/-- Communicating states are simultaneously positive recurrent or not. -/
theorem Communicates.isPositiveRecurrent_iff [MeasurableSingletonClass α] {κ : Kernel α α}
    [IsMarkovKernel κ] {x y : α} (hxy : κ.Communicates x y) :
    κ.IsPositiveRecurrent x ↔ κ.IsPositiveRecurrent y :=
  ⟨fun hx => hx.of_reaches ((communicates_def x y).mp hxy).1,
    fun hy => hy.of_reaches ((communicates_def x y).mp hxy).2⟩

/-! ### Uniqueness, Kac's formula, and equilibrium on countable irreducible chains -/

section Irreducible

variable [Countable α] [MeasurableSingletonClass α]

/-- On a countable irreducible chain, every nonzero invariant measure charges every singleton. -/
theorem Invariant.apply_singleton_pos_of_ne_zero {κ : Kernel α α} [IsIrreducible Measure.count κ]
    {μ : Measure α} (hμ : κ.Invariant μ) (hμ0 : μ ≠ 0) (x : α) :
    0 < μ {x} := by
  have hex : ∃ y : α, 0 < μ {y} := by
    by_contra! hall
    refine hμ0 (Measure.ext_of_singleton fun y => ?_)
    simpa using nonpos_iff_eq_zero.mp (hall y)
  obtain ⟨y, hy⟩ := hex
  exact hμ.apply_singleton_pos_of_reaches hy ((isIrreducible_count_iff_forall_reaches.mp ‹_›) y x)

/-- On a countable irreducible chain, every invariant probability measure charges every
singleton. -/
theorem Invariant.apply_singleton_pos {κ : Kernel α α} [IsIrreducible Measure.count κ]
    {π : Measure α} [IsProbabilityMeasure π] (hπ : κ.Invariant π) (x : α) :
    0 < π {x} :=
  hπ.apply_singleton_pos_of_ne_zero (IsProbabilityMeasure.ne_zero π) x

/-- **Uniqueness of invariant measures up to scaling.** On a countable irreducible chain, if `x`
returns with probability one and `μ` is a `κ`-invariant measure with `μ {x} ≠ ⊤`, then
`μ = μ {x} • κ.cycleOccupation x`. -/
theorem Invariant.eq_smul_cycleOccupation {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] {μ : Measure α} (hμ : κ.Invariant μ) {x : α}
    (hx : markovChainLaw (Measure.dirac x) κ {w | hittingAfter (fun k w => w k) {x} 1 w ≠ ⊤} = 1)
    (hμx : μ {x} ≠ ⊤) :
    μ = μ {x} • κ.cycleOccupation x := by
  set ν := μ {x} • κ.cycleOccupation x
  have hle : ν ≤ μ := hμ.smul_cycleOccupation_le x
  have hν : κ.Invariant ν := (invariant_cycleOccupation κ hx).smul (μ {x})
  have hνx : ν {x} = μ {x} := by simp [ν]
  refine Measure.ext_of_singleton fun y => le_antisymm ?_ (hle {y})
  by_contra hnot
  classical
  have hlt : ν {y} < μ {y} := not_le.mp hnot
  obtain ⟨n, hn⟩ := (reaches_def y x).mp ((isIrreducible_count_iff_forall_reaches.mp ‹_›) y x)
  have hntop : (κ ^ n) y {x} ≠ ⊤ := measure_ne_top _ _
  have hexpand : ∀ ρ : Measure α, ((κ ^ n) ∘ₘ ρ) {x} =
      ρ {y} * (κ ^ n) y {x} + ∑' z : α, if z = y then 0 else ρ {z} * (κ ^ n) z {x} := fun ρ => by
    rw [Measure.bind_apply (measurableSet_singleton x) (κ ^ n).aemeasurable, lintegral_countable']
    simp_rw [mul_comm ((κ ^ n) _ {x})]
    exact tsum_eq_add_tsum_ite y
  have hν_eq : ν {x} =
      ν {y} * (κ ^ n) y {x} + ∑' z : α, if z = y then 0 else ν {z} * (κ ^ n) z {x} :=
    (congrArg (fun ρ : Measure α => ρ {x}) (hν.pow n).def).symm.trans (hexpand ν)
  have hμ_eq : μ {x} =
      μ {y} * (κ ^ n) y {x} + ∑' z : α, if z = y then 0 else μ {z} * (κ ^ n) z {x} :=
    (congrArg (fun ρ : Measure α => ρ {x}) (hμ.pow n).def).symm.trans (hexpand μ)
  have hrest_ne_top : (∑' z : α, if z = y then 0 else ν {z} * (κ ^ n) z {x}) ≠ ⊤ :=
    ne_top_of_le_ne_top (hνx ▸ hμx) (hν_eq ▸ le_add_self)
  have hrest_le : (∑' z : α, if z = y then 0 else ν {z} * (κ ^ n) z {x}) ≤
      ∑' z : α, if z = y then 0 else μ {z} * (κ ^ n) z {x} := by
    refine tsum_le_tsum fun z => ?_
    split_ifs with hz
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_right (hle {z}) zero_le
  have hmul_lt : ν {y} * (κ ^ n) y {x} < μ {y} * (κ ^ n) y {x} := by
    simpa only [mul_comm] using ENNReal.mul_lt_mul_right hn.ne' hntop hlt
  have hstrict : ν {x} < μ {x} := by
    rw [hν_eq, hμ_eq]
    exact (ENNReal.add_lt_add_right hrest_ne_top hmul_lt).trans_le (add_le_add le_rfl hrest_le)
  exact hstrict.ne hνx

/-- If a countable irreducible chain admits an invariant probability measure, then every state is
positive recurrent. -/
theorem Invariant.isPositiveRecurrent {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] {π : Measure α} [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (x : α) :
    κ.IsPositiveRecurrent x :=
  hπ.isPositiveRecurrent_of_apply_singleton_pos (hπ.apply_singleton_pos x)

/-- **Kac's formula.** For any invariant probability measure `π` of a countable irreducible Markov
chain and any state `x`, `π {x} = (κ.meanReturn x)⁻¹`. No aperiodicity hypothesis is needed. -/
theorem Invariant.apply_singleton_eq_inv_meanReturn {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] {π : Measure α} [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (x : α) :
    π {x} = (κ.meanReturn x)⁻¹ := by
  have hx : κ.IsPositiveRecurrent x := hπ.isPositiveRecurrent x
  have hπ_eq := hπ.eq_smul_cycleOccupation hx.markovChainLaw_hittingAfter_ne_top
    (measure_ne_top π {x})
  have huniv : π Set.univ = π {x} * κ.meanReturn x := by
    simpa [smul_apply, smul_eq_mul] using congrArg (fun ν : Measure α => ν Set.univ) hπ_eq
  rw [measure_univ] at huniv
  exact ENNReal.eq_inv_of_mul_eq_one_left huniv.symm

/-- Every invariant probability measure of a countable irreducible chain equals the normalized
cycle occupation measure `(κ.meanReturn x)⁻¹ • κ.cycleOccupation x` around any state `x`. -/
theorem Invariant.eq_inv_meanReturn_smul_cycleOccupation {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] {π : Measure α} [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) (x : α) :
    π = (κ.meanReturn x)⁻¹ • κ.cycleOccupation x := by
  have hx : κ.IsPositiveRecurrent x := hπ.isPositiveRecurrent x
  rw [← hπ.apply_singleton_eq_inv_meanReturn x]
  exact hπ.eq_smul_cycleOccupation hx.markovChainLaw_hittingAfter_ne_top (measure_ne_top π {x})

/-- **Uniqueness of the invariant probability measure** on a countable irreducible chain. -/
theorem invariant_eq_of_isProbabilityMeasure {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] {π π' : Measure α} [IsProbabilityMeasure π]
    [IsProbabilityMeasure π'] (hπ : κ.Invariant π) (hπ' : κ.Invariant π') :
    π = π' := by
  obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure π
  exact (hπ.eq_inv_meanReturn_smul_cycleOccupation x).trans
    (hπ'.eq_inv_meanReturn_smul_cycleOccupation x).symm

/-- **Existence of an invariant probability measure via a single positive recurrent state.** -/
theorem exists_invariant_probability_iff_exists_isPositiveRecurrent (κ : Kernel α α)
    [IsMarkovKernel κ] [IsIrreducible Measure.count κ] :
    (∃ π : Measure α, IsProbabilityMeasure π ∧ κ.Invariant π) ↔
      ∃ x : α, κ.IsPositiveRecurrent x := by
  constructor
  · rintro ⟨π, hprob, hinv⟩
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure π
    exact ⟨x, hinv.isPositiveRecurrent x⟩
  · rintro ⟨x, hx⟩
    exact ⟨(κ.meanReturn x)⁻¹ • κ.cycleOccupation x,
      hx.isProbabilityMeasure_inv_meanReturn_smul_cycleOccupation,
      hx.invariant_inv_meanReturn_smul_cycleOccupation⟩

/-- **Existence of an invariant probability measure via positive recurrence of all states.** For a
nonempty countable irreducible chain, an invariant probability measure exists if and only if every
state is positive recurrent. -/
theorem exists_invariant_probability_iff_forall_isPositiveRecurrent (κ : Kernel α α)
    [IsMarkovKernel κ] [Nonempty α] [IsIrreducible Measure.count κ] :
    (∃ π : Measure α, IsProbabilityMeasure π ∧ κ.Invariant π) ↔
      ∀ x : α, κ.IsPositiveRecurrent x := by
  rw [exists_invariant_probability_iff_exists_isPositiveRecurrent]
  refine ⟨fun ⟨y, hy⟩ x =>
    hy.of_reaches ((isIrreducible_count_iff_forall_reaches.mp ‹_›) y x), ?_⟩
  intro h
  obtain ⟨x⟩ := ‹Nonempty α›
  exact ⟨x, h x⟩

/-- **Existence and uniqueness of the invariant probability measure** from a positive recurrent
state of a countable irreducible chain. -/
theorem IsPositiveRecurrent.existsUnique_invariant_probability {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] {x : α} (hx : κ.IsPositiveRecurrent x) :
    ∃! π : Measure α, IsProbabilityMeasure π ∧ κ.Invariant π := by
  refine ⟨(κ.meanReturn x)⁻¹ • κ.cycleOccupation x,
    ⟨hx.isProbabilityMeasure_inv_meanReturn_smul_cycleOccupation,
      hx.invariant_inv_meanReturn_smul_cycleOccupation⟩, ?_⟩
  rintro π ⟨hprob, hinv⟩
  exact hinv.eq_inv_meanReturn_smul_cycleOccupation x

end Irreducible

/-! ### Finite irreducible chains -/

section Finite

/-- Every state of a finite irreducible Markov chain is positive recurrent. -/
theorem isPositiveRecurrent_of_finite [Finite α] [MeasurableSingletonClass α] (κ : Kernel α α)
    [IsMarkovKernel κ] [IsIrreducible Measure.count κ] (x : α) :
    κ.IsPositiveRecurrent x := by
  cases nonempty_fintype α
  have hsum_top : ∑ y : α, ∑' n : ℕ, (κ ^ n) x {y} = ⊤ := by
    have h1 : ∀ n : ℕ, ∑ y : α, (κ ^ n) x {y} = 1 := fun n => by simp [sum_measure_singleton]
    rw [← tsum_fintype (L := .unconditional _), tsum_comm]
    simp [h1]
  have hex : ∃ y : α, ∑' n : ℕ, (κ ^ n) x {y} = ⊤ := by
    by_contra! hlt
    exact (ENNReal.sum_lt_top.mpr fun y _ => lt_top_iff_ne_top.mpr (hlt y)).ne hsum_top
  obtain ⟨y, hy_top⟩ := hex
  have hy_diag : ∑' n : ℕ, (κ ^ n) y {y} = ⊤ := by
    have hgreen := κ.tsum_pow_comp_apply_singleton (Measure.dirac x) y
    simp only [Measure.dirac_bind (κ ^ _).measurable] at hgreen
    rw [hy_top] at hgreen
    by_contra hne
    have hlt : markovChainLaw (Measure.dirac x) κ
        {w | hittingAfter (fun n w => w n) {y} 0 w ≠ ⊤} * ∑' n : ℕ, (κ ^ n) y {y} < ⊤ :=
      ENNReal.mul_lt_top (measure_lt_top _ _) (lt_top_iff_ne_top.mpr hne)
    exact hlt.ne hgreen.symm
  have hy_ret : markovChainLaw (Measure.dirac y) κ
      {w | hittingAfter (fun n w => w n) {y} 1 w ≠ ⊤} = 1 :=
    (κ.tsum_pow_apply_singleton_self_eq_top_iff y).mp hy_diag
  have hy_pos : κ.IsPositiveRecurrent y := by
    rw [isPositiveRecurrent_iff, ← cycleOccupation_univ]
    have huniv : κ.cycleOccupation y Set.univ = ∑ z : α, κ.cycleOccupation y {z} := by
      simp [sum_measure_singleton]
    rw [huniv]
    exact ENNReal.sum_lt_top.mpr fun z _ =>
      cycleOccupation_singleton_lt_top_of_reaches κ hy_ret
        ((isIrreducible_count_iff_forall_reaches.mp ‹_›) z y)
  exact hy_pos.of_reaches ((isIrreducible_count_iff_forall_reaches.mp ‹_›) y x)

/-- **Every finite nonempty irreducible Markov chain admits a unique invariant probability
measure.** -/
theorem existsUnique_invariant_probability [Finite α] [Nonempty α] [MeasurableSingletonClass α]
    (κ : Kernel α α) [IsMarkovKernel κ] [IsIrreducible Measure.count κ] :
    ∃! π : Measure α, IsProbabilityMeasure π ∧ κ.Invariant π := by
  obtain ⟨x⟩ := ‹Nonempty α›
  exact (κ.isPositiveRecurrent_of_finite x).existsUnique_invariant_probability

end Finite

/-! ### Deterministic and constant-kernel evaluations -/

section Deterministic

variable [MeasurableSingletonClass α]

open scoped Classical in
/-- Under `deterministic f hf`, the mean return time of `x` is `Function.minimalPeriod f x` when
`x` is periodic under `f`, and `∞` otherwise. -/
@[simp]
theorem meanReturn_deterministic {f : α → α} (hf : Measurable f) (x : α) :
    (deterministic f hf).meanReturn x =
      if x ∈ Function.periodicPts f then (Function.minimalPeriod f x : ℝ≥0∞) else ⊤ := by
  let g : WithTop ℕ → ℝ≥0∞ := WithTop.recTopCoe ⊤ Nat.cast
  have hτ : Measurable (hittingAfter (fun (n : ℕ) (w : ℕ → α) => w n) {x} 1) :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (f := Filtration.piLE (X := fun _ : ℕ => α)) (measurableSet_singleton x)).measurable'
  have hm : Measurable fun w : ℕ → α =>
      g (hittingAfter (fun (n : ℕ) (w : ℕ → α) => w n) {x} 1 w) :=
    (Measurable.of_discrete (f := g)).comp hτ
  rw [meanReturn_def, markovChainLaw_dirac_deterministic, lintegral_dirac' _ hm]
  have hex : (∃ j : ℕ, 1 ≤ j ∧ f^[j] x ∈ ({x} : Set α)) ↔ x ∈ Function.periodicPts f := by
    rw [Function.mem_periodicPts]
    exact ⟨fun ⟨j, hj, hx⟩ => ⟨j, hj, hx⟩, fun ⟨j, hj, hx⟩ => ⟨j, hj, hx⟩⟩
  have hset : {i : ℕ | 1 ≤ i ∧ f^[i] x ∈ ({x} : Set α)} =
      {n : ℕ | 0 < n ∧ Function.IsPeriodicPt f n x} := by
    ext i
    simp [Nat.pos_iff_ne_zero, Nat.one_le_iff_ne_zero, Function.IsPeriodicPt, Function.IsFixedPt]
  rw [hittingAfter_def]
  dsimp only [g]
  by_cases hx : x ∈ Function.periodicPts f
  · rw [ite_eq_left (hex.mpr hx), ite_eq_left hx, hset,
      ← Function.minimalPeriod_eq_sInf_n_pos_IsPeriodicPt, WithTop.recTopCoe_coe]
  · rw [ite_eq_right (mt hex.mp hx), ite_eq_right hx]
    rfl

open scoped Classical in
/-- Under `deterministic f hf`, `x` is positive recurrent if and only if `x` is a periodic point of
`f`. -/
@[simp]
theorem isPositiveRecurrent_deterministic {f : α → α} (hf : Measurable f) (x : α) :
    (deterministic f hf).IsPositiveRecurrent x ↔ x ∈ Function.periodicPts f := by
  rw [isPositiveRecurrent_iff, meanReturn_deterministic]
  split_ifs with hx <;> simp [hx]

/-- Under the constant kernel `const α (Measure.dirac a)` sending every state to `a`, the mean
return time is `1` at `a` and `∞` at every `x ≠ a` (distinguishing positive return times `t ≥ 1`
from time-zero entrance). -/
@[simp]
theorem meanReturn_const_dirac [DecidableEq α] (a x : α) :
    (const α (Measure.dirac a)).meanReturn x = if x = a then 1 else ⊤ := by
  have hconst : const α (Measure.dirac a) = deterministic (fun _ : α => a) measurable_const := by
    ext1 y
    simp [deterministic_apply]
  rw [meanReturn_congr hconst, meanReturn_deterministic]
  by_cases hxa : x = a
  · subst hxa
    have hper : x ∈ Function.periodicPts (fun _ : α => x) :=
      Function.mk_mem_periodicPts zero_lt_one rfl
    have hmin : Function.minimalPeriod (fun _ : α => x) x = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mpr rfl
    simp [hper, hmin]
  · have hnper : x ∉ Function.periodicPts (fun _ : α => a) := by
      rw [Function.mem_periodicPts]
      rintro ⟨n, hn, hfix⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      have ha : (fun _ : α => a)^[k + 1] x = a := by
        rw [Function.iterate_succ_apply']
      exact hxa (hfix.symm.trans ha)
    simp [hxa, hnper]

/-- Under `const α (Measure.dirac a)`, `x` is positive recurrent if and only if `x = a`. -/
@[simp]
theorem isPositiveRecurrent_const_dirac (a x : α) :
    (const α (Measure.dirac a)).IsPositiveRecurrent x ↔ x = a := by
  classical
  rw [isPositiveRecurrent_iff, meanReturn_const_dirac]
  split_ifs with hxa <;> simp [hxa]

end Deterministic

end ProbabilityTheory.Kernel
