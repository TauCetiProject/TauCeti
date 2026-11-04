/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.ClosedClass
public import TauCeti.Probability.MarkovChain.Visits

/-!
# Recurrent states of a Markov chain

Let `κ` be a Markov kernel on a measurable space `α` with measurable singletons, write
`ℙ_x = markovChainLaw (dirac x) κ` for the law of the chain started at `x`, and on a path `X`
write `H_y = hittingAfter X {y} 0` for the first entrance time of `y` and
`T_x⁺ = hittingAfter X {x} 1` for the first return time to `x`. A state `x` is *recurrent*
(`ProbabilityTheory.Kernel.IsRecurrent`) when `ℙ_x(T_x⁺ < ∞) = 1`, and *transient* otherwise.

By the dichotomy for the number of visits, `x` is recurrent exactly when the chain started at `x`
visits `x` infinitely often almost surely, and exactly when `∑ n, (κ ^ n) x {x} = ∞`.

This file proves that recurrence is a property of communicating classes. If `x` is recurrent
and reaches `y`, then:

* the chain started at `y` enters `x` almost surely: otherwise, with positive probability the
  chain started at `x` would sit at `y` at some time and never visit `x` afterwards, so it would
  visit `x` only finitely often;
* hence `y` reaches `x`, and `x` and `y` communicate;
* `y` is recurrent, by comparing Green functions:
  `(κ ^ b) y {x} · (κ ^ n) x {x} · (κ ^ a) x {y} ≤ (κ ^ (b + n + a)) y {y}`.

Consequently recurrence and transience are class properties, the communicating class of a
recurrent state is closed, and within it the chain started anywhere enters every state almost
surely. For an irreducible chain, either every state is recurrent or none is; if they are, then
from every initial law the chain enters every state almost surely and visits every state
infinitely often. On a finite nonempty state space some state is recurrent, so there is a closed
communicating class, and every state of a finite irreducible chain is recurrent.

## Main definitions

* `ProbabilityTheory.Kernel.IsRecurrent`: the chain started at `x` returns to `x` almost surely.

## Main results

* `ProbabilityTheory.Kernel.isRecurrent_iff_ae_infinite_setOf_eq` and
  `ProbabilityTheory.Kernel.isRecurrent_iff_tsum_pow_apply_singleton_self_eq_top`: the
  characterizations of recurrence by infinitely many visits and by the Green function.
* `ProbabilityTheory.Kernel.IsRecurrent.communicates_of_reaches` and
  `ProbabilityTheory.Kernel.IsRecurrent.of_reaches`: a state reachable from a recurrent state
  communicates with it and is recurrent.
* `ProbabilityTheory.Kernel.Communicates.isRecurrent_iff`: recurrence is a class property.
* `ProbabilityTheory.Kernel.IsRecurrent.markovChainLaw_dirac_setOf_hittingAfter_zero_ne_top`:
  in the class of a recurrent state, the chain started anywhere enters every state almost surely.
* `ProbabilityTheory.Kernel.IsRecurrent.isClosedSet_communicatingClass`: the communicating class
  of a recurrent state is closed.
* `ProbabilityTheory.Kernel.isRecurrent_iff_isRecurrent`,
  `ProbabilityTheory.Kernel.IsRecurrent.ae_hittingAfter_zero_ne_top` and
  `ProbabilityTheory.Kernel.IsRecurrent.ae_forall_infinite_setOf_eq`: for an irreducible chain,
  recurrence does not depend on the state, and a recurrent irreducible chain started from any
  initial law enters, and visits infinitely often, every state.
* `ProbabilityTheory.Kernel.exists_isRecurrent`,
  `ProbabilityTheory.Kernel.exists_isClosedSet_communicatingClass` and
  `ProbabilityTheory.Kernel.isRecurrent_of_finite`: finite state spaces.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Theorems 1.5.4, 1.5.5, 1.5.6
  and 1.5.7.
-/

public section

open MeasureTheory TauCeti.Probability

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] {κ : Kernel α α} [IsMarkovKernel κ] {x y z : α}

variable (κ) in
/-- A state `x` is **recurrent** for the Markov kernel `κ` if the chain started at `x` returns to
`x` at a positive time almost surely. A state that is not recurrent is *transient*. -/
def IsRecurrent (x : α) : Prop :=
  markovChainLaw (Measure.dirac x) κ {ω | hittingAfter (fun n ω => ω n) {x} 1 ω ≠ ⊤} = 1

/-- The defining equation of recurrence: the return probability is one. -/
theorem isRecurrent_iff :
    κ.IsRecurrent x ↔
      markovChainLaw (Measure.dirac x) κ {ω | hittingAfter (fun n ω => ω n) {x} 1 ω ≠ ⊤} = 1 :=
  Iff.rfl

variable [MeasurableSingletonClass α]

/-- **The Green-function criterion for recurrence.** A state `x` is recurrent exactly when the
mean number of visits `∑ n, (κ ^ n) x {x}` of the chain started at `x` is infinite. -/
theorem isRecurrent_iff_tsum_pow_apply_singleton_self_eq_top :
    κ.IsRecurrent x ↔ ∑' n : ℕ, (κ ^ n) x {x} = ∞ :=
  (tsum_pow_apply_singleton_self_eq_top_iff κ x).symm

/-- **The visit criterion for recurrence.** A state `x` is recurrent exactly when the chain started
at `x` visits `x` infinitely often almost surely. -/
theorem isRecurrent_iff_ae_infinite_setOf_eq :
    κ.IsRecurrent x ↔ ∀ᵐ ω ∂markovChainLaw (Measure.dirac x) κ, {n | ω n = x}.Infinite := by
  refine ⟨ae_infinite_setOf_eq_markovChainLaw_dirac κ, fun h => ?_⟩
  by_contra hx
  have h0 := Measure.markovChainLaw_setOf_infinite_setOf_eq_eq_zero (Measure.dirac x) κ
    (lt_of_le_of_ne prob_le_one hx)
  rw [measure_congr (ae_eq_univ.mpr (mem_ae_iff.mp h)), measure_univ] at h0
  exact one_ne_zero h0

/-- If `x` is recurrent and reaches `y`, then the chain started at `y` enters `x` almost surely.
Otherwise the chain started at `x` would, with positive probability, sit at `y` at some time and
never visit `x` afterwards, and so visit `x` only finitely often. -/
private theorem IsRecurrent.markovChainLaw_setOf_hittingAfter_zero_ne_top_of_reaches
    (hx : κ.IsRecurrent x) (hxy : κ.Reaches x y) :
    markovChainLaw (Measure.dirac y) κ {ω | hittingAfter (fun n ω => ω n) {x} 0 ω ≠ ⊤} = 1 := by
  obtain ⟨a, ha⟩ := (reaches_def x y).mp hxy
  have hB : MeasurableSet {ω : ℕ → α | hittingAfter (fun n ω => ω n) {x} 0 ω = ⊤} :=
    (measurableSet_singleton ⊤).preimage
      (Filtration.adapted_piLE.isStoppingTime_hittingAfter
        (f := Filtration.piLE (X := fun _ : ℕ => α)) (measurableSet_singleton x)).measurable'
  -- A path at `y` at time `a` that never visits `x` afterwards visits `x` finitely often.
  have hsub : {ω : ℕ → α | ω a = y} ∩
      (shift α)^[a] ⁻¹' {ω | hittingAfter (fun n ω => ω n) {x} 0 ω = ⊤} ⊆
        {ω | ¬{n | ω n = x}.Infinite} := by
    rintro ω ⟨-, hω⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hittingAfter_eq_top_iff, shift_iterate_apply,
      Set.mem_singleton_iff] at hω
    refine Set.not_infinite.mpr ((Set.finite_lt_nat a).subset fun n hn => ?_)
    by_contra hna
    exact hω (n - a) (Nat.zero_le _) (by rwa [Nat.sub_add_cancel (not_lt.mp hna)])
  have h0 := measure_mono_null hsub (ae_iff.mp (isRecurrent_iff_ae_infinite_setOf_eq.mp hx))
  rw [Measure.markovChainLaw_setOf_apply_eq_inter_preimage_shift_iterate _ _ a y hB,
    Measure.dirac_bind (κ ^ a).measurable, mul_eq_zero] at h0
  simp_rw [ne_eq, ← Set.compl_ofPred]
  exact (prob_compl_eq_one_iff hB).mpr (h0.resolve_left ha.ne')

/-- If `x` is recurrent and reaches `y`, then the mean number of visits to `x` of the chain started
at `y` is infinite. -/
private theorem IsRecurrent.tsum_pow_apply_singleton_eq_top_of_reaches (hx : κ.IsRecurrent x)
    (hxy : κ.Reaches x y) :
    ∑' n : ℕ, (κ ^ n) y {x} = ∞ := by
  have h := tsum_pow_comp_apply_singleton κ (Measure.dirac y) x
  simp_rw [Measure.dirac_bind (Kernel.measurable _)] at h
  rw [h, hx.markovChainLaw_setOf_hittingAfter_zero_ne_top_of_reaches hxy, one_mul,
    isRecurrent_iff_tsum_pow_apply_singleton_self_eq_top.mp hx]

/-- **A state reachable from a recurrent state communicates with it.** -/
theorem IsRecurrent.communicates_of_reaches (hx : κ.IsRecurrent x) (hxy : κ.Reaches x y) :
    κ.Communicates x y := by
  refine (communicates_def x y).mpr ⟨hxy, ?_⟩
  by_contra hyx
  have h0 : ∑' n : ℕ, (κ ^ n) y {x} = 0 := tsum_eq_zero_iff.mpr fun n =>
    nonpos_iff_eq_zero.mp (not_lt.mp fun hn => hyx ((reaches_def y x).mpr ⟨n, hn⟩))
  exact ENNReal.zero_ne_top (h0 ▸ hx.tsum_pow_apply_singleton_eq_top_of_reaches hxy)

/-- **A state reachable from a recurrent state is recurrent.** -/
theorem IsRecurrent.of_reaches (hx : κ.IsRecurrent x) (hxy : κ.Reaches x y) :
    κ.IsRecurrent y := by
  obtain ⟨b, hb⟩ := (reaches_def y x).mp ((communicates_def x y).mp
    (hx.communicates_of_reaches hxy)).2
  obtain ⟨a, ha⟩ := (reaches_def x y).mp hxy
  rw [isRecurrent_iff_tsum_pow_apply_singleton_self_eq_top] at hx ⊢
  -- Going `y → x` in `b` steps, `x → x` in `n` steps and `x → y` in `a` steps returns to `y`.
  have hle : ∀ n, (κ ^ b) y {x} * (κ ^ n) x {x} * (κ ^ a) x {y} ≤ (κ ^ (n + (b + a))) y {y} :=
    fun n => calc
      _ ≤ (κ ^ (b + n)) y {x} * (κ ^ a) x {y} := by
        gcongr
        exact pow_apply_singleton_mul_le_pow_add_apply κ b n y x (measurableSet_singleton x)
      _ ≤ (κ ^ (b + n + a)) y {y} :=
        pow_apply_singleton_mul_le_pow_add_apply κ (b + n) a y x (measurableSet_singleton y)
      _ = (κ ^ (n + (b + a))) y {y} := by rw [show b + n + a = n + (b + a) by omega]
  refine top_unique ?_
  calc ∞ = (κ ^ b) y {x} * (∑' n : ℕ, (κ ^ n) x {x}) * (κ ^ a) x {y} := by
        rw [hx, ENNReal.mul_top hb.ne', ENNReal.top_mul ha.ne']
    _ = ∑' n : ℕ, (κ ^ b) y {x} * (κ ^ n) x {x} * (κ ^ a) x {y} := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    _ ≤ ∑' n : ℕ, (κ ^ (n + (b + a))) y {y} := tsum_le_tsum hle
    _ ≤ ∑' n : ℕ, (κ ^ n) y {y} :=
        tsum_comp_le_tsum_of_injective (add_left_injective (b + a)) fun n => (κ ^ n) y {y}

/-- **Recurrence is a class property.** Communicating states are either both recurrent or both
transient. -/
theorem Communicates.isRecurrent_iff (h : κ.Communicates x y) :
    κ.IsRecurrent x ↔ κ.IsRecurrent y :=
  ⟨fun hx => hx.of_reaches ((communicates_def x y).mp h).1,
    fun hy => hy.of_reaches ((communicates_def x y).mp h).2⟩

/-- **A recurrent class is entered almost surely.** If `y` and `z` lie in the communicating class
of a recurrent state `x`, then the chain started at `y` enters `z` almost surely. In particular
`ℙ_x(H_y < ∞) = ℙ_y(H_x < ∞) = 1` whenever `x` is recurrent and reaches `y`. -/
theorem IsRecurrent.markovChainLaw_dirac_setOf_hittingAfter_zero_ne_top (hx : κ.IsRecurrent x)
    (hy : κ.Communicates x y) (hz : κ.Communicates x z) :
    markovChainLaw (Measure.dirac y) κ {ω | hittingAfter (fun n ω => ω n) {z} 0 ω ≠ ⊤} = 1 :=
  have hz' := (communicates_def x z).mp hz
  (hx.of_reaches hz'.1).markovChainLaw_setOf_hittingAfter_zero_ne_top_of_reaches
    (hz'.2.trans ((communicates_def x y).mp hy).1)

/-- **A recurrent class is closed.** No mass leaves the communicating class of a recurrent
state. -/
theorem IsRecurrent.isClosedSet_communicatingClass [Countable α] (hx : κ.IsRecurrent x) :
    κ.IsClosedSet (κ.communicatingClass x) :=
  isClosedSet_iff_forall_reaches_mem.mpr fun y hy z hyz => (mem_communicatingClass_iff x z).mpr <|
    hx.communicates_of_reaches
      (((communicates_def x y).mp ((mem_communicatingClass_iff x y).mp hy)).1.trans hyz)

section Irreducible

variable [IsIrreducible Measure.count κ]

/-- **Recurrence of an irreducible chain does not depend on the state.** -/
theorem isRecurrent_iff_isRecurrent (x y : α) : κ.IsRecurrent x ↔ κ.IsRecurrent y :=
  Communicates.isRecurrent_iff (isIrreducible_count_iff_forall_communicates.mp ‹_› x y)

/-- **A recurrent irreducible chain enters every state.** From every initial measure, the chain
enters `y` almost surely. -/
theorem IsRecurrent.ae_hittingAfter_zero_ne_top (hx : κ.IsRecurrent x) (ν : Measure α) (y : α) :
    ∀ᵐ ω ∂markovChainLaw ν κ, hittingAfter (fun n ω => ω n) {y} 0 ω ≠ ⊤ := by
  have hB : MeasurableSet {ω : ℕ → α | hittingAfter (fun n ω => ω n) {y} 0 ω = ⊤} :=
    (measurableSet_singleton ⊤).preimage
      (Filtration.adapted_piLE.isStoppingTime_hittingAfter
        (f := Filtration.piLE (X := fun _ : ℕ => α)) (measurableSet_singleton y)).measurable'
  have hreach := isIrreducible_count_iff_forall_communicates.mp ‹_›
  -- Started at any state `w`, the chain enters `y` almost surely.
  have hw : ∀ w, markovChainLaw (Measure.dirac w) κ
      {ω | hittingAfter (fun n ω => ω n) {y} 0 ω = ⊤} = 0 := fun w => by
    have h := hx.markovChainLaw_dirac_setOf_hittingAfter_zero_ne_top (hreach x w) (hreach x y)
    simp_rw [ne_eq, ← Set.compl_ofPred] at h
    exact (prob_compl_eq_one_iff hB).mp h
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [Measure.markovChainLaw_eq_comp, Measure.bind_apply hB (Kernel.aemeasurable _)]
  simp [Kernel.markovChainKernel_apply, hw]

/-- **A recurrent irreducible chain visits every state infinitely often.** On a countable state
space, from every finite initial measure, almost every path visits every state infinitely
often. -/
theorem IsRecurrent.ae_forall_infinite_setOf_eq [Countable α] (hx : κ.IsRecurrent x)
    (ν : Measure α) [IsFiniteMeasure ν] :
    ∀ᵐ ω ∂markovChainLaw ν κ, ∀ y, {n | ω n = y}.Infinite := by
  refine ae_all_iff.mpr fun y => ?_
  filter_upwards [hx.ae_hittingAfter_zero_ne_top ν y,
    Measure.ae_infinite_setOf_eq_of_hittingAfter_ne_top ν κ
      ((isRecurrent_iff_isRecurrent x y).mp hx)] with ω hH hω
  exact hω hH

end Irreducible

section Finite

/-- **A finite chain has a recurrent state.** The chain started at `x` spends its infinitely many
time steps among finitely many states, so some state `y` is visited infinitely often in mean, and
then `∑ n, (κ ^ n) y {y} = ∞`. -/
theorem exists_isRecurrent [Finite α] [Nonempty α] : ∃ y, κ.IsRecurrent y := by
  have := Fintype.ofFinite α
  obtain ⟨x⟩ := ‹Nonempty α›
  have htop : ∑ y, ∑' n : ℕ, (κ ^ n) x {y} = ∞ := by
    rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
    simp_rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  obtain ⟨y, -, hy⟩ := ENNReal.sum_eq_top.mp htop
  refine ⟨y, isRecurrent_iff_tsum_pow_apply_singleton_self_eq_top.mpr (top_unique ?_)⟩
  have h := tsum_pow_comp_apply_singleton κ (Measure.dirac x) y
  simp_rw [Measure.dirac_bind (Kernel.measurable _)] at h
  rw [← hy, h]
  exact mul_le_of_le_one_left' prob_le_one

/-- **A finite chain has a closed communicating class**, namely the class of a recurrent
state. -/
theorem exists_isClosedSet_communicatingClass [Finite α] [Nonempty α] :
    ∃ x, κ.IsClosedSet (κ.communicatingClass x) := by
  obtain ⟨x, hx⟩ := exists_isRecurrent (κ := κ)
  exact ⟨x, hx.isClosedSet_communicatingClass⟩

/-- **Every state of a finite irreducible chain is recurrent.** -/
theorem isRecurrent_of_finite [Finite α] [IsIrreducible Measure.count κ] (x : α) :
    κ.IsRecurrent x := by
  have : Nonempty α := ⟨x⟩
  obtain ⟨y, hy⟩ := exists_isRecurrent (κ := κ)
  exact (isRecurrent_iff_isRecurrent y x).mp hy

end Finite

end ProbabilityTheory.Kernel
