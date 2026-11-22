/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.MarkovChain.Visits
public import TauCeti.Probability.Kernel.ClosedClass.Basic
public import TauCeti.Probability.Process.HittingTime.Orbit
import TauCeti.Probability.Process.HittingTime.Basic

/-!
# Recurrence and communicating classes

A state of a Markov kernel is recurrent if the chain started there returns at a positive
time almost surely, and transient otherwise. Recurrence is equivalent to divergence of
the diagonal Green function, and is constant on communicating classes. The mean return
time is the extended nonnegative expectation of the first return time; it is at least one,
equals the sum of the pre-return tail probabilities when singletons are measurable, and is
infinite at a transient state. A measurable state-space map intertwining two Markov kernels
projects recurrence and bounds the target mean return time from above whenever target singletons
are measurable.

Every state reachable from a recurrent state is recurrent and hits the original state
almost surely. Consequently a recurrent communicating class is closed. In an irreducible
chain with a recurrent state, every state is hit almost surely from every initial law, and almost
every path visits every state infinitely often; countability of the state space follows from
irreducibility with measurable singletons. These results
supply the state-classification input to coupling arguments.

On a finite nonempty state space some state is recurrent: the chain spends its infinitely many
time steps among finitely many states, so some diagonal Green function diverges. Hence every
state of a finite irreducible chain is recurrent.

As checks on the definitions, for a deterministic kernel `deterministic f hf` the first positive
return time to `x` is almost surely `Function.minimalPeriod f x` on `Function.periodicPts f` and
`⊤` off it, the mean return time is `Function.minimalPeriod f x` on `Function.periodicPts f` and
`∞` off it, and recurrence (respectively transience) coincides with membership (respectively
non-membership) in `Function.periodicPts f`; for a constant point-mass kernel `const S (dirac a)`
the mean return time is `1` at `a` and `∞` away from `a`, distinguishing positive return times
from time-zero entrance.

The first entrance and first return use `hittingAfter` starting at zero and one,
respectively. The class-property and hitting results need only measurable singletons;
countability is used for closedness of the communicating class.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.5, in particular
  Theorems 1.5.4, 1.5.6 and 1.5.7.
-/

public section

open MeasureTheory TauCeti.Probability

open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]
  {κ : Kernel S S} [IsMarkovKernel κ] {x y : S}

/-- A state is recurrent if the chain started there returns at a positive time almost surely. -/
def IsRecurrent (κ : Kernel S S) [IsMarkovKernel κ] (x : S) : Prop :=
  markovChainLaw (Measure.dirac x) κ
    {ω | hittingAfter (fun n ω => ω n) {x} 1 ω ≠ ⊤} = 1

/-- The first return in the definition of recurrence starts at time one. -/
theorem isRecurrent_iff : κ.IsRecurrent x ↔
    markovChainLaw (Measure.dirac x) κ
      {ω | hittingAfter (fun n ω => ω n) {x} 1 ω ≠ ⊤} = 1 := Iff.rfl

/-- A state is transient if it is not recurrent. -/
def IsTransient (κ : Kernel S S) [IsMarkovKernel κ] (x : S) : Prop :=
  ¬ κ.IsRecurrent x

/-- Transience is the failure of almost-sure return. -/
theorem isTransient_iff : κ.IsTransient x ↔ ¬ κ.IsRecurrent x := Iff.rfl

/-- The return probability of a transient state is strictly less than one. -/
theorem isTransient_iff_return_probability_lt_one : κ.IsTransient x ↔
    markovChainLaw (Measure.dirac x) κ
      {ω | hittingAfter (fun n ω => ω n) {x} 1 ω ≠ ⊤} < 1 := by
  rw [isTransient_iff, isRecurrent_iff]
  exact ⟨fun h => lt_of_le_of_ne prob_le_one h, fun h => h.ne⟩

/-- The mean return time `m_x = 𝔼_x[T_x⁺]` of a state: the expected first return time at a
positive time of the chain started at `x`, as an extended nonnegative integral. A missing return
counts as infinity, so `m_x = ∞` as soon as the chain fails to return with positive
probability. -/
noncomputable def meanReturnTime (κ : Kernel S S) [IsMarkovKernel κ] (x : S) : ℝ≥0∞ :=
  ∫⁻ ω, ENat.toENNReal (hittingAfter (fun n ω => ω n) {x} 1 ω)
    ∂markovChainLaw (Measure.dirac x) κ

/-- The mean return time is the integral of the first return time, which starts at time one. -/
theorem meanReturnTime_def : κ.meanReturnTime x =
    ∫⁻ ω, ENat.toENNReal (hittingAfter (fun n ω => ω n) {x} 1 ω)
      ∂markovChainLaw (Measure.dirac x) κ := (rfl)

/-- A return takes at least one step, so the mean return time is at least one. -/
theorem one_le_meanReturnTime : 1 ≤ κ.meanReturnTime x := by
  calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂markovChainLaw (Measure.dirac x) κ := by simp
    _ ≤ κ.meanReturnTime x := lintegral_mono fun ω => by
      have h := le_hittingAfter (u := fun n (ω : ℕ → S) => ω n) (s := {x}) (n := 1) ω
      exact_mod_cast ENat.natCast_le_toENNReal.2 h

/-- Congruence in the kernel argument of `Kernel.meanReturnTime`. -/
theorem meanReturnTime_congr {κ η : Kernel S S} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : κ = η) (x : S) :
    κ.meanReturnTime x = η.meanReturnTime x := by
  subst h
  rfl

/-- The mean return time of any state is strictly positive. -/
theorem meanReturnTime_pos (κ : Kernel S S) [IsMarkovKernel κ] (x : S) :
    0 < κ.meanReturnTime x :=
  zero_lt_one.trans_le κ.one_le_meanReturnTime

/-- The mean return time of any state is nonzero. -/
theorem meanReturnTime_ne_zero (κ : Kernel S S) [IsMarkovKernel κ] (x : S) :
    κ.meanReturnTime x ≠ 0 :=
  (κ.meanReturnTime_pos x).ne'

/-- **A transient state has infinite mean return time.** The chain started there fails to return
with positive probability, and the first return time is infinite on that event. -/
theorem IsTransient.meanReturnTime_eq_top (hx : κ.IsTransient x) : κ.meanReturnTime x = ∞ := by
  set μ := markovChainLaw (Measure.dirac x) κ
  set A := {ω : ℕ → S | hittingAfter (fun n ω => ω n) {x} 1 ω ≠ ⊤}
  -- The failure set is only null-measurable, so work with a measurable superset of `A`.
  have hlt : μ (toMeasurable μ A) < 1 := by
    rw [measure_toMeasurable]
    exact isTransient_iff_return_probability_lt_one.mp hx
  have hpos : 0 < μ (toMeasurable μ A)ᶜ := by
    rw [prob_compl_eq_one_sub (measurableSet_toMeasurable μ A)]
    exact tsub_pos_of_lt hlt
  refine eq_top_iff.mpr ?_
  calc (⊤ : ℝ≥0∞) = ∫⁻ ω, (toMeasurable μ A)ᶜ.indicator (fun _ => (∞ : ℝ≥0∞)) ω ∂μ := by
        rw [lintegral_indicator_const (measurableSet_toMeasurable μ A).compl]
        exact (ENNReal.top_mul hpos.ne').symm
    _ ≤ κ.meanReturnTime x := lintegral_mono fun ω => by
      by_cases hω : ω ∈ (toMeasurable μ A)ᶜ
      · -- Off `A` the first return is missing, so its value is `∞`.
        have hωA : ω ∉ A := fun h => hω (subset_toMeasurable μ A h)
        rw [Set.indicator_of_mem hω]
        simp only [A, Set.mem_ofPred_eq, not_not] at hωA
        exact (ENat.toENNReal_eq_top.mpr hωA).ge
      · rw [Set.indicator_of_notMem hω]
        exact zero_le

/-- If a measurable map `f` intertwines `κ` with `η` via `(κ s).map f = η (f s)` for every state
`s`, then recurrence of `x` under `κ` implies recurrence of `f x` under `η`. Only measurable
singletons on the target space `γ` are needed. -/
theorem IsRecurrent.of_map_eq {γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {η : Kernel γ γ} [IsMarkovKernel η] (hx : κ.IsRecurrent x) {f : S → γ}
    (hf : Measurable f) (h : ∀ s, (κ s).map f = η (f s)) :
    η.IsRecurrent (f x) := by
  have hE : MeasurableSet {u : ℕ → γ | hittingAfter (fun n u => u n) {f x} 1 u ≠ ⊤} :=
    measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton (f x)) 1
  rw [isRecurrent_iff, ← κ.markovChainLaw_dirac_map_comp η hf h x,
    Measure.map_apply (by fun_prop) hE]
  refine le_antisymm prob_le_one ?_
  rw [← isRecurrent_iff.mp hx]
  exact measure_mono fun w hw => ne_top_of_le_ne_top hw <|
    (Set.mapsTo_singleton.mpr rfl : Set.MapsTo f {x} {f x}).hittingAfter_comp_le
      (fun n w => w n) 1 w

/-- If a measurable map `f` intertwines `κ` with `η` via `(κ s).map f = η (f s)` for every state
`s`, then returning to `x` requires returning to `f x`, so
`η.meanReturnTime (f x) ≤ κ.meanReturnTime x`. Only measurable singletons on the target space `γ`
are needed. -/
theorem meanReturnTime_le_of_map_eq {γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass γ]
    {η : Kernel γ γ} [IsMarkovKernel η] {f : S → γ}
    (hf : Measurable f) (h : ∀ s, (κ s).map f = η (f s)) (x : S) :
    η.meanReturnTime (f x) ≤ κ.meanReturnTime x := by
  have hτ : Measurable fun u : ℕ → γ =>
      ENat.toENNReal (hittingAfter (fun n u => u n) {f x} 1 u) :=
    Measurable.of_discrete.comp
      (Filtration.adapted_piLE.isStoppingTime_hittingAfter
        (f := Filtration.piLE (X := fun _ : ℕ => γ)) (measurableSet_singleton (f x))).measurable'
  rw [meanReturnTime_def, meanReturnTime_def, ← κ.markovChainLaw_dirac_map_comp η hf h x,
    MeasureTheory.lintegral_map hτ (by fun_prop)]
  exact lintegral_mono fun w => ENat.toENNReal_mono <|
    (Set.mapsTo_singleton.mpr rfl : Set.MapsTo f {x} {f x}).hittingAfter_comp_le
      (fun n w => w n) 1 w

variable [MeasurableSingletonClass S]

omit [MeasurableSingletonClass S] in
/-- Finite extended mean return time implies almost-sure return. -/
theorem isRecurrent_of_meanReturnTime_ne_top (h : κ.meanReturnTime x ≠ ∞) :
    κ.IsRecurrent x := by
  by_contra hx
  exact h ((isTransient_iff.mpr hx).meanReturnTime_eq_top)

/-- **Tail-sum formula for the mean return time.** -/
theorem meanReturnTime_eq_tsum (κ : Kernel S S) [IsMarkovKernel κ] (x : S) :
    κ.meanReturnTime x =
      ∑' n : ℕ, markovChainLaw (Measure.dirac x) κ
        {ω | (n : WithTop ℕ) < hittingAfter (fun k ω => ω k) {x} 1 ω} := by
  have hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => S))
      (hittingAfter (fun k (ω : ℕ → S) => ω k) {x} 1) :=
    Filtration.adapted_piLE.isStoppingTime_hittingAfter (measurableSet_singleton x)
  exact lintegral_enat_eq_tsum _ fun n => Filtration.le _ n _ (hτ.measurableSet_gt n)

/-- A state is recurrent exactly when its diagonal Green function is infinite. -/
theorem isRecurrent_iff_tsum_eq_top :
    κ.IsRecurrent x ↔ ∑' n : ℕ, (κ ^ n) x {x} = ∞ :=
  (κ.tsum_pow_apply_singleton_self_eq_top_iff x).symm

/-- Recurrence is constant on communicating classes. -/
theorem Communicates.isRecurrent_iff (hxy : κ.Communicates x y) :
    κ.IsRecurrent x ↔ κ.IsRecurrent y := by
  suffices h : ∀ {x y : S}, κ.Communicates x y → κ.IsRecurrent x → κ.IsRecurrent y from
    ⟨h hxy, h hxy.symm⟩
  intro x y hxy hx
  obtain ⟨hxy, hyx⟩ := (communicates_def x y).mp hxy
  obtain ⟨a, ha⟩ := (reaches_def y x).mp hyx
  obtain ⟨b, hb⟩ := (reaches_def x y).mp hxy
  rw [isRecurrent_iff_tsum_eq_top] at hx ⊢
  have hbound : (κ ^ a) y {x} * (∑' n : ℕ, (κ ^ n) x {x}) * (κ ^ b) x {y} ≤
      ∑' n : ℕ, (κ ^ n) y {y} := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    refine (tsum_le_tsum fun n => ?_).trans
      (tsum_comp_le_tsum_of_injective (f := fun n : ℕ => a + n + b)
        (by intro m n h; dsimp only at h; omega) (fun n => (κ ^ n) y {y}))
    exact (mul_le_mul_left
      (pow_apply_singleton_mul_le_pow_add_apply κ a n y x)
      ((κ ^ b) x {y})).trans
      (pow_apply_singleton_mul_le_pow_add_apply κ (a + n) b y x)
  simpa [hx, ha.ne', hb.ne'] using hbound

/-- Transience is constant on communicating classes. -/
theorem Communicates.isTransient_iff (hxy : κ.Communicates x y) :
    κ.IsTransient x ↔ κ.IsTransient y := by
  rw [ProbabilityTheory.Kernel.isTransient_iff, ProbabilityTheory.Kernel.isTransient_iff]
  exact not_congr hxy.isRecurrent_iff

/-- From a state reachable from a recurrent state, the chain hits the recurrent state
almost surely. The entrance may occur at time zero. -/
theorem IsRecurrent.ae_hittingAfter_ne_top_of_reaches (hx : κ.IsRecurrent x)
    (hxy : κ.Reaches x y) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac y) κ,
      hittingAfter (fun n ω => ω n) {x} 0 ω ≠ ⊤ := by
  obtain ⟨n, hn⟩ := (reaches_def x y).mp hxy
  have hE := TauCeti.Probability.measurableSet_hittingAfter_coord_ne_top
    (measurableSet_singleton x) 0
  -- Infinitely many visits imply a visit after time `n`. Disintegrating the future law then
  -- gives almost-sure entrance from `y`, since `y` has positive mass at time `n`.
  have hshift : ∀ᵐ ω ∂(markovChainLaw (Measure.dirac x) κ).map (shift S)^[n],
      hittingAfter (fun n ω => ω n) {x} 0 ω ≠ ⊤ := by
    rw [ae_map_iff (measurable_shift_iterate n).aemeasurable hE]
    filter_upwards [κ.ae_infinite_setOf_eq_markovChainLaw_dirac (isRecurrent_iff.mp hx)]
      with ω hω
    obtain ⟨k, hk, hnk⟩ := hω.exists_gt n
    have hmem : ((shift S)^[n] ω) (k - n) ∈ ({x} : Set S) := by
      simpa [shift_iterate_apply, Nat.sub_add_cancel hnk.le] using hk
    exact ne_top_of_le_ne_top WithTop.coe_ne_top
      (hittingAfter_le_of_mem (Nat.zero_le _) hmem)
  rw [Measure.markovChainLaw_map_shift_iterate, Measure.dirac_bind (κ ^ n).measurable,
    Measure.markovChainLaw_eq_comp] at hshift
  have hrows := Measure.ae_ae_of_ae_comp hshift
  simp only [markovChainKernel_apply] at hrows
  by_contra hy
  exact hn.ne' (measure_mono_null (Set.singleton_subset_iff.mpr hy) (ae_iff.mp hrows))

/-- Every state reachable from a recurrent state can reach it back. -/
theorem IsRecurrent.reaches_of_reaches (hx : κ.IsRecurrent x) (hxy : κ.Reaches x y) :
    κ.Reaches y x := by
  by_contra hyx
  have hzero : ∀ n : ℕ, markovChainLaw (Measure.dirac y) κ {ω | ω n = x} = 0 := by
    intro n
    rw [Measure.markovChainLaw_setOf_apply_eq_comp, Measure.dirac_bind (κ ^ n).measurable]
    exact nonpos_iff_eq_zero.mp (not_lt.mp fun h => hyx ((reaches_def y x).mpr ⟨n, h⟩))
  have havoid : ∀ᵐ ω ∂markovChainLaw (Measure.dirac y) κ, ∀ n, ω n ≠ x :=
    ae_all_iff.mpr fun n => ae_iff.mpr (by simpa using hzero n)
  have hhit := hx.ae_hittingAfter_ne_top_of_reaches hxy
  have : ∀ᵐ _ ∂markovChainLaw (Measure.dirac y) κ, False := by
    filter_upwards [havoid, hhit] with ω hω hH
    exact hH (hittingAfter_eq_top_iff.mpr fun n _ => hω n)
  exact (Filter.Eventually.exists this).elim fun _ h => h

/-- Every state reachable from a recurrent state is recurrent. -/
theorem IsRecurrent.of_reaches (hx : κ.IsRecurrent x) (hxy : κ.Reaches x y) :
    κ.IsRecurrent y :=
  (Communicates.isRecurrent_iff
    ((communicates_def x y).mpr ⟨hxy, hx.reaches_of_reaches hxy⟩)).mp hx

/-- A recurrent state hits every state reachable from it almost surely. -/
theorem IsRecurrent.ae_hittingAfter_ne_top (hx : κ.IsRecurrent x) (hxy : κ.Reaches x y) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac x) κ,
      hittingAfter (fun n ω => ω n) {y} 0 ω ≠ ⊤ :=
  (hx.of_reaches hxy).ae_hittingAfter_ne_top_of_reaches (hx.reaches_of_reaches hxy)

/-- A communicating class containing a recurrent state is closed under transitions. -/
theorem IsRecurrent.isClosedSet_communicatingClass [Countable S] (hx : κ.IsRecurrent x) :
    κ.IsClosedSet (κ.communicatingClass x) := by
  rw [isClosedSet_iff_forall_reaches_mem]
  intro y hy z hyz
  rw [mem_communicatingClass_iff, communicates_def] at hy ⊢
  have hxz := hy.1.trans hyz
  exact ⟨hxz, hx.reaches_of_reaches hxz⟩

/-- In an irreducible chain with a recurrent state, every state is hit almost surely
from any initial measure. In particular this holds for any initial probability law. -/
theorem IsRecurrent.ae_hittingAfter_ne_top_of_isIrreducible [IsIrreducible Measure.count κ]
    (hx : κ.IsRecurrent x) (ν : Measure S) (y : S) :
    ∀ᵐ ω ∂markovChainLaw ν κ, hittingAfter (fun n ω => ω n) {y} 0 ω ≠ ⊤ := by
  have hreaches := (isIrreducible_count_iff_forall_reaches.mp inferInstance :
    ∀ a b : S, κ.Reaches a b)
  rw [Measure.markovChainLaw_eq_comp]
  apply Measure.ae_comp_of_ae_ae
    (TauCeti.Probability.measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton y) 0)
  exact Filter.Eventually.of_forall fun z => by
    rw [markovChainKernel_apply]
    exact (hx.of_reaches (hreaches x z)).ae_hittingAfter_ne_top (hreaches z y)

/-- Recurrence of an irreducible chain does not depend on the state. -/
theorem isRecurrent_iff_isRecurrent [IsIrreducible Measure.count κ] (x y : S) :
    κ.IsRecurrent x ↔ κ.IsRecurrent y :=
  Communicates.isRecurrent_iff (isIrreducible_count_iff_forall_communicates.mp ‹_› x y)

/-- In an irreducible chain with a recurrent state, from any initial measure, almost every path
visits every state infinitely often. The state space is automatically countable by
`countable_of_isIrreducible_count`. -/
theorem IsRecurrent.ae_forall_infinite_setOf_eq [IsIrreducible Measure.count κ]
    (hx : κ.IsRecurrent x) (ν : Measure S) :
    ∀ᵐ ω ∂markovChainLaw ν κ, ∀ y, {n | ω n = y}.Infinite := by
  have := countable_of_isIrreducible_count (κ := κ)
  have hS : MeasurableSet {ω : ℕ → S | ∀ y, {n | ω n = y}.Infinite} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun y => measurableSet_setOf_infinite_setOf_eq
      (fun n => measurable_pi_apply n) (measurableSet_singleton y)
  rw [Measure.markovChainLaw_eq_comp]
  refine Measure.ae_comp_of_ae_ae hS (Filter.Eventually.of_forall fun w => ?_)
  rw [markovChainKernel_apply]
  -- Started at `w`, the chain enters each recurrent state `y`, and then returns to it forever.
  refine ae_all_iff.mpr fun y => ?_
  filter_upwards [hx.ae_hittingAfter_ne_top_of_isIrreducible (Measure.dirac w) y,
    Measure.ae_infinite_setOf_eq_of_hittingAfter_ne_top (Measure.dirac w) κ
      ((isRecurrent_iff_isRecurrent x y).mp hx)] with ω hH hω
  exact hω hH

section Finite

/-- A finite nonempty chain has a recurrent state. The chain started at any state spends its
infinitely many time steps among finitely many states, so some state `y` has infinite mean number
of visits, and then `∑ n, (κ ^ n) y {y} = ∞`. -/
theorem exists_isRecurrent [Finite S] [Nonempty S] : ∃ y, κ.IsRecurrent y := by
  have := Fintype.ofFinite S
  obtain ⟨x⟩ := ‹Nonempty S›
  have htop : ∑ y, ∑' n : ℕ, (κ ^ n) x {y} = ∞ := by
    rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
    simp_rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  obtain ⟨y, -, hy⟩ := ENNReal.sum_eq_top.mp htop
  refine ⟨y, isRecurrent_iff_tsum_eq_top.mpr (top_unique ?_)⟩
  have h := tsum_pow_comp_apply_singleton κ (Measure.dirac x) y
  simp_rw [Measure.dirac_bind (Kernel.measurable _)] at h
  rw [← hy, h]
  exact mul_le_of_le_one_left' prob_le_one

/-- Every state of a finite irreducible chain is recurrent. -/
theorem isRecurrent_of_finite [Finite S] [IsIrreducible Measure.count κ] (x : S) :
    κ.IsRecurrent x := by
  have : Nonempty S := ⟨x⟩
  obtain ⟨y, hy⟩ := exists_isRecurrent (κ := κ)
  exact (isRecurrent_iff_isRecurrent y x).mp hy

end Finite

/-! ### Deterministic and constant-kernel evaluations -/

section Deterministic

open scoped Classical in
/-- Under `markovChainLaw (Measure.dirac x) (deterministic f hf)`, the first positive return time
to `x` is almost surely `Function.minimalPeriod f x` when `x` is periodic under `f`, and `⊤`
otherwise. -/
theorem ae_hittingAfter_one_deterministic {f : S → S} (hf : Measurable f) (x : S) :
    ∀ᵐ w ∂markovChainLaw (Measure.dirac x) (deterministic f hf),
      hittingAfter (fun n w => w n) {x} 1 w =
        if x ∈ Function.periodicPts f then
          (Function.minimalPeriod f x : WithTop ℕ)
        else ⊤ := by
  simp [markovChainLaw_dirac_deterministic]

open scoped Classical in
/-- Under `deterministic f hf`, the mean return time of `x` is `Function.minimalPeriod f x` when
`x` is periodic under `f`, and `∞` otherwise. -/
@[simp]
theorem meanReturnTime_deterministic {f : S → S} (hf : Measurable f) (x : S) :
    (deterministic f hf).meanReturnTime x =
      if x ∈ Function.periodicPts f then (Function.minimalPeriod f x : ℝ≥0∞) else ∞ := by
  rw [meanReturnTime_def, markovChainLaw_dirac_deterministic, lintegral_dirac,
    hittingAfter_one_iterate]
  split_ifs
  · exact ENat.toENNReal_coe _
  · exact ENat.toENNReal_top

/-- Under `deterministic f hf`, `x` is recurrent if and only if `x` is a periodic point of `f`. -/
@[simp]
theorem isRecurrent_deterministic {f : S → S} (hf : Measurable f) (x : S) :
    (deterministic f hf).IsRecurrent x ↔ x ∈ Function.periodicPts f := by
  classical
  rw [isRecurrent_iff, markovChainLaw_dirac_deterministic, Measure.dirac_apply]
  simp [Set.indicator_apply]

/-- Under `deterministic f hf`, `x` is transient if and only if `x` is not a periodic point of
`f`. -/
@[simp]
theorem isTransient_deterministic {f : S → S} (hf : Measurable f) (x : S) :
    (deterministic f hf).IsTransient x ↔ x ∉ Function.periodicPts f := by
  rw [isTransient_iff, isRecurrent_deterministic]

/-- Under the constant kernel `const S (Measure.dirac a)` sending every state to `a`, the mean
return time is `1` at `a` and `∞` at every `x ≠ a` (distinguishing positive return times
`t ≥ 1` from time-zero entrance). -/
@[simp]
theorem meanReturnTime_const_dirac [DecidableEq S] (a x : S) :
    (const S (Measure.dirac a)).meanReturnTime x = if x = a then 1 else ∞ := by
  have hconst : const S (Measure.dirac a) = deterministic (fun _ : S => a) measurable_const := by
    ext1 _
    simp [deterministic_apply]
  rw [meanReturnTime_congr hconst, meanReturnTime_deterministic]
  by_cases hxa : x = a
  · subst hxa
    have hper : x ∈ Function.periodicPts (fun _ : S => x) :=
      Function.mk_mem_periodicPts zero_lt_one rfl
    have hmin : Function.minimalPeriod (fun _ : S => x) x = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mpr rfl
    simp [hper, hmin]
  · have hnper : x ∉ Function.periodicPts (fun _ : S => a) := by
      rw [Function.mem_periodicPts]
      rintro ⟨n, hn, hfix⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      have ha : (fun _ : S => a)^[k + 1] x = a := by
        rw [Function.iterate_succ_apply']
      exact hxa (hfix.symm.trans ha)
    simp [hxa, hnper]

end Deterministic

end ProbabilityTheory.Kernel
