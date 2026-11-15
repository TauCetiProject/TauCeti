/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.ClosedClass.Invariance
public import TauCeti.Probability.MarkovChain.ClosedClass
public import TauCeti.Probability.MarkovChain.Invariant
public import TauCeti.Probability.MarkovChain.Occupation
public import TauCeti.Probability.MarkovChain.Pointwise

/-!
# Null recurrence, recurrence trichotomy, and finite closed communicating classes

A state `x` of a Markov kernel `κ` is **null recurrent**
(`ProbabilityTheory.Kernel.IsNullRecurrent`) when it is recurrent (`κ.IsRecurrent x`) and has
infinite extended mean positive return time (`κ.meanReturnTime x = ∞`). Because transient states
already have `κ.meanReturnTime x = ∞` (`IsTransient.meanReturnTime_eq_top`), positive recurrence
needs only `κ.meanReturnTime x < ∞`, whereas null recurrence splits off the infinite-mean half of
recurrence. Every state of any Markov kernel therefore satisfies the mutually exclusive trichotomy
`κ.IsTransient x ∨ κ.IsPositiveRecurrent x ∨ κ.IsNullRecurrent x`, with neither countability nor
measurable singletons required on the state space.

Restricting a Markov kernel to a measurable closed set preserves positive recurrence and null
recurrence of every state in the set, again without measurable singletons. When singletons are
measurable, null recurrence is inherited along reachability and is constant on communicating
classes, giving the global trichotomy of counting-measure-irreducible chains: either all states are
transient, all states are positive recurrent, or all states are null recurrent.

Around any recurrent state `x`, the cycle occupation measure `κ.cycleOccupation x` assigns finite
mass to every singleton (zero outside the reachable set, finite inside by return reachability) and
is therefore `σ`-finite on countable state spaces. At a null recurrent state its total mass is
infinite, every finite `κ`-invariant measure assigns mass zero to `{x}`, no invariant probability
measure exists when `κ` is irreducible, and on aperiodic irreducible chains the time-`n` singleton
masses decay to zero from every initial probability law.

On countable state spaces with measurable singletons, the occupation strong law characterizes
positive and null recurrence via long-run visit frequencies: positive recurrence is equivalent to a
strictly positive expected (or almost-sure) limiting visit fraction starting from the state, while
null recurrence is equivalent to recurrence with vanishing expected limiting visit fraction.

Finally, restricting to a finite closed communicating class transfers finite irreducible positive
recurrence to arbitrary ambient state spaces with measurable singletons: every state in a finite
closed communicating class is positive recurrent, and `κ` admits a unique invariant probability
measure concentrated on that class. On a finite state space, recurrence and positive recurrence
therefore coincide unconditionally, no state is null recurrent, and almost every trajectory
eventually enters and remains in the closed communicating class of a positive recurrent state.

## Main definitions and statements

* `ProbabilityTheory.Kernel.IsNullRecurrent`: `κ.IsRecurrent x ∧ κ.meanReturnTime x = ∞`.
* `ProbabilityTheory.Kernel.isTransient_or_isPositiveRecurrent_or_isNullRecurrent`: state-level
  recurrence trichotomy.
* `ProbabilityTheory.Kernel.isPositiveRecurrent_subtype_iff` and
  `ProbabilityTheory.Kernel.isNullRecurrent_subtype_iff`: invariance under restriction to a closed
  measurable set.
* `ProbabilityTheory.Kernel.IsNullRecurrent.of_reaches` and
  `ProbabilityTheory.Kernel.Communicates.isNullRecurrent_iff`: class property of null recurrence
  and irreducible-chain trichotomy.
* `ProbabilityTheory.Kernel.IsRecurrent.cycleOccupation_singleton_lt_top` and
  `ProbabilityTheory.Kernel.IsRecurrent.sigmaFinite_cycleOccupation`: singleton finiteness and
  `σ`-finiteness of the cycle occupation measure at any recurrent state.
* `ProbabilityTheory.Kernel.isPositiveRecurrent_iff_exists_pos_tendsto_integral_visitCount_div`:
  occupation-frequency characterizations of positive and null recurrence.
* `ProbabilityTheory.Kernel.IsClosedSet.isPositiveRecurrent_of_finite_communicatingClass`,
  `ProbabilityTheory.Kernel.isPositiveRecurrent_iff_isRecurrent`, and
  `ProbabilityTheory.Kernel.not_isNullRecurrent_of_finite`: finite closed communicating classes and
  finite state spaces.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §§1.5, 1.7, 1.8, and 1.10.
* Olav Kallenberg, *Foundations of Modern Probability*, 2nd edition, Springer, 2002, Theorem 8.6.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set TauCeti TauCeti.Probability

open scoped ENNReal Topology

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α]

/-! ### Null recurrence and the state recurrence trichotomy -/

/-- A state `x` is **null recurrent** under `κ` when it is recurrent and its extended mean positive
return time is infinite. -/
def IsNullRecurrent (κ : Kernel α α) [IsMarkovKernel κ] (x : α) : Prop :=
  κ.IsRecurrent x ∧ κ.meanReturnTime x = ∞

/-- Defining equivalence for `Kernel.IsNullRecurrent`. -/
theorem isNullRecurrent_iff (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    κ.IsNullRecurrent x ↔ κ.IsRecurrent x ∧ κ.meanReturnTime x = ∞ := (Iff.rfl)

/-- Congruence in the kernel argument of `Kernel.IsRecurrent`. -/
theorem isRecurrent_congr {κ η : Kernel α α} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : κ = η) (x : α) :
    κ.IsRecurrent x ↔ η.IsRecurrent x := by
  subst h
  rfl

/-- Congruence in the kernel argument of `Kernel.IsNullRecurrent`. -/
theorem isNullRecurrent_congr {κ η : Kernel α α} [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : κ = η) (x : α) :
    κ.IsNullRecurrent x ↔ η.IsNullRecurrent x := by
  subst h
  rfl

/-- Every null recurrent state is recurrent. -/
theorem IsNullRecurrent.isRecurrent {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsNullRecurrent x) : κ.IsRecurrent x :=
  hx.1

/-- Elimination of `Kernel.IsNullRecurrent` to `κ.meanReturnTime x = ∞`. -/
theorem IsNullRecurrent.meanReturnTime_eq_top {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsNullRecurrent x) : κ.meanReturnTime x = ∞ :=
  hx.2

/-- Null recurrence is recurrence without positive recurrence. -/
theorem isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent {κ : Kernel α α}
    [IsMarkovKernel κ] {x : α} :
    κ.IsNullRecurrent x ↔ κ.IsRecurrent x ∧ ¬ κ.IsPositiveRecurrent x := by
  rw [isNullRecurrent_iff, isPositiveRecurrent_iff, not_lt_top_iff]

/-- A null recurrent state is not positive recurrent. -/
theorem IsNullRecurrent.not_isPositiveRecurrent {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsNullRecurrent x) : ¬ κ.IsPositiveRecurrent x :=
  (isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent.mp hx).2

/-- A null recurrent state is not transient. -/
theorem IsNullRecurrent.not_isTransient {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsNullRecurrent x) : ¬ κ.IsTransient x := by
  rw [isTransient_iff, not_not]
  exact hx.isRecurrent

/-- A positive recurrent state is not null recurrent. -/
theorem IsPositiveRecurrent.not_isNullRecurrent {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsPositiveRecurrent x) : ¬ κ.IsNullRecurrent x :=
  fun h => h.not_isPositiveRecurrent hx

/-- A positive recurrent state is not transient. -/
theorem IsPositiveRecurrent.not_isTransient {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsPositiveRecurrent x) : ¬ κ.IsTransient x := by
  rw [isTransient_iff, not_not]
  exact hx.isRecurrent

/-- A transient state is not positive recurrent. -/
theorem IsTransient.not_isPositiveRecurrent {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsTransient x) : ¬ κ.IsPositiveRecurrent x :=
  fun h => h.not_isTransient hx

/-- A transient state is not null recurrent. -/
theorem IsTransient.not_isNullRecurrent {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsTransient x) : ¬ κ.IsNullRecurrent x :=
  fun h => h.not_isTransient hx

/-- Every recurrent state is either positive recurrent or null recurrent. -/
theorem IsRecurrent.isPositiveRecurrent_or_isNullRecurrent {κ : Kernel α α} [IsMarkovKernel κ]
    {x : α} (hx : κ.IsRecurrent x) :
    κ.IsPositiveRecurrent x ∨ κ.IsNullRecurrent x := by
  by_cases hpos : κ.IsPositiveRecurrent x
  · exact Or.inl hpos
  · exact Or.inr (isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent.mpr ⟨hx, hpos⟩)

/-- A state is recurrent if and only if it is positive recurrent or null recurrent. -/
theorem isRecurrent_iff_isPositiveRecurrent_or_isNullRecurrent {κ : Kernel α α}
    [IsMarkovKernel κ] {x : α} :
    κ.IsRecurrent x ↔ κ.IsPositiveRecurrent x ∨ κ.IsNullRecurrent x :=
  ⟨IsRecurrent.isPositiveRecurrent_or_isNullRecurrent,
    fun h => h.elim IsPositiveRecurrent.isRecurrent IsNullRecurrent.isRecurrent⟩

/-- **State recurrence trichotomy.** Every state of a Markov kernel is transient, positive
recurrent, or null recurrent. -/
theorem isTransient_or_isPositiveRecurrent_or_isNullRecurrent (κ : Kernel α α)
    [IsMarkovKernel κ] (x : α) :
    κ.IsTransient x ∨ κ.IsPositiveRecurrent x ∨ κ.IsNullRecurrent x := by
  by_cases hx : κ.IsRecurrent x
  · exact Or.inr hx.isPositiveRecurrent_or_isNullRecurrent
  · exact Or.inl (isTransient_iff.mpr hx)

/-- A state fails to be positive recurrent if and only if it is transient or null recurrent. -/
theorem not_isPositiveRecurrent_iff {κ : Kernel α α} [IsMarkovKernel κ] {x : α} :
    ¬ κ.IsPositiveRecurrent x ↔ κ.IsTransient x ∨ κ.IsNullRecurrent x := by
  constructor
  · intro hnot
    rcases κ.isTransient_or_isPositiveRecurrent_or_isNullRecurrent x with ht | hp | hn
    · exact Or.inl ht
    · exact absurd hp hnot
    · exact Or.inr hn
  · rintro (ht | hn)
    · exact ht.not_isPositiveRecurrent
    · exact hn.not_isPositiveRecurrent

/-- The extended mean return time of `x` is infinite if and only if `x` is transient or null
recurrent. -/
theorem meanReturnTime_eq_top_iff {κ : Kernel α α} [IsMarkovKernel κ] {x : α} :
    κ.meanReturnTime x = ∞ ↔ κ.IsTransient x ∨ κ.IsNullRecurrent x := by
  rw [← not_lt_top_iff, ← isPositiveRecurrent_iff, not_isPositiveRecurrent_iff]

/-- The real reciprocal mean return time `(κ.meanReturnTime x)⁻¹.toReal` is strictly positive if
and only if `x` is positive recurrent. -/
theorem inv_meanReturnTime_toReal_pos_iff {κ : Kernel α α} [IsMarkovKernel κ] {x : α} :
    0 < (κ.meanReturnTime x)⁻¹.toReal ↔ κ.IsPositiveRecurrent x := by
  rw [ENNReal.toReal_pos_iff, ENNReal.inv_pos, lt_top_iff_ne_top, ENNReal.inv_ne_top,
    isPositiveRecurrent_iff]
  exact ⟨fun h => lt_top_iff_ne_top.mpr h.1, fun hx => ⟨hx.ne, κ.meanReturnTime_ne_zero x⟩⟩

/-- The real reciprocal mean return time `(κ.meanReturnTime x)⁻¹.toReal` vanishes if and only if
`x` is not positive recurrent. -/
theorem inv_meanReturnTime_toReal_eq_zero_iff {κ : Kernel α α} [IsMarkovKernel κ] {x : α} :
    (κ.meanReturnTime x)⁻¹.toReal = 0 ↔ ¬ κ.IsPositiveRecurrent x := by
  rw [← inv_meanReturnTime_toReal_pos_iff]
  exact ⟨fun h hpos => hpos.ne' h, fun h => le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg⟩

/-! ### Restriction to a closed set and singleton-free cycle occupation bounds -/

/-- Restricting a Markov kernel to a closed set preserves and reflects positive recurrence of each
of its states. -/
@[simp]
theorem isPositiveRecurrent_subtype_iff {s : Set α} (κ : Kernel α α) [IsMarkovKernel κ]
    (hs : MeasurableSet s) [IsMarkovKernel (κ.subtype hs)] (x : s) :
    (κ.subtype hs).IsPositiveRecurrent x ↔ κ.IsPositiveRecurrent x.val := by
  simp only [isPositiveRecurrent_iff, meanReturnTime_subtype]

/-- Restricting a Markov kernel to a closed set preserves and reflects null recurrence of each of
its states. -/
@[simp]
theorem isNullRecurrent_subtype_iff {s : Set α} (κ : Kernel α α) [IsMarkovKernel κ]
    (hs : MeasurableSet s) [IsMarkovKernel (κ.subtype hs)] (x : s) :
    (κ.subtype hs).IsNullRecurrent x ↔ κ.IsNullRecurrent x.val := by
  simp only [isNullRecurrent_iff, isRecurrent_subtype_iff, meanReturnTime_subtype]

/-- If `x` does not reach `y`, the cycle occupation measure around `x` assigns mass zero to `{y}`.
No measurability of singletons is needed. -/
theorem cycleOccupation_singleton_eq_zero_of_not_reaches {κ : Kernel α α} [IsMarkovKernel κ]
    {x y : α} (hxy : ¬ κ.Reaches x y) :
    κ.cycleOccupation x {y} = 0 := by
  let P := markovChainLaw (Measure.dirac x) κ
  let μ : ℕ → Measure α := fun n =>
    (P.restrict {w | (n : WithTop ℕ) < hittingAfter (fun k w => w k) {x} 1 w}).map fun w => w n
  have hstep : ∀ n : ℕ, μ n {y} = 0 := fun n => by
    have hpow : (κ ^ n) x {y} = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp fun hn => hxy ((reaches_def x y).mpr ⟨n, hn⟩))
    let B := toMeasurable ((κ ^ n) x) {y}
    have hB : MeasurableSet B := measurableSet_toMeasurable _ _
    have hyB : ({y} : Set α) ⊆ B := subset_toMeasurable _ _
    refine nonpos_iff_eq_zero.mp ((measure_mono hyB).trans ?_)
    rw [Measure.map_apply (measurable_pi_apply n) hB,
      Measure.restrict_apply (hB.preimage (measurable_pi_apply n))]
    refine (measure_mono inter_subset_left).trans ?_
    have hlaw : P ((fun w : ℕ → α => w n) ⁻¹' B) = (κ ^ n) x B := by
      rw [← Measure.map_apply (measurable_pi_apply n) hB, Measure.markovChainLaw_map_eval,
        Measure.dirac_bind (κ ^ n).measurable]
    rw [hlaw, measure_toMeasurable, hpow]
  let B := ⋂ n : ℕ, toMeasurable (μ n) {y}
  have hB : MeasurableSet B := MeasurableSet.iInter fun n => measurableSet_toMeasurable _ _
  have hyB : ({y} : Set α) ⊆ B :=
    subset_iInter fun n => subset_toMeasurable (μ n) {y}
  refine nonpos_iff_eq_zero.mp ((measure_mono hyB).trans ?_)
  rw [cycleOccupation_def, Measure.sum_apply _ hB]
  refine (tsum_eq_zero_iff.mpr fun n => nonpos_iff_eq_zero.mp ?_).le
  exact (measure_mono (iInter_subset _ n)).trans (by rw [measure_toMeasurable, hstep n])

/-- The total mass of the cycle occupation measure around `x` is at least `κ.meanReturnTime x`,
even without measurable singletons. -/
theorem meanReturnTime_le_cycleOccupation_univ (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    κ.meanReturnTime x ≤ κ.cycleOccupation x Set.univ := by
  refine (meanReturnTime_def.trans_le (lintegral_enat_le_tsum _ _)).trans_eq ?_
  rw [cycleOccupation_def, Measure.sum_apply _ MeasurableSet.univ]
  refine tsum_congr fun n => ?_
  rw [Measure.map_apply (measurable_pi_apply n) MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ]
  rfl

/-- At a null recurrent state `x`, the cycle occupation measure has infinite total mass. -/
theorem IsNullRecurrent.cycleOccupation_univ {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsNullRecurrent x) :
    κ.cycleOccupation x Set.univ = ∞ :=
  top_unique (hx.meanReturnTime_eq_top ▸ κ.meanReturnTime_le_cycleOccupation_univ x)

/-- At a null recurrent state `x`, the cycle occupation measure is not finite. -/
theorem IsNullRecurrent.not_isFiniteMeasure_cycleOccupation {κ : Kernel α α} [IsMarkovKernel κ]
    {x : α} (hx : κ.IsNullRecurrent x) :
    ¬ IsFiniteMeasure (κ.cycleOccupation x) :=
  fun _ => (measure_lt_top (κ.cycleOccupation x) Set.univ).ne hx.cycleOccupation_univ

private theorem exists_forall_measurableSet_iff_of_isRecurrent_deterministic {f : α → α}
    (hf : Measurable f) {x : α} (hrec : (deterministic f hf).IsRecurrent x) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ B : Set α, MeasurableSet B → (f^[k] x ∈ B ↔ x ∈ B) := by
  let w₀ : ℕ → α := fun n => f^[n] x
  by_contra! hsep
  have hA : ∀ k : {k : ℕ // 1 ≤ k},
      ∃ A : Set α, MeasurableSet A ∧ x ∈ A ∧ w₀ k.1 ∉ A := fun ⟨k, hk⟩ => by
    rcases hsep k hk with ⟨B, hB, ⟨hwB, hxB⟩ | ⟨hwB, hxB⟩⟩
    · exact ⟨Bᶜ, hB.compl, hxB, not_not.mpr hwB⟩
    · exact ⟨B, hB, hxB, hwB⟩
  choose A hAm hxA hwA using hA
  let E : Set (ℕ → α) := ⋃ k : {k : ℕ // 1 ≤ k}, (fun w : ℕ → α => w k.1) ⁻¹' A k
  have hEm : MeasurableSet E :=
    MeasurableSet.iUnion fun k => (hAm k).preimage (measurable_pi_apply k.1)
  have hw₀E : w₀ ∉ E := by simp [E, hwA]
  have hsub : {w : ℕ → α | hittingAfter (fun n w => w n) {x} 1 w ≠ ⊤} ⊆ E := fun w hw => by
    simp only [mem_ofPred_eq, ne_eq, hittingAfter_eq_top_iff, mem_singleton_iff, not_forall,
      not_not] at hw
    obtain ⟨k, hk, rfl⟩ := hw
    exact mem_iUnion.mpr ⟨⟨k, hk⟩, hxA ⟨k, hk⟩⟩
  have h1 := isRecurrent_iff.mp hrec
  rw [markovChainLaw_dirac_deterministic] at h1
  have h0 : (Measure.dirac w₀ : Measure (ℕ → α))
      {w | hittingAfter (fun n w => w n) {x} 1 w ≠ ⊤} = 0 :=
    nonpos_iff_eq_zero.mp
      ((measure_mono hsub).trans (by simp [Measure.dirac_apply' _ hEm, hw₀E]))
  exact one_ne_zero (h1.symm.trans h0)

/-- A deterministic kernel has no null recurrent states on any measurable space: if the orbit
`n ↦ f^[n] x` cannot be measurably separated from `x` at all positive times, replacing one
inseparable positive step `k` by `x` preserves the Dirac path measure and bounds the mean return
time by `k`. -/
@[simp]
theorem not_isNullRecurrent_deterministic {f : α → α} (hf : Measurable f) (x : α) :
    ¬ (deterministic f hf).IsNullRecurrent x := by
  rintro ⟨hrec, hmean⟩
  obtain ⟨k, hk, hBiff⟩ := exists_forall_measurableSet_iff_of_isRecurrent_deterministic hf hrec
  let w₀ : ℕ → α := fun n => f^[n] x
  let w' : ℕ → α := Function.update w₀ k x
  have hiff_meas : ∀ S : Set (ℕ → α), MeasurableSet S → (w₀ ∈ S ↔ w' ∈ S) := by
    intro S hS
    let m' : MeasurableSpace (ℕ → α) :=
      { MeasurableSet' T := w₀ ∈ T ↔ w' ∈ T
        measurableSet_empty := by simp
        measurableSet_compl _ hT := not_congr hT
        measurableSet_iUnion _ hT := by simp [hT] }
    have hle : (MeasurableSpace.pi : MeasurableSpace (ℕ → α)) ≤ m' := by
      rw [MeasurableSpace.pi, iSup_le_iff]
      rintro j _ ⟨B, hB, rfl⟩
      change w₀ j ∈ B ↔ w' j ∈ B
      by_cases hjk : j = k
      · subst hjk
        simpa [w', w₀] using hBiff B hB
      · simp [w', hjk]
    exact hle S hS
  have hdirac : (Measure.dirac (fun n => f^[n] x) : Measure (ℕ → α)) = Measure.dirac w' := by
    ext S hS
    have hiff := hiff_meas S hS
    simp only [Measure.dirac_apply' _ hS, Set.indicator]
    by_cases hw : w₀ ∈ S
    · simp [w₀, hw, hiff.mp hw]
    · simp [w₀, hw, mt hiff.mpr hw]
  have hlt : (deterministic f hf).meanReturnTime x ≤ (k : ℝ≥0∞) := by
    rw [meanReturnTime_def, markovChainLaw_dirac_deterministic, hdirac, lintegral_def]
    refine iSup₂_le fun s hs => ?_
    rw [← s.lintegral_eq_lintegral, lintegral_dirac' _ s.measurable]
    exact (hs w').trans (ENat.toENNReal_mono (hittingAfter_le_of_mem hk (by simp [w'])))
  exact (hlt.trans_lt (ENNReal.natCast_lt_top k)).ne hmean

/-- Under `const α (Measure.dirac a)`, no state is null recurrent on any measurable space. -/
@[simp]
theorem not_isNullRecurrent_const_dirac (a x : α) :
    ¬ (const α (Measure.dirac a)).IsNullRecurrent x := by
  have hconst : const α (Measure.dirac a) = deterministic (fun _ : α => a) measurable_const := by
    ext1 _
    simp [deterministic_apply]
  rw [isNullRecurrent_congr hconst]
  exact not_isNullRecurrent_deterministic measurable_const x

/-! ### Class properties, cycle occupation, invariant measures, and pointwise decay -/

section MeasurableSingleton

variable [MeasurableSingletonClass α]

/-- Started at a recurrent state `x`, the chain returns to `x` at a positive time almost surely. -/
theorem IsRecurrent.ae_hittingAfter_one_ne_top {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsRecurrent x) :
    ∀ᵐ w ∂markovChainLaw (Measure.dirac x) κ, hittingAfter (fun n w => w n) {x} 1 w ≠ ⊤ :=
  ae_iff.mpr ((prob_compl_eq_zero_iff
    (measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton x) 1)).mpr
      (isRecurrent_iff.mp hx))

/-- Started at a null recurrent state `x`, the chain returns to `x` almost surely. -/
theorem IsNullRecurrent.ae_hittingAfter_ne_top {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsNullRecurrent x) :
    ∀ᵐ w ∂markovChainLaw (Measure.dirac x) κ, hittingAfter (fun n w => w n) {x} 1 w ≠ ⊤ :=
  hx.isRecurrent.ae_hittingAfter_one_ne_top

/-- A null recurrent state has divergent diagonal Green function `∑' n, (κ ^ n) x {x} = ∞`. -/
theorem IsNullRecurrent.tsum_pow_apply_singleton_self_eq_top {κ : Kernel α α} [IsMarkovKernel κ]
    {x : α} (hx : κ.IsNullRecurrent x) :
    ∑' n : ℕ, (κ ^ n) x {x} = ∞ :=
  isRecurrent_iff_tsum_eq_top.mp hx.isRecurrent

/-- **Null recurrence is inherited by reachable states.** If `x` is null recurrent and reaches `y`,
then `y` is null recurrent. -/
theorem IsNullRecurrent.of_reaches {κ : Kernel α α} [IsMarkovKernel κ] {x y : α}
    (hx : κ.IsNullRecurrent x) (hxy : κ.Reaches x y) :
    κ.IsNullRecurrent y :=
  isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent.mpr
    ⟨hx.isRecurrent.of_reaches hxy,
      fun hy => hx.not_isPositiveRecurrent (hy.of_reaches (hx.isRecurrent.reaches_of_reaches hxy))⟩

/-- Communicating states are simultaneously null recurrent or not. -/
theorem Communicates.isNullRecurrent_iff {κ : Kernel α α} [IsMarkovKernel κ] {x y : α}
    (hxy : κ.Communicates x y) :
    κ.IsNullRecurrent x ↔ κ.IsNullRecurrent y :=
  ⟨fun hx => hx.of_reaches ((communicates_def x y).mp hxy).1,
    fun hy => hy.of_reaches ((communicates_def x y).mp hxy).2⟩

/-- Transience of a counting-measure-irreducible chain does not depend on the state. -/
theorem isTransient_iff_isTransient {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] (x y : α) :
    κ.IsTransient x ↔ κ.IsTransient y :=
  Communicates.isTransient_iff (isIrreducible_count_iff_forall_communicates.mp ‹_› x y)

/-- Positive recurrence of a counting-measure-irreducible chain does not depend on the state. -/
theorem isPositiveRecurrent_iff_isPositiveRecurrent {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] (x y : α) :
    κ.IsPositiveRecurrent x ↔ κ.IsPositiveRecurrent y :=
  Communicates.isPositiveRecurrent_iff (isIrreducible_count_iff_forall_communicates.mp ‹_› x y)

/-- Null recurrence of a counting-measure-irreducible chain does not depend on the state. -/
theorem isNullRecurrent_iff_isNullRecurrent {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] (x y : α) :
    κ.IsNullRecurrent x ↔ κ.IsNullRecurrent y :=
  Communicates.isNullRecurrent_iff (isIrreducible_count_iff_forall_communicates.mp ‹_› x y)

/-- **Global recurrence trichotomy for irreducible Markov chains.** In a
counting-measure-irreducible Markov chain, either every state is transient, every state is positive
recurrent, or every state is null recurrent. -/
theorem forall_isTransient_or_forall_isPositiveRecurrent_or_forall_isNullRecurrent
    (κ : Kernel α α) [IsMarkovKernel κ] [IsIrreducible Measure.count κ] :
    (∀ x, κ.IsTransient x) ∨ (∀ x, κ.IsPositiveRecurrent x) ∨ (∀ x, κ.IsNullRecurrent x) := by
  rcases isEmpty_or_nonempty α with hEmpty | ⟨x₀⟩
  · exact Or.inl fun x => hEmpty.elim x
  · obtain ⟨x₀⟩ := ‹Nonempty α›
    rcases κ.isTransient_or_isPositiveRecurrent_or_isNullRecurrent x₀ with ht | hp | hn
    · exact Or.inl fun x => (isTransient_iff_isTransient x₀ x).mp ht
    · exact Or.inr (Or.inl fun x => (isPositiveRecurrent_iff_isPositiveRecurrent x₀ x).mp hp)
    · exact Or.inr (Or.inr fun x => (isNullRecurrent_iff_isNullRecurrent x₀ x).mp hn)

/-- Around any recurrent state `x`, the cycle occupation measure assigns finite mass to every
singleton `{y}`: states reachable from `x` reach `x` back, and unreachable states receive mass
zero. -/
theorem IsRecurrent.cycleOccupation_singleton_lt_top {κ : Kernel α α} [IsMarkovKernel κ]
    {x : α} (hx : κ.IsRecurrent x) (y : α) :
    κ.cycleOccupation x {y} < ∞ := by
  by_cases hxy : κ.Reaches x y
  · exact hx.cycleOccupation_singleton_lt_top_of_reaches (hx.reaches_of_reaches hxy)
  · simp [cycleOccupation_singleton_eq_zero_of_not_reaches hxy]

/-- Around a recurrent state `x`, `κ.cycleOccupation x {y}` is positive if and only if `x` and `y`
communicate. -/
theorem IsRecurrent.cycleOccupation_singleton_pos_iff {κ : Kernel α α} [IsMarkovKernel κ]
    {x y : α} (hx : κ.IsRecurrent x) :
    0 < κ.cycleOccupation x {y} ↔ κ.Communicates x y := by
  constructor
  · intro hpos
    have hxy : κ.Reaches x y :=
      by_contra fun hnot => hpos.ne' (cycleOccupation_singleton_eq_zero_of_not_reaches hnot)
    exact (communicates_def x y).mpr ⟨hxy, hx.reaches_of_reaches hxy⟩
  · intro hcomm
    exact hx.cycleOccupation_singleton_pos_of_reaches ((communicates_def x y).mp hcomm).1

/-- Every finite `κ`-invariant measure assigns mass zero to any null recurrent state. -/
theorem Invariant.apply_singleton_eq_zero_of_isNullRecurrent {κ : Kernel α α} [IsMarkovKernel κ]
    {μ : Measure α} [IsFiniteMeasure μ] (hμ : κ.Invariant μ) {x : α} (hx : κ.IsNullRecurrent x) :
    μ {x} = 0 :=
  hμ.apply_singleton_eq_zero_of_not_isPositiveRecurrent hx.not_isPositiveRecurrent

/-- A counting-measure-irreducible chain with a null recurrent state admits no invariant
probability measure. -/
theorem IsNullRecurrent.not_invariant_of_isProbabilityMeasure {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] {x : α} (hx : κ.IsNullRecurrent x)
    (π : Measure α) [IsProbabilityMeasure π] :
    ¬ κ.Invariant π :=
  fun hπ => hx.not_isPositiveRecurrent (hπ.isPositiveRecurrent x)

omit [MeasurableSingletonClass α] in
private theorem lintegral_return_eq_top_of_not_isPositiveRecurrent {κ : Kernel α α}
    [IsMarkovKernel κ] {y : α} (hy : ¬ κ.IsPositiveRecurrent y) :
    (∫⁻ ω, (hittingAfter (fun n ω => ω n) {y} 1 ω).recTopCoe ⊤ (fun n => (n : ℝ≥0∞))
      ∂markovChainLaw (Measure.dirac y) κ) = ⊤ := by
  have hm : κ.meanReturnTime y = ⊤ := not_lt_top_iff.mp ((isPositiveRecurrent_iff κ y).not.mp hy)
  refine (lintegral_congr fun ω => ?_).trans ((meanReturnTime_def (κ := κ) (x := y)).symm.trans hm)
  induction hittingAfter (fun n ω => ω n) {y} 1 ω using WithTop.recTopCoe <;> rfl

/-- **Pointwise decay at non-positive-recurrent states.** On a counting-measure-irreducible
aperiodic chain, if `y` is not positive recurrent, then the time-`n` singleton probability at `y`
tends to zero from every initial probability law. -/
theorem tendsto_pow_comp_real_singleton_of_isAperiodic_of_not_isPositiveRecurrent
    {κ : Kernel α α} [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    (hκ : κ.IsAperiodic) {y : α} (hy : ¬ κ.IsPositiveRecurrent y)
    (ν : Measure α) [IsProbabilityMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) :=
  κ.tendsto_pow_comp_real_singleton_of_isAperiodic_of_lintegral_return_eq_top hκ
    (lintegral_return_eq_top_of_not_isPositiveRecurrent hy) ν

/-- **Pointwise decay at null recurrent states.** On a counting-measure-irreducible aperiodic
chain, if `y` is null recurrent, then the time-`n` singleton probability at `y` tends to zero from
every initial probability law. -/
theorem IsNullRecurrent.tendsto_pow_comp_real_singleton {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] (hκ : κ.IsAperiodic) {y : α} (hy : κ.IsNullRecurrent y)
    (ν : Measure α) [IsProbabilityMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) :=
  tendsto_pow_comp_real_singleton_of_isAperiodic_of_not_isPositiveRecurrent hκ
    hy.not_isPositiveRecurrent ν

/-! ### Deterministic and constant-kernel recurrence classifications -/

/-- Under `deterministic f hf`, `x` is recurrent if and only if `x` is a periodic point of `f`. -/
@[simp]
theorem isRecurrent_deterministic {f : α → α} (hf : Measurable f) (x : α) :
    (deterministic f hf).IsRecurrent x ↔ x ∈ Function.periodicPts f := by
  refine ⟨fun hrec => by_contra fun hnper => ?_,
    fun hper => ((isPositiveRecurrent_deterministic hf x).mpr hper).isRecurrent⟩
  have hE : MeasurableSet {w : ℕ → α | hittingAfter (fun n w => w n) {x} 1 w ≠ ⊤} :=
    measurableSet_hittingAfter_coord_ne_top (measurableSet_singleton x) 1
  have hmem : (fun n => f^[n] x) ∉ {w : ℕ → α | hittingAfter (fun n w => w n) {x} 1 w ≠ ⊤} := by
    simp only [mem_ofPred_eq, not_not, hittingAfter_eq_top_iff, mem_singleton_iff]
    intro j hj hfx
    exact hnper (Function.mk_mem_periodicPts (Nat.pos_of_ne_zero (by omega)) hfx)
  have hzero : markovChainLaw (Measure.dirac x) (deterministic f hf)
      {w | hittingAfter (fun n w => w n) {x} 1 w ≠ ⊤} = 0 := by
    rw [markovChainLaw_dirac_deterministic, Measure.dirac_apply' _ hE, indicator_of_notMem hmem]
  exact one_ne_zero ((isRecurrent_iff.mp hrec).symm.trans hzero)

/-- Under `deterministic f hf`, `x` is transient if and only if `x` is not a periodic point of
`f`. -/
@[simp]
theorem isTransient_deterministic {f : α → α} (hf : Measurable f) (x : α) :
    (deterministic f hf).IsTransient x ↔ x ∉ Function.periodicPts f := by
  rw [isTransient_iff, isRecurrent_deterministic]

/-- Under `const α (Measure.dirac a)`, `x` is recurrent if and only if `x = a`. -/
@[simp]
theorem isRecurrent_const_dirac (a x : α) :
    (const α (Measure.dirac a)).IsRecurrent x ↔ x = a := by
  have hconst : const α (Measure.dirac a) = deterministic (fun _ : α => a) measurable_const := by
    ext1 _
    simp [deterministic_apply]
  rw [isRecurrent_congr hconst, isRecurrent_deterministic,
    ← isPositiveRecurrent_deterministic measurable_const x,
    ← isPositiveRecurrent_congr hconst, isPositiveRecurrent_const_dirac]

/-- Under `const α (Measure.dirac a)`, `x` is transient if and only if `x ≠ a`. -/
@[simp]
theorem isTransient_const_dirac (a x : α) :
    (const α (Measure.dirac a)).IsTransient x ↔ x ≠ a := by
  rw [isTransient_iff, isRecurrent_const_dirac]

end MeasurableSingleton

/-! ### Countable state spaces: `σ`-finiteness and occupation-frequency characterizations -/

section Countable

variable [Countable α] [MeasurableSingletonClass α]

/-- On a countable state space with measurable singletons, the cycle occupation measure around any
recurrent state is `σ`-finite. In particular, every null recurrent state carries an infinite
`σ`-finite `κ`-invariant measure `κ.cycleOccupation x`. -/
theorem IsRecurrent.sigmaFinite_cycleOccupation {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsRecurrent x) :
    SigmaFinite (κ.cycleOccupation x) :=
  Measure.sigmaFinite_iff_measure_singleton_lt_top.mpr hx.cycleOccupation_singleton_lt_top

/-- Started at `y`, the expected positive-time visit fraction converges to the real reciprocal mean
return time `(κ.meanReturnTime y)⁻¹.toReal`. -/
theorem tendsto_integral_visitCount_div_markovChainLaw_dirac (κ : Kernel α α) [IsMarkovKernel κ]
    (y : α) :
    Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => ω (k + 1)) y n : ℝ) / n
        ∂markovChainLaw (Measure.dirac y) κ)
      atTop (𝓝 (κ.meanReturnTime y)⁻¹.toReal) :=
  (HasLaw.id
    (μ := markovChainLaw (Measure.dirac y) κ)).tendsto_integral_visitCount_div_markovChainLaw_dirac

/-- The Cesàro averages of the positive-time return probabilities `((κ ^ (i + 1)) y).real {y}`
converge to `(κ.meanReturnTime y)⁻¹.toReal`. -/
theorem tendsto_cesaro_pow_real_singleton_self (κ : Kernel α α) [IsMarkovKernel κ] (y : α) :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, ((κ ^ (i + 1)) y).real {y}) / n)
      atTop (𝓝 (κ.meanReturnTime y)⁻¹.toReal) := by
  simpa only [integral_div, κ.integral_visitCount_succ_markovChainLaw_dirac] using
    κ.tendsto_integral_visitCount_div_markovChainLaw_dirac y

/-- **Expected occupation characterization of positive recurrence.** A state `y` is positive
recurrent if and only if its expected positive-time visit fraction starting from `y` converges to a
strictly positive limit. -/
theorem isPositiveRecurrent_iff_exists_pos_tendsto_integral_visitCount_div {κ : Kernel α α}
    [IsMarkovKernel κ] {y : α} :
    κ.IsPositiveRecurrent y ↔
      ∃ r > 0, Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => ω (k + 1)) y n : ℝ) / n
        ∂markovChainLaw (Measure.dirac y) κ) atTop (𝓝 r) := by
  rw [← inv_meanReturnTime_toReal_pos_iff]
  refine ⟨fun hpos => ⟨_, hpos, κ.tendsto_integral_visitCount_div_markovChainLaw_dirac y⟩, ?_⟩
  rintro ⟨r, hr, hlim⟩
  exact (tendsto_nhds_unique (κ.tendsto_integral_visitCount_div_markovChainLaw_dirac y) hlim) ▸ hr

/-- **Almost-sure occupation characterization of positive recurrence.** A state `y` is positive
recurrent if and only if, starting from `y`, its positive-time visit fraction converges almost
surely to a strictly positive deterministic limit. -/
theorem isPositiveRecurrent_iff_exists_pos_ae_tendsto_visitCount_div {κ : Kernel α α}
    [IsMarkovKernel κ] {y : α} :
    κ.IsPositiveRecurrent y ↔
      ∃ r > 0, ∀ᵐ ω ∂markovChainLaw (Measure.dirac y) κ,
        Tendsto (fun n : ℕ => (visitCount (fun k => ω (k + 1)) y n : ℝ) / n) atTop (𝓝 r) := by
  rw [← inv_meanReturnTime_toReal_pos_iff]
  refine ⟨fun hpos => ⟨_, hpos, κ.ae_tendsto_visitCount_div_markovChainLaw_dirac y⟩, ?_⟩
  rintro ⟨r, hr, hae⟩
  obtain ⟨ω, hω₁, hω₂⟩ := ((κ.ae_tendsto_visitCount_div_markovChainLaw_dirac y).and hae).exists
  exact (tendsto_nhds_unique hω₁ hω₂) ▸ hr

/-- **Expected occupation characterization of null recurrence.** A state `y` is null recurrent if
and only if it is recurrent and its expected positive-time visit fraction starting from `y` tends
to zero. -/
theorem isNullRecurrent_iff_isRecurrent_and_tendsto_integral_visitCount_div_zero {κ : Kernel α α}
    [IsMarkovKernel κ] {y : α} :
    κ.IsNullRecurrent y ↔
      κ.IsRecurrent y ∧
        Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => ω (k + 1)) y n : ℝ) / n
          ∂markovChainLaw (Measure.dirac y) κ) atTop (𝓝 0) := by
  rw [isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent,
    ← inv_meanReturnTime_toReal_eq_zero_iff]
  refine and_congr_right fun _ => ⟨fun h0 => ?_, fun hlim =>
    tendsto_nhds_unique (κ.tendsto_integral_visitCount_div_markovChainLaw_dirac y) hlim⟩
  simpa only [h0] using κ.tendsto_integral_visitCount_div_markovChainLaw_dirac y

/-- From any initial measure `ν`, the positive-time visit fraction at a non-positive-recurrent
state tends to zero almost surely. -/
theorem ae_tendsto_visitCount_div_zero_of_not_isPositiveRecurrent {κ : Kernel α α}
    [IsMarkovKernel κ] (ν : Measure α) {y : α} (hy : ¬ κ.IsPositiveRecurrent y) :
    ∀ᵐ ω ∂markovChainLaw ν κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => ω (k + 1)) y n : ℝ) / n) atTop (𝓝 0) := by
  have h0 : (κ.meanReturnTime y)⁻¹.toReal = 0 := inv_meanReturnTime_toReal_eq_zero_iff.mpr hy
  simpa only [h0, ite_self] using ν.ae_tendsto_visitCount_div_markovChainLaw κ y

/-- From any initial measure `ν`, the positive-time visit fraction at a null recurrent state tends
to zero almost surely, even though the state may be visited infinitely often. -/
theorem IsNullRecurrent.ae_tendsto_visitCount_div_zero {κ : Kernel α α} [IsMarkovKernel κ]
    {y : α} (hy : κ.IsNullRecurrent y) (ν : Measure α) :
    ∀ᵐ ω ∂markovChainLaw ν κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => ω (k + 1)) y n : ℝ) / n) atTop (𝓝 0) :=
  ae_tendsto_visitCount_div_zero_of_not_isPositiveRecurrent ν hy.not_isPositiveRecurrent

end Countable

/-! ### Finite closed communicating classes and finite state spaces -/

section FiniteClass

variable [MeasurableSingletonClass α]

/-- **Every finite closed communicating class is positive recurrent.** If the communicating class
of `x` is closed under `κ` and finite, then every state in `κ.communicatingClass x` is positive
recurrent. No countability assumption on the ambient state space is required. -/
theorem IsClosedSet.isPositiveRecurrent_of_finite_communicatingClass {κ : Kernel α α}
    [IsMarkovKernel κ] {x : α} (hclosed : κ.IsClosedSet (κ.communicatingClass x))
    (hfin : (κ.communicatingClass x).Finite) {y : α} (hy : y ∈ κ.communicatingClass x) :
    κ.IsPositiveRecurrent y := by
  have hs : MeasurableSet (κ.communicatingClass x) := hfin.measurableSet
  have : Finite (κ.communicatingClass x) := hfin.to_subtype
  have : IsMarkovKernel (κ.subtype hs) := (isMarkovKernel_subtype_iff_isClosedSet hs).mpr hclosed
  have : IsIrreducible Measure.count (κ.subtype hs) :=
    (isIrreducible_subtype_iff hs hclosed).mpr fun a ha b hb =>
      ((mem_communicatingClass_iff x a).mp ha).symm.trans ((mem_communicatingClass_iff x b).mp hb)
  exact (isPositiveRecurrent_subtype_iff κ hs ⟨y, hy⟩).mp
    ((κ.subtype hs).isPositiveRecurrent_of_finite ⟨y, hy⟩)

/-- The representative `x` of a finite closed communicating class is positive recurrent. -/
theorem IsClosedSet.isPositiveRecurrent_self_of_finite_communicatingClass {κ : Kernel α α}
    [IsMarkovKernel κ] {x : α} (hclosed : κ.IsClosedSet (κ.communicatingClass x))
    (hfin : (κ.communicatingClass x).Finite) :
    κ.IsPositiveRecurrent x :=
  hclosed.isPositiveRecurrent_of_finite_communicatingClass hfin
    ((mem_communicatingClass_iff x x).mpr (Communicates.refl x))

/-- **Existence and uniqueness of the stationary law on a finite closed communicating class.**
If `κ.communicatingClass x` is closed and finite, then `κ` admits a unique invariant probability
measure concentrated on `κ.communicatingClass x`. -/
theorem IsClosedSet.existsUnique_invariant_probability_of_finite_communicatingClass
    {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hclosed : κ.IsClosedSet (κ.communicatingClass x))
    (hfin : (κ.communicatingClass x).Finite) :
    ∃! π : Measure α,
      IsProbabilityMeasure π ∧ κ.Invariant π ∧ π (κ.communicatingClass x)ᶜ = 0 := by
  have hs : MeasurableSet (κ.communicatingClass x) := hfin.measurableSet
  have : Finite (κ.communicatingClass x) := hfin.to_subtype
  have : Nonempty (κ.communicatingClass x) :=
    ⟨⟨x, (mem_communicatingClass_iff x x).mpr (Communicates.refl x)⟩⟩
  have : IsMarkovKernel (κ.subtype hs) := (isMarkovKernel_subtype_iff_isClosedSet hs).mpr hclosed
  have : IsIrreducible Measure.count (κ.subtype hs) :=
    (isIrreducible_subtype_iff hs hclosed).mpr fun a ha b hb =>
      ((mem_communicatingClass_iff x a).mp ha).symm.trans ((mem_communicatingClass_iff x b).mp hb)
  exact (existsUnique_invariant_probability_subtype_iff κ hs hclosed).mp
    (existsUnique_invariant_probability (κ.subtype hs))

/-- On a finite state space with measurable singletons, every recurrent state is positive
recurrent, with no irreducibility hypothesis on `κ`. -/
theorem IsRecurrent.isPositiveRecurrent [Finite α] {κ : Kernel α α} [IsMarkovKernel κ] {x : α}
    (hx : κ.IsRecurrent x) :
    κ.IsPositiveRecurrent x :=
  hx.isClosedSet_communicatingClass.isPositiveRecurrent_self_of_finite_communicatingClass
    (Set.toFinite _)

/-- On a finite state space with measurable singletons, positive recurrence is equivalent to
recurrence. -/
theorem isPositiveRecurrent_iff_isRecurrent [Finite α] {κ : Kernel α α} [IsMarkovKernel κ]
    {x : α} :
    κ.IsPositiveRecurrent x ↔ κ.IsRecurrent x :=
  ⟨IsPositiveRecurrent.isRecurrent, IsRecurrent.isPositiveRecurrent⟩

/-- **A finite-state Markov chain has no null recurrent states.** -/
@[simp]
theorem not_isNullRecurrent_of_finite [Finite α] (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    ¬ κ.IsNullRecurrent x := by
  simp [isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent,
    isPositiveRecurrent_iff_isRecurrent]

/-- Almost every path of a finite-state Markov chain eventually enters and remains in the closed
communicating class of a positive recurrent state. -/
theorem ae_exists_isPositiveRecurrent_and_forall_mem_communicatingClass [Finite α]
    (κ : Kernel α α) [IsMarkovKernel κ] (ν : Measure α) :
    ∀ᵐ w ∂markovChainLaw ν κ, ∃ n,
      κ.IsPositiveRecurrent (w n) ∧ κ.IsClosedSet (κ.communicatingClass (w n)) ∧
        ∀ m, n ≤ m → w m ∈ κ.communicatingClass (w n) := by
  filter_upwards [κ.ae_exists_forall_mem_isClosedSet_communicatingClass ν] with w ⟨n, hclosed, hm⟩
  exact ⟨n, hclosed.isPositiveRecurrent_self_of_finite_communicatingClass (Set.toFinite _),
    hclosed, hm⟩

end FiniteClass

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

/-- On any realization of a counting-measure-irreducible aperiodic chain, the probability of
occupying a non-positive-recurrent state tends to zero. -/
theorem tendsto_measureReal_apply_eq_of_isAperiodic_of_not_isPositiveRecurrent
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] {κ : Kernel α α} [IsMarkovKernel κ]
    [Kernel.IsIrreducible Measure.count κ] {ν : Measure α} [IsProbabilityMeasure ν]
    {P : Measure Ω} {X : ℕ → Ω → α}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    (hκ : κ.IsAperiodic) {y : α} (hy : ¬ κ.IsPositiveRecurrent y) :
    Tendsto (fun n : ℕ => P.real {ω | X n ω = y}) atTop (𝓝 0) :=
  hX.tendsto_measureReal_apply_eq_of_isAperiodic_of_lintegral_return_eq_top hκ
    (Kernel.lintegral_return_eq_top_of_not_isPositiveRecurrent hy)

/-- On any realization of a counting-measure-irreducible aperiodic chain, the probability of
occupying a null recurrent state tends to zero. -/
theorem tendsto_measureReal_apply_eq_of_isAperiodic_of_isNullRecurrent
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] {κ : Kernel α α} [IsMarkovKernel κ]
    [Kernel.IsIrreducible Measure.count κ] {ν : Measure α} [IsProbabilityMeasure ν]
    {P : Measure Ω} {X : ℕ → Ω → α}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    (hκ : κ.IsAperiodic) {y : α} (hy : κ.IsNullRecurrent y) :
    Tendsto (fun n : ℕ => P.real {ω | X n ω = y}) atTop (𝓝 0) :=
  hX.tendsto_measureReal_apply_eq_of_isAperiodic_of_not_isPositiveRecurrent hκ
    hy.not_isPositiveRecurrent

end ProbabilityTheory.HasLaw
