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
import TauCeti.Data.ENat.ENNReal

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

At a null recurrent state `x`, the cycle occupation measure `κ.cycleOccupation x` has infinite total
mass (`IsNullRecurrent.cycleOccupation_univ`), every finite `κ`-invariant measure assigns mass zero
to `{x}`, no invariant probability measure exists when `κ` is irreducible, and on
counting-measure-irreducible chains the time-`n` singleton masses decay to zero from every finite
initial law with no aperiodicity assumption.

On countable state spaces with measurable singletons, the occupation strong law characterizes
positive and null recurrence via long-run visit frequencies: positive recurrence is equivalent to a
strictly positive expected (or almost-sure) limiting visit fraction starting from the state, while
null recurrence is equivalent to recurrence with vanishing expected limiting visit fraction.

Finally, restricting to a finite closed communicating class transfers finite irreducible positive
recurrence to arbitrary ambient state spaces with measurable singletons: every state in a finite
closed communicating class is positive recurrent, and `κ` admits a unique invariant probability
measure concentrated on that class. On a countable state space every recurrent state with a finite
communicating class is positive recurrent; on a finite state space recurrence and positive
recurrence therefore coincide unconditionally, no state is null recurrent, and almost every
trajectory eventually enters and remains in the closed communicating class of a positive recurrent
state.

## Main definitions and statements

* `Kernel.IsNullRecurrent`: `κ.IsRecurrent x ∧ κ.meanReturnTime x = ∞`.
* `Kernel.isTransient_or_isPositiveRecurrent_or_isNullRecurrent`: state-level recurrence
  trichotomy.
* `Kernel.isPositiveRecurrent_subtype_iff` and `Kernel.isNullRecurrent_subtype_iff`: invariance
  under restriction to a closed measurable set.
* `Kernel.IsNullRecurrent.of_reaches` and `Kernel.Communicates.isNullRecurrent_iff`: class
  property of null recurrence.
* `Kernel.forall_isTransient_or_forall_isPositiveRecurrent_or_forall_isNullRecurrent`: global
  recurrence trichotomy for counting-measure-irreducible chains.
* `Kernel.tendsto_pow_comp_real_singleton_of_not_isPositiveRecurrent` and
  `Kernel.IsNullRecurrent.tendsto_pow_comp_real_singleton`: pointwise decay of transition masses
  without aperiodicity.
* `Kernel.isPositiveRecurrent_iff_exists_pos_tendsto_integral_visitCount_div`,
  `Kernel.isPositiveRecurrent_iff_exists_pos_ae_tendsto_visitCount_div`,
  `Kernel.isNullRecurrent_iff_isRecurrent_and_tendsto_integral_visitCount_div_zero`, and
  `Kernel.IsNullRecurrent.ae_tendsto_visitCount_div_zero`: occupation-frequency characterizations
  and limits for positive and null recurrence.
* `Kernel.IsClosedSet.isPositiveRecurrent_of_finite_communicatingClass`,
  `Kernel.IsRecurrent.isPositiveRecurrent_of_finite_communicatingClass`,
  `Kernel.isPositiveRecurrent_iff_isRecurrent_of_finite`, and
  `Kernel.not_isNullRecurrent_of_finite`: finite closed communicating classes and finite state
  spaces.

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

/-! ### Restriction to a closed set and singleton-free properties -/

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

/-- A deterministic kernel has no null recurrent states, on any measurable space. -/
@[simp]
theorem not_isNullRecurrent_deterministic {f : α → α} (hf : Measurable f) (x : α) :
    ¬ (deterministic f hf).IsNullRecurrent x := by
  -- If `x` is recurrent under `f`, some positive iterate `f^[k] x` cannot be measurably separated
  -- from `x`; replacing coordinate `k` of the orbit `w₀` by `x` preserves `Measure.dirac w₀` and
  -- bounds the mean positive return time by `k`.
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
    -- Unfold `m'.MeasurableSet'` and preimage membership explicitly on each cylinder generator.
    have hm'_iff (T : Set (ℕ → α)) : @MeasurableSet (ℕ → α) m' T ↔ (w₀ ∈ T ↔ w' ∈ T) := Iff.rfl
    have hle : (MeasurableSpace.pi : MeasurableSpace (ℕ → α)) ≤ m' := by
      rw [MeasurableSpace.pi, iSup_le_iff]
      rintro j _ ⟨B, hB, rfl⟩
      rw [hm'_iff, mem_preimage, mem_preimage]
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
  rw [isNullRecurrent_congr (const_dirac_eq_deterministic a)]
  exact not_isNullRecurrent_deterministic measurable_const x

/-! ### Class properties and invariant measures -/

section MeasurableSingleton

variable [MeasurableSingletonClass α]

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
  cases isEmpty_or_nonempty α with
  | inl hEmpty => exact Or.inl fun x => hEmpty.elim x
  | inr hne =>
    let ⟨x₀⟩ := hne
    rcases κ.isTransient_or_isPositiveRecurrent_or_isNullRecurrent x₀ with ht | hp | hn
    · exact Or.inl fun x => (isTransient_iff_isTransient x₀ x).mp ht
    · exact Or.inr (Or.inl fun x => (isPositiveRecurrent_iff_isPositiveRecurrent x₀ x).mp hp)
    · exact Or.inr (Or.inr fun x => (isNullRecurrent_iff_isNullRecurrent x₀ x).mp hn)

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

end MeasurableSingleton

/-! ### Countable state spaces: occupation-frequency characterizations and period sampling -/

section Countable

variable [Countable α] [MeasurableSingletonClass α]

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

omit [Countable α] in
private theorem period_pos_of_isRecurrent {κ : Kernel α α} [IsMarkovKernel κ] {y : α}
    (hy : κ.IsRecurrent y) :
    0 < κ.period y := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have hempty := period_eq_zero_iff.mp h0
  have hzero (n : ℕ) : (κ ^ (n + 1)) y {y} = 0 :=
    nonpos_iff_eq_zero.mp (not_lt.mp fun hpos =>
      Set.eq_empty_iff_forall_notMem.mp hempty (n + 1)
        (mem_returnLengths.mpr ⟨Nat.succ_pos n, hpos⟩))
  have hsum : ∑' n : ℕ, (κ ^ n) y {y} = 1 := by
    rw [tsum_eq_zero_add' CompleteLattice.summable]
    simp [hzero, one_def, id_apply]
  exact ENNReal.one_ne_top (hsum.symm.trans (isRecurrent_iff_tsum_eq_top.mp hy))

omit [Countable α] [MeasurableSingletonClass α] in
private theorem cesaro_pow_mul_le (κ : Kernel α α) {d : ℕ} (hd : 0 < d) (y : α) (k : ℕ) :
    (∑ j ∈ Finset.range k, (((κ ^ d) ^ (j + 1)) y).real {y}) / k ≤
      (d : ℝ) * ((∑ i ∈ Finset.range (d * k), ((κ ^ (i + 1)) y).real {y}) / (d * k : ℕ)) := by
  let φ : ℕ → ℕ := fun j => d * (j + 1) - 1
  have hφ (j : ℕ) : φ j + 1 = d * (j + 1) :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hd (Nat.succ_pos j)))
  have hφ_inj : Function.Injective φ := fun i j hij => by
    have hmul : d * (i + 1) = d * (j + 1) := by rw [← hφ i, ← hφ j, hij]
    exact Nat.succ.inj (mul_right_injective₀ hd.ne' hmul)
  have hsub : (Finset.range k).image φ ⊆ Finset.range (d * k) := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_range] at hj ⊢
    exact Nat.lt_of_lt_of_le (by rw [← hφ j]; exact Nat.lt_succ_self _)
      (Nat.mul_le_mul_left d hj)
  have hsum_le :
      (∑ j ∈ Finset.range k, (((κ ^ d) ^ (j + 1)) y).real {y}) ≤
        ∑ i ∈ Finset.range (d * k), ((κ ^ (i + 1)) y).real {y} := calc
    (∑ j ∈ Finset.range k, (((κ ^ d) ^ (j + 1)) y).real {y})
      = ∑ j ∈ Finset.range k, ((κ ^ (φ j + 1)) y).real {y} := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← pow_mul, hφ j]
    _ = ∑ i ∈ (Finset.range k).image φ, ((κ ^ (i + 1)) y).real {y} :=
          (Finset.sum_image (f := fun i => ((κ ^ (i + 1)) y).real {y})
            fun _ _ _ _ hij => hφ_inj hij).symm
    _ ≤ ∑ i ∈ Finset.range (d * k), ((κ ^ (i + 1)) y).real {y} :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => measureReal_nonneg
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [Nat.cast_mul, ← mul_div_assoc, mul_div_mul_left _ _ hd0]
  exact div_le_div_of_nonneg_right hsum_le (Nat.cast_nonneg k)

/-- Sampling a chain at multiples of `κ.period y` preserves null recurrence of `y`. -/
theorem IsNullRecurrent.pow_period {κ : Kernel α α} [IsMarkovKernel κ] {y : α}
    (hy : κ.IsNullRecurrent y) :
    (κ ^ κ.period y).IsNullRecurrent y := by
  -- Positive return probabilities occur only at multiples of `κ.period y`, while Cesàro return
  -- averages of `κ ^ κ.period y` are bounded by `κ.period y` times those of `κ`.
  set d := κ.period y
  have hd : 0 < d := period_pos_of_isRecurrent hy.isRecurrent
  have hrec : (κ ^ d).IsRecurrent y := by
    rw [isRecurrent_iff_tsum_eq_top]
    simp_rw [← pow_mul]
    have htsum : (∑' k : ℕ, (κ ^ (d * k)) y {y}) = ∑' n : ℕ, (κ ^ n) y {y} := by
      refine Function.Injective.tsum_eq (f := fun n => (κ ^ n) y {y})
        (mul_right_injective₀ hd.ne') fun n hn => ?_
      rw [Function.mem_support] at hn
      obtain ⟨k, rfl⟩ := Classical.not_not.mp
        (mt pow_apply_singleton_self_eq_zero_of_not_period_dvd hn)
      exact ⟨k, rfl⟩
    exact htsum.trans (isRecurrent_iff_tsum_eq_top.mp hy.isRecurrent)
  refine ⟨hrec, ?_⟩
  rw [← not_lt_top_iff, ← isPositiveRecurrent_iff, ← inv_meanReturnTime_toReal_eq_zero_iff]
  refine tendsto_nhds_unique ((κ ^ d).tendsto_cesaro_pow_real_singleton_self y) ?_
  have hlim0 : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, ((κ ^ (i + 1)) y).real {y}) / n)
      atTop (𝓝 0) := by
    simpa only [inv_meanReturnTime_toReal_eq_zero_iff.mpr hy.not_isPositiveRecurrent] using
      κ.tendsto_cesaro_pow_real_singleton_self y
  have hlim_dk : Tendsto (fun k : ℕ =>
      (d : ℝ) * ((∑ i ∈ Finset.range (d * k), ((κ ^ (i + 1)) y).real {y}) / (d * k : ℕ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using (tendsto_const_nhds (x := (d : ℝ))).mul
      (hlim0.comp (tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k hd) tendsto_id))
  exact squeeze_zero (fun k => div_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
    (Nat.cast_nonneg k)) (cesaro_pow_mul_le κ hd y) hlim_dk

end Countable

/-! ### Pointwise decay at non-positive-recurrent states -/

section PointwiseDecay

variable [MeasurableSingletonClass α]

omit [MeasurableSingletonClass α] in
private theorem lintegral_return_eq_top_of_not_isPositiveRecurrent {κ : Kernel α α}
    [IsMarkovKernel κ] {y : α} (hy : ¬ κ.IsPositiveRecurrent y) :
    (∫⁻ ω, (hittingAfter (fun n ω => ω n) {y} 1 ω).recTopCoe ⊤ (fun n => (n : ℝ≥0∞))
      ∂markovChainLaw (Measure.dirac y) κ) = ⊤ := by
  simp_rw [WithTop.recTopCoe_top_natCast_eq_toENNReal]
  rw [← meanReturnTime_def]
  exact not_lt_top_iff.mp ((isPositiveRecurrent_iff κ y).not.mp hy)

private theorem tendsto_pow_comp_real_singleton_of_isAperiodic_of_not_isPositiveRecurrent_finite
    {κ : Kernel α α} [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    (hκ : κ.IsAperiodic) {y : α} (hy : ¬ κ.IsPositiveRecurrent y)
    (ν : Measure α) [IsFiniteMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
  by_cases h0 : ν Set.univ = 0
  · have hzero (n : ℕ) : ((κ ^ n) ∘ₘ ν).real {y} = 0 := by
      rw [Measure.measure_univ_eq_zero.mp h0, measureReal_def,
        Measure.bind_apply (measurableSet_singleton y) (κ ^ n).aemeasurable]
      simp
    simp_rw [hzero]
    exact tendsto_const_nhds
  · let ν₀ : Measure α := (ν Set.univ)⁻¹ • ν
    have : IsProbabilityMeasure ν₀ :=
      ⟨by simp [ν₀, smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 (measure_ne_top ν Set.univ)]⟩
    have hν : ν = ν Set.univ • ν₀ := by
      simp [ν₀, smul_smul, ENNReal.mul_inv_cancel h0 (measure_ne_top ν Set.univ)]
    have hprob := κ.tendsto_pow_comp_real_singleton_of_isAperiodic_of_lintegral_return_eq_top hκ
      (lintegral_return_eq_top_of_not_isPositiveRecurrent hy) ν₀
    have hscale (n : ℕ) : ((κ ^ n) ∘ₘ ν).real {y} =
        ν.real Set.univ * ((κ ^ n) ∘ₘ ν₀).real {y} := by
      conv_lhs => rw [hν]
      simp [Measure.comp_smul, Measure.real, smul_apply, smul_eq_mul, ENNReal.toReal_mul]
    simp_rw [hscale]
    simpa only [mul_zero] using (tendsto_const_nhds (x := ν.real Set.univ)).mul hprob

private theorem pow_period_mul_comp_restrict_compl_singleton_eq_zero
    {κ : Kernel α α} [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    (y : α) (μ : Measure α) (q : ℕ) :
    (((κ ^ κ.period y) ^ q) ∘ₘ (μ.restrict ((κ ^ κ.period y).communicatingClass y)ᶜ)) {y} = 0 := by
  have := countable_of_isIrreducible_count (κ := κ)
  set d := κ.period y
  set η := κ ^ d
  set s := η.communicatingClass y
  have hs : MeasurableSet s := η.measurableSet_communicatingClass y
  have hzero_outside : ∀ z ∈ sᶜ, (η ^ q) z {y} = 0 := fun z hz => by
    refine nonpos_iff_eq_zero.mp (not_lt.mp fun hpos => hz ?_)
    obtain ⟨a, ha⟩ := exists_pos_pow_apply_singleton (κ := κ) y z
    have hpos' : 0 < (κ ^ (d * q)) z {y} := by rwa [pow_mul]
    have hdvd_sum : d ∣ a + d * q := Classical.not_not.mp
      (mt pow_apply_singleton_self_eq_zero_of_not_period_dvd (pow_add_apply_pos ha hpos').ne')
    obtain ⟨m, rfl⟩ := (Nat.dvd_add_left (dvd_mul_right d q)).mp hdvd_sum
    have hyz : η.Reaches y z := (reaches_def y z).mpr ⟨m, by rwa [← pow_mul]⟩
    have hzy : η.Reaches z y := (reaches_def z y).mpr ⟨q, hpos⟩
    exact (mem_communicatingClass_iff y z).mpr ((communicates_def y z).mpr ⟨hyz, hzy⟩)
  rw [Measure.bind_apply (measurableSet_singleton y) (η ^ q).aemeasurable]
  exact (lintegral_eq_zero_iff ((η ^ q).measurable_coe (measurableSet_singleton y))).mpr
    ((ae_restrict_iff' hs.compl).mpr (Eventually.of_forall hzero_outside))

private theorem tendsto_pow_period_mul_comp_real_singleton_of_isNullRecurrent
    {κ : Kernel α α} [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    {y : α} (hy : κ.IsNullRecurrent y) (μ : Measure α) [IsFiniteMeasure μ] :
    Tendsto (fun q : ℕ => ((κ ^ (κ.period y * q)) ∘ₘ μ).real {y}) atTop (𝓝 0) := by
  have := countable_of_isIrreducible_count (κ := κ)
  set d := κ.period y
  set η := κ ^ d
  have hη : η.IsNullRecurrent y := hy.pow_period
  set s := η.communicatingClass y
  have hs : MeasurableSet s := η.measurableSet_communicatingClass y
  have hclosed : η.IsClosedSet s := hη.isRecurrent.isClosedSet_communicatingClass
  have : IsMarkovKernel (η.subtype hs) := (isMarkovKernel_subtype_iff_isClosedSet hs).mpr hclosed
  have : IsIrreducible Measure.count (η.subtype hs) :=
    hclosed.isIrreducible_subtype_communicatingClass hs
  let y_s : s := ⟨y, (mem_communicatingClass_iff y y).mpr (Communicates.refl y)⟩
  have haper : (η.subtype hs).IsAperiodic := by
    rw [isAperiodic_iff_period_eq_one y_s, period_subtype hs hclosed]
    exact period_pow_period κ y
  have hy_s : ¬ (η.subtype hs).IsPositiveRecurrent y_s := by
    rw [isPositiveRecurrent_subtype_iff η hs y_s]
    exact hη.not_isPositiveRecurrent
  let μ_s : Measure s := μ.comap Subtype.val
  have : IsFiniteMeasure μ_s := ⟨by
    rw [(MeasurableEmbedding.subtype_coe hs).comap_apply]
    exact measure_lt_top _ _⟩
  have heq (q : ℕ) : ((κ ^ (d * q)) ∘ₘ μ).real {y} =
      (((η.subtype hs) ^ q) ∘ₘ μ_s).real {y_s} := by
    rw [pow_mul]
    conv_lhs => rw [← Measure.restrict_add_restrict_compl hs (μ := μ)]
    rw [Measure.comp_add, measureReal_def, add_apply,
      pow_period_mul_comp_restrict_compl_singleton_eq_zero y μ q, add_zero,
      ← map_comap_subtype_coe hs μ, ← map_pow_comp_subtype η hs hclosed q μ_s,
      (MeasurableEmbedding.subtype_coe hs).map_apply]
    have hpre : (Subtype.val : s → α) ⁻¹' {y_s.val} = {y_s} := by
      rw [← Set.image_singleton, Subtype.coe_injective.preimage_image]
    rw [← measureReal_def]
    exact congrArg (((η.subtype hs) ^ q) ∘ₘ μ_s).real hpre
  simp_rw [heq]
  exact tendsto_pow_comp_real_singleton_of_isAperiodic_of_not_isPositiveRecurrent_finite
    haper hy_s μ_s

/-- **Pointwise decay at null recurrent states.** On a counting-measure-irreducible chain (periodic
or aperiodic), if `y` is null recurrent, then the time-`n` singleton mass at `y` tends to zero from
every finite initial measure. -/
theorem IsNullRecurrent.tendsto_pow_comp_real_singleton {κ : Kernel α α} [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] {y : α} (hy : κ.IsNullRecurrent y)
    (ν : Measure α) [IsFiniteMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
  set d := κ.period y
  have hd : 0 < d := period_pos_of_isRecurrent hy.isRecurrent
  have hres (r : ℕ) : Tendsto (fun q : ℕ => ((κ ^ (d * q + r)) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
    have hcomp (q : ℕ) :
        (κ ^ (d * q + r)) ∘ₘ ν = (κ ^ (d * q)) ∘ₘ ((κ ^ r : Kernel α α) ∘ₘ ν) := by
      rw [pow_add, Measure.comp_assoc]
    simp_rw [hcomp]
    exact tendsto_pow_period_mul_comp_real_singleton_of_isNullRecurrent hy
      ((κ ^ r : Kernel α α) ∘ₘ ν)
  refine tendsto_def.mpr fun U hU => mem_preimage.mp ?_
  have hall : ∀ᶠ n in atTop, ∀ r ∈ Finset.range d,
      ((κ ^ (d * (n / d) + r)) ∘ₘ ν).real {y} ∈ U :=
    (eventually_all_finset (Finset.range d)).mpr fun r _ =>
      ((hres r).comp (Nat.tendsto_div_const_atTop hd.ne')).eventually hU
  exact hall.mono fun n hn => by
    simpa only [Nat.div_add_mod] using hn (n % d) (Finset.mem_range.mpr (Nat.mod_lt n hd))

/-- **Pointwise decay at non-positive-recurrent states.** On a counting-measure-irreducible chain
(periodic or aperiodic), if `y` is not positive recurrent, then the time-`n` singleton mass at `y`
tends to zero from every finite initial measure. -/
theorem tendsto_pow_comp_real_singleton_of_not_isPositiveRecurrent
    {κ : Kernel α α} [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    {y : α} (hy : ¬ κ.IsPositiveRecurrent y)
    (ν : Measure α) [IsFiniteMeasure ν] :
    Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ ν).real {y}) atTop (𝓝 0) := by
  rcases not_isPositiveRecurrent_iff.mp hy with ht | hn
  · exact ht.tendsto_pow_comp_real_singleton ν
  · exact hn.tendsto_pow_comp_real_singleton ν

end PointwiseDecay

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
    hclosed.isIrreducible_subtype_communicatingClass hs
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
    hclosed.isIrreducible_subtype_communicatingClass hs
  exact (existsUnique_invariant_probability_subtype_iff κ hs hclosed).mp
    (existsUnique_invariant_probability (κ.subtype hs))

/-- On a countable state space with measurable singletons, every recurrent state whose
communicating class is finite is positive recurrent. -/
theorem IsRecurrent.isPositiveRecurrent_of_finite_communicatingClass [Countable α]
    {κ : Kernel α α} [IsMarkovKernel κ] {x : α} (hx : κ.IsRecurrent x)
    (hfin : (κ.communicatingClass x).Finite) :
    κ.IsPositiveRecurrent x :=
  hx.isClosedSet_communicatingClass.isPositiveRecurrent_self_of_finite_communicatingClass hfin

/-- On a finite state space with measurable singletons, every recurrent state is positive
recurrent, with no irreducibility hypothesis on `κ`. -/
theorem IsRecurrent.isPositiveRecurrent_of_finite [Finite α] {κ : Kernel α α} [IsMarkovKernel κ]
    {x : α} (hx : κ.IsRecurrent x) :
    κ.IsPositiveRecurrent x :=
  hx.isPositiveRecurrent_of_finite_communicatingClass (Set.toFinite _)

/-- On a finite state space with measurable singletons, positive recurrence is equivalent to
recurrence. -/
theorem isPositiveRecurrent_iff_isRecurrent_of_finite [Finite α] {κ : Kernel α α}
    [IsMarkovKernel κ] {x : α} :
    κ.IsPositiveRecurrent x ↔ κ.IsRecurrent x :=
  ⟨IsPositiveRecurrent.isRecurrent, IsRecurrent.isPositiveRecurrent_of_finite⟩

/-- **A finite-state Markov chain has no null recurrent states.** -/
@[simp]
theorem not_isNullRecurrent_of_finite [Finite α] (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    ¬ κ.IsNullRecurrent x := by
  simp [isNullRecurrent_iff_isRecurrent_and_not_isPositiveRecurrent,
    isPositiveRecurrent_iff_isRecurrent_of_finite]

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

/-- On any realization of a counting-measure-irreducible chain (periodic or aperiodic) started from
a finite initial law, the time-`n` measure of occupying a non-positive-recurrent state tends to
zero. -/
theorem tendsto_measureReal_apply_eq_of_not_isPositiveRecurrent
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] {κ : Kernel α α} [IsMarkovKernel κ]
    [Kernel.IsIrreducible Measure.count κ] {ν : Measure α} [IsFiniteMeasure ν]
    {P : Measure Ω} {X : ℕ → Ω → α}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    {y : α} (hy : ¬ κ.IsPositiveRecurrent y) :
    Tendsto (fun n : ℕ => P.real {ω | X n ω = y}) atTop (𝓝 0) := by
  have heq (n : ℕ) : P.real {ω | X n ω = y} = ((κ ^ n) ∘ₘ ν).real {y} :=
    (hX.eval_markovChainLaw ν κ n).measureReal_eq (measurableSet_singleton y)
  simp_rw [heq]
  exact Kernel.tendsto_pow_comp_real_singleton_of_not_isPositiveRecurrent hy ν

/-- On any realization of a counting-measure-irreducible chain (periodic or aperiodic) started from
a finite initial law, the time-`n` measure of occupying a null recurrent state tends to zero. -/
theorem tendsto_measureReal_apply_eq_of_isNullRecurrent
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] {κ : Kernel α α} [IsMarkovKernel κ]
    [Kernel.IsIrreducible Measure.count κ] {ν : Measure α} [IsFiniteMeasure ν]
    {P : Measure Ω} {X : ℕ → Ω → α}
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    {y : α} (hy : κ.IsNullRecurrent y) :
    Tendsto (fun n : ℕ => P.real {ω | X n ω = y}) atTop (𝓝 0) :=
  hX.tendsto_measureReal_apply_eq_of_not_isPositiveRecurrent hy.not_isPositiveRecurrent

end ProbabilityTheory.HasLaw
