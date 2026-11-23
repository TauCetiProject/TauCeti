/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.Piecewise
public import TauCeti.Data.Set.Countable

/-!
# Measurability of stopped values

For a process `u` and a random time `τ : Ω → WithTop ι`, Mathlib's `stoppedValue u τ` is the value
`u (τ ω) ω`, with an arbitrary index used where `τ ω = ⊤`. Mathlib proves that it is measurable
for the σ-algebra of a stopping time when `u` is progressively measurable with values in a
pseudo-metrizable Borel space (`MeasureTheory.measurable_stoppedValue`).

When time is countable, neither progressive measurability nor a topology on the values is needed:
the stopped value is pieced together from the countably many events `{τ = i}`, as recorded by the
preimage decomposition `MeasureTheory.stoppedValue_preimage_eq`. This file proves that

* `stoppedValue u τ` is measurable whenever `τ` and every `u i` are
  (`MeasureTheory.measurable_stoppedValue_of_countable`), which applies to processes, such as the
  shifted paths of a chain, that are not adapted to the filtration of `τ`;
* `stoppedValue u τ` is measurable for the σ-algebra of the stopping time `τ` whenever `u` is
  adapted in the measurable sense (`MeasureTheory.Adapted.measurable_stoppedValue`).

These are the measurability facts needed to state the strong Markov property of a chain with values
in an arbitrary measurable space.

Even for uncountable time, a random time with countable range and measurable level sets—in
particular any countable-range stopping time, whose infinite level set belongs to the stopping
σ-algebra by `MeasureTheory.IsStoppingTime.measurableSet_eq_top_of_countable_range`—makes the
stopped value of a coordinatewise measurable process measurable in the ambient σ-algebra
(`MeasureTheory.IsStoppingTime.measurable_stoppedValue_of_countable_range`), and permits strongly
measurable gluing for adapted processes without any topology on time and without a separability
assumption or any algebraic structure on the values. Capping such a time at each deterministic
horizon shows that a strongly adapted process remains strongly adapted after stopping, including on
a raw filtration. For restarted increments `u (τ + t) - u τ`,
`MeasureTheory.stoppedValue_add_const_sub_stoppedValue`,
`MeasureTheory.stoppedValue_add_const_sub_stoppedValue_of_eq_top`, and
`MeasureTheory.continuous_stoppedValue_add_const_sub_stoppedValue` relate the difference of stopped
values to the stopped increment family on `{τ ≠ ⊤}`, record its vanishing at `⊤`, and show that it
preserves pathwise continuity.

For everywhere-continuous processes with coordinatewise strongly measurable evaluations on a
second-countable metrizable ordered Borel time domain, evaluating `stoppedValue` at any measurable
random time yields a strongly measurable map
(`MeasureTheory.stronglyMeasurable_stoppedValue_of_continuous`), with no filtration, stopping-time,
or Borel state-space assumption.
-/

public section

open Filter

namespace MeasureTheory

/-- At a stopping time `τ` with countable range over a partial order, the infinite level set
`{ω | τ ω = ⊤}` is measurable with respect to the stopping σ-algebra `hτ.measurableSpace`. -/
theorem IsStoppingTime.measurableSet_eq_top_of_countable_range {Ω ι : Type*} [PartialOrder ι]
    {m : MeasurableSpace Ω} {ℱ : Filtration ι m} {τ : Ω → WithTop ι} (hτ : IsStoppingTime ℱ τ)
    (hc : (Set.range τ).Countable) :
    MeasurableSet[hτ.measurableSpace] {ω | τ ω = ⊤} := by
  have hR : {i : ι | (i : WithTop ι) ∈ Set.range τ}.Countable :=
    hc.preimage WithTop.coe_injective
  have hmeas (i : ι) : MeasurableSet[hτ.measurableSpace] {ω | τ ω = i} := by
    rw [← Set.univ_inter {ω | τ ω = i}, hτ.measurableSet_inter_eq_iff, Set.univ_inter]
    exact hτ.measurableSet_eq_of_countable_range hc i
  have htop : {ω | τ ω = ⊤} =
      (⋃ i ∈ {i : ι | (i : WithTop ι) ∈ Set.range τ}, {ω | τ ω = i})ᶜ := by
    ext ω
    cases h : τ ω with
    | top => simp [h]
    | coe i => simpa [h] using (⟨ω, h⟩ : ∃ y, τ y = (i : WithTop ι))
  rw [htop]
  exact (MeasurableSet.biUnion hR fun i _ ↦ hmeas i).compl

variable {Ω ι β : Type*} [Nonempty ι] {m : MeasurableSpace Ω} {u : ι → Ω → β}
  {τ : Ω → WithTop ι}

/-- On a finite-time slice, the stopped value is the value of the process at that time. -/
theorem stoppedValue_of_eq {i : ι} {ω : Ω} (h : τ ω = i) :
    stoppedValue u τ ω = u i ω := by
  simp [stoppedValue, h]

/-- On the finite-time event `{τ ≠ ⊤}`, subtracting the stopped value from the stopped value at a
translated time agrees with sampling the shifted increment process at `τ`. -/
theorem stoppedValue_add_const_sub_stoppedValue [Add ι] [Sub β] (t : ι) {ω : Ω} (h : τ ω ≠ ⊤) :
    stoppedValue u (fun ω' ↦ τ ω' + t) ω - stoppedValue u τ ω =
      stoppedValue (fun s ω' ↦ u (s + t) ω' - u s ω') τ ω := by
  cases hτ : τ ω with
  | top => exact absurd hτ h
  | coe s => simp [stoppedValue, hτ, ← WithTop.coe_add]

/-- At an infinite stopping time, translating the time by a finite increment leaves both stopped
values at the fallback index, so their difference vanishes. -/
theorem stoppedValue_add_const_sub_stoppedValue_of_eq_top [Add ι] [AddGroup β] (t : ι) {ω : Ω}
    (h : τ ω = ⊤) :
    stoppedValue u (fun ω' ↦ τ ω' + t) ω - stoppedValue u τ ω = 0 := by
  simp [stoppedValue, h]

/-- If `u · ω` is continuous, then for fixed `ω` the restarted increment path
`t ↦ stoppedValue u (fun ω' ↦ τ ω' + t) ω - stoppedValue u τ ω` is continuous: it shifts and
recenters `u · ω` when `τ ω` is finite and vanishes identically when `τ ω = ⊤`. -/
theorem continuous_stoppedValue_add_const_sub_stoppedValue [TopologicalSpace ι] [Add ι]
    [ContinuousAdd ι] [TopologicalSpace β] [AddGroup β] [ContinuousSub β] (τ : Ω → WithTop ι)
    {ω : Ω} (hu : Continuous (u · ω)) :
    Continuous (fun t : ι ↦ stoppedValue u (fun ω' ↦ τ ω' + t) ω - stoppedValue u τ ω) := by
  cases h : τ ω with
  | top =>
    simpa only [stoppedValue_add_const_sub_stoppedValue_of_eq_top _ h] using continuous_const
  | coe s =>
    have heq :
        (fun t : ι ↦ stoppedValue u (fun ω' ↦ τ ω' + t) ω - stoppedValue u τ ω) =
          fun t ↦ u (s + t) ω - u s ω :=
      funext fun t ↦
        (stoppedValue_add_const_sub_stoppedValue (u := u) (τ := τ) t
          (h ▸ WithTop.coe_ne_top)).trans (stoppedValue_of_eq h)
    rw [heq]
    exact (hu.comp (continuous_const.add continuous_id)).sub continuous_const

/-- The preimage of a set under a stopped value, decomposed along the values of the stopping
time. -/
theorem stoppedValue_preimage_eq (t : Set β) :
    stoppedValue u τ ⁻¹' t =
      (⋃ i : ι, {ω | τ ω = i} ∩ u i ⁻¹' t) ∪
        ({ω | τ ω = ⊤} ∩ u (⊤ : WithTop ι).untopA ⁻¹' t) := by
  ext ω
  simp only [stoppedValue, Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  cases h : τ ω with
  | top => simp
  | coe i => simp

/-- The level-set partition used to glue stopped values. -/
private noncomputable def stoppedValuePartition (τ : Ω → WithTop ι) :
    IndexedPartition (fun v : Set.range τ => {ω | τ ω = v.val}) where
  eq_of_mem := fun hv hw => Subtype.ext (hv.symm.trans hw)
  some := fun v => v.property.choose
  some_mem := fun v => v.property.choose_spec
  index := fun ω => ⟨τ ω, ω, rfl⟩
  mem_index := fun _ => rfl

private theorem stoppedValue_eq_partition (ω : Ω) :
    stoppedValue u τ ω = u ((stoppedValuePartition τ).index ω).val.untopA ω := by
  have h := Set.mem_ofPred_eq.mp ((stoppedValuePartition τ).mem_index ω)
  simp only [stoppedValue, h]

variable [MeasurableSpace β]

/-- At a random time with countable range whose level sets are measurable, the stopped value of a
coordinatewise measurable process is measurable. Neither a topology on time nor adaptation of the
process is required. -/
theorem measurable_stoppedValue_of_countable_range_of_measurableSet_eq
    (hu : ∀ i, Measurable (u i)) (hc : (Set.range τ).Countable)
    (hτ : ∀ v ∈ Set.range τ, MeasurableSet {ω | τ ω = v}) :
    Measurable (stoppedValue u τ) := by
  intro t ht
  have hpre : stoppedValue u τ ⁻¹' t =
      ⋃ v ∈ Set.range τ, {ω | τ ω = v} ∩ u v.untopA ⁻¹' t := by
    ext ω
    simp only [stoppedValue, Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq, exists_prop]
    exact ⟨fun h => ⟨τ ω, ⟨ω, rfl⟩, rfl, h⟩,
      fun ⟨v, _, hv, h⟩ => by simpa only [hv] using h⟩
  rw [hpre]
  exact MeasurableSet.biUnion hc fun v hv => (hτ v hv).inter (hu v.untopA ht)

/-- At a measurable random time with countable range, the stopped value of a coordinatewise
measurable process is measurable. -/
theorem measurable_stoppedValue_of_countable_range [MeasurableSpace (WithTop ι)]
    [MeasurableSingletonClass (WithTop ι)] (hu : ∀ i, Measurable (u i))
    (hτ : Measurable τ) (hc : (Set.range τ).Countable) :
    Measurable (stoppedValue u τ) :=
  measurable_stoppedValue_of_countable_range_of_measurableSet_eq hu hc
    fun v _ => hτ (measurableSet_singleton v)

/-- In countable time, a stopped value of a measurable process at a measurable random time is
measurable. -/
theorem measurable_stoppedValue_of_countable [Countable ι] [MeasurableSpace (WithTop ι)]
    [MeasurableSingletonClass (WithTop ι)] (hu : ∀ i, Measurable (u i)) (hτ : Measurable τ) :
    Measurable (stoppedValue u τ) :=
  measurable_stoppedValue_of_countable_range hu hτ (Set.to_countable _)

/-- At a stopping time with countable range, the stopped value of a coordinatewise measurable
process is measurable in the ambient σ-algebra. Neither adaptation of the process nor any topology
on time is required; at infinity the stopped value uses `(⊤ : WithTop ι).untopA`. -/
theorem IsStoppingTime.measurable_stoppedValue_of_countable_range [PartialOrder ι]
    {ℱ : Filtration ι m} (hτ : IsStoppingTime ℱ τ) (hc : (Set.range τ).Countable)
    (hu : ∀ i, Measurable (u i)) :
    Measurable (stoppedValue u τ) := by
  refine measurable_stoppedValue_of_countable_range_of_measurableSet_eq hu hc fun v _ ↦ ?_
  cases v with
  | top => exact hτ.measurableSpace_le _ (hτ.measurableSet_eq_top_of_countable_range hc)
  | coe i => exact ℱ.le i _ (hτ.measurableSet_eq_of_countable_range hc i)

omit [Nonempty ι] in
/-- Every level set of a countable-range stopping time, including its infinite-time event,
is measurable for the stopped sigma-algebra, even in a partially ordered time type. -/
theorem IsStoppingTime.measurableSet_stopping_eq_of_countable_range [PartialOrder ι]
    {ℱ : Filtration ι m} (hτ : IsStoppingTime ℱ τ) (hc : (Set.range τ).Countable)
    (v : WithTop ι) : MeasurableSet[hτ.measurableSpace] {ω | τ ω = v} := by
  cases v with
  | top => exact hτ.measurableSet_eq_top_of_countable_range hc
  | coe i =>
    rw [← Set.univ_inter {ω | τ ω = i}, hτ.measurableSet_inter_eq_iff, Set.univ_inter]
    exact hτ.measurableSet_eq_of_countable_range hc i

section CountableTime

variable [PartialOrder ι] [Countable ι] {f : Filtration ι m}

/-- In countable time, a stopped value of an adapted process is measurable for the σ-algebra of
the stopping time. -/
theorem Adapted.measurable_stoppedValue (hu : Adapted f u) (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] (stoppedValue u τ) := by
  intro t ht
  have hu' : ∀ i, MeasurableSet[⨆ j, f j] (u i ⁻¹' t) := fun i =>
    le_iSup f i _ (hu i ht)
  have heq : ∀ i : ι, MeasurableSet[⨆ j, f j] {ω | τ ω = i} := fun i =>
    le_iSup f i _ (hτ.measurableSet_eq_of_countable i)
  have htop : MeasurableSet[⨆ j, f j] {ω | τ ω = ⊤} := by
    have : {ω | τ ω = ⊤} = (⋃ i : ι, {ω | τ ω = i})ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      simpa [eq_comm] using WithTop.eq_top_iff_forall_ne (x := τ ω)
    rw [this]
    exact (MeasurableSet.iUnion heq).compl
  refine ⟨?_, fun i => ?_⟩
  · rw [stoppedValue_preimage_eq]
    exact .union (.iUnion fun i => (heq i).inter (hu' i)) (htop.inter (hu' _))
  · -- Before time `i`, only the countably many values `j ≤ i` of the stopping time contribute.
    have : stoppedValue u τ ⁻¹' t ∩ {ω | τ ω ≤ i} =
        ⋃ j : ι, ⋃ (_ : j ≤ i), {ω | τ ω = j} ∩ u j ⁻¹' t := by
      ext ω
      simp only [stoppedValue, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
        Set.mem_iUnion, exists_prop]
      cases h : τ ω with
      | top => simp
      | coe k => simp [and_comm]
    rw [this]
    exact .iUnion fun j => .iUnion fun hj =>
      (f.mono hj _ (hτ.measurableSet_eq_of_countable j)).inter (f.mono hj _ (hu j ht))

end CountableTime

/-- An adapted process evaluated at a countable-range stopping time is strongly measurable for the
stopping sigma algebra. Neither path regularity nor a topology on time is required, and the time
may take the value `⊤`, where the stopped value is the process at the junk index
`(⊤ : WithTop ι).untopA`. The countability assumption is on the range of the time, not on all
times. -/
theorem StronglyAdapted.stronglyMeasurable_stoppedValue_of_countable_range
    {E : Type*} [TopologicalSpace E] [PartialOrder ι]
    {ℱ : Filtration ι m} {X : ι → Ω → E} (hX : StronglyAdapted ℱ X)
    (hτ : IsStoppingTime ℱ τ) (hc : (Set.range τ).Countable) :
    StronglyMeasurable[hτ.measurableSpace] (stoppedValue X τ) := by
  classical
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω₀⟩⟩
  · exact .of_subsingleton_dom
  -- the gluing below uses indicator functions; any value of the process serves as their zero
  let : Zero E := ⟨X (Classical.arbitrary ι) ω₀⟩
  have := hc.to_subtype
  let s : Set.range τ → Set Ω := fun v ↦ {ω | τ ω = v.val}
  let hs := stoppedValuePartition τ
  have htop := hτ.measurableSet_stopping_eq_of_countable_range hc ⊤
  have hind (v : Set.range τ) :
      StronglyMeasurable[hτ.measurableSpace] ((s v).indicator (X v.val.untopA)) := by
    obtain ⟨v, hv⟩ := v
    induction v using WithTop.recTopCoe with
    | top =>
      refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on
        (m := ⨆ i, ℱ i) (hτ.measurableSpace_le' _ htop) (fun t ht ↦ ⟨ht, fun i ↦ ?_⟩)
        (((hX _).mono (le_iSup ℱ _)).indicator (hτ.measurableSpace_le' _ htop))
        (fun ω hω ↦ Set.indicator_of_notMem hω _)
      have : {ω | τ ω = ⊤} ∩ t ∩ {ω | τ ω ≤ i} = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨h, -⟩, h'⟩
        simp [h] at h'
      rw [this]
      exact @MeasurableSet.empty _ (ℱ i)
    | coe i =>
      have hslice : MeasurableSet[ℱ i] (s ⟨i, hv⟩) := hτ.measurableSet_eq_of_countable_range hc i
      refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hslice
        (fun t ht ↦ ?_) ((hX i).indicator hslice) (fun ω hω ↦ Set.indicator_of_notMem hω _)
      rw [Set.inter_comm, hτ.measurableSet_inter_eq_iff, Set.inter_comm]
      exact ht
  have hm (v : Set.range τ) : MeasurableSet[hτ.measurableSpace] (s v) :=
    hτ.measurableSet_stopping_eq_of_countable_range hc v.val
  let : MeasurableSpace Ω := hτ.measurableSpace
  convert hs.stronglyMeasurable_piecewise hm hind using 1
  ext ω
  rw [IndexedPartition.piecewise_apply, Set.indicator_of_mem (hs.mem_index ω)]
  exact stoppedValue_eq_partition ω

/-- Stopping a strongly adapted process at a countable-range stopping time preserves literal
strong adaptation on a raw filtration, with no path regularity or finiteness assumption on
the stopping time. Each deterministic horizon caps the time at a finite value. -/
theorem StronglyAdapted.stoppedProcess_of_countable_range
    {E : Type*} [TopologicalSpace E] [LinearOrder ι]
    {ℱ : Filtration ι m} {X : ι → Ω → E} (hX : StronglyAdapted ℱ X)
    (hτ : IsStoppingTime ℱ τ) (hc : (Set.range τ).Countable) :
    StronglyAdapted ℱ (MeasureTheory.stoppedProcess X τ) := by
  rw [stoppedProcess_eq_stoppedValue]
  intro t
  have hct := ((Set.countable_singleton (t : WithTop ι)).mono Set.range_const_subset).range_min hc
  exact (hX.stronglyMeasurable_stoppedValue_of_countable_range
    ((isStoppingTime_const ℱ t).min hτ) hct).mono
      (((isStoppingTime_const ℱ t).min hτ).measurableSpace_le_of_le_const
        (fun _ ↦ min_le_left _ _))

/-- Evaluating an everywhere-continuous, coordinatewise strongly measurable process at a measurable
random time yields a strongly measurable random variable. -/
theorem stronglyMeasurable_stoppedValue_of_continuous {ι Ω E : Type*}
    [LinearOrder ι] [Nonempty ι] [TopologicalSpace ι] [OrderTopology ι]
    [TopologicalSpace.MetrizableSpace ι] [SecondCountableTopology ι]
    [MeasurableSpace ι] [BorelSpace ι] [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] {_ : MeasurableSpace Ω}
    {X : ι → Ω → E} {τ : Ω → WithTop ι}
    (hX : ∀ t, StronglyMeasurable (X t)) (hc : ∀ ω, Continuous (X · ω)) (hτ : Measurable τ) :
    StronglyMeasurable (stoppedValue X τ) :=
  (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hc hX).comp_measurable
    (hτ.untopA.prodMk measurable_id)

end MeasureTheory
