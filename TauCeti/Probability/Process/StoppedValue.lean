/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping

/-!
# Measurability of stopped values in countable time

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
-/

public section

open Filter

namespace MeasureTheory

variable {Ω ι β : Type*} [Nonempty ι] {m : MeasurableSpace Ω} {u : ι → Ω → β}
  {τ : Ω → WithTop ι}

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

variable [MeasurableSpace β]

/-- In countable time, a stopped value of a measurable process at a measurable random time is
measurable. -/
theorem measurable_stoppedValue_of_countable [Countable ι] [MeasurableSpace (WithTop ι)]
    [MeasurableSingletonClass (WithTop ι)] (hu : ∀ i, Measurable (u i)) (hτ : Measurable τ) :
    Measurable (stoppedValue u τ) := by
  intro t ht
  rw [stoppedValue_preimage_eq]
  refine .union (.iUnion fun i => ?_) ?_
  · exact (hτ (measurableSet_singleton _)).inter (hu i ht)
  · exact (hτ (measurableSet_singleton _)).inter (hu _ ht)

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

end MeasureTheory
