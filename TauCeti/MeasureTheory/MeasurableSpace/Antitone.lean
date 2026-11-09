/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Filter.AtTopBot.CompleteLattice

/-!
# Pullbacks of decreasing σ-algebras

Pullback commutes with the infimum of a decreasing family of σ-algebras indexed by a directed
order whose `atTop` filter is countably generated, such as `ℕ`. This allows tail σ-algebras on a
state space to be pulled back to the sample space of a process, without requiring the process map
to be surjective or imposing any measurable structure on its domain.

## Implementation notes

After passing to a cofinal monotone sequence of indices, an event in every pulled-back σ-algebra
has a representative at every time. Their set limsup is measurable for every original σ-algebra
and has the same preimage as all the representatives.
-/

public section

open Filter MeasureTheory

namespace TauCeti.MeasureTheory

/-- Pullback commutes with the infimum of a decreasing family of σ-algebras indexed by a directed
order with countably generated `atTop`, such as `ℕ`. No surjectivity or measurability
assumption on the map is needed. -/
theorem comap_iInf_of_antitone {α β ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    [(atTop : Filter ι).IsCountablyGenerated] (f : α → β)
    {m : ι → MeasurableSpace β} (hm : Antitone m) :
    MeasurableSpace.comap f (⨅ i, m i) = ⨅ i, MeasurableSpace.comap f (m i) := by
  obtain ⟨u, hu, hut⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  have hcomap : Antitone fun i => MeasurableSpace.comap f (m i) :=
    fun _ _ hij => MeasurableSpace.comap_mono (hm hij)
  rw [← hm.iInf_comp_tendsto_atTop hut, ← hcomap.iInf_comp_tendsto_atTop hut]
  refine le_antisymm (le_iInf fun n => MeasurableSpace.comap_mono (iInf_le _ n)) fun s hs => ?_
  choose t ht hpre using MeasurableSpace.measurableSet_iInf.1 hs
  refine ⟨limsup t atTop, MeasurableSpace.measurableSet_iInf.2 fun n => ?_, ?_⟩
  · rw [← limsup_nat_add t n]
    exact @MeasurableSet.measurableSet_limsup β (m (u n)) _
      fun k => hm (hu (Nat.le_add_left n k)) _ (ht (k + n))
  · ext x
    have hmem (n : ℕ) : f x ∈ t n ↔ x ∈ s := by rw [← hpre n, Set.mem_preimage]
    simp [mem_limsup_iff_frequently_mem, hmem]

end TauCeti.MeasureTheory
