/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

/-!
# Pullbacks of decreasing σ-algebras

Pullback commutes with the intersection of a decreasing sequence of σ-algebras. This allows
tail σ-algebras on a state space to be pulled back to the sample space of a process, without
requiring the process map to be surjective or imposing any measurable structure on its domain.

An event in every pulled-back σ-algebra has a representative at every time. Their set limsup
is measurable for every original σ-algebra and has the same preimage as all the representatives.
-/

public section

open Filter MeasureTheory

namespace TauCeti.MeasureTheory

/-- Pullback commutes with a decreasing countable intersection of σ-algebras. No surjectivity
or measurability assumption on the map is needed. -/
theorem comap_iInf_of_antitone {α β : Type*} (f : α → β)
    {m : ℕ → MeasurableSpace β} (hm : Antitone m) :
    MeasurableSpace.comap f (⨅ n, m n) = ⨅ n, MeasurableSpace.comap f (m n) := by
  classical
  apply le_antisymm
  · exact le_iInf fun n => MeasurableSpace.comap_mono (iInf_le m n)
  · intro s hs
    have hrep : ∀ n, ∃ t : Set β, MeasurableSet[m n] t ∧ f ⁻¹' t = s :=
      MeasurableSpace.measurableSet_iInf.1 hs
    choose t ht hpre using hrep
    refine ⟨limsup t atTop, MeasurableSpace.measurableSet_iInf.2 ?_, ?_⟩
    · intro n
      rw [← limsup_nat_add t n]
      exact @MeasurableSet.measurableSet_limsup β (m n) (fun k => t (k + n))
        (fun k => hm (Nat.le_add_left n k) _ (ht (k + n)))
    · ext x
      simp only [Set.mem_preimage, mem_limsup_iff_frequently_mem]
      have hmem : ∀ n, f x ∈ t n ↔ x ∈ s := fun n => by
        rw [← Set.mem_preimage, hpre n]
      simp only [hmem, frequently_const]

end TauCeti.MeasureTheory
