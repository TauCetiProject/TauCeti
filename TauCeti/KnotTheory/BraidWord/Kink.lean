/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode
public import TauCeti.KnotTheory.PDCode.Kauffman
import Mathlib.Tactic.FinCases

/-!
# The closure of a single crossing is a kink

The closure of the one-letter braid word `σ 0 ^ ε` on two strands is the one-crossing diagram of
the unknot, `TauCeti.PDCode.kink` for `ε = 1` and its mirror image for `ε = -1`. This checks the
slot, arc and over-strand conventions of `TauCeti.BraidWord.closure` against the kink used by the
first Reidemeister move, and shows that these closures are knots.

## Main results

* `TauCeti.BraidWord.toPDCode_closure_sigma_zero`: the closure of `σ 0` is the kink.
* `TauCeti.BraidWord.toPDCode_closure_sigma_zero_inv`: the closure of `σ 0⁻¹` is the mirror kink.
* `TauCeti.BraidWord.componentCount_closure_sigma_zero`: the closure of `σ 0 ^ ε` has one
  component.
-/

public section

namespace TauCeti

namespace BraidWord

open BraidGroup PDCode

/-- The arcs of the closure of a one-letter word on two strands are those of the kink. -/
private theorem edgePair_closure_single (ε : ℤˣ) :
    (closure ([(0, ε)] : BraidWord 2)).edgePair = kink.edgePair := by
  let w : BraidWord 2 := [(0, ε)]
  have : Subsingleton (Fin w.length) := inferInstanceAs (Subsingleton (Fin 1))
  have hnext (p : Fin 2) (j : Fin w.length) : w.nextCrossing p j = j := Subsingleton.elim _ _
  -- The arcs leaving the crossing upwards on its two positions.
  have hsucc := w.edgePair_closure_outgoingSlot (w.mem_crossingsAt_strandSucc 0)
  have hlow := w.edgePair_closure_outgoingSlot (w.mem_crossingsAt_strand 0)
  simp only [crossing_closure, outgoingSlot_strandSucc, outgoingSlot_strand, hnext,
    incomingSlot_strandSucc, incomingSlot_strand] at hsucc hlow
  apply Subtype.ext
  refine Equiv.ext fun h ↦ ?_
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv 1).surjective h
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rw [kink_edgePair_apply, slotSmoothing_true]
  fin_cases slot <;> simp +decide only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  · exact PerfectMatching.apply_eq_of_apply_eq _ hsucc
  · exact hsucc
  · exact hlow
  · exact PerfectMatching.apply_eq_of_apply_eq _ hlow

/-- Both strand positions of a one-letter word on two strands are involved in its crossing. -/
private theorem crossingsAt_single_ne_nil (ε : ℤˣ) (p : Fin 2) :
    crossingsAt ([(0, ε)] : BraidWord 2) p ≠ [] := by
  rw [Ne, crossingsAt_eq_nil_iff]
  intro h
  have := h 0
  fin_cases p <;> simp [Fin.ext_iff] at this

/-- The closure of the positive crossing `σ 0` on two strands is the kink. -/
theorem toPDCode_closure_sigma_zero : (closure ([(0, 1)] : BraidWord 2)).toPDCode = kink := by
  apply PDCode.ext
  · simp
  · exact edgePair_closure_single 1
  · rw [crossinglessComponentCount_closure, kink_crossinglessComponentCount, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    exact fun p _ ↦ crossingsAt_single_ne_nil 1 p
  · funext i
    simp

/-- The closure of the negative crossing `σ 0⁻¹` on two strands is the mirror image of the
kink. -/
theorem toPDCode_closure_sigma_zero_inv :
    (closure ([(0, -1)] : BraidWord 2)).toPDCode = kink.mirror := by
  apply PDCode.ext
  · simp
  · rw [mirror_edgePair]
    exact edgePair_closure_single (-1)
  · rw [crossinglessComponentCount_closure, mirror_crossinglessComponentCount,
      kink_crossinglessComponentCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun p _ ↦ crossingsAt_single_ne_nil (-1) p
  · funext i
    simp

/-- The closure of a single crossing on two strands is a knot. -/
theorem componentCount_closure_sigma_zero (ε : ℤˣ) :
    (closure ([(0, ε)] : BraidWord 2)).componentCount = 1 := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · rw [toPDCode_closure_sigma_zero, componentCount_eq, crossingComponentCount_kink,
      kink_crossinglessComponentCount]
  · rw [toPDCode_closure_sigma_zero_inv, componentCount_mirror, componentCount_eq,
      crossingComponentCount_kink, kink_crossinglessComponentCount]

end BraidWord

end TauCeti
