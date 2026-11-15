/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode
public import TauCeti.Data.List.Rotate

/-!
# Closures of braid words with the same crossings along every strand

The closure of a braid word is determined by its letters together with, for each strand
position, the cyclic order in which a strand running along that position meets the crossings
involving it. Two words with the same letters, listed in different orders, therefore have the same
closure up to renaming crossings and half-edges, as soon as along every strand position the
crossings of one word are met in the same cyclic order as the corresponding crossings of the
other.

This is the common source of the word-level moves that keep the closure diagram: cyclically
rotating a word (`TauCeti.BraidWord.closure_rotate`) and exchanging two adjacent letters on
disjoint strands (`TauCeti.BraidWord.closure_append_cons_cons_comm`).

## Main results

* `TauCeti.BraidWord.closure_eq_relabel_of_isRotated`: if a renaming of crossings matches the
  letters of two words and carries the crossings of one word along each strand position to a
  cyclic rotation of those of the other, the two closures differ by that renaming.
-/

public section

namespace TauCeti

namespace BraidWord

open BraidGroup PDCode

variable {n : ℕ} {w w' : BraidWord n}

variable (e : Fin w'.length ≃ Fin w.length) {p : Fin n}

/-- If a renaming carries the crossings of `w'` along a strand position to a cyclic rotation of
those of `w`, it intertwines the two successor permutations along that position. -/
private theorem apply_nextCrossing_of_isRotated
    (hrot : (w'.crossingsAt p).map e ~r w.crossingsAt p) (j : Fin w'.length) :
    e (w'.nextCrossing p j) = w.nextCrossing p (e j) := by
  have h : e.permCongr (w'.nextCrossing p) = w.nextCrossing p := by
    rw [nextCrossing_def, nextCrossing_def, ← List.formPerm_map_equiv]
    exact List.formPerm_eq_of_isRotated
      ((w'.sortedLT_crossingsAt p).nodup.map e.injective) hrot
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using
    Equiv.congr_fun h (e j)

private theorem nextCrossing_eq_symm_apply_of_isRotated
    (hrot : (w'.crossingsAt p).map e ~r w.crossingsAt p) (j : Fin w'.length) :
    w'.nextCrossing p j = e.symm (w.nextCrossing p (e j)) := by
  rw [← apply_nextCrossing_of_isRotated e hrot, Equiv.symm_apply_apply]

private theorem nextCrossing_symm_eq_symm_apply_of_isRotated
    (hrot : (w'.crossingsAt p).map e ~r w.crossingsAt p) (j : Fin w'.length) :
    (w'.nextCrossing p).symm j = e.symm ((w.nextCrossing p).symm (e j)) := by
  apply (w'.nextCrossing p).injective
  rw [Equiv.apply_symm_apply, nextCrossing_eq_symm_apply_of_isRotated e hrot,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

private theorem crossingsAt_eq_nil_iff_of_isRotated
    (hrot : (w'.crossingsAt p).map e ~r w.crossingsAt p) :
    w'.crossingsAt p = [] ↔ w.crossingsAt p = [] := by
  rw [← List.map_eq_nil_iff (f := e)]
  constructor
  · intro h0
    rw [h0, List.isRotated_nil_iff'] at hrot
    exact hrot.symm
  · intro h0
    rwa [h0, List.isRotated_nil_iff] at hrot

/-- The closure arc at a slot of a crossing of `w'` is the renamed closure arc of `w` at the same
slot of the corresponding crossing. -/
private theorem edgePair_closure_crossingSlotEquiv_of_isRotated
    (he : ∀ j : Fin w'.length, w'[j.1] = w[(e j).1])
    (hrot : ∀ p, (w'.crossingsAt p).map e ~r w.crossingsAt p) (j : Fin w'.length)
    (slot : Fin 4) :
    w'.closure.edgePair.val (crossingSlotEquiv w'.length (j, slot)) =
      crossingBlockEquiv e.symm
        (w.closure.edgePair.val (crossingSlotEquiv w.length (e j, slot))) := by
  have hin (j : Fin w'.length) := incomingSlot_congr (he j)
  have hout (j : Fin w'.length) := outgoingSlot_congr (he j)
  obtain rfl | rfl | rfl | rfl : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  all_goals
    simp only [edgePair_closure_crossingSlotEquiv_zero, edgePair_closure_crossingSlotEquiv_one,
      edgePair_closure_crossingSlotEquiv_two, edgePair_closure_crossingSlotEquiv_three, he,
      crossingBlockEquiv_apply_crossingSlotEquiv, hin, hout, Equiv.apply_symm_apply,
      nextCrossing_eq_symm_apply_of_isRotated e (hrot _),
      nextCrossing_symm_eq_symm_apply_of_isRotated e (hrot _)]

/-- Two braid words have the same closure up to renaming, if a renaming `e` of their crossings
matches their letters and carries the crossings of `w'` along every strand position to a cyclic
rotation of the crossings of `w` along that position. The crossings are renamed by `e.symm`, and
`PDCode.crossingBlockEquiv` applies the same renaming to all four slots of each crossing. -/
theorem closure_eq_relabel_of_isRotated (he : ∀ j : Fin w'.length, w'[j.1] = w[(e j).1])
    (hrot : ∀ p, (w'.crossingsAt p).map e ~r w.crossingsAt p) :
    w'.closure = w.closure.relabel (crossingBlockEquiv e.symm) e.symm := by
  have hnil (p : Fin n) := crossingsAt_eq_nil_iff_of_isRotated e (hrot p)
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · rw [halfEdge_closure, OrientedPDCode.relabel_toPDCode, PDCode.relabel_halfEdge,
        halfEdge_closure]
      ext h
      simp [Equiv.Perm.one_def, ← crossingBlockEquiv_symm]
    · apply Subtype.ext
      refine Equiv.ext fun h ↦ ?_
      obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv w'.length).surjective h
      rw [edgePair_closure_crossingSlotEquiv_of_isRotated e he hrot]
      simp only [OrientedPDCode.relabel_toPDCode, PDCode.relabel_edgePair,
        PerfectMatching.congr_val_apply, crossingBlockEquiv_symm,
        crossingBlockEquiv_apply_crossingSlotEquiv, Equiv.symm_symm]
    · simp only [crossinglessComponentCount_closure, OrientedPDCode.relabel_toPDCode,
        PDCode.relabel_crossinglessComponentCount, hnil]
    · funext j
      simp only [overPair_closure, he, OrientedPDCode.relabel_toPDCode, PDCode.relabel_overPair,
        Equiv.symm_symm]
  · funext h
    obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv w'.length).surjective h
    simp only [orientation_closure, OrientedPDCode.relabel_orientation, crossingBlockEquiv_symm,
      crossingBlockEquiv_apply_crossingSlotEquiv, Equiv.symm_symm]
  · simp only [crossinglessComponents_closure, OrientedPDCode.relabel_crossinglessComponents, hnil]

end BraidWord

end TauCeti
