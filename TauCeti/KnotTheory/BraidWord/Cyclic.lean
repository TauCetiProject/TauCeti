/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode
public import TauCeti.KnotTheory.PDCode.Renaming
import TauCeti.Data.Fin.Basic

/-!
# Cyclic rotation of braid-word closures

Cyclically rotating a braid word cuts its closed braid between two different levels. The closure
diagram therefore does not change: only its crossing and half-edge names do. This file describes
that renaming explicitly and proves equality of the resulting oriented PD-codes.

For a word `w` and a rotation distance `k`, `rotateIndexEquiv w k` sends an index in `w.rotate k`
to the index of the same letter in `w`. Its inverse renames the old crossings, and the induced
crossing-block equivalence renames their four half-edges. The main theorem proves that these
renamings account for the entire closure construction, including arcs which cross the cut.

Taking `w = u ++ v` and `k = u.length` specializes the theorem to the familiar equality of the
closures of `u ++ v` and `v ++ u`. This is the diagram-level content of cyclic conjugation, the
word-level generator needed for the conjugation part of Markov equivalence.

## Main definitions

* `TauCeti.BraidWord.rotateIndexEquiv`: identify the letters before and after rotating a word.

## Main results

* `TauCeti.BraidWord.closure_rotate`: rotating a braid word changes its closure only by the
  explicit induced renaming.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Proposition
  16.10.
-/

public section

namespace TauCeti

namespace BraidWord

open PDCode

private theorem formPerm_map_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (l : List α) (hl : l.Nodup) :
    (l.map e).formPerm = e.permCongr l.formPerm := by
  ext x
  by_cases hx : x ∈ l.map e
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_map] at hi
    rw [List.formPerm_apply_getElem _ (hl.map e.injective), List.getElem_map,
      Equiv.permCongr_apply]
    simp only [List.getElem_map, Equiv.symm_apply_apply, List.length_map]
    rw [List.formPerm_apply_getElem _ hl]
  · rw [List.formPerm_apply_of_notMem hx, Equiv.permCongr_apply,
      List.formPerm_apply_of_notMem]
    · exact (e.apply_symm_apply x).symm
    · intro hmem
      apply hx
      exact List.mem_map.2 ⟨e.symm x, hmem, e.apply_symm_apply x⟩

private theorem isRotated_filter {α : Type*}
    {l l' : List α} (h : l ~r l') (p : α → Bool) :
    l.filter p ~r l'.filter p := by
  obtain ⟨k, rfl⟩ := h
  rw [List.rotate_eq_drop_append_take_mod, List.filter_append]
  have hrot := List.isRotated_append
    (l := (l.take (k % l.length)).filter p)
    (l' := (l.drop (k % l.length)).filter p)
  simpa only [← List.filter_append, List.take_append_drop] using hrot

/-- The equivalence which sends the index of a letter in `w.rotate k` to its original index in
`w`. It is the cast along preservation of length followed by addition of `k` modulo the word
length. -/
def rotateIndexEquiv (w : BraidWord n) (k : ℕ) :
    Fin (w.rotate k).length ≃ Fin w.length :=
  (finCongr (List.length_rotate w k)).trans (finRotate w.length ^ k)

/-- Looking up a letter after rotation and translating its index gives the same letter in the
original word. -/
theorem getElem_rotateIndexEquiv (w : BraidWord n) (k : ℕ)
    (j : Fin (w.rotate k).length) :
    (w.rotate k)[j.1] = w[(w.rotateIndexEquiv k j).1] := by
  rw [List.getElem_rotate]
  congr 1
  simp [rotateIndexEquiv, Fin.coe_finRotate_pow]

private theorem map_finRange_rotateIndexEquiv (w : BraidWord n) (k : ℕ) :
    (List.finRange (w.rotate k).length).map (w.rotateIndexEquiv k) =
      (List.finRange w.length).rotate k := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.length_map, List.length_finRange] at hi
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_rotate]
    apply Fin.ext
    simp [rotateIndexEquiv, Fin.coe_finRotate_pow]

private theorem crossingsAt_rotate_isRotated (w : BraidWord n) (k : ℕ) (p : Fin n) :
    (crossingsAt (w.rotate k) p).map (w.rotateIndexEquiv k) ~r w.crossingsAt p := by
  have hfin :
      (List.finRange (w.rotate k).length).map (w.rotateIndexEquiv k) ~r
        List.finRange w.length := by
    rw [map_finRange_rotateIndexEquiv]
    exact List.IsRotated.forall _ _
  have hfilter := isRotated_filter hfin
    (fun j : Fin w.length => p = BraidGroup.strand w[j.1].1 ∨
      p = BraidGroup.strandSucc w[j.1].1)
  rw [List.filter_map] at hfilter
  rw [crossingsAt_def, crossingsAt_def]
  simpa only [Function.comp_def, getElem_rotateIndexEquiv] using hfilter

private theorem nextCrossing_rotate (w : BraidWord n) (k : ℕ) (p : Fin n) :
    (w.rotateIndexEquiv k).permCongr (nextCrossing (w.rotate k) p) =
      w.nextCrossing p := by
  rw [nextCrossing_def, nextCrossing_def]
  calc
    (w.rotateIndexEquiv k).permCongr
        (crossingsAt (w.rotate k) p).formPerm =
        ((crossingsAt (w.rotate k) p).map (w.rotateIndexEquiv k)).formPerm :=
      (formPerm_map_equiv _ _ ((sortedLT_crossingsAt (w.rotate k) p).nodup)).symm
    _ = (w.crossingsAt p).formPerm :=
      List.formPerm_eq_of_isRotated
        (((sortedLT_crossingsAt (w.rotate k) p).nodup).map
          (w.rotateIndexEquiv k).injective)
        (crossingsAt_rotate_isRotated w k p)

private theorem nextCrossing_rotate_apply (w : BraidWord n) (k : ℕ) (p : Fin n)
    (j : Fin (w.rotate k).length) :
    w.rotateIndexEquiv k (nextCrossing (w.rotate k) p j) =
      w.nextCrossing p (w.rotateIndexEquiv k j) := by
  have h := Equiv.congr_fun (nextCrossing_rotate w k p) (w.rotateIndexEquiv k j)
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using h

private theorem nextCrossing_rotate_symm_apply (w : BraidWord n) (k : ℕ) (p : Fin n)
    (j : Fin (w.rotate k).length) :
    w.rotateIndexEquiv k ((nextCrossing (w.rotate k) p).symm j) =
      (w.nextCrossing p).symm (w.rotateIndexEquiv k j) := by
  apply (w.nextCrossing p).injective
  rw [Equiv.apply_symm_apply, ← nextCrossing_rotate_apply, Equiv.apply_symm_apply]

private theorem nextCrossing_rotate_eq_symm_apply (w : BraidWord n) (k : ℕ) (p : Fin n)
    (j : Fin (w.rotate k).length) :
    nextCrossing (w.rotate k) p j =
      (w.rotateIndexEquiv k).symm (w.nextCrossing p (w.rotateIndexEquiv k j)) := by
  apply (w.rotateIndexEquiv k).injective
  simp only [nextCrossing_rotate_apply, Equiv.apply_symm_apply]

private theorem nextCrossing_rotate_symm_eq_symm_apply (w : BraidWord n) (k : ℕ)
    (p : Fin n) (j : Fin (w.rotate k).length) :
    (nextCrossing (w.rotate k) p).symm j =
      (w.rotateIndexEquiv k).symm ((w.nextCrossing p).symm (w.rotateIndexEquiv k j)) := by
  apply (w.rotateIndexEquiv k).injective
  simp only [nextCrossing_rotate_symm_apply, Equiv.apply_symm_apply]

/-- The incoming slot at a rotated crossing is the incoming slot at its original name. -/
@[simp]
theorem incomingSlot_rotateIndexEquiv (w : BraidWord n) (k : ℕ)
    (j : Fin (w.rotate k).length) (p : Fin n) :
    incomingSlot (w.rotate k) j p = w.incomingSlot (w.rotateIndexEquiv k j) p := by
  rw [incomingSlot_def, incomingSlot_def, getElem_rotateIndexEquiv]

/-- The outgoing slot at a rotated crossing is the outgoing slot at its original name. -/
@[simp]
theorem outgoingSlot_rotateIndexEquiv (w : BraidWord n) (k : ℕ)
    (j : Fin (w.rotate k).length) (p : Fin n) :
    outgoingSlot (w.rotate k) j p = w.outgoingSlot (w.rotateIndexEquiv k j) p := by
  rw [outgoingSlot_def, outgoingSlot_def, getElem_rotateIndexEquiv]

private theorem crossingsAt_rotate_eq_nil_iff (w : BraidWord n) (k : ℕ) (p : Fin n) :
    crossingsAt (w.rotate k) p = [] ↔ w.crossingsAt p = [] := by
  have hlen := (crossingsAt_rotate_isRotated w k p).perm.length_eq
  simp only [List.length_map] at hlen
  constructor
  · intro h
    apply List.length_eq_zero_iff.mp
    rw [← hlen]
    simp [h]
  · intro h
    apply List.length_eq_zero_iff.mp
    rw [hlen]
    simp [h]

/-- The closure arc at a slot of a rotated crossing is the renamed closure arc at the same slot
of the corresponding original crossing. -/
private theorem edgePair_closure_rotate_crossingSlotEquiv (w : BraidWord n) (k : ℕ)
    (j : Fin (w.rotate k).length) (slot : Fin 4) :
    (closure (w.rotate k)).edgePair.val (crossingSlotEquiv (w.rotate k).length (j, slot)) =
      crossingBlockEquiv (w.rotateIndexEquiv k).symm
        (w.closure.edgePair.val (crossingSlotEquiv w.length (w.rotateIndexEquiv k j, slot))) := by
  obtain rfl | rfl | rfl | rfl : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by omega
  all_goals
    simp only [edgePair_closure_crossingSlotEquiv_zero, edgePair_closure_crossingSlotEquiv_one,
      edgePair_closure_crossingSlotEquiv_two, edgePair_closure_crossingSlotEquiv_three,
      getElem_rotateIndexEquiv, crossingBlockEquiv_apply_crossingSlotEquiv,
      nextCrossing_rotate_eq_symm_apply, nextCrossing_rotate_symm_eq_symm_apply,
      incomingSlot_rotateIndexEquiv, outgoingSlot_rotateIndexEquiv, Equiv.apply_symm_apply]

/-- Rotating a braid word changes its oriented closure PD-code only by renaming crossings and
half-edges. The inverse of `rotateIndexEquiv` sends each old crossing name to its name in the
rotated word, and `PDCode.crossingBlockEquiv` applies the same renaming to all four crossing
slots. -/
theorem closure_rotate (w : BraidWord n) (k : ℕ) :
    closure (w.rotate k) =
      w.closure.rename
        (PDCode.crossingBlockEquiv (w.rotateIndexEquiv k).symm)
        (w.rotateIndexEquiv k).symm := by
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · rw [halfEdge_closure, OrientedPDCode.rename_toPDCode, PDCode.rename_halfEdge,
        halfEdge_closure]
      ext h
      simp [Equiv.Perm.one_def]
    · apply Subtype.ext
      refine Equiv.ext fun h ↦ ?_
      obtain ⟨⟨j, slot⟩, rfl⟩ :=
        (crossingSlotEquiv (w.rotate k).length).surjective h
      rw [edgePair_closure_rotate_crossingSlotEquiv]
      simp only [OrientedPDCode.rename_toPDCode, PDCode.rename_edgePair,
        PerfectMatching.congr_val_apply, crossingBlockEquiv_symm_apply_crossingSlotEquiv,
        Equiv.symm_symm]
    · simp only [crossinglessComponentCount_closure, OrientedPDCode.rename_toPDCode,
        PDCode.rename_crossinglessComponentCount]
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact crossingsAt_rotate_eq_nil_iff w k p
    · funext j
      rw [overPair_closure, getElem_rotateIndexEquiv]
      simp only [OrientedPDCode.rename_toPDCode, PDCode.rename_overPair_apply,
        Equiv.symm_symm]
      exact (overPair_closure w (w.rotateIndexEquiv k j)).symm
  · funext h
    obtain ⟨⟨j, slot⟩, rfl⟩ :=
      (crossingSlotEquiv (w.rotate k).length).surjective h
    rw [orientation_closure]
    simp only [OrientedPDCode.rename_orientation_apply,
      crossingBlockEquiv_symm_apply_crossingSlotEquiv, Equiv.symm_symm,
      orientation_closure]
  · rw [crossinglessComponents_closure, OrientedPDCode.rename_crossinglessComponents,
      crossinglessComponents_closure]
    congr 2
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact crossingsAt_rotate_eq_nil_iff w k p

end BraidWord

end TauCeti
