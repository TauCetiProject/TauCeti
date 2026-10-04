/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode
public import TauCeti.Data.List.Rotate
-- Transporting crossings and slots along the rotation unfolds their unexposed bodies.
import all TauCeti.KnotTheory.BraidWord.PDCode

/-!
# Cyclic rotation of braid-word closures

Cyclically rotating a braid word cuts its closed braid between two different levels. The closure
diagram therefore does not change: only its crossing and half-edge names do. This file describes
that renaming explicitly and proves equality of the resulting oriented PD-codes.

For a word `w` and a rotation distance `k`, `List.rotateIndexEquiv w k` sends an index in
`w.rotate k` to the index of the same letter in `w`. Its inverse renames the old crossings, and
the induced crossing-block equivalence renames their four half-edges. The main theorem proves
that these renamings account for the entire closure construction, including arcs which cross the
cut.

Taking `w = u ++ v` and `k = u.length` specializes the theorem to the familiar equality of the
closures of `u ++ v` and `v ++ u`. This is the diagram-level content of cyclic conjugation, the
word-level generator needed for the conjugation part of Markov equivalence.

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

private theorem crossingsAt_rotate_isRotated (w : BraidWord n) (k : ℕ) (p : Fin n) :
    (crossingsAt (w.rotate k) p).map (w.rotateIndexEquiv k) ~r w.crossingsAt p := by
  have hfin :
      (List.finRange (w.rotate k).length).map (w.rotateIndexEquiv k) ~r
        List.finRange w.length := by
    rw [List.map_finRange_rotateIndexEquiv]
    exact List.IsRotated.forall _ _
  have hfilter := hfin.filter
    (fun j : Fin w.length => p = BraidGroup.strand w[j.1].1 ∨
      p = BraidGroup.strandSucc w[j.1].1)
  rw [List.filter_map] at hfilter
  rw [crossingsAt, crossingsAt]
  simpa only [Function.comp_def, List.getElem_rotateIndexEquiv] using hfilter

private theorem nextCrossing_rotate (w : BraidWord n) (k : ℕ) (p : Fin n) :
    (w.rotateIndexEquiv k).permCongr (nextCrossing (w.rotate k) p) =
      w.nextCrossing p := by
  rw [nextCrossing_def, nextCrossing_def]
  calc
    (w.rotateIndexEquiv k).permCongr
        (crossingsAt (w.rotate k) p).formPerm =
        ((crossingsAt (w.rotate k) p).map (w.rotateIndexEquiv k)).formPerm :=
      ((crossingsAt (w.rotate k) p).formPerm_map_equiv (w.rotateIndexEquiv k)).symm
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
  rw [incomingSlot, incomingSlot, List.getElem_rotateIndexEquiv]

/-- The outgoing slot at a rotated crossing is the outgoing slot at its original name. -/
@[simp]
theorem outgoingSlot_rotateIndexEquiv (w : BraidWord n) (k : ℕ)
    (j : Fin (w.rotate k).length) (p : Fin n) :
    outgoingSlot (w.rotate k) j p = w.outgoingSlot (w.rotateIndexEquiv k j) p := by
  rw [outgoingSlot, outgoingSlot, List.getElem_rotateIndexEquiv]

private theorem crossingsAt_rotate_eq_nil_iff (w : BraidWord n) (k : ℕ) (p : Fin n) :
    crossingsAt (w.rotate k) p = [] ↔ w.crossingsAt p = [] := by
  have h := crossingsAt_rotate_isRotated w k p
  rw [← List.map_eq_nil_iff (f := w.rotateIndexEquiv k)]
  constructor
  · intro h0
    rw [h0, List.isRotated_nil_iff'] at h
    exact h.symm
  · intro h0
    rwa [h0, List.isRotated_nil_iff] at h

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
      List.getElem_rotateIndexEquiv, crossingBlockEquiv_apply_crossingSlotEquiv,
      nextCrossing_rotate_eq_symm_apply, nextCrossing_rotate_symm_eq_symm_apply,
      incomingSlot_rotateIndexEquiv, outgoingSlot_rotateIndexEquiv, Equiv.apply_symm_apply]

/-- Rotating a braid word changes its oriented closure PD-code only by renaming crossings and
half-edges. The inverse of `rotateIndexEquiv` sends each old crossing name to its name in the
rotated word, and `PDCode.crossingBlockEquiv` applies the same renaming to all four crossing
slots. -/
theorem closure_rotate (w : BraidWord n) (k : ℕ) :
    closure (w.rotate k) =
      w.closure.relabel
        (PDCode.crossingBlockEquiv (w.rotateIndexEquiv k).symm)
        (w.rotateIndexEquiv k).symm := by
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · rw [halfEdge_closure, OrientedPDCode.relabel_toPDCode, PDCode.relabel_halfEdge,
        halfEdge_closure]
      ext h
      simp [Equiv.Perm.one_def, ← crossingBlockEquiv_symm]
    · apply Subtype.ext
      refine Equiv.ext fun h ↦ ?_
      obtain ⟨⟨j, slot⟩, rfl⟩ :=
        (crossingSlotEquiv (w.rotate k).length).surjective h
      rw [edgePair_closure_rotate_crossingSlotEquiv]
      simp only [OrientedPDCode.relabel_toPDCode, PDCode.relabel_edgePair,
        PerfectMatching.congr_val_apply, crossingBlockEquiv_symm,
        crossingBlockEquiv_apply_crossingSlotEquiv, Equiv.symm_symm]
    · simp only [crossinglessComponentCount_closure, OrientedPDCode.relabel_toPDCode,
        PDCode.relabel_crossinglessComponentCount]
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact crossingsAt_rotate_eq_nil_iff w k p
    · funext j
      rw [overPair_closure, List.getElem_rotateIndexEquiv]
      simp only [OrientedPDCode.relabel_toPDCode, PDCode.relabel_overPair,
        Equiv.symm_symm]
      exact (overPair_closure w (w.rotateIndexEquiv k j)).symm
  · funext h
    obtain ⟨⟨j, slot⟩, rfl⟩ :=
      (crossingSlotEquiv (w.rotate k).length).surjective h
    rw [orientation_closure]
    simp only [OrientedPDCode.relabel_orientation,
      crossingBlockEquiv_symm, crossingBlockEquiv_apply_crossingSlotEquiv, Equiv.symm_symm,
      orientation_closure]
  · rw [crossinglessComponents_closure, OrientedPDCode.relabel_crossinglessComponents,
      crossinglessComponents_closure]
    congr 2
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact crossingsAt_rotate_eq_nil_iff w k p

end BraidWord

end TauCeti
