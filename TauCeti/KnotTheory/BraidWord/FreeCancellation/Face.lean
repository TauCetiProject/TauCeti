/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.FreeCancellation.Clasp
import TauCeti.KnotTheory.BraidWord.Cyclic

/-!
# The face condition for cancellation in closed braids

Adjacent closing arcs of a braid border a common face on the sides used by clasp insertion,
or belong to different components of the underlying crossing graph. Thus an inverse pair
on two positions already meeting crossings gives a genuine Reidemeister-II move, rather
than merely an algebraic identification with a clasp.

The closing-arc locality results are supplied by `BraidWord/ClosingArcs.lean`.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup PDCode

variable {n : ℕ} (w : BraidWord n)

/-- Prepending an inverse pair on two positions already meeting crossings gives
Reidemeister-equivalent oriented closures. No face or planarity assumption is needed. -/
theorem reidemeisterEquiv_closure_cons_cons_freeCancel
    (i : Fin (n - 1)) (ε : ℤˣ)
    (hp : w.crossingsAt (strand i) ≠ []) (hq : w.crossingsAt (strandSucc i) ≠ []) :
    OrientedPDCode.ReidemeisterEquiv (closure ((i, ε) :: (i, -ε) :: w)) w.closure := by
  exact (reidemeisterEquiv_closure_cons_cons_freeCancel_insertClasp w i ε hp hq).trans
    (OrientedPDCode.reidemeisterEquiv_insertClasp w.closure
      (w.closingHalfEdge (strand i) hp) (w.closingHalfEdge (strandSucc i) hq)
      (!decide (ε = 1)) (w.closingHalfEdge_ne hq hp (strand_ne_strandSucc i).symm)
      (w.closingHalfEdge_ne_edgePair_closingHalfEdge _ _ hp hq)
      (w.closingHalfEdge_clasp_face_condition i hp hq)).symm

/-- Inserting an inverse pair anywhere in a braid word gives Reidemeister-equivalent
closures when both positions already meet crossings in the original word. -/
theorem reidemeisterEquiv_closure_append_cons_cons_freeCancel
    (u v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)
    (hp : (u ++ v).crossingsAt (strand i) ≠ [])
    (hq : (u ++ v).crossingsAt (strandSucc i) ≠ []) :
    OrientedPDCode.ReidemeisterEquiv (closure (u ++ (i, ε) :: (i, -ε) :: v))
      (closure (u ++ v)) := by
  have hp' : (v ++ u).crossingsAt (strand i) ≠ [] := by
    simpa only [ne_eq, crossingsAt_append_eq_nil_iff, and_comm] using hp
  have hq' : (v ++ u).crossingsAt (strandSucc i) ≠ [] := by
    simpa only [ne_eq, crossingsAt_append_eq_nil_iff, and_comm] using hq
  have hrot := reidemeisterEquiv_closure_rotate (u ++ (i, ε) :: (i, -ε) :: v) u.length
  rw [List.rotate_append_length_eq] at hrot
  have hrot' := reidemeisterEquiv_closure_rotate (u ++ v) u.length
  rw [List.rotate_append_length_eq] at hrot'
  have hcancel : OrientedPDCode.ReidemeisterEquiv
      (closure (((i, ε) :: (i, -ε) :: v) ++ u)) (closure (v ++ u)) := by
    simpa only [List.cons_append] using
      reidemeisterEquiv_closure_cons_cons_freeCancel (v ++ u) i ε hp' hq'
  exact hrot.trans (hcancel.trans hrot'.symm)

end TauCeti.BraidWord
