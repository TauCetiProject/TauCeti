/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode

/-!
# Closing arcs of braid closures

For every strand position which meets a crossing, the closing arc of a braid closure runs from
the outgoing half-edge at the last crossing on that position to the incoming half-edge at its
first crossing. This file names the outgoing endpoint and records its partner.

Closing endpoints on different positions are distinct. Moreover, no closing endpoint is paired
with any closing endpoint, since all of them point out of their crossings while their partners
point in. These are precisely the disjointness conditions needed to cut two closing arcs and
insert a Reidemeister-II clasp. In particular, they supply the legality hypotheses for identifying
the closure of a braid word with an inserted inverse pair with `PDCode.insertClasp`.

## Main definitions

* `TauCeti.BraidWord.closingHalfEdge`: the outgoing endpoint of the closing arc at a strand
  position.

## Main results

* `TauCeti.BraidWord.edgePair_closingHalfEdge`: the other endpoint is the incoming half-edge at
  the first crossing on the position.
* `TauCeti.BraidWord.closingHalfEdge_ne`: different positions have different closing endpoints.
* `TauCeti.BraidWord.closingHalfEdge_ne_edgePair_closingHalfEdge`: closing endpoints are never
  paired with one another.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
-/

public section

namespace TauCeti.BraidWord

open PDCode

variable {n : ℕ}

/-- The outgoing endpoint of the closing arc on a strand position which meets at least one
crossing: the outgoing half-edge at the last crossing on that position. -/
def closingHalfEdge (v : BraidWord n) (p : Fin n) (h : v.crossingsAt p ≠ []) :
    Fin (4 * v.length) :=
  v.closure.crossing ((v.crossingsAt p).getLast h)
    (v.outgoingSlot ((v.crossingsAt p).getLast h) p)

/-- The successor of the last crossing on a strand position is its first crossing, through the
closing arc. -/
@[simp]
theorem nextCrossing_getLast_crossingsAt (v : BraidWord n) (p : Fin n)
    (h : v.crossingsAt p ≠ []) :
    v.nextCrossing p ((v.crossingsAt p).getLast h) = (v.crossingsAt p).head h := by
  rw [nextCrossing_def]
  obtain ⟨j, js, heq⟩ := List.exists_cons_of_ne_nil h
  simp only [heq, List.formPerm_apply_getLast, List.head_cons]

/-- The closing half-edge points away from its last crossing. -/
@[simp]
theorem orientation_closingHalfEdge (v : BraidWord n) (p : Fin n)
    (h : v.crossingsAt p ≠ []) :
    v.closure.orientation (v.closingHalfEdge p h) = true := by
  rw [closingHalfEdge, crossing_closure, orientation_closure]
  rcases v.outgoingSlot_eq_one_or_two ((v.crossingsAt p).getLast h) p with hslot | hslot <;>
    simp [hslot]

/-- The closing arc on a strand position joins the outgoing half-edge at its last crossing to the
incoming half-edge at its first crossing. -/
@[simp]
theorem edgePair_closingHalfEdge (v : BraidWord n) (p : Fin n)
    (h : v.crossingsAt p ≠ []) :
    v.closure.edgePair.val (v.closingHalfEdge p h) =
      v.closure.crossing ((v.crossingsAt p).head h)
        (v.incomingSlot ((v.crossingsAt p).head h) p) := by
  rw [closingHalfEdge, v.edgePair_closure_outgoingSlot (List.getLast_mem h),
    nextCrossing_getLast_crossingsAt]

/-- Different strand positions have different outgoing endpoints of their closing arcs. -/
theorem closingHalfEdge_ne (v : BraidWord n) {p q : Fin n}
    (hp : v.crossingsAt p ≠ []) (hq : v.crossingsAt q ≠ []) (hpq : p ≠ q) :
    v.closingHalfEdge p hp ≠ v.closingHalfEdge q hq := by
  intro heq
  simp only [closingHalfEdge, crossing_closure] at heq
  have h := (crossingSlotEquiv v.length).injective heq
  obtain ⟨hj, hslot⟩ := Prod.ext_iff.mp h
  simp only at hj hslot
  have hmp := List.getLast_mem hp
  have hmq := List.getLast_mem hq
  rw [hj] at hmp hslot
  exact hpq (v.eq_of_outgoingSlot_eq hmp hmq hslot)

/-- A closing endpoint is not the partner of any closing endpoint, including one selected on the
same strand position. -/
theorem closingHalfEdge_ne_edgePair_closingHalfEdge (v : BraidWord n) (p q : Fin n)
    (hp : v.crossingsAt p ≠ []) (hq : v.crossingsAt q ≠ []) :
    v.closingHalfEdge q hq ≠ v.closure.edgePair.val (v.closingHalfEdge p hp) := by
  intro heq
  have hqorient := v.orientation_closingHalfEdge q hq
  have hporient := v.orientation_closingHalfEdge p hp
  have harc := v.closure.orientation_edgePair (v.closingHalfEdge p hp)
  rw [← heq, hqorient, hporient] at harc
  contradiction

end TauCeti.BraidWord
