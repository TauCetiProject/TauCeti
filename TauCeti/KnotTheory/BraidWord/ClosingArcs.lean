/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode
public import TauCeti.KnotTheory.PDCode.Planar

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

Adjacent closing arcs border a common face on the sides used by clasp insertion, or belong
to different components of the underlying crossing graph. The common face can be followed
from the bottom of the braid to the first crossing between the positions. If there is no such
crossing, the cut between them separates the crossing graph. This supplies the locality
condition for a Reidemeister-II clasp insertion.

## Main definitions

* `TauCeti.BraidWord.closingHalfEdge`: the outgoing endpoint of the closing arc at a strand
  position.

## Main results

* `TauCeti.BraidWord.edgePair_closingHalfEdge`: the other endpoint is the incoming half-edge at
  the first crossing on the position.
* `TauCeti.BraidWord.closingHalfEdge_ne`: different positions have different closing endpoints.
* `TauCeti.BraidWord.closingHalfEdge_ne_edgePair_closingHalfEdge`: closing endpoints are never
  paired with one another.
* `TauCeti.BraidWord.closingHalfEdge_clasp_face_condition`: adjacent closing arcs border a
  common face on the selected sides, or lie in separate graph components.

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

/-- The closing endpoint is the outgoing slot at the last crossing on its position. -/
theorem closingHalfEdge_def (v : BraidWord n) (p : Fin n) (h : v.crossingsAt p ≠ []) :
    v.closingHalfEdge p h = v.closure.crossing ((v.crossingsAt p).getLast h)
      (v.outgoingSlot ((v.crossingsAt p).getLast h) p) := (rfl)

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

/-- An outgoing half-edge is a closing endpoint exactly when it is the last crossing
on that same strand position. -/
theorem crossing_outgoingSlot_eq_closingHalfEdge_iff (v : BraidWord n) {j : Fin v.length}
    {p q : Fin n} (hj : j ∈ v.crossingsAt p) (hq : v.crossingsAt q ≠ []) :
    v.closure.crossing j (v.outgoingSlot j p) = v.closingHalfEdge q hq ↔
      p = q ∧ j = (v.crossingsAt q).getLast hq := by
  constructor
  · intro h
    have he := (crossingSlotEquiv v.length).injective
      (by simpa only [closingHalfEdge, crossing_closure] using h)
    obtain ⟨hj', hs⟩ := Prod.ext_iff.mp he
    simp only at hj' hs
    subst j
    exact ⟨v.eq_of_outgoingSlot_eq hj (List.getLast_mem hq) hs, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

open BraidGroup

variable (w : BraidWord n)

private theorem face_incoming_next {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) (hin : w.incomingSlot j p = 0)
    (hout : w.outgoingSlot j p = 1) :
    w.closure.face (w.closure.crossing (w.nextCrossing p j)
        (w.incomingSlot (w.nextCrossing p j) p)) =
      w.closure.face (w.closure.crossing j (w.incomingSlot j p)) := by
  have h := w.closure.toPDCode.face_facePerm (w.closure.crossing j 0)
  rw [facePerm_apply, crossing_apply, crossingRotation_crossing] at h
  norm_num only [Fin.reduceAdd] at h
  rw [← hout, w.edgePair_closure_outgoingSlot hj, ← hin] at h
  simpa only [← crossing_apply] using h

private theorem face_edge_incoming_next {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) (hin : w.incomingSlot j p = 3)
    (hout : w.outgoingSlot j p = 2) :
    w.closure.face (w.closure.edgePair.val (w.closure.crossing (w.nextCrossing p j)
        (w.incomingSlot (w.nextCrossing p j) p))) =
      w.closure.face (w.closure.edgePair.val
        (w.closure.crossing j (w.incomingSlot j p))) := by
  have h := w.closure.toPDCode.face_facePerm (w.closure.crossing j 2)
  rw [facePerm_apply, crossing_apply, crossingRotation_crossing] at h
  norm_num only [Fin.reduceAdd] at h
  rw [← hin, ← hout] at h
  rw [← w.edgePair_closure_outgoingSlot hj, w.closure.edgePair.apply_apply]
  simpa only [← crossing_apply] using h.symm

private theorem face_head_eq_of_next {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) (f : Fin w.length → w.closure.Face)
    (hnext : ∀ t ∈ w.crossingsAt p, t < j → f (w.nextCrossing p t) = f t) :
    f ((w.crossingsAt p).head (List.ne_nil_of_mem hj)) = f j := by
  obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hj
  have horder := List.pairwise_iff_getElem.mp
    (List.sortedLT_iff_pairwise.mp (w.sortedLT_crossingsAt p))
  have hchain : ∀ m, (hm : m ≤ k) →
      f ((w.crossingsAt p)[0]'(by omega)) =
        f ((w.crossingsAt p)[m]'(by omega)) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hmk : m < k := by omega
      have hmem := List.getElem_mem (l := w.crossingsAt p) (n := m) (by omega)
      have hlt : (w.crossingsAt p)[m]'(by omega) < j := by
        rw [← heq]
        exact horder m k (by omega) hk hmk
      have hstep := hnext _ hmem hlt
      simp only [w.nextCrossing_apply_getElem p m (by omega),
        Nat.mod_eq_of_lt (by omega : m + 1 < (w.crossingsAt p).length)] at hstep
      exact (ih (by omega)).trans hstep.symm
  simpa only [List.head_eq_getElem, heq] using hchain k le_rfl

/-- If a braid has a crossing between two adjacent positions, their closing arcs border
one face on the sides used by clasp insertion. -/
theorem face_edgePair_closingHalfEdge_eq_of_exists (i : Fin (n - 1))
    (hp : w.crossingsAt (strand i) ≠ []) (hq : w.crossingsAt (strandSucc i) ≠ [])
    (hi : ∃ j : Fin w.length, w[j.1].1 = i) :
    w.closure.face (w.closure.edgePair.val (w.closingHalfEdge (strand i) hp)) =
      w.closure.face (w.closingHalfEdge (strandSucc i) hq) := by
  classical
  let S := Finset.univ.filter fun j : Fin w.length => w[j.1].1 = i
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hi
    exact ⟨j, by simp [S, hj]⟩
  let j := S.min' hS
  have hj : w[j.1].1 = i := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hfirst (t : Fin w.length) (ht : t < j) : w[t.1].1 ≠ i := by
    intro hti
    have hle := S.min'_le t (by simp [S, hti])
    exact (not_le_of_gt ht) hle
  have hl : j ∈ w.crossingsAt (strand i) := by simp [hj]
  have hr : j ∈ w.crossingsAt (strandSucc i) := by simp [hj]
  have hleft := w.face_head_eq_of_next hl
    (fun t => w.closure.face (w.closure.crossing t (w.incomingSlot t (strand i))))
    (fun t ht htj => by
      have hpos : strand i = strandSucc w[t.1].1 :=
        (w.mem_crossingsAt.mp ht).resolve_left (fun h => hfirst t htj (by
          apply Fin.ext
          simpa only [val_strand] using congrArg Fin.val h.symm))
      exact w.face_incoming_next ht (by simp [hpos]) (by simp [hpos]))
  have hright := w.face_head_eq_of_next hr
    (fun t => w.closure.face (w.closure.edgePair.val
      (w.closure.crossing t (w.incomingSlot t (strandSucc i)))))
    (fun t ht htj => by
      have hpos : strandSucc i = strand w[t.1].1 :=
        (w.mem_crossingsAt.mp ht).resolve_right
          (fun h => hfirst t htj (by
            apply Fin.ext
            have hv := congrArg Fin.val h
            simp only [val_strandSucc] at hv
            omega))
      exact w.face_edge_incoming_next ht (by simp [hpos]) (by simp [hpos]))
  have hmiddle := w.closure.toPDCode.face_facePerm (w.closure.crossing j 3)
  rw [facePerm_apply, crossing_apply, crossingRotation_crossing] at hmiddle
  norm_num only [Fin.reduceAdd] at hmiddle
  rw [w.edgePair_closingHalfEdge _ hp]
  rw [← w.closure.edgePair.apply_apply (w.closingHalfEdge (strandSucc i) hq),
    w.edgePair_closingHalfEdge _ hq]
  have hin : w.incomingSlot j (strand i) = 3 := by rw [← hj]; simp
  have hin' : w.incomingSlot j (strandSucc i) = 0 := by rw [← hj]; simp
  refine hleft.trans (Eq.trans ?_ hright.symm)
  rw [hin, hin']
  simpa only [← crossing_apply] using hmiddle.symm

private theorem same_side_of_mem_crossingsAt (i : Fin (n - 1))
    (hi : ∀ j : Fin w.length, w[j.1].1 ≠ i) {p : Fin n} {j k : Fin w.length}
    (hj : j ∈ w.crossingsAt p) (hk : k ∈ w.crossingsAt p) :
    decide ((w[j.1].1 : ℕ) < i) = decide ((w[k.1].1 : ℕ) < i) := by
  have hji : (w[j.1].1 : ℕ) ≠ i := fun h => hi j (Fin.ext h)
  have hki : (w[k.1].1 : ℕ) ≠ i := fun h => hi k (Fin.ext h)
  simp only [mem_crossingsAt, Fin.ext_iff, val_strand, val_strandSucc] at hj hk
  simp only [decide_eq_decide]
  omega

/-- If a braid never crosses the cut between two adjacent positions, their closing arcs
lie in different connected components of the underlying crossing graph. -/
theorem closingHalfEdge_not_mem_orbit_of_forall_ne (i : Fin (n - 1))
    (hp : w.crossingsAt (strand i) ≠ []) (hq : w.crossingsAt (strandSucc i) ≠ [])
    (hi : ∀ j : Fin w.length, w[j.1].1 ≠ i) :
    w.closingHalfEdge (strandSucc i) hq ∉
      MulAction.orbit w.closure.toPermutationTriple.monodromyGroup
        (w.closingHalfEdge (strand i) hp) := by
  -- Record which side of the cut contains each crossing; both graph generators preserve it.
  let side := fun h : Fin (4 * w.length) =>
    decide ((w[((crossingSlotEquiv w.length).symm h).1.val].1 : ℕ) < i)
  have hside (j : Fin w.length) (s : Fin 4) :
      side (w.closure.crossing j s) = decide ((w[j.1].1 : ℕ) < i) := by
    simp [side]
  have hout {j : Fin w.length} {p : Fin n} (hj : j ∈ w.crossingsAt p) :
      side (w.closure.edgePair.val (w.closure.crossing j (w.outgoingSlot j p))) =
        side (w.closure.crossing j (w.outgoingSlot j p)) := by
    rw [w.edgePair_closure_outgoingSlot hj, hside, hside]
    exact w.same_side_of_mem_crossingsAt i hi (w.nextCrossing_mem_crossingsAt_iff.mpr hj) hj
  have hin {j : Fin w.length} {p : Fin n} (hj : j ∈ w.crossingsAt p) :
      side (w.closure.edgePair.val (w.closure.crossing j (w.incomingSlot j p))) =
        side (w.closure.crossing j (w.incomingSlot j p)) := by
    rw [w.edgePair_closure_incomingSlot hj, hside, hside]
    exact w.same_side_of_mem_crossingsAt i hi
      (w.nextCrossing_symm_mem_crossingsAt_iff.mpr hj) hj
  have hrot (x : Fin (4 * w.length)) : side (w.closure.crossingRotation x) = side x := by
    obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv w.length).surjective x
    rw [← crossing_closure, crossing_apply, crossingRotation_crossing, hside]
    rw [← crossing_apply, hside]
  -- The incoming and outgoing formulas cover all four slots of each crossing.
  have hedge (x : Fin (4 * w.length)) : side (w.closure.edgePair.val x) = side x := by
    obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv w.length).surjective x
    rw [← crossing_closure]
    have hl := w.mem_crossingsAt_strand j
    have hr := w.mem_crossingsAt_strandSucc j
    obtain rfl | rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by
      fin_cases s <;> simp
    · simpa only [incomingSlot_strandSucc] using hin hr
    · simpa only [outgoingSlot_strandSucc] using hout hr
    · simpa only [outgoingSlot_strand] using hout hl
    · simpa only [incomingSlot_strand] using hin hl
  rintro ⟨g, hg⟩
  have h := w.closure.toPermutationTriple.apply_eq_of_mem_monodromyGroup (f := side)
    (fun x => by simpa only [toPermutationTriple_σ0] using hrot x)
    (fun x => by simpa only [toPermutationTriple_σ1] using hedge x) g.2
    (w.closingHalfEdge (strand i) hp)
  -- The permutation action on half-edges is evaluation.
  have hg' : g.val (w.closingHalfEdge (strand i) hp) =
      w.closingHalfEdge (strandSucc i) hq := hg
  rw [hg', closingHalfEdge_def, closingHalfEdge_def, hside, hside] at h
  -- The two closing endpoints have different labels, contradicting orbit invariance.
  have hl := w.mem_crossingsAt.mp (List.getLast_mem hp)
  have hr := w.mem_crossingsAt.mp (List.getLast_mem hq)
  have hli : (w[((w.crossingsAt (strand i)).getLast hp).val].1 : ℕ) ≠ i :=
    fun he => hi _ (Fin.ext he)
  have hri : (w[((w.crossingsAt (strandSucc i)).getLast hq).val].1 : ℕ) ≠ i :=
    fun he => hi _ (Fin.ext he)
  simp only [Fin.ext_iff, val_strand, val_strandSucc] at hl hr
  have hl' : (w[((w.crossingsAt (strand i)).getLast hp).val].1 : ℕ) < i := by omega
  have hr' : ¬(w[((w.crossingsAt (strandSucc i)).getLast hq).val].1 : ℕ) < i := by omega
  simp [hl', hr'] at h

/-- Adjacent closing arcs always satisfy the locality condition for Reidemeister-II clasp
insertion: the selected sides border one face, or the arcs lie in separate graph components. -/
theorem closingHalfEdge_clasp_face_condition (i : Fin (n - 1))
    (hp : w.crossingsAt (strand i) ≠ []) (hq : w.crossingsAt (strandSucc i) ≠ []) :
    w.closure.face (w.closure.edgePair.val (w.closingHalfEdge (strand i) hp)) =
        w.closure.face (w.closingHalfEdge (strandSucc i) hq) ∨
      w.closingHalfEdge (strandSucc i) hq ∉
        MulAction.orbit w.closure.toPermutationTriple.monodromyGroup
          (w.closingHalfEdge (strand i) hp) := by
  by_cases hi : ∃ j : Fin w.length, w[j.1].1 = i
  · exact Or.inl (w.face_edgePair_closingHalfEdge_eq_of_exists i hp hq hi)
  · exact Or.inr (w.closingHalfEdge_not_mem_orbit_of_forall_ne i hp hq (by simpa using hi))

end TauCeti.BraidWord
