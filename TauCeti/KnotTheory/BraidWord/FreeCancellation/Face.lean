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

The common face can be followed from the bottom of the braid to the first crossing between
the positions. If there is no such crossing, the cut between them separates the crossing graph.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup PDCode

variable {n : ℕ} (w : BraidWord n)

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
