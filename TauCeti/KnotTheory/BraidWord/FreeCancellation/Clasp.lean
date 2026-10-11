/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.ClosingArcs
import TauCeti.KnotTheory.BraidWord.Cyclic
import TauCeti.KnotTheory.BraidWord.DoubleCrossing.ExternalArcs
import TauCeti.KnotTheory.BraidWord.CrossinglessComponents
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence

/-!
# Free cancellation as an algebraic clasp

An adjacent inverse pair in a braid closure cuts the two closing arcs and inserts a clasp.
When both positions already meet crossings, this is precisely the two-arc clasp on the
original oriented PD-code, up to renaming and reading the new crossings from another slot.
This comparison identifies the entire diagram, including the external arcs and oriented
crossing-free circles. If both participating positions are crossing-free, the inserted pair
is instead a closed two-circle clasp, and hence gives a Reidemeister-II move in any word context.
For the two-existing-arcs case, the common-face condition needed for a planar Reidemeister move
is separate from the algebraic identification.

The proof uses `edgePair_closure_eq_of_outgoingSlot` and the double-crossing arc formulas
already supplied by the braid closure API, together with oriented clasp insertion.

## Main results

* `reidemeisterEquiv_closure_cons_cons_freeCancel_insertClasp`: identify a prepended inverse
  pair with the clasp on the two existing closing arcs, using relabeling and crossing rotation.
* `reidemeisterEquiv_closure_append_cons_cons_freeCancel_of_crossingsAt_eq_nil`: insertion
  of an inverse pair on two crossing-free positions preserves the closure up to Reidemeister moves.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup PDCode Equiv

variable {n : ℕ}

private def claspCross (N : ℕ) : Fin (N + 2) ≃ Fin (N + 2) :=
  finAddFlip.trans (finCongr (Nat.add_comm 2 N))

@[simp] private theorem claspCross_old (N : ℕ) (j : Fin N) :
    claspCross N j.castSucc.castSucc = j.succ.succ := by
  have h : j.castSucc.castSucc = Fin.castAdd 2 j := Fin.castSucc_castAdd j
  simp only [claspCross, Equiv.trans_apply, h, finAddFlip_apply_castAdd, finCongr_apply]
  apply Fin.ext
  simp only [Fin.val_natAdd, Fin.val_succ, Fin.val_cast]
  omega

@[simp] private theorem claspCross_first (N : ℕ) :
    claspCross N (Fin.last N).castSucc = 0 := by
  have h : (Fin.last N).castSucc = Fin.natAdd N (0 : Fin 2) := by
    apply Fin.ext
    simp
  simp only [claspCross, Equiv.trans_apply, h, finAddFlip_apply_natAdd, finCongr_apply]
  apply Fin.ext
  simp

@[simp] private theorem claspCross_second (N : ℕ) :
    claspCross N (Fin.last (N + 1)) = 1 := by
  have h : Fin.last (N + 1) = Fin.natAdd N (1 : Fin 2) := by
    apply Fin.ext
    simp
  simp only [claspCross, Equiv.trans_apply, h, finAddFlip_apply_natAdd, finCongr_apply]
  apply Fin.ext
  simp

private def claspHalf (N : ℕ) : Fin (4 * (N + 2)) ≃ Fin (4 * (N + 2)) :=
  (crossingSlotEquiv (N + 2)).symm.trans
    ((Equiv.prodCongrRight fun j : Fin (N + 2) =>
      if j.val < N then Equiv.refl (Fin 4) else (finRotate 4).symm).trans
      ((Equiv.prodCongr (claspCross N) (Equiv.refl (Fin 4))).trans
        (crossingSlotEquiv (N + 2))))

@[simp] private theorem claspHalf_old_crossing (N : ℕ) (j : Fin N) (s : Fin 4) :
    claspHalf N (halfEdgeSuccEquiv (N + 1)
      (.inl (halfEdgeSuccEquiv N (.inl (crossingSlotEquiv N (j, s)))))) =
      crossingSlotEquiv (N + 2) (j.succ.succ, s) := by
  simp [← crossingSlotEquiv_succ_castSucc, claspHalf]

@[simp] private theorem claspHalf_first (N : ℕ) (s : Fin 4) :
    claspHalf N (halfEdgeSuccEquiv (N + 1) (.inl (halfEdgeSuccEquiv N (.inr s)))) =
      crossingSlotEquiv (N + 2) (0, s - 1) := by
  simp [← crossingSlotEquiv_succ_last, ← crossingSlotEquiv_succ_castSucc, claspHalf]

@[simp] private theorem claspHalf_second (N : ℕ) (s : Fin 4) :
    claspHalf N (halfEdgeSuccEquiv (N + 1) (.inr s)) =
      crossingSlotEquiv (N + 2) (1, s - 1) := by
  simp [← crossingSlotEquiv_succ_last, claspHalf]

@[simp] private theorem claspCross_symm_old (N : ℕ) (j : Fin N) :
    (claspCross N).symm j.succ.succ = j.castSucc.castSucc :=
  (claspCross N).symm_apply_eq.mpr (claspCross_old N j).symm

@[simp] private theorem claspCross_symm_zero (N : ℕ) :
    (claspCross N).symm 0 = (Fin.last N).castSucc :=
  (claspCross N).symm_apply_eq.mpr (claspCross_first N).symm

@[simp] private theorem claspCross_symm_one (N : ℕ) :
    (claspCross N).symm 1 = Fin.last (N + 1) :=
  (claspCross N).symm_apply_eq.mpr (claspCross_second N).symm

private def readClasp (D : OrientedPDCode (N + 2)) : OrientedPDCode (N + 2) :=
  ((D.relabel (claspHalf N) (claspCross N)).rotateCrossing 0).rotateCrossing 1

private theorem readClasp_edgePair_apply (D : OrientedPDCode (N + 2))
    (x : Fin (4 * (N + 2))) :
    (readClasp D).edgePair.val (claspHalf N x) = claspHalf N (D.edgePair.val x) := by
  simp [readClasp]

variable (v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)
  (hp : v.crossingsAt (strand i) ≠ []) (hq : v.crossingsAt (strandSucc i) ≠ [])

private def closingClasp : OrientedPDCode (v.length + 2) :=
  v.closure.insertClasp (v.closingHalfEdge (strand i) hp)
    (v.closingHalfEdge (strandSucc i) hq) (!decide (ε = 1))
    (v.closingHalfEdge_ne hq hp (strand_ne_strandSucc i).symm)
    (v.closingHalfEdge_ne_edgePair_closingHalfEdge _ _ hp hq)

private theorem readClosingClasp_halfEdge :
    (readClasp (closingClasp v i ε hp hq)).halfEdge =
      (closure ((i, ε) :: (i, -ε) :: v)).halfEdge := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv (v.length + 2)).surjective x
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · simp [readClasp, closingClasp]
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp [readClasp, closingClasp, one_ne_zero]
    · have h0 : j.succ.succ ≠ (0 : Fin (v.length + 2)) := Fin.succ_ne_zero _
      have h1 : j.succ.succ ≠ (1 : Fin (v.length + 2)) := by simp [Fin.ext_iff]
      simp [crossing_apply, readClasp, closingClasp, h0, h1]

private theorem readClosingClasp_edgePair_old {j : Fin v.length} {p : Fin n}
    (hjold : j ∈ v.crossingsAt p) :
    (closure ((i, ε) :: (i, -ε) :: v)).edgePair.val
        (crossingSlotEquiv (v.length + 2) (j.succ.succ, v.outgoingSlot j p)) =
      (readClasp (closingClasp v i ε hp hq)).edgePair.val
        (crossingSlotEquiv (v.length + 2) (j.succ.succ, v.outgoingSlot j p)) := by
  let D := closingClasp v i ε hp hq
  have hinlo : incomingSlot ((i, ε) :: (i, -ε) :: v) 0 (strand i) = 3 := by
    simpa using incomingSlot_strand ((i, ε) :: (i, -ε) :: v) 0
  have hinhi : incomingSlot ((i, ε) :: (i, -ε) :: v) 0 (strandSucc i) = 0 := by
    simpa using incomingSlot_strandSucc ((i, ε) :: (i, -ε) :: v) 0
  let x := v.closure.crossing j (v.outgoingSlot j p)
  have hx : v.closure.orientation x = true := by
    rcases v.outgoingSlot_eq_one_or_two j p with hs | hs <;>
      simp [x, hs]
  have hxe : x ≠ v.closure.edgePair.val (v.closingHalfEdge (strand i) hp) := by
    intro he
    have hh := v.closure.orientation_edgePair (v.closingHalfEdge (strand i) hp)
    rw [← he, hx, orientation_closingHalfEdge] at hh
    contradiction
  have hxe' : x ≠ v.closure.edgePair.val (v.closingHalfEdge (strandSucc i) hq) := by
    intro he
    have hh := v.closure.orientation_edgePair (v.closingHalfEdge (strandSucc i) hq)
    rw [← he, hx, orientation_closingHalfEdge] at hh
    contradiction
  have hmatch := readClasp_edgePair_apply D
    (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inl x))))
  have hxembed : claspHalf v.length
      (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inl x)))) =
      crossingSlotEquiv (v.length + 2) (j.succ.succ, v.outgoingSlot j p) := by
    simp only [x, crossing_closure, claspHalf_old_crossing]
  rw [hxembed] at hmatch
  -- The two closing endpoints enter the first new crossing.
  by_cases hxp : x = v.closingHalfEdge (strand i) hp
  · obtain ⟨rfl, rfl⟩ := (crossing_outgoingSlot_eq_closingHalfEdge_iff v hjold hp).mp hxp
    simp only [D, closingClasp, OrientedPDCode.toPDCode_insertClasp,
      hxp, insertClasp_edgePair_inl_inl_self, claspHalf_first,
      Fin.reduceSub] at hmatch
    have h := edgePair_closure_cons_cons_of_mem v i ε (-ε) (List.getLast_mem hp)
    simp only [nextCrossing_getLast_crossingsAt, true_or, true_and, ite_true,
      crossing_closure, List.length_cons, hinlo] at h
    simpa only [List.length_cons, hinlo, D, closingClasp] using h.trans hmatch.symm
  · by_cases hxq : x = v.closingHalfEdge (strandSucc i) hq
    · obtain ⟨rfl, rfl⟩ := (crossing_outgoingSlot_eq_closingHalfEdge_iff v hjold hq).mp hxq
      simp only [D, closingClasp, OrientedPDCode.toPDCode_insertClasp,
        hxq, insertClasp_edgePair_inl_inl_right, claspHalf_first,
        Fin.reduceSub] at hmatch
      have h := edgePair_closure_cons_cons_of_mem v i ε (-ε) (List.getLast_mem hq)
      simp only [nextCrossing_getLast_crossingsAt, or_true, true_and, ite_true,
        crossing_closure, List.length_cons, hinhi] at h
      simpa only [List.length_cons, hinhi, D, closingClasp] using h.trans hmatch.symm
    · simp only [D, closingClasp, OrientedPDCode.toPDCode_insertClasp,
        v.closure.toPDCode.insertClasp_edgePair_inl_inl_of_ne _ _ _ _ _ hxp hxe hxq hxe'] at hmatch
      simp only [x] at hmatch
      rw [edgePair_closure_outgoingSlot v hjold, crossing_closure,
        claspHalf_old_crossing] at hmatch
      -- All other outgoing arcs retain their old successor.
      have hc : ¬ ((p = strand i ∨ p = strandSucc i) ∧
          v.nextCrossing p j = (v.crossingsAt p).head (List.ne_nil_of_mem hjold)) := by
        rintro ⟨hpos, hn⟩
        rcases hpos with rfl | rfl
        · apply hxp
          apply (crossing_outgoingSlot_eq_closingHalfEdge_iff v hjold hp).mpr
          refine ⟨rfl, (v.nextCrossing (strand i)).injective ?_⟩
          simpa using hn
        · apply hxq
          apply (crossing_outgoingSlot_eq_closingHalfEdge_iff v hjold hq).mpr
          refine ⟨rfl, (v.nextCrossing (strandSucc i)).injective ?_⟩
          simpa using hn
      have h := edgePair_closure_cons_cons_of_mem v i ε (-ε) hjold
      simp only [hc, ite_false, crossing_closure, List.length_cons] at h
      simpa only [D, closingClasp] using h.trans hmatch.symm

private theorem readClosingClasp_edgePair :
    (closure ((i, ε) :: (i, -ε) :: v)).edgePair =
      (readClasp (closingClasp v i ε hp hq)).edgePair := by
  let w : BraidWord n := (i, ε) :: (i, -ε) :: v
  let D := closingClasp v i ε hp hq
  have hlo₀ : w.outgoingSlot 0 (strand i) = 2 := by
    simpa [w] using outgoingSlot_strand w 0
  have hhi₀ : w.outgoingSlot 0 (strandSucc i) = 1 := by
    simpa [w] using outgoingSlot_strandSucc w 0
  have hlo₁ : w.outgoingSlot 1 (strand i) = 2 := by
    simpa [w] using outgoingSlot_strand w 1
  have hhi₁ : w.outgoingSlot 1 (strandSucc i) = 1 := by
    simpa [w] using outgoingSlot_strandSucc w 1
  have hfirst₁ := readClasp_edgePair_apply D
    (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inr 2))))
  have hfirst₂ := readClasp_edgePair_apply D
    (halfEdgeSuccEquiv (v.length + 1) (.inl (halfEdgeSuccEquiv v.length (.inr 3))))
  have hsecond₁ := readClasp_edgePair_apply D
    (halfEdgeSuccEquiv (v.length + 1) (.inr 2))
  have hsecond₂ := readClasp_edgePair_apply D
    (halfEdgeSuccEquiv (v.length + 1) (.inr 3))
  simp only [D, closingClasp, OrientedPDCode.toPDCode_insertClasp,
    insertClasp_edgePair_inl_inr_two, insertClasp_edgePair_inl_inr_three,
    insertClasp_edgePair_inr_two, insertClasp_edgePair_inr_three,
    claspHalf_first, claspHalf_second, edgePair_closingHalfEdge, crossing_closure,
    claspHalf_old_crossing, Fin.reduceSub] at hfirst₁ hfirst₂ hsecond₁ hsecond₂
  apply edgePair_closure_eq_of_outgoingSlot
  intro j p hj
  simp only [w, List.length_cons] at *
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · have hpos : p = strand i ∨ p = strandSucc i := by
      simpa [w] using (mem_crossingsAt (w := w)).mp hj
    rcases hpos with rfl | rfl
    · simpa only [List.length_cons, hlo₀, D, closingClasp] using
        (edgePair_closure_cons_cons_two v i ε (-ε)).trans hfirst₂.symm
    · simpa only [List.length_cons, hhi₀, D, closingClasp] using
        (edgePair_closure_cons_cons_one v i ε (-ε)).trans hfirst₁.symm
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · have hpos : p = strand i ∨ p = strandSucc i := by
        simpa [w] using (mem_crossingsAt (w := w)).mp hj
      rcases hpos with rfl | rfl
      · have h := edgePair_closure_cons_cons_outgoingSlot_one_of_ne_nil
          v i ε (-ε) (Or.inl rfl) hp
        simp only [crossing_closure, List.length_cons] at h
        simpa only [Fin.succ_zero_eq_one, List.length_cons, hlo₁, D, closingClasp] using
          h.trans hsecond₂.symm
      · have h := edgePair_closure_cons_cons_outgoingSlot_one_of_ne_nil
          v i ε (-ε) (Or.inr rfl) hq
        simp only [crossing_closure, List.length_cons] at h
        simpa only [Fin.succ_zero_eq_one, List.length_cons, hhi₁, D, closingClasp] using
          h.trans hsecond₁.symm
    · have hjold : j ∈ v.crossingsAt p := by
        simpa [w] using (mem_crossingsAt (w := w)).mp hj
      have hletter : w[j.succ.succ.val] = v[j.val] := by simp [w]
      rw [outgoingSlot_congr hletter p]
      exact readClosingClasp_edgePair_old v i ε hp hq hjold

private theorem readClosingClasp_orientation :
    (readClasp (closingClasp v i ε hp hq)).orientation =
      (closure ((i, ε) :: (i, -ε) :: v)).orientation := by
  funext x
  obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv (v.length + 2)).surjective x
  have hori : (closure ((i, ε) :: (i, -ε) :: v)).orientation
      (crossingSlotEquiv (v.length + 2) (j, s)) = decide (s = 1 ∨ s = 2) := by
    simpa only [List.length_cons] using
      orientation_closure ((i, ε) :: (i, -ε) :: v) j s
  rw [hori]
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · have h := claspHalf_first v.length (s + 1)
    simp only [add_sub_cancel_right] at h
    rw [← h]
    simp only [readClasp, OrientedPDCode.rotateCrossing_orientation,
      OrientedPDCode.relabel_orientation, Equiv.symm_apply_apply, closingClasp,
      OrientedPDCode.orientation_insertClasp_inl_inr, orientation_closingHalfEdge]
    fin_cases s <;> decide
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · have h := claspHalf_second v.length (s + 1)
      simp only [add_sub_cancel_right] at h
      rw [Fin.succ_zero_eq_one, ← h]
      simp only [readClasp, OrientedPDCode.rotateCrossing_orientation,
        OrientedPDCode.relabel_orientation, Equiv.symm_apply_apply, closingClasp,
        OrientedPDCode.orientation_insertClasp_inr, orientation_closingHalfEdge]
      fin_cases s <;> decide
    · rw [← claspHalf_old_crossing]
      simp only [readClasp, OrientedPDCode.rotateCrossing_orientation,
        OrientedPDCode.relabel_orientation, Equiv.symm_apply_apply, closingClasp,
        OrientedPDCode.orientation_insertClasp_inl_inl, orientation_closure]

private theorem readClosingClasp_overPair :
    (readClasp (closingClasp v i ε hp hq)).overPair =
      (closure ((i, ε) :: (i, -ε) :: v)).overPair := by
  funext j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [readClasp, closingClasp]
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rcases Int.units_eq_one_or ε with rfl | rfl <;>
        simp [readClasp, closingClasp, Fin.succ_zero_eq_one, one_ne_zero]
    · have h0 : j.succ.succ ≠ (0 : Fin (v.length + 2)) := Fin.succ_ne_zero _
      have h1 : j.succ.succ ≠ (1 : Fin (v.length + 2)) := by simp [Fin.ext_iff]
      simp [readClasp, closingClasp, h0, h1]

private theorem readClosingClasp_eq :
    readClasp (closingClasp v i ε hp hq) = closure ((i, ε) :: (i, -ε) :: v) := by
  have hc := crossinglessComponents_closure_insert_pair ([] : BraidWord n) v i ε (-ε)
  simp only [List.nil_append, hp, hq, ite_false, Multiset.replicate_zero, add_zero] at hc
  have hc' : (readClasp (closingClasp v i ε hp hq)).crossinglessComponents =
      (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponents := by
    simpa [readClasp, closingClasp] using hc.symm
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · exact readClosingClasp_halfEdge v i ε hp hq
    · exact (readClosingClasp_edgePair v i ε hp hq).symm
    · simpa only [OrientedPDCode.card_crossinglessComponents] using
        congrArg Multiset.card hc'
    · exact readClosingClasp_overPair v i ε hp hq
  · exact readClosingClasp_orientation v i ε hp hq
  · exact hc'

/-- When both positions meet old crossings, an inverse pair in a braid closure is the
algebraic clasp on their closing arcs, up to the diagram isomorphisms generated by relabeling
and crossing rotation. No common-face or planarity hypothesis is required for this comparison. -/
theorem reidemeisterEquiv_closure_cons_cons_freeCancel_insertClasp :
    OrientedPDCode.ReidemeisterEquiv (closure ((i, ε) :: (i, -ε) :: v))
      (v.closure.insertClasp (v.closingHalfEdge (strand i) hp)
        (v.closingHalfEdge (strandSucc i) hq) (!decide (ε = 1))
        (v.closingHalfEdge_ne hq hp (strand_ne_strandSucc i).symm)
        (v.closingHalfEdge_ne_edgePair_closingHalfEdge _ _ hp hq)) := by
  rw [← readClosingClasp_eq v i ε hp hq]
  exact ((OrientedPDCode.reidemeisterEquiv_relabel _ _ _).trans
    ((OrientedPDCode.reidemeisterEquiv_rotateCrossing _ 0).trans
      (OrientedPDCode.reidemeisterEquiv_rotateCrossing _ 1))).symm

private theorem unionOld (N : ℕ) (j : Fin N) (s : Fin 4) :
    disjointUnionHalfEdgeEquiv N 2 (.inl (crossingSlotEquiv N (j, s))) =
      halfEdgeSuccEquiv (N + 1) (.inl (halfEdgeSuccEquiv N
        (.inl (crossingSlotEquiv N (j, s))))) := by
  have h : j.castSucc.castSucc = Fin.castAdd 2 j := Fin.castSucc_castAdd j
  simp only [disjointUnionHalfEdgeEquiv_inl_crossingSlot,
    ← crossingSlotEquiv_succ_castSucc, h]

private theorem unionFirst (N : ℕ) (s : Fin 4) :
    disjointUnionHalfEdgeEquiv N 2 (.inr (crossingSlotEquiv 2 (0, s))) =
      halfEdgeSuccEquiv (N + 1) (.inl (halfEdgeSuccEquiv N (.inr s))) := by
  have h : Fin.natAdd N (0 : Fin 2) = (Fin.last N).castSucc := by
    apply Fin.ext
    simp
  simp only [disjointUnionHalfEdgeEquiv_inr_crossingSlot, h,
    ← crossingSlotEquiv_succ_castSucc, ← crossingSlotEquiv_succ_last]

private theorem unionSecond (N : ℕ) (s : Fin 4) :
    disjointUnionHalfEdgeEquiv N 2 (.inr (crossingSlotEquiv 2 (1, s))) =
      halfEdgeSuccEquiv (N + 1) (.inr s) := by
  have h : Fin.natAdd N (1 : Fin 2) = Fin.last (N + 1) := Fin.natAdd_last
  simp only [disjointUnionHalfEdgeEquiv_inr_crossingSlot, h, ← crossingSlotEquiv_succ_last]

section TwoCircles

variable (v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)
  (hp₀ : v.crossingsAt (strand i) = []) (hq₀ : v.crossingsAt (strandSucc i) = [])

variable (D : OrientedPDCode v.length)
  (hD : (D.adjoinCircle true).adjoinCircle true = v.closure)

include hD

private theorem twoCircleCore_halfEdge : D.halfEdge = v.closure.halfEdge := by
  simpa using congrArg (fun C => C.halfEdge) hD

private theorem twoCircleCore_edgePair : D.edgePair = v.closure.edgePair := by
  simpa using congrArg (fun C => C.edgePair) hD

private theorem twoCircleCore_overPair : D.overPair = v.closure.overPair := by
  simpa using congrArg (fun C => C.overPair) hD

private theorem twoCircleCore_orientation : D.orientation = v.closure.orientation := by
  simpa using congrArg OrientedPDCode.orientation hD

include hp₀ hq₀ in
private theorem twoCircleCore_crossinglessComponents :
    D.crossinglessComponents = (closure ((i, ε) :: (i, -ε) :: v)).crossinglessComponents := by
  have hc := crossinglessComponents_closure_insert_pair ([] : BraidWord n) v i ε (-ε)
  simp only [List.nil_append, hp₀, hq₀, ite_true, Multiset.replicate_one] at hc
  have hcircles := congrArg OrientedPDCode.crossinglessComponents hD
  simp only [OrientedPDCode.crossinglessComponents_adjoinCircle] at hcircles
  rw [← hc] at hcircles
  rw [Multiset.add_comm _ {true}, Multiset.singleton_add,
    Multiset.add_comm _ {true}, Multiset.singleton_add] at hcircles
  simpa only [Multiset.cons_inj_right, List.cons_append, List.nil_append] using hcircles

omit hD in
private def twoCircleDiagram : OrientedPDCode (v.length + 2) :=
  D.adjoinTwoCircleClasp true true (!decide (ε = 1))

private theorem readTwoCircleDiagram_edgePair_inl (x : Fin (4 * v.length)) :
    (readClasp (twoCircleDiagram v ε D)).edgePair.val
        (claspHalf v.length (disjointUnionHalfEdgeEquiv v.length 2 (.inl x))) =
      claspHalf v.length
        (disjointUnionHalfEdgeEquiv v.length 2 (.inl (v.closure.edgePair.val x))) := by
  have h := readClasp_edgePair_apply (twoCircleDiagram v ε D)
    (disjointUnionHalfEdgeEquiv v.length 2 (.inl x))
  simpa [twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def,
    disjointUnion_edgePair_val, twoCircleCore_edgePair v D hD] using h

omit hD in
private theorem readTwoCircleDiagram_edgePair_inr (j : Fin 2) (s : Fin 4) :
    (readClasp (twoCircleDiagram v ε D)).edgePair.val
        (claspHalf v.length (disjointUnionHalfEdgeEquiv v.length 2
          (.inr (crossingSlotEquiv 2 (j, s))))) =
      claspHalf v.length (disjointUnionHalfEdgeEquiv v.length 2
        (.inr (crossingSlotEquiv 2 (j.rev, s.rev)))) := by
  have h := readClasp_edgePair_apply (twoCircleDiagram v ε D)
    (disjointUnionHalfEdgeEquiv v.length 2 (.inr (crossingSlotEquiv 2 (j, s))))
  simpa [twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def,
    disjointUnion_edgePair_val] using h

include hp₀ hq₀ in
private theorem readTwoCircleDiagram_edgePair_old {j : Fin v.length} {p : Fin n}
    (hjold : j ∈ v.crossingsAt p) :
    (closure ((i, ε) :: (i, -ε) :: v)).edgePair.val
        (crossingSlotEquiv _ (j.succ.succ, v.outgoingSlot j p)) =
      (readClasp (twoCircleDiagram v ε D)).edgePair.val
        (crossingSlotEquiv _ (j.succ.succ, v.outgoingSlot j p)) := by
  have hpos : p ≠ strand i ∧ p ≠ strandSucc i := by
    constructor <;> intro h <;> subst p <;> simp_all
  have h := edgePair_closure_cons_cons_of_mem v i ε (-ε) hjold
  simp only [hpos.1, hpos.2, false_or, false_and, ite_false, crossing_closure,
    List.length_cons] at h
  have hm := readTwoCircleDiagram_edgePair_inl v ε D hD
    (v.closure.crossing j (v.outgoingSlot j p))
  rw [edgePair_closure_outgoingSlot v hjold] at hm
  simp only [crossing_closure, unionOld, claspHalf_old_crossing] at hm
  exact h.trans hm.symm

include hp₀ hq₀ in
private theorem readTwoCircleDiagram_edgePair :
    (closure ((i, ε) :: (i, -ε) :: v)).edgePair =
      (readClasp (twoCircleDiagram v ε D)).edgePair := by
  let w : BraidWord n := (i, ε) :: (i, -ε) :: v
  let C := twoCircleDiagram v ε D
  -- The closed clasp matching supplies all four outgoing arcs at the new crossings.
  have hmatchFirst (s : Fin 4) :
      (readClasp C).edgePair.val (crossingSlotEquiv (v.length + 2) (0, s - 1)) =
        crossingSlotEquiv (v.length + 2) (1, s.rev - 1) := by
    simpa only [unionFirst, unionSecond, claspHalf_first, claspHalf_second, Fin.reduceRev]
      using readTwoCircleDiagram_edgePair_inr v ε D 0 s
  have hmatchSecond (s : Fin 4) :
      (readClasp C).edgePair.val (crossingSlotEquiv (v.length + 2) (1, s - 1)) =
        crossingSlotEquiv (v.length + 2) (0, s.rev - 1) := by
    simpa only [unionFirst, unionSecond, claspHalf_first, claspHalf_second, Fin.reduceRev]
      using readTwoCircleDiagram_edgePair_inr v ε D 1 s
  have hm₀₂ := hmatchFirst 3
  have hm₀₁ := hmatchFirst 2
  have hm₁₂ := hmatchSecond 3
  have hm₁₁ := hmatchSecond 2
  norm_num [Fin.rev] at hm₀₂ hm₀₁ hm₁₂ hm₁₁
  have hneg : (-1 : Fin 4) = 3 := by decide
  rw [hneg] at hm₁₂
  apply edgePair_closure_eq_of_outgoingSlot
  intro j p hj
  simp only [List.length_cons] at *
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · have hpos : p = strand i ∨ p = strandSucc i := by
      simpa [w] using (mem_crossingsAt (w := w)).mp hj
    rcases hpos with rfl | rfl
    · have hout : w.outgoingSlot 0 (strand i) = 2 := outgoingSlot_strand w 0
      simpa only [w, hout, List.length_cons] using
        (edgePair_closure_cons_cons_two v i ε (-ε)).trans hm₀₂.symm
    · have hout : w.outgoingSlot 0 (strandSucc i) = 1 := outgoingSlot_strandSucc w 0
      simpa only [w, hout, List.length_cons] using
        (edgePair_closure_cons_cons_one v i ε (-ε)).trans hm₀₁.symm
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · have hpos : p = strand i ∨ p = strandSucc i := by
        simpa [w] using (mem_crossingsAt (w := w)).mp hj
      rcases hpos with rfl | rfl
      · have h := edgePair_closure_cons_cons_outgoingSlot_one_of_nil v i ε (-ε)
          (Or.inl rfl) hp₀
        have hout : w.outgoingSlot 1 (strand i) = 2 := outgoingSlot_strand w 1
        have hin : w.incomingSlot 0 (strand i) = 3 := incomingSlot_strand w 0
        dsimp only [w] at hin hout
        simp only [crossing_closure, hin, List.length_cons] at h
        simpa only [w, hout, List.length_cons, Fin.succ_zero_eq_one] using h.trans hm₁₂.symm
      · have h := edgePair_closure_cons_cons_outgoingSlot_one_of_nil v i ε (-ε)
          (Or.inr rfl) hq₀
        have hout : w.outgoingSlot 1 (strandSucc i) = 1 := outgoingSlot_strandSucc w 1
        have hin : w.incomingSlot 0 (strandSucc i) = 0 := incomingSlot_strandSucc w 0
        dsimp only [w] at hin hout
        simp only [crossing_closure, hin, List.length_cons] at h
        simpa only [w, hout, List.length_cons, Fin.succ_zero_eq_one] using h.trans hm₁₁.symm
    · have hjold : j ∈ v.crossingsAt p := by
        simpa [w] using (mem_crossingsAt (w := w)).mp hj
      have hletter : w[j.succ.succ.val] = v[j.val] := by simp [w]
      rw [outgoingSlot_congr hletter p]
      -- Every old crossing lies on an unaffected position, so its arc is preserved.
      exact readTwoCircleDiagram_edgePair_old v i ε hp₀ hq₀ D hD hjold

private theorem readTwoCircleDiagram_orientation :
    (readClasp (twoCircleDiagram v ε D)).orientation =
      (closure ((i, ε) :: (i, -ε) :: v)).orientation := by
  funext x
  obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv (v.length + 2)).surjective x
  have hori : (closure ((i, ε) :: (i, -ε) :: v)).orientation
      (crossingSlotEquiv (v.length + 2) (j, s)) = decide (s = 1 ∨ s = 2) := by
    simpa only [List.length_cons] using
      orientation_closure ((i, ε) :: (i, -ε) :: v) j s
  rw [hori]
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
  · have h := claspHalf_first v.length (s + 1)
    simp only [add_sub_cancel_right] at h
    rw [← h]
    simp only [readClasp, OrientedPDCode.rotateCrossing_orientation,
      OrientedPDCode.relabel_orientation, Equiv.symm_apply_apply, twoCircleDiagram,
      OrientedPDCode.adjoinTwoCircleClasp_def]
    rw [← unionFirst, OrientedPDCode.orientation_disjointUnion_inr]
    rw [OrientedPDCode.orientation_twoCircleClasp]
    fin_cases s <;> simp
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · have h := claspHalf_second v.length (s + 1)
      simp only [add_sub_cancel_right] at h
      rw [Fin.succ_zero_eq_one, ← h]
      simp only [readClasp, OrientedPDCode.rotateCrossing_orientation,
        OrientedPDCode.relabel_orientation, Equiv.symm_apply_apply, twoCircleDiagram,
        OrientedPDCode.adjoinTwoCircleClasp_def]
      rw [← unionSecond, OrientedPDCode.orientation_disjointUnion_inr]
      rw [OrientedPDCode.orientation_twoCircleClasp]
      fin_cases s <;> simp
    · rw [← claspHalf_old_crossing]
      simp only [readClasp, OrientedPDCode.rotateCrossing_orientation,
        OrientedPDCode.relabel_orientation, Equiv.symm_apply_apply, twoCircleDiagram,
        OrientedPDCode.adjoinTwoCircleClasp_def]
      rw [← unionOld, OrientedPDCode.orientation_disjointUnion_inl]
      simp [twoCircleCore_orientation v D hD]

include hp₀ hq₀ in
private theorem readTwoCircleDiagram_eq :
    readClasp (twoCircleDiagram v ε D) = closure ((i, ε) :: (i, -ε) :: v) := by
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · ext x
      obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv (v.length + 2)).surjective x
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · simp [readClasp, twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def,
          disjointUnion_halfEdge, twoCircleCore_halfEdge v D hD]
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · simp [readClasp, twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def,
            disjointUnion_halfEdge, twoCircleCore_halfEdge v D hD]
        · simp [readClasp, twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def,
            disjointUnion_halfEdge, twoCircleCore_halfEdge v D hD, Fin.ext_iff]
    · exact (readTwoCircleDiagram_edgePair v i ε hp₀ hq₀ D hD).symm
    · rw [← OrientedPDCode.card_crossinglessComponents,
        ← OrientedPDCode.card_crossinglessComponents]
      simp [readClasp, twoCircleDiagram,
        twoCircleCore_crossinglessComponents v i ε hp₀ hq₀ D hD]
    · have hfirst : (Fin.last v.length).castSucc = Fin.natAdd v.length (0 : Fin 2) := by
        apply Fin.ext
        simp
      have hsecond : Fin.last (v.length + 1) = Fin.natAdd v.length (1 : Fin 2) :=
        Fin.natAdd_last.symm
      funext j
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · rcases Int.units_eq_one_or ε with rfl | rfl <;>
          simp [readClasp, twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def, hfirst]
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · rcases Int.units_eq_one_or ε with rfl | rfl <;>
            simp [readClasp, twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def, hsecond]
        · have hj : j.castSucc.castSucc = Fin.castAdd 2 j := Fin.castSucc_castAdd j
          simp [readClasp, twoCircleDiagram, OrientedPDCode.adjoinTwoCircleClasp_def,
            twoCircleCore_overPair v D hD, hj, Fin.ext_iff]
  · exact readTwoCircleDiagram_orientation v i ε D hD
  · simp [readClasp, twoCircleDiagram,
        twoCircleCore_crossinglessComponents v i ε hp₀ hq₀ D hD]

omit D hD in
include hp₀ hq₀ in
/-- Inserting inverse letters on two crossing-free positions is a Reidemeister-II move
between their two circles, even in the presence of arbitrary other crossings. -/
theorem reidemeisterEquiv_closure_cons_cons_freeCancel_of_crossingsAt_eq_nil :
    OrientedPDCode.ReidemeisterEquiv v.closure (closure ((i, ε) :: (i, -ε) :: v)) := by
  have hc := crossinglessComponents_closure_insert_pair ([] : BraidWord n) v i ε (-ε)
  simp only [List.nil_append, hp₀, hq₀, ite_true, Multiset.replicate_one] at hc
  rw [Multiset.add_comm _ {true}, Multiset.singleton_add,
    Multiset.add_comm _ {true}, Multiset.singleton_add] at hc
  have hmem : true ∈ v.closure.crossinglessComponents := by
    rw [← hc]
    simp
  obtain ⟨D₁, hD₁⟩ := OrientedPDCode.exists_eq_adjoinCircle_of_mem hmem
  have hcircles := congrArg OrientedPDCode.crossinglessComponents hD₁
  rw [← hc] at hcircles
  simp only [OrientedPDCode.crossinglessComponents_adjoinCircle,
    Multiset.cons_inj_right] at hcircles
  have hmem₁ : true ∈ D₁.crossinglessComponents := by
    rw [← hcircles]
    simp
  obtain ⟨D, hD⟩ := OrientedPDCode.exists_eq_adjoinCircle_of_mem hmem₁
  have hcore : (D.adjoinCircle true).adjoinCircle true = v.closure := by
    rw [← hD, ← hD₁]
  rw [← readTwoCircleDiagram_eq v i ε hp₀ hq₀ D hcore, ← hcore]
  exact (OrientedPDCode.reidemeisterEquiv_adjoinTwoCircleClasp _ true true _).trans
    ((OrientedPDCode.reidemeisterEquiv_relabel _ _ _).trans
      ((OrientedPDCode.reidemeisterEquiv_rotateCrossing _ 0).trans
        (OrientedPDCode.reidemeisterEquiv_rotateCrossing _ 1)))

end TwoCircles

/-- Inserting inverse letters anywhere in a word gives Reidemeister equivalent closures
when both participating positions are crossing-free in the original word. -/
theorem reidemeisterEquiv_closure_append_cons_cons_freeCancel_of_crossingsAt_eq_nil
    (u v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)
    (hp : (u ++ v).crossingsAt (strand i) = [])
    (hq : (u ++ v).crossingsAt (strandSucc i) = []) :
    OrientedPDCode.ReidemeisterEquiv (closure (u ++ v))
      (closure (u ++ (i, ε) :: (i, -ε) :: v)) := by
  have hp' : (v ++ u).crossingsAt (strand i) = [] := by
    simpa only [crossingsAt_append_eq_nil_iff, and_comm] using hp
  have hq' : (v ++ u).crossingsAt (strandSucc i) = [] := by
    simpa only [crossingsAt_append_eq_nil_iff, and_comm] using hq
  have hleft := reidemeisterEquiv_closure_rotate (u ++ v) u.length
  have hright := reidemeisterEquiv_closure_rotate (u ++ (i, ε) :: (i, -ε) :: v) u.length
  rw [List.rotate_append_length_eq] at hleft hright
  simp only [List.cons_append] at hright
  exact hleft.trans
    ((reidemeisterEquiv_closure_cons_cons_freeCancel_of_crossingsAt_eq_nil
      (v ++ u) i ε hp' hq').trans hright.symm)

end TauCeti.BraidWord
