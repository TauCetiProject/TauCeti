/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.ClosingArcs
public import TauCeti.KnotTheory.PDCode.Jones.Skein
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence
import TauCeti.Data.Fin.Basic
import TauCeti.Data.List.Rotate

/-!
# A braid letter as a crossing insertion

Adding a letter `σᵢ ^ ε` at the bottom of a braid word `v` adds one crossing to its closure. When
both strand positions `i` and `i + 1` of the letter already meet crossings of `v`, the closure of
`(i, ε) :: v` is a crossing inserted, by `TauCeti.OrientedPDCode.insertCrossing`, into the code
obtained from the closure of `v` by exchanging the ends of the two closing arcs on these
positions, up to renaming crossings and half-edges
(`TauCeti.BraidWord.closure_cons_eq_relabel_insertCrossing`). Smoothing the new crossing in the
orientation-preserving way restores the two closing arcs, that is, the closure of `v`. This is the
diagrammatic content of the skein triple `σᵢ c`, `σᵢ⁻¹ c`, `c` of braids, and it gives the skein
relation of the writhe-normalized Kauffman bracket on braid closures
(`TauCeti.BraidWord.normalizedKauffmanBracket_closure_cons_skein`).

## Main definitions

* `TauCeti.BraidWord.swapClosingArcs`: the closure of `v` with the ends of the closing arcs on two
  adjacent positions exchanged.

## Main results

* `TauCeti.BraidWord.nextCrossing_cons_of_ne`, `TauCeti.BraidWord.nextCrossing_cons_zero` and
  `TauCeti.BraidWord.nextCrossing_cons_of_mem`: the successors along each strand position after
  adding a letter at the bottom.
* `TauCeti.BraidWord.closure_cons_eq_relabel_insertCrossing`: the closure of `(i, ε) :: v` is a
  crossing inserted into a reconnection of the closure of `v`.
* `TauCeti.BraidWord.normalizedKauffmanBracket_closure_cons_skein`: the skein relation
  `A⁴ ⟨σᵢ v⟩ - A⁻⁴ ⟨σᵢ⁻¹ v⟩ = (A⁻² - A²) ⟨v⟩` of the normalized bracket of braid closures.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3,
  Proposition 3.7.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup PDCode

variable {n : ℕ} (v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)

/-! ### Successors after adding a letter at the bottom -/

/-- On a position outside the new letter, every old successor is unchanged, after shifting
indices. -/
theorem nextCrossing_cons_of_ne {p : Fin n} (hp : p ≠ strand i) (hp' : p ≠ strandSucc i)
    (j : Fin v.length) :
    nextCrossing ((i, ε) :: v) p j.succ = (v.nextCrossing p j).succ := by
  rw [nextCrossing_def, crossingsAt_cons, ite_eq_right_iff.mpr fun h ↦ absurd h (by tauto),
    List.nil_append, nextCrossing_def]
  exact List.formPerm_map_apply (Fin.succ_injective _) _ j

/-- On a position of the new letter which already met crossings, the new crossing leads to the
old first crossing. -/
theorem nextCrossing_cons_zero {p : Fin n} (hp : p = strand i ∨ p = strandSucc i)
    (hv : v.crossingsAt p ≠ []) :
    DFunLike.coe (F := Equiv.Perm (Fin (v.length + 1)))
      (α := Fin (v.length + 1)) (β := fun _ ↦ Fin (v.length + 1))
      (nextCrossing ((i, ε) :: v) p) 0 = ((v.crossingsAt p).head hv).succ := by
  have hnd := (sortedLT_crossingsAt ((i, ε) :: v) p).nodup
  rw [crossingsAt_cons, ite_eq_left hp] at hnd
  obtain ⟨j, js, hj⟩ := List.exists_cons_of_ne_nil hv
  rw [nextCrossing_def, crossingsAt_cons, ite_eq_left hp]
  simp only [hj, List.map_cons, List.singleton_append, List.head_cons] at hnd ⊢
  exact List.formPerm_apply_head _ _ _ hnd

/-- An old crossing on a position of the new letter keeps its successor, except at the end of the
old cycle, where it now leads to the new crossing. -/
theorem nextCrossing_cons_of_mem {p : Fin n} (hp : p = strand i ∨ p = strandSucc i)
    {j : Fin v.length} (hj : j ∈ v.crossingsAt p) :
    nextCrossing ((i, ε) :: v) p j.succ =
      if v.nextCrossing p j = (v.crossingsAt p).head (List.ne_nil_of_mem hj) then 0
      else (v.nextCrossing p j).succ := by
  have hnd := (sortedLT_crossingsAt ((i, ε) :: v) p).nodup
  rw [crossingsAt_cons, ite_eq_left hp] at hnd
  have h := List.formPerm_append_apply_of_mem_right hnd (List.mem_map.mpr ⟨j, hj, rfl⟩)
  rw [nextCrossing_def, crossingsAt_cons, ite_eq_left hp]
  simpa only [List.formPerm_map_apply (Fin.succ_injective _), List.head_map, List.singleton_append,
    List.head_cons, Fin.succ_inj, nextCrossing_def] using h

/-- Every arc leaving an old crossing is retained, except the closing arc on a position of the new
letter, which now enters the new crossing. -/
theorem edgePair_closure_cons_of_mem {p : Fin n} {j : Fin v.length}
    (hj : j ∈ v.crossingsAt p) :
    (closure ((i, ε) :: v)).edgePair.val
        ((closure ((i, ε) :: v)).crossing j.succ (v.outgoingSlot j p)) =
      if (p = strand i ∨ p = strandSucc i) ∧
          v.nextCrossing p j = (v.crossingsAt p).head (List.ne_nil_of_mem hj) then
        (closure ((i, ε) :: v)).crossing 0 (incomingSlot ((i, ε) :: v) 0 p)
      else (closure ((i, ε) :: v)).crossing (v.nextCrossing p j).succ
        (v.incomingSlot (v.nextCrossing p j) p) := by
  let w : BraidWord n := (i, ε) :: v
  have hletter (k : Fin v.length) : w[k.succ.val] = v[k.val] := by simp [w]
  have hout := outgoingSlot_congr (hletter j) p
  have hmem : j.succ ∈ w.crossingsAt p := by
    apply (mem_crossingsAt (w := w) (j := j.succ)).mpr
    rw [hletter]
    exact (mem_crossingsAt (w := v)).mp hj
  have hnext : w.nextCrossing p j.succ =
      if (p = strand i ∨ p = strandSucc i) ∧
          v.nextCrossing p j = (v.crossingsAt p).head (List.ne_nil_of_mem hj) then 0
      else (v.nextCrossing p j).succ := by
    by_cases hp : p = strand i ∨ p = strandSucc i
    · simpa only [hp, true_and] using nextCrossing_cons_of_mem v i ε hp hj
    · simpa only [hp, false_and, ite_false] using
        nextCrossing_cons_of_ne v i ε (not_or.mp hp).1 (not_or.mp hp).2 j
  refine (congrArg w.closure.edgePair.val
    (congrArg (w.closure.crossing j.succ) hout.symm)).trans
      ((edgePair_closure_outgoingSlot w hmem).trans ?_)
  rw [hnext]
  split_ifs
  · rfl
  · rw [incomingSlot_congr (hletter (v.nextCrossing p j)) p]

/-- The arc leaving the new crossing upwards on a position which already met crossings enters the
old first crossing on that position. -/
theorem edgePair_closure_cons_outgoingSlot_zero {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) (hv : v.crossingsAt p ≠ []) :
    (closure ((i, ε) :: v)).edgePair.val
        ((closure ((i, ε) :: v)).crossing 0 (outgoingSlot ((i, ε) :: v) 0 p)) =
      (closure ((i, ε) :: v)).crossing ((v.crossingsAt p).head hv).succ
        (v.incomingSlot ((v.crossingsAt p).head hv) p) := by
  let w : BraidWord n := (i, ε) :: v
  have hmem : (0 : Fin w.length) ∈ w.crossingsAt p :=
    (mem_crossingsAt (w := w) (j := 0)).mpr (by simpa [w] using hp)
  rw [edgePair_closure_outgoingSlot w hmem, nextCrossing_cons_zero v i ε hp hv,
    incomingSlot_congr (w := v) (w' := w) (j := ((v.crossingsAt p).head hv).succ)
      (i := (v.crossingsAt p).head hv) (by simp [w]) p]

/-! ### The closure as a crossing insertion -/

section Insertion

variable (hp : v.crossingsAt (strand i) ≠ []) (hq : v.crossingsAt (strandSucc i) ≠ [])

/-- The closure of `v` with the ends of its closing arcs on the positions `i` and `i + 1`
exchanged: the closing arc leaving position `i + 1` enters the first crossing on position `i`,
and the closing arc leaving position `i` enters the first crossing on position `i + 1`. A crossing
inserted between these two arcs is the closure of a word with one more letter at the bottom. -/
def swapClosingArcs : OrientedPDCode v.length :=
  v.closure.reconnect (v.closingHalfEdge (strandSucc i) hq)
    (v.closure.edgePair.val (v.closingHalfEdge (strand i) hp)) (by
      simp only [OrientedPDCode.orientation_edgePair, orientation_closingHalfEdge, Bool.not_true,
        Bool.not_false])

/-- As an unoriented code, `swapClosingArcs` is the closure with the two closing arcs
reconnected. -/
@[simp]
theorem toPDCode_swapClosingArcs :
    (v.swapClosingArcs i hp hq).toPDCode =
      v.closure.toPDCode.reconnect (v.closingHalfEdge (strandSucc i) hq)
        (v.closure.edgePair.val (v.closingHalfEdge (strand i) hp)) := by
  simp [swapClosingArcs]

/-- Exchanging the closing arcs keeps the crossing-free circles. -/
@[simp]
theorem crossinglessComponents_swapClosingArcs :
    (v.swapClosingArcs i hp hq).crossinglessComponents = v.closure.crossinglessComponents := by
  simp [swapClosingArcs]

/-- The arcs of `swapClosingArcs` are those of the closure with the two closing arcs reconnected. -/
theorem edgePair_swapClosingArcs :
    (v.swapClosingArcs i hp hq).edgePair =
      v.closure.edgePair.reconnect (v.closingHalfEdge (strandSucc i) hq)
        (v.closure.edgePair.val (v.closingHalfEdge (strand i) hp)) := by
  simp [swapClosingArcs]

/-- Exchanging the closing arcs keeps every half-edge direction. -/
@[simp]
theorem orientation_swapClosingArcs (x : Fin (4 * v.length)) :
    (v.swapClosingArcs i hp hq).orientation x = v.closure.orientation x := by
  simp [swapClosingArcs]

/-- In `swapClosingArcs`, the closing half-edge on position `i + 1` is joined to the first
crossing on position `i`. -/
theorem edgePair_swapClosingArcs_closingHalfEdge :
    (v.swapClosingArcs i hp hq).edgePair.val (v.closingHalfEdge (strandSucc i) hq) =
      v.closure.edgePair.val (v.closingHalfEdge (strand i) hp) := by
  rw [edgePair_swapClosingArcs, PerfectMatching.reconnect_val_self
    (v.closingHalfEdge_ne_edgePair_closingHalfEdge _ _ hp hq).symm]

/-- In `swapClosingArcs`, the first crossing on position `i + 1` is joined to the closing
half-edge on position `i`. -/
theorem edgePair_swapClosingArcs_edgePair_closingHalfEdge :
    (v.swapClosingArcs i hp hq).edgePair.val
        (v.closure.edgePair.val (v.closingHalfEdge (strandSucc i) hq)) =
      v.closingHalfEdge (strand i) hp := by
  rw [edgePair_swapClosingArcs, PerfectMatching.reconnect_val_val_self
    (v.closingHalfEdge_ne_edgePair_closingHalfEdge _ _ hp hq).symm,
    PerfectMatching.apply_apply]

/-- In `swapClosingArcs`, a half-edge pointing out of its crossing which is not a closing
half-edge on the positions `i` or `i + 1` keeps its partner. -/
theorem edgePair_swapClosingArcs_of_ne {x : Fin (4 * v.length)}
    (hx : v.closure.orientation x = true) (hxp : x ≠ v.closingHalfEdge (strand i) hp)
    (hxq : x ≠ v.closingHalfEdge (strandSucc i) hq) :
    (v.swapClosingArcs i hp hq).edgePair.val x = v.closure.edgePair.val x := by
  rw [edgePair_swapClosingArcs]
  refine PerfectMatching.reconnect_val_of_ne hxq
    (v.closure.ne_edgePair_of_orientation_eq (hx.trans (orientation_closingHalfEdge ..).symm)) ?_ ?_
  · exact v.closure.ne_edgePair_of_orientation_eq (hx.trans (orientation_closingHalfEdge ..).symm)
  · rwa [PerfectMatching.apply_apply]

/-- The two arcs of `swapClosingArcs` ending at the closing half-edge on position `i + 1` and at
its old partner are distinct, so a crossing can be inserted between them. -/
theorem edgePair_closingHalfEdge_ne_edgePair_swapClosingArcs :
    v.closure.edgePair.val (v.closingHalfEdge (strandSucc i) hq) ≠
      (v.swapClosingArcs i hp hq).edgePair.val (v.closingHalfEdge (strandSucc i) hq) := by
  rw [edgePair_swapClosingArcs_closingHalfEdge]
  exact fun h ↦ v.closingHalfEdge_ne hq hp (strand_ne_strandSucc i).symm
    (v.closure.edgePair.val.injective h)

/-- In `swapClosingArcs`, the closing half-edge on position `i + 1` and its old partner have
opposite orientations, so the crossing inserted between them is smoothed by an oriented
smoothing. -/
theorem orientation_xor_swapClosingArcs :
    ((v.swapClosingArcs i hp hq).orientation (v.closingHalfEdge (strandSucc i) hq) ^^
      (v.swapClosingArcs i hp hq).orientation
        (v.closure.edgePair.val (v.closingHalfEdge (strandSucc i) hq))) = true := by
  simp only [orientation_swapClosingArcs, OrientedPDCode.orientation_edgePair,
    orientation_closingHalfEdge, Bool.not_true, Bool.xor_false]

/-- The closure of `(i, ε) :: v` before renaming its crossings. -/
private abbrev insertLetter : OrientedPDCode (v.length + 1) :=
  (v.swapClosingArcs i hp hq).insertCrossing (v.closingHalfEdge (strandSucc i) hq)
    (v.closure.edgePair.val (v.closingHalfEdge (strandSucc i) hq)) (decide (ε = 1))
    (v.closure.edgePair.apply_ne _) (edgePair_closingHalfEdge_ne_edgePair_swapClosingArcs v i hp hq)

/-- An arc leaving an old crossing of the closure of `(i, ε) :: v` is the renamed arc of the
insertion at the same slot. -/
private theorem edgePair_insertLetter_old {j : Fin v.length} {p : Fin n}
    (hj : j ∈ v.crossingsAt p) :
    (closure ((i, ε) :: v)).edgePair.val
        (crossingSlotEquiv (v.length + 1) (j.succ, v.outgoingSlot j p)) =
      crossingBlockEquiv (finRotate (v.length + 1)) ((insertLetter v i ε hp hq).edgePair.val
        (halfEdgeSuccEquiv v.length (.inl (crossingSlotEquiv v.length
          (j, v.outgoingSlot j p))))) := by
  have hqe := edgePair_closingHalfEdge_ne_edgePair_swapClosingArcs v i hp hq
  set x := v.closure.crossing j (v.outgoingSlot j p) with hxdef
  have hx : v.closure.orientation x = true := by
    rcases v.outgoingSlot_eq_one_or_two j p with hs | hs <;> simp [x, hs]
  have hlhs := edgePair_closure_cons_of_mem v i ε hj
  simp only [crossing_closure, List.length_cons] at hlhs hxdef
  refine hlhs.trans ?_
  rw [← hxdef]
  by_cases hxp : x = v.closingHalfEdge (strand i) hp
  · -- The closing arc on position `i` now enters the new crossing at slot `3`.
    obtain ⟨rfl, rfl⟩ := (crossing_outgoingSlot_eq_closingHalfEdge_iff v hj hp).mp hxp
    rw [ite_eq_left ⟨Or.inl rfl, nextCrossing_getLast_crossingsAt v _ hp⟩, hxp,
      ← edgePair_swapClosingArcs_edgePair_closingHalfEdge v i hp hq,
      OrientedPDCode.toPDCode_insertCrossing, PDCode.insertCrossing_edgePair_inl_edgePair_right _
        (v.closure.edgePair.apply_ne _) hqe, crossingBlockEquiv_finRotate_halfEdgeSuccEquiv_inr]
    simpa using incomingSlot_strand ((i, ε) :: v) 0
  by_cases hxq : x = v.closingHalfEdge (strandSucc i) hq
  · -- The closing arc on position `i + 1` now enters the new crossing at slot `0`.
    obtain ⟨rfl, rfl⟩ := (crossing_outgoingSlot_eq_closingHalfEdge_iff v hj hq).mp hxq
    rw [ite_eq_left ⟨Or.inr rfl, nextCrossing_getLast_crossingsAt v _ hq⟩, hxq,
      OrientedPDCode.toPDCode_insertCrossing, PDCode.insertCrossing_edgePair_inl_self _
        (v.closure.edgePair.apply_ne _) hqe, crossingBlockEquiv_finRotate_halfEdgeSuccEquiv_inr]
    simpa using incomingSlot_strandSucc ((i, ε) :: v) 0
  -- Every other arc leaving an old crossing keeps its old successor.
  have hc : ¬((p = strand i ∨ p = strandSucc i) ∧
      v.nextCrossing p j = (v.crossingsAt p).head (List.ne_nil_of_mem hj)) := by
    rintro ⟨hpos, hn⟩
    rcases hpos with rfl | rfl
    · refine hxp ((crossing_outgoingSlot_eq_closingHalfEdge_iff v hj hp).mpr ⟨rfl, ?_⟩)
      exact (v.nextCrossing (strand i)).injective (by simpa using hn)
    · refine hxq ((crossing_outgoingSlot_eq_closingHalfEdge_iff v hj hq).mpr ⟨rfl, ?_⟩)
      exact (v.nextCrossing (strandSucc i)).injective (by simpa using hn)
  have hin {y : Fin (4 * v.length)} (hy : v.closure.orientation y = true) :
      x ≠ v.closure.edgePair.val y :=
    v.closure.ne_edgePair_of_orientation_eq (hx.trans hy.symm)
  rw [ite_eq_right hc, OrientedPDCode.toPDCode_insertCrossing,
    PDCode.insertCrossing_edgePair_inl_of_ne _ hxq (hin (orientation_closingHalfEdge ..))
      (by rw [edgePair_swapClosingArcs_closingHalfEdge]
          exact hin (orientation_closingHalfEdge ..))
      (by rw [edgePair_swapClosingArcs_edgePair_closingHalfEdge]; exact hxp),
    edgePair_swapClosingArcs_of_ne v i hp hq hx hxp hxq]
  have hCx : v.closure.edgePair.val x =
      crossingSlotEquiv v.length (v.nextCrossing p j, v.incomingSlot (v.nextCrossing p j) p) := by
    simpa [x, crossing_closure] using edgePair_closure_outgoingSlot v hj
  rw [hCx, crossingBlockEquiv_finRotate_halfEdgeSuccEquiv_inl]

/-- An arc leaving the new crossing of the closure of `(i, ε) :: v` is the renamed arc of the
insertion at the same slot of the inserted crossing. -/
private theorem edgePair_insertLetter_new {p : Fin n} (hpos : p = strand i ∨ p = strandSucc i) :
    (closure ((i, ε) :: v)).edgePair.val
        (crossingSlotEquiv (v.length + 1) (0, outgoingSlot ((i, ε) :: v) 0 p)) =
      crossingBlockEquiv (finRotate (v.length + 1)) ((insertLetter v i ε hp hq).edgePair.val
        (halfEdgeSuccEquiv v.length (.inr (outgoingSlot ((i, ε) :: v) 0 p)))) := by
  have hqe := edgePair_closingHalfEdge_ne_edgePair_swapClosingArcs v i hp hq
  have hqp : v.closure.edgePair.val (v.closingHalfEdge (strandSucc i) hq) ≠
      v.closingHalfEdge (strandSucc i) hq := v.closure.edgePair.apply_ne _
  rcases hpos with rfl | rfl
  · -- The arc leaving upwards on position `i` enters the old first crossing on position `i`.
    have h0 := edgePair_closure_cons_outgoingSlot_zero v i ε (Or.inl rfl) hp
    have hs : outgoingSlot ((i, ε) :: v) 0 (strand i) = 2 := by
      simpa using outgoingSlot_strand ((i, ε) :: v) 0
    simp only [crossing_closure, List.length_cons, hs] at h0 ⊢
    rw [h0, OrientedPDCode.toPDCode_insertCrossing,
      PDCode.insertCrossing_edgePair_inr_two _ hqp hqe,
      edgePair_swapClosingArcs_closingHalfEdge, edgePair_closingHalfEdge, crossing_closure,
      crossingBlockEquiv_finRotate_halfEdgeSuccEquiv_inl]
  · -- The arc leaving upwards on position `i + 1` enters the old first crossing on `i + 1`.
    have h0 := edgePair_closure_cons_outgoingSlot_zero v i ε (Or.inr rfl) hq
    have hs : outgoingSlot ((i, ε) :: v) 0 (strandSucc i) = 1 := by
      simpa using outgoingSlot_strandSucc ((i, ε) :: v) 0
    simp only [crossing_closure, List.length_cons, hs] at h0 ⊢
    rw [h0, OrientedPDCode.toPDCode_insertCrossing,
      PDCode.insertCrossing_edgePair_inr_one _ hqp hqe, edgePair_closingHalfEdge,
      crossing_closure, crossingBlockEquiv_finRotate_halfEdgeSuccEquiv_inl]

include hp hq in
private theorem crossinglessComponentCount_closure_cons :
    (closure ((i, ε) :: v)).crossinglessComponentCount = v.closure.crossinglessComponentCount := by
  rw [crossinglessComponentCount_closure, crossinglessComponentCount_closure]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, crossingsAt_cons_eq_nil_iff]
  constructor
  · exact fun h ↦ h.1
  · rintro h
    exact ⟨h, fun hp' ↦ hp (hp' ▸ h), fun hq' ↦ hq (hq' ▸ h)⟩

/-- **A letter added at the bottom is an inserted crossing.** If both positions of the letter
`(i, ε)` meet crossings of `v`, the closure of `(i, ε) :: v` is obtained from `swapClosingArcs`, the
closure of `v` with the ends of its closing arcs on these positions exchanged, by inserting a
crossing between the closing arc on position `i + 1` and the arc ending at its old partner, with the
over-strand of the letter. The new crossing is the last one of the insertion and the first of the
closure, so crossings and half-edges are renamed cyclically. -/
theorem closure_cons_eq_relabel_insertCrossing :
    closure ((i, ε) :: v) =
      ((v.swapClosingArcs i hp hq).insertCrossing (v.closingHalfEdge (strandSucc i) hq)
          (v.closure.edgePair.val (v.closingHalfEdge (strandSucc i) hq)) (decide (ε = 1))
          (v.closure.edgePair.apply_ne _)
          (edgePair_closingHalfEdge_ne_edgePair_swapClosingArcs v i hp hq)).relabel
        (crossingBlockEquiv (finRotate (v.length + 1))) (finRotate (v.length + 1)) := by
  have hcount := crossinglessComponentCount_closure_cons v i ε hp hq
  have hrotSucc (k : Fin v.length) : (finRotate (v.length + 1)).symm k.succ =
      k.castSucc := (finRotate _).symm_apply_eq.mpr (Fin.finRotate_castSucc k).symm
  have hrotZero : (finRotate (v.length + 1)).symm 0 = Fin.last v.length :=
    (finRotate _).symm_apply_eq.mpr finRotate_last.symm
  -- Compare the two codes field by field. In each field, crossing `0` of the closure is the
  -- inserted crossing, and crossing `k + 1` is the old crossing `k`.
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · -- Both codes list the half-edges of each crossing in slot order.
      rw [halfEdge_closure]
      refine Equiv.ext fun h ↦ ?_
      obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv _).surjective h
      simp only [List.length_cons, OrientedPDCode.relabel_toPDCode, PDCode.relabel_halfEdge,
        Equiv.equivCongr_apply_apply, crossingBlockEquiv_symm,
        crossingBlockEquiv_apply_crossingSlotEquiv, Equiv.Perm.coe_one, id_eq]
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · rw [hrotZero, crossingSlotEquiv_succ_last,
          OrientedPDCode.toPDCode_insertCrossing, PDCode.insertCrossing_crossing_last,
          crossingBlockEquiv_finRotate_halfEdgeSuccEquiv_inr]
      · rw [hrotSucc, crossingSlotEquiv_succ_castSucc,
          OrientedPDCode.toPDCode_insertCrossing, PDCode.insertCrossing_crossing_castSucc,
          PDCode.crossing_apply, toPDCode_swapClosingArcs, PDCode.reconnect_halfEdge,
          halfEdge_closure, Equiv.Perm.coe_one, id_eq,
          crossingBlockEquiv_finRotate_halfEdgeSuccEquiv_inl]
    · -- A matching of a closure is determined by the arcs leaving crossings, which are
      -- `edgePair_insertLetter_new` and `edgePair_insertLetter_old`.
      refine edgePair_closure_eq_of_outgoingSlot _ fun j p hj ↦ ?_
      simp only [OrientedPDCode.relabel_toPDCode, PDCode.relabel_edgePair]
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · have hpos : p = strand i ∨ p = strandSucc i := by
          simpa using (mem_crossingsAt (w := (i, ε) :: v) (j := 0)).mp hj
        refine (edgePair_insertLetter_new v i ε hp hq hpos).trans ?_
        simp only [List.length_cons]
        rw [← crossingBlockEquiv_finRotate_halfEdgeSuccEquiv_inr,
          PerfectMatching.congr_val_apply_apply]
      · have hk : k ∈ v.crossingsAt p := by
          simpa using (mem_crossingsAt (w := (i, ε) :: v) (j := k.succ)).mp hj
        rw [outgoingSlot_congr (w := v) (w' := (i, ε) :: v) (j := k.succ) (i := k) (by simp) p]
        simp only [List.length_cons]
        refine (edgePair_insertLetter_old v i ε hp hq hk).trans ?_
        rw [← crossingBlockEquiv_finRotate_halfEdgeSuccEquiv_inl,
          PerfectMatching.congr_val_apply_apply]
    · -- The insertion keeps the crossing-free circles.
      simpa using hcount
    · -- The new crossing has the over-strand of the letter; old crossings keep theirs.
      funext j
      rw [overPair_closure, OrientedPDCode.relabel_toPDCode, PDCode.relabel_overPair,
        OrientedPDCode.toPDCode_insertCrossing]
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · rw [hrotZero, PDCode.insertCrossing_overPair_last]
        exact decide_eq_decide.mpr (by simp)
      · rw [hrotSucc, PDCode.insertCrossing_overPair_castSucc, toPDCode_swapClosingArcs,
          PDCode.reconnect_overPair, overPair_closure]
        simp
  · -- The new crossing takes the orientations of the two arcs it is inserted into; old
    -- half-edges keep theirs.
    have ho₁ := v.orientation_closingHalfEdge (strandSucc i) hq
    have ho₂ :
        v.closure.orientation (v.closure.edgePair.val (v.closingHalfEdge (strandSucc i) hq)) =
          false := by
      rw [OrientedPDCode.orientation_edgePair, ho₁, Bool.not_true]
    funext h
    obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv _).surjective h
    rw [orientation_closure]
    simp only [List.length_cons, OrientedPDCode.relabel_orientation, crossingBlockEquiv_symm,
      crossingBlockEquiv_apply_crossingSlotEquiv]
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · rw [hrotZero, crossingSlotEquiv_succ_last,
        OrientedPDCode.orientation_insertCrossing_inr, orientation_swapClosingArcs,
        orientation_swapClosingArcs, ho₁, ho₂]
      fin_cases s <;> rfl
    · rw [hrotSucc, crossingSlotEquiv_succ_castSucc,
        OrientedPDCode.orientation_insertCrossing_inl, orientation_swapClosingArcs,
        orientation_closure]
  · -- The crossing-free circles are those of the closure of `v`.
    rw [crossinglessComponents_closure, OrientedPDCode.relabel_crossinglessComponents,
      OrientedPDCode.crossinglessComponents_insertCrossing, crossinglessComponents_swapClosingArcs,
      crossinglessComponents_closure]
    congr 1
    simpa using hcount

/-- Smoothing the inserted crossing in the orientation-preserving way restores the two closing
arcs: the oriented smoothing of `swapClosingArcs` at the closing half-edge on position `i + 1` and
its old partner is the closure of `v`. -/
theorem orientedSmoothing_swapClosingArcs :
    (v.swapClosingArcs i hp hq).orientedSmoothing (v.closingHalfEdge (strandSucc i) hq)
        (v.closure.edgePair.val (v.closingHalfEdge (strandSucc i) hq)) = v.closure := by
  apply OrientedPDCode.ext
  · rw [OrientedPDCode.toPDCode_orientedSmoothing, orientation_xor_swapClosingArcs, Bool.cond_true,
      toPDCode_swapClosingArcs]
    apply PDCode.ext
    · simp
    · simp only [PDCode.reconnect_edgePair]
      exact PerfectMatching.reconnect_reconnect_val
    · simp
    · simp
  · funext x
    simp
  · simp

include hp hq in
/-- **The skein relation of the normalized Kauffman bracket on braid closures.** If both positions
of `i` meet crossings of `v`, then
`A⁴ ⟨σᵢ v⟩ - A⁻⁴ ⟨σᵢ⁻¹ v⟩ = (A⁻² - A²) ⟨v⟩` for the writhe-normalized brackets of the closures of
`(i, 1) :: v`, `(i, -1) :: v` and `v`. -/
theorem normalizedKauffmanBracket_closure_cons_skein {R : Type*} [CommRing R] (a : Rˣ) :
    (a : R) ^ 4 * (closure ((i, 1) :: v)).normalizedKauffmanBracket a -
        ((a⁻¹ : Rˣ) : R) ^ 4 * (closure ((i, -1) :: v)).normalizedKauffmanBracket a =
      (((a⁻¹ : Rˣ) : R) ^ 2 - (a : R) ^ 2) * v.closure.normalizedKauffmanBracket a := by
  have hqe := edgePair_closingHalfEdge_ne_edgePair_swapClosingArcs v i hp hq
  have h := OrientedPDCode.normalizedKauffmanBracket_insertCrossing_skein
    (v.swapClosingArcs i hp hq) (v.closingHalfEdge (strandSucc i) hq)
    (v.closure.edgePair.val (v.closingHalfEdge (strandSucc i) hq))
    (v.closure.edgePair.apply_ne _) hqe a
  simp only [orientation_xor_swapClosingArcs, Bool.not_true, orientedSmoothing_swapClosingArcs]
    at h
  rw [closure_cons_eq_relabel_insertCrossing v i 1 hp hq,
    closure_cons_eq_relabel_insertCrossing v i (-1) hp hq,
    ← (OrientedPDCode.reidemeisterEquiv_relabel _ _ _).normalizedKauffmanBracket_eq,
    ← (OrientedPDCode.reidemeisterEquiv_relabel _ _ _).normalizedKauffmanBracket_eq]
  convert h using 4 <;> simp

end Insertion


end TauCeti.BraidWord
