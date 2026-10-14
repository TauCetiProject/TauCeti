/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.DoubleCrossing.Basic

/-!
# External arcs of a pair of consecutive braid crossings

Prepending two letters with the same generator index cuts the closing arc on each affected
position. The old first crossing now receives its incoming arc from the second new crossing,
and the first new crossing receives its incoming arc from the old last crossing. The other
incoming arcs at old crossings are unchanged. If the position had no old crossing, the external
arc instead joins the second new crossing back to the first.

Together with the internal arcs and the old outgoing arcs in `DoubleCrossing.Basic`, these
formulas describe every arc incident to the inserted pair and every arc at an old crossing.
They are the external matching data for identifying an inverse pair with a Reidemeister-II
clasp. Both signs are arbitrary here; the inverse-pair condition concerns crossing data,
rather than this arc matching.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1 (Reidemeister-II moves).
-/

public section

namespace TauCeti.BraidWord

open BraidGroup PDCode

variable {n : ℕ} (v : BraidWord n) (i : Fin (n - 1)) (ε η : ℤˣ)

/-- On an affected position, the old first crossing is preceded by the second inserted
crossing; every other old crossing retains its old predecessor, shifted by two. -/
theorem nextCrossing_symm_cons_cons_of_mem {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) {j : Fin v.length} (hj : j ∈ v.crossingsAt p) :
    (nextCrossing ((i, ε) :: (i, η) :: v) p).symm j.succ.succ =
      if j = (v.crossingsAt p).head (List.ne_nil_of_mem hj) then 1
      else ((v.nextCrossing p).symm j).succ.succ := by
  let w : BraidWord n := (i, ε) :: (i, η) :: v
  apply (w.nextCrossing p).injective
  rw [Equiv.apply_symm_apply]
  split_ifs with h
  · rw [nextCrossing_cons_cons_one_of_ne_nil v i ε η hp (List.ne_nil_of_mem hj), ← h]
  · have hprev := v.nextCrossing_symm_mem_crossingsAt_iff.mpr hj
    rw [nextCrossing_cons_cons_of_mem v i ε η hp hprev, Equiv.apply_symm_apply]
    simp only [h, ite_false]

/-- On an affected position, the incoming arc at an old crossing is unchanged except at the
old first crossing, which now receives the outgoing arc of the second inserted crossing.
The old slots are expressed using the original braid word. -/
theorem edgePair_closure_cons_cons_incomingSlot_of_mem {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) {j : Fin v.length} (hj : j ∈ v.crossingsAt p) :
    let w : BraidWord n := (i, ε) :: (i, η) :: v
    w.closure.edgePair.val (w.closure.crossing j.succ.succ (v.incomingSlot j p)) =
      if j = (v.crossingsAt p).head (List.ne_nil_of_mem hj) then
        w.closure.crossing 1 (w.outgoingSlot 1 p)
      else w.closure.crossing ((v.nextCrossing p).symm j).succ.succ
        (v.outgoingSlot ((v.nextCrossing p).symm j) p) := by
  dsimp only
  let w : BraidWord n := (i, ε) :: (i, η) :: v
  have hletter (k : Fin v.length) : w[k.succ.succ.val] = v[k.val] := by simp [w]
  have hmem : j.succ.succ ∈ w.crossingsAt p := by
    apply (mem_crossingsAt (w := w) (j := j.succ.succ)).mpr
    rw [hletter]
    exact (mem_crossingsAt (w := v)).mp hj
  rw [← incomingSlot_congr (hletter j) p, edgePair_closure_incomingSlot w hmem,
    nextCrossing_symm_cons_cons_of_mem v i ε η hp hj]
  split_ifs
  · rfl
  · rw [outgoingSlot_congr (hletter ((v.nextCrossing p).symm j)) p]

/-- If an affected position had no crossing, the external arc leaving the second inserted
crossing enters the first inserted crossing on the same position. -/
theorem edgePair_closure_cons_cons_outgoingSlot_one_of_nil {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) (hv : v.crossingsAt p = []) :
    let w : BraidWord n := (i, ε) :: (i, η) :: v
    w.closure.edgePair.val (w.closure.crossing 1 (w.outgoingSlot 1 p)) =
      w.closure.crossing 0 (w.incomingSlot 0 p) := by
  dsimp only
  let w : BraidWord n := (i, ε) :: (i, η) :: v
  have hmem : (1 : Fin w.length) ∈ w.crossingsAt p := by
    rw [crossingsAt_cons_cons_same_index, ite_eq_left hp]
    simp
  rw [edgePair_closure_outgoingSlot w hmem, nextCrossing_cons_cons_one_of_nil v i ε η hp hv]

/-- If an affected position already had crossings, the external arc leaving the second
inserted crossing enters the old first crossing, with its original incoming slot. -/
theorem edgePair_closure_cons_cons_outgoingSlot_one_of_ne_nil {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) (hv : v.crossingsAt p ≠ []) :
    let w : BraidWord n := (i, ε) :: (i, η) :: v
    w.closure.edgePair.val (w.closure.crossing 1 (w.outgoingSlot 1 p)) =
      w.closure.crossing ((v.crossingsAt p).head hv).succ.succ
        (v.incomingSlot ((v.crossingsAt p).head hv) p) := by
  dsimp only
  let w : BraidWord n := (i, ε) :: (i, η) :: v
  have hmem : (1 : Fin w.length) ∈ w.crossingsAt p := by
    rw [crossingsAt_cons_cons_same_index, ite_eq_left hp]
    simp
  have hletter (k : Fin v.length) : w[k.succ.succ.val] = v[k.val] := by simp [w]
  rw [edgePair_closure_outgoingSlot w hmem,
    nextCrossing_cons_cons_one_of_ne_nil v i ε η hp hv,
    incomingSlot_congr (hletter ((v.crossingsAt p).head hv)) p]

/-- If an affected position had no crossing, the incoming external arc at the first inserted
crossing comes from the second inserted crossing. -/
theorem edgePair_closure_cons_cons_incomingSlot_zero_of_nil {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) (hv : v.crossingsAt p = []) :
    let w : BraidWord n := (i, ε) :: (i, η) :: v
    w.closure.edgePair.val (w.closure.crossing 0 (w.incomingSlot 0 p)) =
      w.closure.crossing 1 (w.outgoingSlot 1 p) := by
  exact (closure ((i, ε) :: (i, η) :: v)).edgePair.apply_eq_of_apply_eq
    (edgePair_closure_cons_cons_outgoingSlot_one_of_nil v i ε η hp hv)

/-- If an affected position already had crossings, the incoming external arc at the first
inserted crossing comes from the old last crossing, with its original outgoing slot. -/
theorem edgePair_closure_cons_cons_incomingSlot_zero_of_ne_nil {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) (hv : v.crossingsAt p ≠ []) :
    let w : BraidWord n := (i, ε) :: (i, η) :: v
    w.closure.edgePair.val (w.closure.crossing 0 (w.incomingSlot 0 p)) =
      w.closure.crossing ((v.crossingsAt p).getLast hv).succ.succ
        (v.outgoingSlot ((v.crossingsAt p).getLast hv) p) := by
  dsimp only
  let w : BraidWord n := (i, ε) :: (i, η) :: v
  have hlast : v.nextCrossing p ((v.crossingsAt p).getLast hv) =
      (v.crossingsAt p).head hv := by
    rw [nextCrossing_def]
    obtain ⟨j, js, heq⟩ := List.exists_cons_of_ne_nil hv
    simp only [heq, List.formPerm_apply_getLast, List.head_cons]
  have hout : w.closure.edgePair.val
      (w.closure.crossing ((v.crossingsAt p).getLast hv).succ.succ
        (v.outgoingSlot ((v.crossingsAt p).getLast hv) p)) =
      w.closure.crossing 0 (w.incomingSlot 0 p) := by
    simpa only [hp, hlast, true_and, ite_true] using
      edgePair_closure_cons_cons_of_mem v i ε η (List.getLast_mem hv)
  exact w.closure.edgePair.apply_eq_of_apply_eq hout

end TauCeti.BraidWord
