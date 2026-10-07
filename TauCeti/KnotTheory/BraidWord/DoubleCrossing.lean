/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode
import TauCeti.Data.List.Rotate

/-!
# Successors after inserting two crossings on the same strand positions

Prepending two letters with the same generator index inserts two consecutive crossings on
both affected strand positions. On each position, the old last crossing now leads to the
first inserted crossing, the first inserted crossing leads to the second, and the second
leads back to the old first crossing. If the position previously carried no crossing, the two
inserted crossings instead form their own cycle. All other positions keep their successors.

These formulas identify the arcs that must be reconnected when removing an inverse pair
from a braid closure by the second Reidemeister move. In particular, skipping the inserted
pair recovers the original successor on every old crossing. The successor calculations
allow arbitrary signs on the two letters; only the over-strand calculation requires them
to be opposite. This file does not identify the resulting whole diagram with a Reidemeister
move, which also requires the external arcs and crossing-free components to be matched.

The list calculations reuse `List.formPerm_map_apply` and the two append formulas from
`TauCeti.Data.List.Rotate`.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1, the second Reidemeister move.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup PDCode

variable {n : ℕ} (v : BraidWord n) (i : Fin (n - 1)) (ε η : ℤˣ)

/-- On an unaffected position, every old successor is unchanged, after shifting indices. -/
theorem nextCrossing_cons_cons_of_ne {p : Fin n}
    (hp : p ≠ strand i) (hp' : p ≠ strandSucc i) (j : Fin v.length) :
    nextCrossing ((i, ε) :: (i, η) :: v) p j.succ.succ =
      (v.nextCrossing p j).succ.succ := by
  rw [nextCrossing_def, crossingsAt_cons_cons_same_index, ite_eq_right (not_or.mpr ⟨hp, hp'⟩),
    List.nil_append]
  rw [nextCrossing_def]
  exact List.formPerm_map_apply (f := fun j : Fin v.length => j.succ.succ)
    ((Fin.succ_injective _).comp (Fin.succ_injective _)) _ j

/-- On either affected position, the first inserted crossing leads to the second. -/
@[simp]
theorem nextCrossing_cons_cons_zero {p : Fin n} (hp : p = strand i ∨ p = strandSucc i) :
    DFunLike.coe (F := Equiv.Perm (Fin (v.length + 1 + 1)))
      (α := Fin (v.length + 1 + 1)) (β := fun _ => Fin (v.length + 1 + 1))
      (nextCrossing ((i, ε) :: (i, η) :: v) p) 0 = 1 := by
  have hnd := (sortedLT_crossingsAt ((i, ε) :: (i, η) :: v) p).nodup
  rw [crossingsAt_cons_cons_same_index, ite_eq_left hp] at hnd
  rw [nextCrossing_def, crossingsAt_cons_cons_same_index, ite_eq_left hp]
  exact List.formPerm_apply_head _ _ _ hnd

/-- If an affected position previously had no crossing, the second inserted crossing returns
to the first, giving a two-element cycle. -/
@[simp]
theorem nextCrossing_cons_cons_one_of_nil {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) (hv : v.crossingsAt p = []) :
    DFunLike.coe (F := Equiv.Perm (Fin (v.length + 1 + 1)))
      (α := Fin (v.length + 1 + 1)) (β := fun _ => Fin (v.length + 1 + 1))
      (nextCrossing ((i, ε) :: (i, η) :: v) p) 1 = 0 := by
  rw [nextCrossing_def, crossingsAt_cons_cons_same_index, ite_eq_left hp, hv]
  simp

/-- If an affected position already carried crossings, the second inserted crossing leads
to its old first crossing. -/
@[simp]
theorem nextCrossing_cons_cons_one_of_ne_nil {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) (hv : v.crossingsAt p ≠ []) :
    DFunLike.coe (F := Equiv.Perm (Fin (v.length + 1 + 1)))
      (α := Fin (v.length + 1 + 1)) (β := fun _ => Fin (v.length + 1 + 1))
      (nextCrossing ((i, ε) :: (i, η) :: v) p) 1 =
      ((v.crossingsAt p).head hv).succ.succ := by
  have hnd := (sortedLT_crossingsAt ((i, ε) :: (i, η) :: v) p).nodup
  rw [crossingsAt_cons_cons_same_index, ite_eq_left hp] at hnd
  have h := List.formPerm_append_apply_getLast_left hnd (by simp :
    ([0, 1] : List (Fin (v.length + 1 + 1))) ≠ [])
  rw [nextCrossing_def, crossingsAt_cons_cons_same_index, ite_eq_left hp]
  simpa [List.head_append_left, hv] using h

/-- An old crossing on an affected position keeps its successor except at the end of the
old cycle, where it now leads to the first inserted crossing. -/
theorem nextCrossing_cons_cons_of_mem {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) {j : Fin v.length} (hj : j ∈ v.crossingsAt p) :
    nextCrossing ((i, ε) :: (i, η) :: v) p j.succ.succ =
      if v.nextCrossing p j = (v.crossingsAt p).head (List.ne_nil_of_mem hj) then 0
      else (v.nextCrossing p j).succ.succ := by
  have hnd := (sortedLT_crossingsAt ((i, ε) :: (i, η) :: v) p).nodup
  rw [crossingsAt_cons_cons_same_index, ite_eq_left hp] at hnd
  have h := List.formPerm_append_apply_of_mem_right hnd (List.mem_map.mpr ⟨j, hj, rfl⟩)
  rw [nextCrossing_def, crossingsAt_cons_cons_same_index, ite_eq_left hp]
  simpa only [List.formPerm_map_apply (f := fun j : Fin v.length => j.succ.succ)
      ((Fin.succ_injective _).comp (Fin.succ_injective _)),
    List.head_map, List.head_cons, List.cons_append, Fin.succ_inj, nextCrossing_def] using h

/-- Skipping the two newly inserted crossings recovers the old successor on an affected
position. This includes a position with just one old crossing. -/
theorem nextCrossing_cons_cons_skip_pair {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) {j : Fin v.length} (hj : j ∈ v.crossingsAt p) :
    let w : BraidWord n := (i, ε) :: (i, η) :: v
    (if w.nextCrossing p j.succ.succ = 0 then
      w.nextCrossing p (w.nextCrossing p (w.nextCrossing p j.succ.succ))
    else w.nextCrossing p j.succ.succ) = (v.nextCrossing p j).succ.succ := by
  dsimp only
  rw [nextCrossing_cons_cons_of_mem v i ε η hp hj]
  by_cases h : v.nextCrossing p j = (v.crossingsAt p).head (List.ne_nil_of_mem hj)
  · simp only [h, ite_true]
    rw [nextCrossing_cons_cons_zero v i ε η hp,
      nextCrossing_cons_cons_one_of_ne_nil v i ε η hp (List.ne_nil_of_mem hj)]
  · simp [h]

/-- Every arc leaving an old crossing is retained except the closing arc on an affected
position, which now enters the first inserted crossing. The formula uses the original slots
at old crossings, so it can be applied without unfolding the closure construction. -/
theorem edgePair_closure_cons_cons_of_mem {p : Fin n} {j : Fin v.length}
    (hj : j ∈ v.crossingsAt p) :
    let w : BraidWord n := (i, ε) :: (i, η) :: v
    w.closure.edgePair.val (w.closure.crossing j.succ.succ (v.outgoingSlot j p)) =
      if (p = strand i ∨ p = strandSucc i) ∧
          v.nextCrossing p j = (v.crossingsAt p).head (List.ne_nil_of_mem hj) then
        w.closure.crossing 0 (w.incomingSlot 0 p)
      else w.closure.crossing (v.nextCrossing p j).succ.succ
        (v.incomingSlot (v.nextCrossing p j) p) := by
  dsimp only
  let w : BraidWord n := (i, ε) :: (i, η) :: v
  have hletter (k : Fin v.length) : w[k.succ.succ.val] = v[k.val] := by simp [w]
  have hout := outgoingSlot_congr (hletter j) p
  have hmem : j.succ.succ ∈ w.crossingsAt p := by
    apply (mem_crossingsAt (w := w) (j := j.succ.succ)).mpr
    rw [hletter]
    exact (mem_crossingsAt (w := v)).mp hj
  have hnext : w.nextCrossing p j.succ.succ =
      if (p = strand i ∨ p = strandSucc i) ∧
          v.nextCrossing p j = (v.crossingsAt p).head (List.ne_nil_of_mem hj) then 0
      else (v.nextCrossing p j).succ.succ := by
    by_cases hp : p = strand i ∨ p = strandSucc i
    · simpa only [hp, true_and] using nextCrossing_cons_cons_of_mem v i ε η hp hj
    · simpa only [hp, false_and, ite_false] using
        nextCrossing_cons_cons_of_ne v i ε η (not_or.mp hp).1 (not_or.mp hp).2 j
  refine (congrArg w.closure.edgePair.val
    (congrArg (w.closure.crossing j.succ.succ) hout.symm)).trans
      ((edgePair_closure_outgoingSlot w hmem).trans ?_)
  rw [hnext]
  split_ifs
  · rfl
  · rw [incomingSlot_congr (hletter (v.nextCrossing p j)) p]

/-- The upper internal arc of the inserted pair joins slot `1` of the first crossing to
slot `0` of the second. -/
theorem edgePair_closure_cons_cons_one :
    (closure ((i, ε) :: (i, η) :: v)).edgePair.val
        (crossingSlotEquiv ((i, ε) :: (i, η) :: v).length (0, 1)) =
      crossingSlotEquiv ((i, ε) :: (i, η) :: v).length (1, 0) := by
  let w : BraidWord n := (i, ε) :: (i, η) :: v
  have hout : w.outgoingSlot 0 (strandSucc i) = 1 := outgoingSlot_strandSucc w 0
  have hin : w.incomingSlot 1 (strandSucc i) = 0 := incomingSlot_strandSucc w 1
  have hmem : (0 : Fin w.length) ∈ w.crossingsAt (strandSucc i) :=
    mem_crossingsAt_strandSucc w 0
  have hnext : w.nextCrossing (strandSucc i) 0 = 1 :=
    nextCrossing_cons_cons_zero v i ε η (Or.inr rfl)
  -- Express the endpoint through the crossing API before simplifying its successor.
  refine (congrArg w.closure.edgePair.val
    ((crossing_closure w 0 _).symm.trans
      (congrArg (w.closure.crossing 0) hout.symm))).trans
      ((edgePair_closure_outgoingSlot w hmem).trans ?_)
  rw [hnext, hin, crossing_closure]

/-- The lower internal arc of the inserted pair joins slot `2` of the first crossing to
slot `3` of the second. -/
theorem edgePair_closure_cons_cons_two :
    (closure ((i, ε) :: (i, η) :: v)).edgePair.val
        (crossingSlotEquiv ((i, ε) :: (i, η) :: v).length (0, 2)) =
      crossingSlotEquiv ((i, ε) :: (i, η) :: v).length (1, 3) := by
  let w : BraidWord n := (i, ε) :: (i, η) :: v
  have hout : w.outgoingSlot 0 (strand i) = 2 := outgoingSlot_strand w 0
  have hin : w.incomingSlot 1 (strand i) = 3 := incomingSlot_strand w 1
  have hmem : (0 : Fin w.length) ∈ w.crossingsAt (strand i) :=
    mem_crossingsAt_strand w 0
  have hnext : w.nextCrossing (strand i) 0 = 1 :=
    nextCrossing_cons_cons_zero v i ε η (Or.inl rfl)
  -- Express the endpoint through the crossing API before simplifying its successor.
  refine (congrArg w.closure.edgePair.val
    ((crossing_closure w 0 _).symm.trans
      (congrArg (w.closure.crossing 0) hout.symm))).trans
      ((edgePair_closure_outgoingSlot w hmem).trans ?_)
  rw [hnext, hin, crossing_closure]

/-- Opposite letters give opposite over-pair indicators at the two inserted crossings.
Together with the internal-arc formulas, this means the same physical strand is over twice. -/
theorem overPair_closure_freeCancel_one :
    (closure ((i, ε) :: (i, -ε) :: v)).overPair 1 =
      !(closure ((i, ε) :: (i, -ε) :: v)).overPair 0 := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [overPair_closure]

end TauCeti.BraidWord
