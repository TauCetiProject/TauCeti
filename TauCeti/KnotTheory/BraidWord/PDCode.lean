/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Braid.Word
public import TauCeti.KnotTheory.PDCode.Basic
public import Mathlib.GroupTheory.Perm.List
import Mathlib.Tactic.FinCases

/-!
# The closure of a braid word as a PD-code

Closing a braid, by joining the top end of each strand position to its bottom end, presents an
oriented link. This file writes that link down as an oriented PD-code, with one crossing for
every letter of a braid word. It is the combinatorial edge from the braid presentation of a
link to the diagram presentation.

The braid is drawn with its strands running upwards, the letters of the word from the bottom to
the top, and the closing strands passing to the side. The four slots of the crossing of a
letter `(i, ε)` are, counterclockwise: slot `0` entering from below on position `i + 1`, slot `1`
leaving above on position `i + 1`, slot `2` leaving above on position `i`, and slot `3` entering
from below on position `i`. So the strand entering on position `i` occupies slots `3` and `1`;
it is the over-strand when `ε = 1`, which makes the crossing positive, and the under-strand when
`ε = -1`. Leaving a crossing upwards on position `p`, a strand next meets the first crossing
above it that involves position `p`, or else runs through the closure back to the lowest such
crossing; that successor is `TauCeti.BraidWord.nextCrossing`. A position involved in no crossing
closes up to a crossing-free circle.

## Main definitions

* `TauCeti.BraidWord.crossingsAt`: the crossings involving a strand position, from the bottom.
* `TauCeti.BraidWord.nextCrossing`: the next crossing met along a strand position.
* `TauCeti.BraidWord.closure`: the oriented PD-code of the closure of a braid word.

## Main results

* `TauCeti.BraidWord.crossingsAt_cons`: a letter added at the bottom of a word comes first along
  its two strand positions.
* `TauCeti.BraidWord.edgePair_closure_outgoingSlot`: the arcs of the closure join each crossing
  to the next crossing along the same strand position.
* `TauCeti.BraidWord.edgePair_closure_incomingSlot`: the same arcs, read from the crossing they
  enter.
* `TauCeti.BraidWord.edgePair_closure_crossingSlotEquiv_zero` and its siblings for the slots `1`,
  `2` and `3`: the arc at each slot of a crossing of the closure.
* `TauCeti.BraidWord.edgePair_closure_eq_of_outgoingSlot`: a perfect matching of the half-edges
  agreeing with the arcs of the closure at the slots where strands leave their crossings is the arc
  matching of the closure.
* `TauCeti.BraidWord.crossingSign_closure`: the sign of each crossing is the sign of its letter.
* `TauCeti.BraidWord.writhe_closure`: the writhe of the closure is the exponent sum of the braid.
* `TauCeti.BraidWord.closure_nil`: the closure of the empty word on `n` strands is the
  `n`-component unlink.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2.
-/

public section

namespace TauCeti

namespace BraidWord

open BraidGroup PDCode

variable {n : ℕ} (w : BraidWord n)

/-! ### Following a strand position through the crossings -/

/-- The crossings of a braid word involving the strand position `p`, listed from the bottom: the
letters `(i, ε)` with `p = i` or `p = i + 1`. -/
def crossingsAt (p : Fin n) : List (Fin w.length) :=
  (List.finRange w.length).filter fun j ↦ p = strand w[j.1].1 ∨ p = strandSucc w[j.1].1

/-- The crossings involving a strand position are the indices of the letters with that position
as one of their two strands, in increasing order. -/
theorem crossingsAt_def (p : Fin n) :
    w.crossingsAt p =
      (List.finRange w.length).filter fun j ↦ p = strand w[j.1].1 ∨ p = strandSucc w[j.1].1 :=
  (rfl)

/-- A crossing involves a strand position exactly when that position is one of its two strands. -/
@[simp]
theorem mem_crossingsAt {p : Fin n} {j : Fin w.length} :
    j ∈ w.crossingsAt p ↔ p = strand w[j.1].1 ∨ p = strandSucc w[j.1].1 := by
  simp [crossingsAt]

/-- A crossing involves the lower position of its letter. -/
theorem mem_crossingsAt_strand (j : Fin w.length) :
    j ∈ w.crossingsAt (strand w[j.1].1) := by
  simp

/-- A crossing involves the upper position of its letter. -/
theorem mem_crossingsAt_strandSucc (j : Fin w.length) :
    j ∈ w.crossingsAt (strandSucc w[j.1].1) := by
  simp

/-- A strand position is involved in no crossing exactly when it is neither position of any
letter. -/
theorem crossingsAt_eq_nil_iff {p : Fin n} :
    w.crossingsAt p = [] ↔
      ∀ j : Fin w.length, p ≠ strand w[j.1].1 ∧ p ≠ strandSucc w[j.1].1 := by
  simp [List.eq_nil_iff_forall_not_mem, not_or]

/-- The crossings involving a strand position are listed from the bottom. -/
theorem sortedLT_crossingsAt (p : Fin n) : (w.crossingsAt p).SortedLT := by
  rw [List.sortedLT_iff_pairwise] at ⊢
  exact (List.sortedLT_iff_pairwise.1 (List.sortedLT_finRange w.length)).filter _

/-- Adding a letter at the bottom of a braid word: along a strand position, its crossing comes
first when the letter involves that position, followed by the crossings of the old word. -/
theorem crossingsAt_cons (x : Fin (n - 1) × ℤˣ) (v : BraidWord n) (p : Fin n) :
    crossingsAt (x :: v) p =
      (if p = strand x.1 ∨ p = strandSucc x.1 then [0] else []) ++
        (v.crossingsAt p).map Fin.succ := by
  refine List.SortedLT.eq_of_mem_iff (sortedLT_crossingsAt _ p) ?_ fun k ↦ ?_
  · rw [List.sortedLT_append, Fin.strictMono_succ.sortedLT_listMap]
    refine ⟨?_, sortedLT_crossingsAt v p, ?_⟩
    · split_ifs <;> simp [List.sortedLT_iff_pairwise]
    · intro a ha b hb
      split_ifs at ha <;> simp only [List.mem_singleton, List.not_mem_nil] at ha
      subst ha
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hb
      exact Fin.succ_pos b
  · refine Fin.cases ?_ (fun k ↦ ?_) k
    · rw [mem_crossingsAt (w := x :: v) (j := 0)]
      simp
    · rw [mem_crossingsAt (w := x :: v) (j := k.succ)]
      simp [Fin.succ_ne_zero]

/-- Two letters on the same positions come first on either position, followed by the old
crossings shifted by two. Positions outside the pair see only the shifted old crossings. -/
theorem crossingsAt_cons_cons_same_index (v : BraidWord n) (i : Fin (n - 1)) (ε η : ℤˣ)
    (p : Fin n) :
    crossingsAt ((i, ε) :: (i, η) :: v) p =
      (if p = strand i ∨ p = strandSucc i then [0, 1] else []) ++
        (v.crossingsAt p).map (fun j => j.succ.succ) := by
  rw [crossingsAt_cons, crossingsAt_cons]
  split_ifs <;> simp

/-- The crossing met next along the strand position `p` after the crossing `j`: the next
crossing above `j` involving `p`, or, through the closure, the lowest one. Crossings not
involving `p` are fixed. -/
def nextCrossing (p : Fin n) : Equiv.Perm (Fin w.length) :=
  (w.crossingsAt p).formPerm

/-- The successor along a strand position is the cyclic permutation of the crossings involving it,
listed from the bottom. -/
theorem nextCrossing_def (p : Fin n) : w.nextCrossing p = (w.crossingsAt p).formPerm :=
  (rfl)

/-- Along a strand position, each crossing involving it is followed by the next one in the
bottom-to-top list `TauCeti.BraidWord.crossingsAt`, and the topmost by the lowest. -/
theorem nextCrossing_apply_getElem (p : Fin n) (k : ℕ) (hk : k < (w.crossingsAt p).length) :
    w.nextCrossing p (w.crossingsAt p)[k] =
      (w.crossingsAt p)[(k + 1) % (w.crossingsAt p).length]'(Nat.mod_lt _ (by omega)) :=
  List.formPerm_apply_getElem _ (w.sortedLT_crossingsAt p).nodup k hk

/-- The next crossing along a position involves that position exactly when the current one
does. -/
theorem nextCrossing_mem_crossingsAt_iff {p : Fin n} {j : Fin w.length} :
    w.nextCrossing p j ∈ w.crossingsAt p ↔ j ∈ w.crossingsAt p :=
  List.formPerm_mem_iff_mem

/-- The previous crossing along a position involves that position exactly when the current one
does. -/
theorem nextCrossing_symm_mem_crossingsAt_iff {p : Fin n} {j : Fin w.length} :
    (w.nextCrossing p).symm j ∈ w.crossingsAt p ↔ j ∈ w.crossingsAt p := by
  rw [← w.nextCrossing_mem_crossingsAt_iff, Equiv.apply_symm_apply]

/-- The slot of the crossing `j` at which a strand enters it from below on the position `p`:
slot `3` on the lower position `i` of the letter, slot `0` on the upper position `i + 1`. -/
def incomingSlot (j : Fin w.length) (p : Fin n) : Fin 4 :=
  if p = strand w[j.1].1 then 3 else 0

/-- The slot of the crossing `j` at which a strand leaves it upwards on the position `p`:
slot `2` on the lower position `i` of the letter, slot `1` on the upper position `i + 1`. -/
def outgoingSlot (j : Fin w.length) (p : Fin n) : Fin 4 :=
  if p = strand w[j.1].1 then 2 else 1

/-- A strand enters a crossing on the lower position of its letter at slot `3`. -/
@[simp]
theorem incomingSlot_strand (j : Fin w.length) : w.incomingSlot j (strand w[j.1].1) = 3 := by
  simp [incomingSlot]

/-- A strand enters a crossing on the upper position of its letter at slot `0`. -/
@[simp]
theorem incomingSlot_strandSucc (j : Fin w.length) :
    w.incomingSlot j (strandSucc w[j.1].1) = 0 := by
  simp [incomingSlot, (strand_ne_strandSucc _).symm]

/-- A strand leaves a crossing on the lower position of its letter at slot `2`. -/
@[simp]
theorem outgoingSlot_strand (j : Fin w.length) : w.outgoingSlot j (strand w[j.1].1) = 2 := by
  simp [outgoingSlot]

/-- A strand leaves a crossing on the upper position of its letter at slot `1`. -/
@[simp]
theorem outgoingSlot_strandSucc (j : Fin w.length) :
    w.outgoingSlot j (strandSucc w[j.1].1) = 1 := by
  simp [outgoingSlot, (strand_ne_strandSucc _).symm]

/-- A strand enters a crossing at slot `0` or slot `3`. -/
theorem incomingSlot_eq_zero_or_three (j : Fin w.length) (p : Fin n) :
    w.incomingSlot j p = 0 ∨ w.incomingSlot j p = 3 := by
  unfold incomingSlot
  split_ifs <;> simp

/-- A strand leaves a crossing at slot `1` or slot `2`. -/
theorem outgoingSlot_eq_one_or_two (j : Fin w.length) (p : Fin n) :
    w.outgoingSlot j p = 1 ∨ w.outgoingSlot j p = 2 := by
  unfold outgoingSlot
  split_ifs <;> simp

/-- A crossing is left upwards along the two positions of its letter at different slots. -/
theorem eq_of_outgoingSlot_eq {j : Fin w.length} {p q : Fin n} (hp : j ∈ w.crossingsAt p)
    (hq : j ∈ w.crossingsAt q) (h : w.outgoingSlot j p = w.outgoingSlot j q) : p = q := by
  rw [mem_crossingsAt] at hp hq
  have hne := strand_ne_strandSucc w[j.1].1
  unfold outgoingSlot at h
  rcases hp with rfl | rfl <;> rcases hq with hq | hq <;> simp_all

/-- The incoming slot at a crossing depends only on the letter of that crossing. -/
theorem incomingSlot_congr {w w' : BraidWord n} {j : Fin w'.length} {i : Fin w.length}
    (h : w'[j.1] = w[i.1]) (p : Fin n) : w'.incomingSlot j p = w.incomingSlot i p := by
  rw [incomingSlot, incomingSlot, h]

/-- The outgoing slot at a crossing depends only on the letter of that crossing. -/
theorem outgoingSlot_congr {w w' : BraidWord n} {j : Fin w'.length} {i : Fin w.length}
    (h : w'[j.1] = w[i.1]) (p : Fin n) : w'.outgoingSlot j p = w.outgoingSlot i p := by
  rw [outgoingSlot, outgoingSlot, h]

/-! ### The arcs of the closure -/

/-- The strand position of a slot of the crossing `j`. -/
private def slotStrand (j : Fin w.length) (slot : Fin 4) : Fin n :=
  if slot = 0 ∨ slot = 1 then strandSucc w[j.1].1 else strand w[j.1].1

/-- Whether a slot is one at which a strand leaves its crossing upwards. -/
private def IsOutgoing (slot : Fin 4) : Prop := slot = 1 ∨ slot = 2

private instance : DecidablePred IsOutgoing := fun slot ↦
  inferInstanceAs (Decidable (slot = 1 ∨ slot = 2))

private theorem mem_crossingsAt_slotStrand (j : Fin w.length) (slot : Fin 4) :
    j ∈ w.crossingsAt (w.slotStrand j slot) := by
  rw [mem_crossingsAt, slotStrand]
  split_ifs <;> simp

private theorem slotStrand_incomingSlot {j : Fin w.length} {p : Fin n}
    (hj : j ∈ w.crossingsAt p) : w.slotStrand j (w.incomingSlot j p) = p := by
  rw [mem_crossingsAt] at hj
  unfold slotStrand incomingSlot
  split_ifs <;> simp_all

private theorem slotStrand_outgoingSlot {j : Fin w.length} {p : Fin n}
    (hj : j ∈ w.crossingsAt p) : w.slotStrand j (w.outgoingSlot j p) = p := by
  rw [mem_crossingsAt] at hj
  unfold slotStrand outgoingSlot
  split_ifs <;> simp_all

private theorem incomingSlot_slotStrand (j : Fin w.length) {slot : Fin 4}
    (hslot : ¬IsOutgoing slot) : w.incomingSlot j (w.slotStrand j slot) = slot := by
  have hne := (strand_ne_strandSucc w[j.1].1).symm
  unfold IsOutgoing at hslot
  unfold incomingSlot slotStrand
  fin_cases slot <;> simp_all

private theorem outgoingSlot_slotStrand (j : Fin w.length) {slot : Fin 4}
    (hslot : IsOutgoing slot) : w.outgoingSlot j (w.slotStrand j slot) = slot := by
  have hne := (strand_ne_strandSucc w[j.1].1).symm
  unfold IsOutgoing at hslot
  unfold outgoingSlot slotStrand
  fin_cases slot <;> simp_all

private theorem not_isOutgoing_incomingSlot (j : Fin w.length) (p : Fin n) :
    ¬IsOutgoing (w.incomingSlot j p) := by
  unfold IsOutgoing incomingSlot
  split_ifs <;> decide

private theorem isOutgoing_outgoingSlot (j : Fin w.length) (p : Fin n) :
    IsOutgoing (w.outgoingSlot j p) := by
  unfold IsOutgoing outgoingSlot
  split_ifs <;> decide

/-- The other end of the arc at a crossing slot: an outgoing slot is joined to the incoming slot
of the next crossing along its position, and an incoming slot to the outgoing slot of the
previous one. -/
private def arc (x : Fin w.length × Fin 4) : Fin w.length × Fin 4 :=
  if IsOutgoing x.2 then
    (w.nextCrossing (w.slotStrand x.1 x.2) x.1,
      w.incomingSlot (w.nextCrossing (w.slotStrand x.1 x.2) x.1) (w.slotStrand x.1 x.2))
  else
    ((w.nextCrossing (w.slotStrand x.1 x.2)).symm x.1,
      w.outgoingSlot ((w.nextCrossing (w.slotStrand x.1 x.2)).symm x.1) (w.slotStrand x.1 x.2))

private theorem isOutgoing_arc (x : Fin w.length × Fin 4) :
    IsOutgoing (w.arc x).2 ↔ ¬IsOutgoing x.2 := by
  unfold arc
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    exact w.not_isOutgoing_incomingSlot _ _
  · simp only [h, not_false_eq_true, iff_true]
    exact w.isOutgoing_outgoingSlot _ _

private theorem arc_arc (x : Fin w.length × Fin 4) : w.arc (w.arc x) = x := by
  obtain ⟨j, slot⟩ := x
  have hj := w.mem_crossingsAt_slotStrand j slot
  by_cases hslot : IsOutgoing slot
  · have hnext : w.nextCrossing (w.slotStrand j slot) j ∈ w.crossingsAt (w.slotStrand j slot) :=
      w.nextCrossing_mem_crossingsAt_iff.2 hj
    simp only [arc, hslot, ↓reduceIte, w.not_isOutgoing_incomingSlot,
      w.slotStrand_incomingSlot hnext, Equiv.symm_apply_apply, w.outgoingSlot_slotStrand j hslot]
  · have hprev : (w.nextCrossing (w.slotStrand j slot)).symm j ∈
        w.crossingsAt (w.slotStrand j slot) :=
      w.nextCrossing_symm_mem_crossingsAt_iff.2 hj
    simp only [arc, hslot, ↓reduceIte, w.isOutgoing_outgoingSlot,
      w.slotStrand_outgoingSlot hprev, Equiv.apply_symm_apply, w.incomingSlot_slotStrand j hslot]

private theorem arc_ne (x : Fin w.length × Fin 4) : w.arc x ≠ x := fun h ↦ by
  have := w.isOutgoing_arc x
  rw [h] at this
  tauto

/-- The arcs of the closure as an involution of the crossing slots. -/
private def arcPerm : Equiv.Perm (Fin w.length × Fin 4) :=
  Function.Involutive.toPerm w.arc w.arc_arc

private theorem arcPerm_apply (x : Fin w.length × Fin 4) : w.arcPerm x = w.arc x :=
  (rfl)

/-- The arcs of the closure as a perfect matching of the crossing slots. -/
private def arcMatching : PerfectMatching (Fin w.length × Fin 4) :=
  PerfectMatching.mk w.arcPerm (fun x ↦ by rw [arcPerm_apply, arcPerm_apply, arc_arc])
    (fun x ↦ by rw [arcPerm_apply]; exact w.arc_ne x)

private theorem arcMatching_apply (x : Fin w.length × Fin 4) : w.arcMatching.val x = w.arc x := by
  rw [arcMatching, PerfectMatching.val_mk, arcPerm_apply]

/-! ### The closure -/

/-- The closure of a braid word, as an oriented PD-code with one crossing for each letter.

The half-edges are labelled by their crossing slots. The strands run upwards, so a half-edge
points away from its crossing exactly at the slots `1` and `2`. The strand entering the crossing
of a letter `(i, ε)` on position `i` occupies slots `3` and `1` and is over exactly when
`ε = 1`. Every strand position involved in no crossing closes up to a crossing-free circle, all of
them with the orientation `true`. -/
def closure : OrientedPDCode w.length where
  halfEdge := 1
  edgePair := PerfectMatching.congr (crossingSlotEquiv w.length) w.arcMatching
  crossinglessComponentCount := (Finset.univ.filter fun p ↦ w.crossingsAt p = []).card
  overPair j := decide (w[j.1].2 = 1)
  orientation h := decide (IsOutgoing ((crossingSlotEquiv w.length).symm h).2)
  orientation_edgePair h := by
    rw [PerfectMatching.congr_val_apply, Equiv.symm_apply_apply]
    simp only [arcMatching_apply, w.isOutgoing_arc, decide_not]
  orientation_oppositeCrossingSlot i slot := by
    simp only [Equiv.Perm.coe_one, id_eq, Equiv.symm_apply_apply, IsOutgoing, Fin.ext_iff,
      oppositeCrossingSlot_apply]
    fin_cases slot <;> decide
  crossinglessComponents :=
    Multiset.replicate (Finset.univ.filter fun p ↦ w.crossingsAt p = []).card true
  card_crossinglessComponents := Multiset.card_replicate _ _

/-- The half-edges of the closure are labelled by their crossing slots. -/
@[simp]
theorem halfEdge_closure : w.closure.halfEdge = 1 := by
  simp [closure]

/-- The half-edge in a crossing slot of the closure is the label of that slot. -/
theorem crossing_closure (j : Fin w.length) (slot : Fin 4) :
    w.closure.crossing j slot = crossingSlotEquiv w.length (j, slot) := by
  simp [closure]

/-- The arc leaving a crossing upwards on the position `p` enters the next crossing along `p`
from below. Since every slot is the incoming or the outgoing slot of its crossing on one of the
two positions of its letter, this determines every arc of the closure. -/
theorem edgePair_closure_outgoingSlot {j : Fin w.length} {p : Fin n}
    (hj : j ∈ w.crossingsAt p) :
    w.closure.edgePair.val (w.closure.crossing j (w.outgoingSlot j p)) =
      w.closure.crossing (w.nextCrossing p j) (w.incomingSlot (w.nextCrossing p j) p) := by
  simp only [crossing_closure]
  simp only [closure, PerfectMatching.congr_val_apply, Equiv.symm_apply_apply, arcMatching_apply,
    arc, w.isOutgoing_outgoingSlot j p, ↓reduceIte, w.slotStrand_outgoingSlot hj]

/-- The arc entering a crossing from below on the position `p` leaves the previous crossing along
`p` upwards. -/
theorem edgePair_closure_incomingSlot {j : Fin w.length} {p : Fin n}
    (hj : j ∈ w.crossingsAt p) :
    w.closure.edgePair.val (w.closure.crossing j (w.incomingSlot j p)) =
      w.closure.crossing ((w.nextCrossing p).symm j)
        (w.outgoingSlot ((w.nextCrossing p).symm j) p) := by
  simp only [crossing_closure]
  simp only [closure, PerfectMatching.congr_val_apply, Equiv.symm_apply_apply, arcMatching_apply,
    arc, w.not_isOutgoing_incomingSlot j p, ↓reduceIte, w.slotStrand_incomingSlot hj]

/-- The arc at slot `0` of a crossing, entering it from below on the upper position of its letter,
leaves the previous crossing along that position upwards. -/
@[simp]
theorem edgePair_closure_crossingSlotEquiv_zero (j : Fin w.length) :
    w.closure.edgePair.val (crossingSlotEquiv w.length (j, 0)) =
      crossingSlotEquiv w.length ((w.nextCrossing (strandSucc w[j.1].1)).symm j,
        w.outgoingSlot ((w.nextCrossing (strandSucc w[j.1].1)).symm j) (strandSucc w[j.1].1)) := by
  simpa [crossing_closure] using w.edgePair_closure_incomingSlot (w.mem_crossingsAt_strandSucc j)

/-- The arc at slot `1` of a crossing, leaving it upwards on the upper position of its letter,
enters the next crossing along that position from below. -/
@[simp]
theorem edgePair_closure_crossingSlotEquiv_one (j : Fin w.length) :
    w.closure.edgePair.val (crossingSlotEquiv w.length (j, 1)) =
      crossingSlotEquiv w.length (w.nextCrossing (strandSucc w[j.1].1) j,
        w.incomingSlot (w.nextCrossing (strandSucc w[j.1].1) j) (strandSucc w[j.1].1)) := by
  simpa [crossing_closure] using w.edgePair_closure_outgoingSlot (w.mem_crossingsAt_strandSucc j)

/-- The arc at slot `2` of a crossing, leaving it upwards on the lower position of its letter,
enters the next crossing along that position from below. -/
@[simp]
theorem edgePair_closure_crossingSlotEquiv_two (j : Fin w.length) :
    w.closure.edgePair.val (crossingSlotEquiv w.length (j, 2)) =
      crossingSlotEquiv w.length (w.nextCrossing (strand w[j.1].1) j,
        w.incomingSlot (w.nextCrossing (strand w[j.1].1) j) (strand w[j.1].1)) := by
  simpa [crossing_closure] using w.edgePair_closure_outgoingSlot (w.mem_crossingsAt_strand j)

/-- The arc at slot `3` of a crossing, entering it from below on the lower position of its letter,
leaves the previous crossing along that position upwards. -/
@[simp]
theorem edgePair_closure_crossingSlotEquiv_three (j : Fin w.length) :
    w.closure.edgePair.val (crossingSlotEquiv w.length (j, 3)) =
      crossingSlotEquiv w.length ((w.nextCrossing (strand w[j.1].1)).symm j,
        w.outgoingSlot ((w.nextCrossing (strand w[j.1].1)).symm j) (strand w[j.1].1)) := by
  simpa [crossing_closure] using w.edgePair_closure_incomingSlot (w.mem_crossingsAt_strand j)

/-- The strand entering the crossing of a letter on the lower position of the letter is over
exactly for a positive letter. -/
@[simp]
theorem overPair_closure (j : Fin w.length) : w.closure.overPair j = decide (w[j.1].2 = 1) := by
  simp [closure]

/-- A half-edge of the closure points away from its crossing exactly at the slots `1` and `2`,
where the strands leave the crossing upwards. -/
@[simp]
theorem orientation_closure (j : Fin w.length) (slot : Fin 4) :
    w.closure.orientation (crossingSlotEquiv w.length (j, slot)) =
      decide (slot = 1 ∨ slot = 2) := by
  simp [closure, IsOutgoing]

/-- The arcs of the closure are determined by the arcs leaving the crossings upwards: a perfect
matching of the half-edges agreeing with them is the arc matching of the closure. -/
theorem edgePair_closure_eq_of_outgoingSlot {M : PerfectMatching (Fin (4 * w.length))}
    (h : ∀ j p, j ∈ w.crossingsAt p →
      w.closure.edgePair.val (crossingSlotEquiv _ (j, w.outgoingSlot j p)) =
        M.val (crossingSlotEquiv _ (j, w.outgoingSlot j p))) :
    w.closure.edgePair = M := by
  refine PerfectMatching.ext_of_eqOn (s := {x | w.closure.orientation x = true})
    (fun x hx ↦ by simpa using hx) fun x hx ↦ ?_
  obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv _).surjective x
  simp only [Set.mem_ofPred_eq, orientation_closure, decide_eq_true_eq] at hx
  rcases hx with rfl | rfl
  · simpa using h j _ (w.mem_crossingsAt_strandSucc j)
  · simpa using h j _ (w.mem_crossingsAt_strand j)

/-- The crossing-free circles of the closure are the strand positions involved in no crossing. -/
@[simp]
theorem crossinglessComponentCount_closure :
    w.closure.crossinglessComponentCount =
      (Finset.univ.filter fun p ↦ w.crossingsAt p = []).card := by
  simp [closure]

/-- The crossing-free circles of the closure all carry the orientation `true`. -/
@[simp]
theorem crossinglessComponents_closure :
    w.closure.crossinglessComponents =
      Multiset.replicate (Finset.univ.filter fun p ↦ w.crossingsAt p = []).card true := by
  simp [closure]

/-- The sign of each crossing of the closure is the sign of its letter. -/
@[simp]
theorem crossingSign_closure (j : Fin w.length) : w.closure.crossingSign j = w[j.1].2 := by
  rw [OrientedPDCode.crossingSign_def]
  simp only [crossing_closure, orientation_closure, overPair_closure]
  rcases Int.units_eq_one_or w[j.1].2 with h | h <;> simp [h]

/-- The writhe of the closure of a braid word is the exponent sum of the braid it represents. -/
@[simp]
theorem writhe_closure :
    w.closure.writhe = Multiplicative.toAdd (ArtinGroup.exponentSum _ w.toBraid) := by
  rw [OrientedPDCode.writhe_def, exponentSum_toBraid, toAdd_ofAdd]
  simp only [crossingSign_closure]
  exact Fin.sum_univ_fun_getElem w fun x ↦ (x.2 : ℤ)

/-! ### Small closures -/

/-- The closure of the empty word on `n` strands is the `n`-component unlink. -/
@[simp]
theorem closure_nil : closure ([] : BraidWord n) =
    OrientedPDCode.unlink (Multiset.replicate n true) := by
  rw [OrientedPDCode.eq_unlink (closure []), crossinglessComponents_closure]
  simp [crossingsAt]

end BraidWord

end TauCeti
