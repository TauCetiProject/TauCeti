/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence
import TauCeti.Data.List.Rotate

/-!
# Stabilization of a braid word is a first Reidemeister move

The Markov stabilization move adds a strand to a braid and crosses it once, in either sense, with
the previous last strand. On braid words it is `TauCeti.BraidWord.stabilize`, which places the new
letter `σ (Fin.last n) ^ ε` at the top of the word. In the closure of the stabilized word the new
strand runs from the new crossing back to it through the closure, meeting no other crossing, so it
is a small loop: the closure gains a kink. This file proves that the closures before and after
stabilization are Reidemeister equivalent, which is the diagram-level content of the stabilization
moves of `TauCeti.IsMarkovMove`.

## Main results

* `TauCeti.BraidWord.reidemeisterEquiv_closure_stabilize`: the closure of a stabilized braid word
  is Reidemeister equivalent to the closure of the original word.

## Implementation notes

There are two cases. If some letter of `w` involves its last strand position, the kink lies on the
arc of the closure of `w` leaving the topmost such crossing upwards, which runs through the closure
back to the lowest one. The closure of the stabilized word is then
`TauCeti.OrientedPDCode.reidemeisterOne` applied to that arc, with the new crossing read from its
slot `2` (two applications of `TauCeti.OrientedPDCode.rotateCrossing`) and crossings and half-edges
renamed. Otherwise the last strand position of `w` closes up to a crossing-free circle, and the
stabilized closure adds a kink to that circle, `TauCeti.OrientedPDCode.adjoinKink`. In both cases
the arcs are compared through `TauCeti.BraidWord.edgePair_closure_eq_of_outgoingSlot`, at the
slots where strands leave their crossings.

## References

* A. A. Markov, *Über die freie Äquivalenz der geschlossenen Zöpfe*, Rec. Math. Moscou 1 (1935),
  73-78.
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1 and
  Proposition 16.10.
-/

public section

namespace TauCeti

namespace BraidWord

open BraidGroup PDCode

variable {n : ℕ} (w : BraidWord (n + 1)) (ε : ℤˣ)

/-- The crossings of the stabilized word: those of `w`, followed by the new one. -/
private def stabilizeCrossingEquiv : Fin (w.length + 1) ≃ Fin (w.stabilize ε).length :=
  finCongr (length_stabilize w ε).symm

private theorem val_stabilizeCrossingEquiv (j : Fin (w.length + 1)) :
    (w.stabilizeCrossingEquiv ε j).1 = j.1 :=
  (rfl)

private theorem getElem_stabilize_castSucc (j : Fin w.length) :
    (w.stabilize ε)[(w.stabilizeCrossingEquiv ε j.castSucc).1] =
      ((w[j.1].1.castSucc : Fin (n + 1)), w[j.1].2) := by
  simp only [val_stabilizeCrossingEquiv, Fin.val_castSucc, stabilize_def, strandIncl_def]
  rw [List.getElem_append_left (by simp), List.getElem_map]

private theorem getElem_stabilize_last :
    (w.stabilize ε)[(w.stabilizeCrossingEquiv ε (Fin.last _)).1] = (Fin.last n, ε) := by
  simp only [val_stabilizeCrossingEquiv, Fin.val_last, stabilize_def, strandIncl_def]
  rw [List.getElem_append_right (by simp)]
  simp

private theorem strand_castSucc (a : Fin (n + 1 - 1)) :
    strand (n := n + 2) (a.castSucc : Fin (n + 1)) = (strand a).castSucc :=
  Fin.ext (by simp)

private theorem strandSucc_castSucc (a : Fin (n + 1 - 1)) :
    strandSucc (n := n + 2) (a.castSucc : Fin (n + 1)) = (strandSucc a).castSucc :=
  Fin.ext (by simp)

private theorem strand_last : strand (n := n + 2) (Fin.last n) = (Fin.last n).castSucc :=
  Fin.ext (by simp)

private theorem strandSucc_last : strandSucc (n := n + 2) (Fin.last n) = Fin.last (n + 1) :=
  Fin.ext (by simp)

/-- The old crossings of the stabilized word, in its crossing numbering. -/
private abbrev oldCrossing (j : Fin w.length) : Fin (w.stabilize ε).length :=
  w.stabilizeCrossingEquiv ε j.castSucc

/-- The new crossing of the stabilized word. -/
private abbrev newCrossing : Fin (w.stabilize ε).length :=
  w.stabilizeCrossingEquiv ε (Fin.last _)

private theorem oldCrossing_injective : Function.Injective (w.oldCrossing ε) :=
  (w.stabilizeCrossingEquiv ε).injective.comp (Fin.castSucc_injective _)

private theorem oldCrossing_strictMono : StrictMono (w.oldCrossing ε) :=
  fun _ _ h ↦ Fin.lt_def.2 (by simpa [val_stabilizeCrossingEquiv] using h)

private theorem oldCrossing_lt_newCrossing (j : Fin w.length) :
    w.oldCrossing ε j < w.newCrossing ε :=
  Fin.lt_def.2 (by simp [val_stabilizeCrossingEquiv])

private theorem oldCrossing_ne_newCrossing (j : Fin w.length) :
    w.oldCrossing ε j ≠ w.newCrossing ε :=
  (w.oldCrossing_lt_newCrossing ε j).ne

private theorem forall_crossing_stabilize {P : Fin (w.stabilize ε).length → Prop}
    (hold : ∀ j, P (w.oldCrossing ε j)) (hnew : P (w.newCrossing ε)) : ∀ j, P j := by
  intro j
  obtain ⟨j, rfl⟩ := (w.stabilizeCrossingEquiv ε).surjective j
  induction j using Fin.lastCases with
  | last => exact hnew
  | cast j => exact hold j

/-- Along an old strand position, the stabilized word meets the old crossings in the same order,
and on the last old position it meets the new crossing last. -/
private theorem crossingsAt_stabilize_castSucc (p : Fin (n + 1)) :
    (w.stabilize ε).crossingsAt p.castSucc =
      (w.crossingsAt p).map (w.oldCrossing ε) ++
        if p = Fin.last n then [w.newCrossing ε] else [] := by
  apply List.SortedLT.eq_of_mem_iff (sortedLT_crossingsAt _ _)
  · rw [List.sortedLT_append, (w.oldCrossing_strictMono ε).sortedLT_listMap]
    refine ⟨sortedLT_crossingsAt _ _, ?_, ?_⟩
    · split_ifs <;> simp [List.sortedLT_nil, List.sortedLT_cons]
    · intro a ha b hb
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
      split_ifs at hb <;> simp_all [w.oldCrossing_lt_newCrossing ε]
  · refine w.forall_crossing_stabilize ε (fun j ↦ ?_) ?_
    · simp only [mem_crossingsAt, getElem_stabilize_castSucc, strand_castSucc,
        strandSucc_castSucc, Fin.castSucc_inj, List.mem_append, List.mem_map,
        (w.oldCrossing_injective ε).eq_iff, exists_eq_right]
      split_ifs <;> simp [w.oldCrossing_ne_newCrossing ε]
    · simp only [mem_crossingsAt, getElem_stabilize_last, strand_last, strandSucc_last,
        Fin.castSucc_inj, List.mem_append, List.mem_map, Fin.castSucc_ne_last]
      split_ifs with hp <;>
        simp [hp]

/-- The new strand position meets only the new crossing. -/
private theorem crossingsAt_stabilize_last :
    (w.stabilize ε).crossingsAt (Fin.last (n + 1)) = [w.newCrossing ε] := by
  apply List.SortedLT.eq_of_mem_iff (sortedLT_crossingsAt _ _)
    (List.sortedLT_iff_pairwise.2 (List.pairwise_singleton _ _))
  refine w.forall_crossing_stabilize ε (fun j ↦ ?_) ?_
  · simp only [mem_crossingsAt, getElem_stabilize_castSucc, strand_castSucc,
      strandSucc_castSucc, List.mem_singleton, w.oldCrossing_ne_newCrossing ε, iff_false]
    simp [Fin.ext_iff]
    omega
  · simp only [mem_crossingsAt, getElem_stabilize_last, strandSucc_last, List.mem_singleton]
    simp

/-- On an old strand position other than the last, the stabilized word passes through the old
crossings as `w` does. -/
private theorem nextCrossing_stabilize_castSucc {p : Fin (n + 1)} (hp : p ≠ Fin.last n)
    (j : Fin w.length) :
    (w.stabilize ε).nextCrossing p.castSucc (w.oldCrossing ε j) =
      w.oldCrossing ε (w.nextCrossing p j) := by
  rw [nextCrossing_def, crossingsAt_stabilize_castSucc, ite_eq_right hp, List.append_nil,
    List.formPerm_map_apply (w.oldCrossing_injective ε), nextCrossing_def]

/-- On the last old position, the stabilized word passes through the new crossing right after the
topmost old crossing `t`. -/
private theorem nextCrossing_stabilize_castSucc_last {l : List (Fin w.length)} {t : Fin w.length}
    (hl : w.crossingsAt (Fin.last n) = l ++ [t]) :
    (w.stabilize ε).nextCrossing (Fin.last n).castSucc =
      ((w.crossingsAt (Fin.last n)).map (w.oldCrossing ε)).formPerm *
        Equiv.swap (w.oldCrossing ε t) (w.newCrossing ε) := by
  rw [nextCrossing_def, crossingsAt_stabilize_castSucc, ite_eq_left rfl, hl, List.map_append,
    List.map_singleton, List.append_assoc, List.singleton_append, List.formPerm_append_pair]

/-- If no old crossing involves the last old position, the stabilized word meets only the new
crossing there. -/
private theorem nextCrossing_stabilize_castSucc_last_of_nil
    (hl : w.crossingsAt (Fin.last n) = []) :
    (w.stabilize ε).nextCrossing (Fin.last n).castSucc = 1 := by
  rw [nextCrossing_def, crossingsAt_stabilize_castSucc, ite_eq_left rfl, hl, List.map_nil,
    List.nil_append, List.formPerm_singleton]

/-- The new strand position meets only the new crossing. -/
private theorem nextCrossing_stabilize_last :
    (w.stabilize ε).nextCrossing (Fin.last (n + 1)) = 1 := by
  rw [nextCrossing_def, crossingsAt_stabilize_last, List.formPerm_singleton]

/-- The old crossings enter and leave the old positions at the same slots as in `w`. -/
private theorem incomingSlot_stabilize_oldCrossing {j : Fin w.length} {p : Fin (n + 1)}
    (hj : j ∈ w.crossingsAt p) :
    (w.stabilize ε).incomingSlot (w.oldCrossing ε j) p.castSucc = w.incomingSlot j p := by
  have hs := (w.stabilize ε).incomingSlot_strand (w.oldCrossing ε j)
  have hs' := (w.stabilize ε).incomingSlot_strandSucc (w.oldCrossing ε j)
  rw [getElem_stabilize_castSucc] at hs hs'
  rw [strand_castSucc] at hs
  rw [strandSucc_castSucc] at hs'
  rcases (w.mem_crossingsAt).1 hj with rfl | rfl
  · rw [hs, incomingSlot_strand]
  · rw [hs', incomingSlot_strandSucc]

private theorem outgoingSlot_stabilize_oldCrossing {j : Fin w.length} {p : Fin (n + 1)}
    (hj : j ∈ w.crossingsAt p) :
    (w.stabilize ε).outgoingSlot (w.oldCrossing ε j) p.castSucc = w.outgoingSlot j p := by
  have hs := (w.stabilize ε).outgoingSlot_strand (w.oldCrossing ε j)
  have hs' := (w.stabilize ε).outgoingSlot_strandSucc (w.oldCrossing ε j)
  rw [getElem_stabilize_castSucc] at hs hs'
  rw [strand_castSucc] at hs
  rw [strandSucc_castSucc] at hs'
  rcases (w.mem_crossingsAt).1 hj with rfl | rfl
  · rw [hs, outgoingSlot_strand]
  · rw [hs', outgoingSlot_strandSucc]

/-- The new crossing is entered from below at slot `3` on the last old position. -/
private theorem incomingSlot_stabilize_newCrossing_castSucc :
    (w.stabilize ε).incomingSlot (w.newCrossing ε) (Fin.last n).castSucc = 3 := by
  have hs := (w.stabilize ε).incomingSlot_strand (w.newCrossing ε)
  rwa [getElem_stabilize_last, strand_last] at hs

private theorem outgoingSlot_stabilize_newCrossing_castSucc :
    (w.stabilize ε).outgoingSlot (w.newCrossing ε) (Fin.last n).castSucc = 2 := by
  have hs := (w.stabilize ε).outgoingSlot_strand (w.newCrossing ε)
  rwa [getElem_stabilize_last, strand_last] at hs

private theorem incomingSlot_stabilize_newCrossing_last :
    (w.stabilize ε).incomingSlot (w.newCrossing ε) (Fin.last (n + 1)) = 0 := by
  have hs := (w.stabilize ε).incomingSlot_strandSucc (w.newCrossing ε)
  rwa [getElem_stabilize_last, strandSucc_last] at hs

private theorem outgoingSlot_stabilize_newCrossing_last :
    (w.stabilize ε).outgoingSlot (w.newCrossing ε) (Fin.last (n + 1)) = 1 := by
  have hs := (w.stabilize ε).outgoingSlot_strandSucc (w.newCrossing ε)
  rwa [getElem_stabilize_last, strandSucc_last] at hs

/-- The stabilized word has the old crossing-free positions except the last old one, which the new
crossing involves. -/
private theorem card_crossingsAt_stabilize_eq_nil :
    (Finset.univ.filter fun q ↦ (w.stabilize ε).crossingsAt q = []).card +
        (if w.crossingsAt (Fin.last n) = [] then 1 else 0) =
      (Finset.univ.filter fun p ↦ w.crossingsAt p = []).card := by
  have hold (p : Fin (n + 1)) :
      (w.stabilize ε).crossingsAt p.castSucc = [] ↔ w.crossingsAt p = [] ∧ p ≠ Fin.last n := by
    rw [crossingsAt_stabilize_castSucc]
    split_ifs with hp <;> simp [hp]
  simp only [Finset.card_filter, Fin.sum_univ_castSucc (n := n + 1), hold,
    crossingsAt_stabilize_last, List.cons_ne_nil, ite_false, add_zero]
  rw [Fin.sum_univ_castSucc (n := n), Fin.sum_univ_castSucc (n := n)]
  simp [Fin.castSucc_ne_last]

/-! ### Facts about the closure of `w` -/

/-- `TauCeti.BraidWord.edgePair_closure_outgoingSlot` with the half-edges of the closure written
as crossing slots. -/
private theorem edgePair_closure_crossingSlotEquiv_outgoingSlot {j : Fin w.length} {p : Fin (n + 1)}
    (hj : j ∈ w.crossingsAt p) :
    w.closure.edgePair.val (crossingSlotEquiv w.length (j, w.outgoingSlot j p)) =
      crossingSlotEquiv w.length
        (w.nextCrossing p j, w.incomingSlot (w.nextCrossing p j) p) := by
  simpa only [crossing_closure] using w.edgePair_closure_outgoingSlot hj

/-! ### Case one: the last old position meets a crossing

Write the crossings on the last old position, from the bottom, as `l ++ [t]`. The arc of the
closure of `w` leaving the topmost crossing `t` upwards runs through the closure back to the
lowest crossing on that position. The stabilized closure is the closure of `w` with a kink added
to that arc, its new crossing read from slot `2`. -/

/-- The half-edge at which the arc leaving `t` upwards along the last old position enters the
next crossing. -/
private def kinkHalfEdge (t : Fin w.length) : Fin (4 * w.length) :=
  crossingSlotEquiv w.length
    (w.nextCrossing (Fin.last n) t, w.incomingSlot (w.nextCrossing (Fin.last n) t) (Fin.last n))

/-- The closure of `w` with a kink added to the arc ending at `w.kinkHalfEdge t`, the new crossing
read from slot `2`. -/
private def kinkCode (t : Fin w.length) : OrientedPDCode (w.length + 1) :=
  (((w.closure.reidemeisterOne (w.kinkHalfEdge t) (decide (ε = 1))).rotateCrossing
    (Fin.last _)).rotateCrossing (Fin.last _))

/-- The half-edge renaming identifying `w.kinkCode ε t` with the stabilized closure. -/
private def kinkHalf (t : Fin w.length) :
    Fin (4 * (w.length + 1)) ≃ Fin (4 * (w.stabilize ε).length) :=
  (w.kinkCode ε t).halfEdge.symm.trans (crossingBlockEquiv (w.stabilizeCrossingEquiv ε))

variable (t : Fin w.length)

private theorem kinkCode_halfEdge_castSucc (j : Fin w.length) (slot : Fin 4) :
    (w.kinkCode ε t).halfEdge (crossingSlotEquiv _ (j.castSucc, slot)) =
      halfEdgeSuccEquiv _ (.inl (crossingSlotEquiv _ (j, slot))) := by
  have hne : j.castSucc ≠ Fin.last w.length := Fin.castSucc_ne_last j
  simp only [kinkCode, OrientedPDCode.toPDCode_rotateCrossing,
    PDCode.rotateCrossing_crossing_of_ne _ _ hne]
  rw [crossingSlotEquiv_succ_castSucc, OrientedPDCode.toPDCode_reidemeisterOne,
    reidemeisterOne_crossing_castSucc, crossing_closure]

private theorem kinkCode_halfEdge_last (slot : Fin 4) :
    (w.kinkCode ε t).halfEdge (crossingSlotEquiv _ (Fin.last _, slot)) =
      halfEdgeSuccEquiv _ (.inr (slot + 2)) := by
  simp only [kinkCode, OrientedPDCode.toPDCode_rotateCrossing,
    PDCode.rotateCrossing_crossing_self]
  simp only [crossingSlotEquiv_succ_last, OrientedPDCode.toPDCode_reidemeisterOne,
    reidemeisterOne_crossing_last, add_assoc, Fin.reduceAdd]

private theorem kinkHalf_inl (j : Fin w.length) (slot : Fin 4) :
    w.kinkHalf ε t (halfEdgeSuccEquiv _ (.inl (crossingSlotEquiv _ (j, slot)))) =
      crossingSlotEquiv _ (w.oldCrossing ε j, slot) := by
  rw [← kinkCode_halfEdge_castSucc, kinkHalf, Equiv.trans_apply, Equiv.symm_apply_apply,
    crossingBlockEquiv_apply_crossingSlotEquiv]

private theorem kinkHalf_inr (slot : Fin 4) :
    w.kinkHalf ε t (halfEdgeSuccEquiv _ (.inr slot)) =
      crossingSlotEquiv _ (w.newCrossing ε, slot + 2) := by
  have h := w.kinkCode_halfEdge_last ε t (slot + 2)
  simp only [add_assoc, Fin.reduceAdd, add_zero] at h
  rw [← h, kinkHalf, Equiv.trans_apply, Equiv.symm_apply_apply,
    crossingBlockEquiv_apply_crossingSlotEquiv]

private theorem kinkHalf_symm_old (j : Fin w.length) (slot : Fin 4) :
    (w.kinkHalf ε t).symm (crossingSlotEquiv _ (w.oldCrossing ε j, slot)) =
      halfEdgeSuccEquiv _ (.inl (crossingSlotEquiv _ (j, slot))) := by
  rw [Equiv.symm_apply_eq, kinkHalf_inl]

private theorem kinkHalf_symm_new (slot : Fin 4) :
    (w.kinkHalf ε t).symm (crossingSlotEquiv _ (w.newCrossing ε, slot)) =
      halfEdgeSuccEquiv _ (.inr (slot + 2)) := by
  rw [Equiv.symm_apply_eq, kinkHalf_inr]
  simp only [add_assoc, Fin.reduceAdd, add_zero]

private theorem kinkCode_edgePair :
    (w.kinkCode ε t).edgePair =
      (w.closure.toPDCode.reidemeisterOne (w.kinkHalfEdge t) (decide (ε = 1))).edgePair := by
  simp only [kinkCode, OrientedPDCode.toPDCode_rotateCrossing, PDCode.rotateCrossing_edgePair,
    OrientedPDCode.toPDCode_reidemeisterOne]

variable {ε t} {l : List (Fin w.length)}

/-- Along the last old position, the stabilized word leaves the topmost old crossing `t` for the
new crossing, and the new crossing for the lowest old crossing; elsewhere it follows `w`. -/
private theorem nextCrossing_stabilize_oldCrossing (hl : w.crossingsAt (Fin.last n) = l ++ [t])
    {j : Fin w.length} {p : Fin (n + 1)} (hj : j ∈ w.crossingsAt p)
    (hjt : ¬(p = Fin.last n ∧ j = t)) :
    (w.stabilize ε).nextCrossing p.castSucc (w.oldCrossing ε j) =
      w.oldCrossing ε (w.nextCrossing p j) := by
  by_cases hp : p = Fin.last n
  · subst hp
    have hjt : j ≠ t := fun h ↦ hjt ⟨rfl, h⟩
    rw [w.nextCrossing_stabilize_castSucc_last ε hl, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne ((w.oldCrossing_injective ε).ne hjt)
        (w.oldCrossing_ne_newCrossing ε j),
      List.formPerm_map_apply (w.oldCrossing_injective ε), nextCrossing_def]
  · exact w.nextCrossing_stabilize_castSucc ε hp j

private theorem nextCrossing_stabilize_top (hl : w.crossingsAt (Fin.last n) = l ++ [t]) :
    (w.stabilize ε).nextCrossing (Fin.last n).castSucc (w.oldCrossing ε t) = w.newCrossing ε := by
  rw [w.nextCrossing_stabilize_castSucc_last ε hl, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    List.formPerm_apply_of_notMem]
  simp [w.oldCrossing_ne_newCrossing ε]

private theorem nextCrossing_stabilize_newCrossing (hl : w.crossingsAt (Fin.last n) = l ++ [t]) :
    (w.stabilize ε).nextCrossing (Fin.last n).castSucc (w.newCrossing ε) =
      w.oldCrossing ε (w.nextCrossing (Fin.last n) t) := by
  rw [w.nextCrossing_stabilize_castSucc_last ε hl, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
    List.formPerm_map_apply (w.oldCrossing_injective ε), nextCrossing_def]

/-- The arc of the closure of `w` leaving `t` upwards is the arc the kink cuts. -/
private theorem edgePair_closure_kinkHalfEdge (ht : t ∈ w.crossingsAt (Fin.last n)) :
    w.closure.edgePair.val (w.kinkHalfEdge t) =
      crossingSlotEquiv _ (t, w.outgoingSlot t (Fin.last n)) :=
  PerfectMatching.apply_eq_of_apply_eq _ (w.edgePair_closure_crossingSlotEquiv_outgoingSlot ht)

/-- Every arc of the stabilized closure, read from the crossing it leaves upwards, is the renamed
arc of `w.kinkCode ε t`. -/
private theorem edgePair_closure_stabilize_outgoingSlot
    (hl : w.crossingsAt (Fin.last n) = l ++ [t]) {i : Fin (w.stabilize ε).length}
    {q : Fin (n + 2)} (hi : i ∈ (w.stabilize ε).crossingsAt q) :
    (w.stabilize ε).closure.edgePair.val
        (crossingSlotEquiv _ (i, (w.stabilize ε).outgoingSlot i q)) =
      w.kinkHalf ε t ((w.kinkCode ε t).edgePair.val
        ((w.kinkHalf ε t).symm (crossingSlotEquiv _ (i, (w.stabilize ε).outgoingSlot i q)))) := by
  have ht : t ∈ w.crossingsAt (Fin.last n) := by simp [hl]
  have hbot := w.nextCrossing_mem_crossingsAt_iff.2 ht
  have hcut := w.edgePair_closure_kinkHalfEdge ht
  rw [edgePair_closure_crossingSlotEquiv_outgoingSlot _ hi, kinkCode_edgePair]
  obtain ⟨i, rfl⟩ := (w.stabilizeCrossingEquiv ε).surjective i
  induction i using Fin.lastCases with
  | cast j =>
    induction q using Fin.lastCases with
    | last =>
      rw [crossingsAt_stabilize_last, List.mem_singleton] at hi
      exact absurd hi (w.oldCrossing_ne_newCrossing ε j)
    | cast p =>
      have hj : j ∈ w.crossingsAt p := by
        simpa [crossingsAt_stabilize_castSucc, (w.oldCrossing_injective ε).eq_iff,
          w.oldCrossing_ne_newCrossing ε] using hi
      rw [outgoingSlot_stabilize_oldCrossing _ _ hj, kinkHalf_symm_old]
      by_cases hpt : p = Fin.last n ∧ j = t
      · -- The arc leaving `t` upwards along the last old position now enters the new crossing.
        obtain ⟨rfl, rfl⟩ := hpt
        rw [nextCrossing_stabilize_top _ hl, incomingSlot_stabilize_newCrossing_castSucc, ← hcut,
          reidemeisterOne_edgePair_inl_edgePair, kinkHalf_inr]
        simp only [Fin.reduceAdd]
      · -- Any other arc leaving an old crossing is an arc of the closure of `w` the kink misses.
        have hne : crossingSlotEquiv _ (j, w.outgoingSlot j p) ≠ w.kinkHalfEdge t := fun h ↦ by
          have h : w.outgoingSlot j p = w.incomingSlot _ (Fin.last n) :=
            congrArg Prod.snd ((crossingSlotEquiv _).injective h)
          rcases w.outgoingSlot_eq_one_or_two j p with h₁ | h₁ <;>
            rcases w.incomingSlot_eq_zero_or_three (w.nextCrossing (Fin.last n) t) (Fin.last n)
              with h₂ | h₂ <;>
            rw [h₁, h₂] at h <;> exact absurd h (by decide)
        have hne' : crossingSlotEquiv _ (j, w.outgoingSlot j p) ≠
            w.closure.edgePair.val (w.kinkHalfEdge t) := fun h ↦ by
          rw [hcut] at h
          obtain ⟨rfl, h⟩ := Prod.ext_iff.1 ((crossingSlotEquiv _).injective h)
          exact hpt ⟨w.eq_of_outgoingSlot_eq hj ht h, rfl⟩
        rw [nextCrossing_stabilize_oldCrossing _ hl hj hpt,
          incomingSlot_stabilize_oldCrossing _ _ (w.nextCrossing_mem_crossingsAt_iff.2 hj),
          reidemeisterOne_edgePair_inl_of_ne _ _ _ hne hne',
          w.edgePair_closure_crossingSlotEquiv_outgoingSlot hj,
          kinkHalf_inl]
  | last =>
    induction q using Fin.lastCases with
    | last =>
      -- The new strand position is the loop of the kink.
      simp only [outgoingSlot_stabilize_newCrossing_last, kinkHalf_symm_new,
        nextCrossing_stabilize_last, Equiv.Perm.one_apply, incomingSlot_stabilize_newCrossing_last,
        Fin.reduceAdd, reidemeisterOne_edgePair_inr_three, kinkHalf_inr]
    | cast p =>
      -- The arc leaving the new crossing along the last old position enters the lowest old
      -- crossing on that position.
      obtain rfl : p = Fin.last n := by
        by_contra hp
        simp [crossingsAt_stabilize_castSucc, hp] at hi
      simp only [outgoingSlot_stabilize_newCrossing_castSucc, kinkHalf_symm_new,
        nextCrossing_stabilize_newCrossing _ hl,
        incomingSlot_stabilize_oldCrossing _ _ hbot, Fin.reduceAdd,
        reidemeisterOne_edgePair_inr_zero, kinkHalfEdge, kinkHalf_inl]

private theorem kinkCode_orientation :
    (w.kinkCode ε t).orientation =
      (w.closure.reidemeisterOne (w.kinkHalfEdge t) (decide (ε = 1))).orientation := by
  simp only [kinkCode, OrientedPDCode.rotateCrossing_orientation]

private theorem kinkCode_overPair_castSucc (j : Fin w.length) :
    (w.kinkCode ε t).overPair j.castSucc = decide (w[j.1].2 = 1) := by
  have hne : j.castSucc ≠ Fin.last w.length := Fin.castSucc_ne_last j
  simp only [kinkCode, OrientedPDCode.toPDCode_rotateCrossing,
    PDCode.rotateCrossing_overPair_of_ne _ _ hne,
    OrientedPDCode.toPDCode_reidemeisterOne, reidemeisterOne_overPair_castSucc, overPair_closure]

private theorem kinkCode_overPair_last :
    (w.kinkCode ε t).overPair (Fin.last _) = decide (ε = 1) := by
  simp only [kinkCode, OrientedPDCode.toPDCode_rotateCrossing, PDCode.rotateCrossing_overPair_self,
    OrientedPDCode.toPDCode_reidemeisterOne, reidemeisterOne_overPair_last, Bool.not_not]

/-- **The closure of a stabilized word is a kink added to the closure of `w`**, when an old crossing
involves the last old position, with topmost such crossing `t`. -/
private theorem closure_stabilize_eq_relabel_kinkCode
    (hl : w.crossingsAt (Fin.last n) = l ++ [t]) :
    (w.stabilize ε).closure =
      (w.kinkCode ε t).relabel (w.kinkHalf ε t) (w.stabilizeCrossingEquiv ε) := by
  have hbot := w.incomingSlot_eq_zero_or_three (w.nextCrossing (Fin.last n) t) (Fin.last n)
  have hcount := w.card_crossingsAt_stabilize_eq_nil ε
  rw [hl, ite_eq_right (List.concat_ne_nil t l), add_zero] at hcount
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · ext x
      simp [kinkHalf, Equiv.equivCongr_apply_apply, -crossingBlockEquiv_symm]
    · refine edgePair_closure_eq_of_outgoingSlot _ fun i q hi ↦ ?_
      rw [edgePair_closure_stabilize_outgoingSlot _ hl hi, OrientedPDCode.relabel_toPDCode,
        relabel_edgePair, PerfectMatching.congr_val_apply]
    · simp only [crossinglessComponentCount_closure, OrientedPDCode.relabel_toPDCode,
        relabel_crossinglessComponentCount, kinkCode,
        OrientedPDCode.toPDCode_rotateCrossing, PDCode.rotateCrossing_crossinglessComponentCount,
        OrientedPDCode.toPDCode_reidemeisterOne,
        reidemeisterOne_crossinglessComponentCount, hcount]
    · funext i
      obtain ⟨i, rfl⟩ := (w.stabilizeCrossingEquiv ε).surjective i
      rw [overPair_closure, OrientedPDCode.relabel_toPDCode, relabel_overPair,
        Equiv.symm_apply_apply]
      induction i using Fin.lastCases with
      | last => rw [getElem_stabilize_last, kinkCode_overPair_last]
      | cast j => rw [getElem_stabilize_castSucc, kinkCode_overPair_castSucc]
  · funext x
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv _).surjective x
    obtain ⟨i, rfl⟩ := (w.stabilizeCrossingEquiv ε).surjective i
    rw [orientation_closure, OrientedPDCode.relabel_orientation]
    induction i using Fin.lastCases with
    | last =>
      have hh : w.closure.orientation (w.kinkHalfEdge t) = false := by
        rcases hbot with h | h <;> rw [kinkHalfEdge, h, orientation_closure] <;> decide
      rw [kinkHalf_symm_new, kinkCode_orientation]
      fin_cases slot <;> simp [hh]
    | cast j =>
      rw [kinkHalf_symm_old, kinkCode_orientation, OrientedPDCode.orientation_reidemeisterOne_inl,
        orientation_closure]
  · simp only [crossinglessComponents_closure, OrientedPDCode.relabel_crossinglessComponents,
      kinkCode, OrientedPDCode.rotateCrossing_crossinglessComponents,
      OrientedPDCode.crossinglessComponents_reidemeisterOne, hcount]

/-! ### Case two: the last old position meets no crossing

Then the last old position closes up to a crossing-free circle of the closure of `w`, and the
stabilized closure is that circle with a kink added. -/

variable {D₀ : OrientedPDCode w.length}

/-- Every arc of the stabilized closure, read from the crossing it leaves upwards, is the renamed
arc of the code with an isolated kink in place of the last old position. -/
private theorem edgePair_closure_stabilize_outgoingSlot_of_nil
    (hl : w.crossingsAt (Fin.last n) = []) (hD₀ : w.closure = D₀.adjoinCircle true)
    {i : Fin (w.stabilize ε).length} {q : Fin (n + 2)} (hi : i ∈ (w.stabilize ε).crossingsAt q) :
    (w.stabilize ε).closure.edgePair.val
        (crossingSlotEquiv _ (i, (w.stabilize ε).outgoingSlot i q)) =
      crossingBlockEquiv (w.stabilizeCrossingEquiv ε)
        ((D₀.adjoinKink true (decide (ε = 1))).edgePair.val
          ((crossingBlockEquiv (w.stabilizeCrossingEquiv ε)).symm
            (crossingSlotEquiv _ (i, (w.stabilize ε).outgoingSlot i q)))) := by
  have hedge : D₀.edgePair = w.closure.edgePair := by
    rw [hD₀, OrientedPDCode.toPDCode_adjoinCircle, adjoinCircle_edgePair]
  rw [edgePair_closure_crossingSlotEquiv_outgoingSlot _ hi, crossingBlockEquiv_symm,
    crossingBlockEquiv_apply_crossingSlotEquiv, OrientedPDCode.toPDCode_adjoinKink]
  obtain ⟨i, rfl⟩ := (w.stabilizeCrossingEquiv ε).surjective i
  rw [Equiv.symm_apply_apply]
  induction i using Fin.lastCases with
  | cast j =>
    induction q using Fin.lastCases with
    | last =>
      rw [crossingsAt_stabilize_last, List.mem_singleton] at hi
      exact absurd hi (w.oldCrossing_ne_newCrossing ε j)
    | cast p =>
      have hj : j ∈ w.crossingsAt p := by
        simpa [crossingsAt_stabilize_castSucc, (w.oldCrossing_injective ε).eq_iff,
          w.oldCrossing_ne_newCrossing ε] using hi
      have hp : p ≠ Fin.last n := by
        rintro rfl
        simp [hl] at hj
      rw [outgoingSlot_stabilize_oldCrossing _ _ hj, nextCrossing_stabilize_castSucc _ _ hp,
        incomingSlot_stabilize_oldCrossing _ _ (w.nextCrossing_mem_crossingsAt_iff.2 hj),
        crossingSlotEquiv_succ_castSucc, adjoinKink_edgePair_inl, hedge,
        w.edgePair_closure_crossingSlotEquiv_outgoingSlot hj, ← crossingSlotEquiv_succ_castSucc,
        crossingBlockEquiv_apply_crossingSlotEquiv]
  | last =>
    induction q using Fin.lastCases with
    | last =>
      rw [outgoingSlot_stabilize_newCrossing_last, nextCrossing_stabilize_last,
        Equiv.Perm.one_apply, incomingSlot_stabilize_newCrossing_last, crossingSlotEquiv_succ_last,
        adjoinKink_edgePair_inr, slotSmoothing_true]
      norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      rw [← crossingSlotEquiv_succ_last, crossingBlockEquiv_apply_crossingSlotEquiv]
    | cast p =>
      obtain rfl : p = Fin.last n := by
        by_contra hp
        simp [crossingsAt_stabilize_castSucc, hp] at hi
      rw [outgoingSlot_stabilize_newCrossing_castSucc,
        w.nextCrossing_stabilize_castSucc_last_of_nil ε hl, Equiv.Perm.one_apply,
        incomingSlot_stabilize_newCrossing_castSucc, crossingSlotEquiv_succ_last,
        adjoinKink_edgePair_inr, slotSmoothing_true]
      norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      rw [← crossingSlotEquiv_succ_last, crossingBlockEquiv_apply_crossingSlotEquiv]

/-- **The closure of a stabilized word is a kink added to a crossing-free circle of the closure of
`w`**, when no old crossing involves the last old position. -/
private theorem closure_stabilize_eq_relabel_adjoinKink
    (hl : w.crossingsAt (Fin.last n) = []) (hD₀ : w.closure = D₀.adjoinCircle true) :
    (w.stabilize ε).closure =
      (D₀.adjoinKink true (decide (ε = 1))).relabel
        (crossingBlockEquiv (w.stabilizeCrossingEquiv ε)) (w.stabilizeCrossingEquiv ε) := by
  have hcount := w.card_crossingsAt_stabilize_eq_nil ε
  rw [hl, ite_eq_left rfl] at hcount
  have hcc : true ::ₘ D₀.crossinglessComponents = w.closure.crossinglessComponents := by
    rw [hD₀, OrientedPDCode.crossinglessComponents_adjoinCircle]
  rw [crossinglessComponents_closure, ← hcount, Multiset.replicate_succ,
    Multiset.cons_inj_right] at hcc
  have hhalf : D₀.halfEdge = 1 := by
    rw [← halfEdge_closure w, hD₀, OrientedPDCode.toPDCode_adjoinCircle, adjoinCircle_halfEdge]
  have horient : D₀.orientation = w.closure.orientation := by
    rw [hD₀, OrientedPDCode.orientation_adjoinCircle]
  have hover : D₀.overPair = w.closure.overPair := by
    rw [hD₀, OrientedPDCode.toPDCode_adjoinCircle, adjoinCircle_overPair]
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · ext x
      simp [Equiv.equivCongr_apply_apply, hhalf, Equiv.permCongr_apply, -crossingBlockEquiv_symm]
    · refine edgePair_closure_eq_of_outgoingSlot _ fun i q hi ↦ ?_
      rw [edgePair_closure_stabilize_outgoingSlot_of_nil _ hl hD₀ hi,
        OrientedPDCode.relabel_toPDCode, relabel_edgePair, PerfectMatching.congr_val_apply]
    · rw [crossinglessComponentCount_closure, OrientedPDCode.relabel_toPDCode,
        relabel_crossinglessComponentCount, OrientedPDCode.toPDCode_adjoinKink,
        adjoinKink_crossinglessComponentCount, ← OrientedPDCode.crossinglessComponents_card, hcc,
        Multiset.card_replicate]
    · funext i
      obtain ⟨i, rfl⟩ := (w.stabilizeCrossingEquiv ε).surjective i
      rw [overPair_closure, OrientedPDCode.relabel_toPDCode, relabel_overPair,
        Equiv.symm_apply_apply, OrientedPDCode.toPDCode_adjoinKink, adjoinKink_overPair]
      induction i using Fin.lastCases with
      | last => rw [getElem_stabilize_last, Fin.snoc_last]
      | cast j => rw [getElem_stabilize_castSucc, Fin.snoc_castSucc, hover, overPair_closure]
  · funext x
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv _).surjective x
    obtain ⟨i, rfl⟩ := (w.stabilizeCrossingEquiv ε).surjective i
    rw [orientation_closure, OrientedPDCode.relabel_orientation, crossingBlockEquiv_symm,
      crossingBlockEquiv_apply_crossingSlotEquiv, Equiv.symm_apply_apply]
    induction i using Fin.lastCases with
    | last =>
      rw [crossingSlotEquiv_succ_last, OrientedPDCode.orientation_adjoinKink_inr]
      fin_cases slot <;> decide
    | cast j =>
      rw [crossingSlotEquiv_succ_castSucc, OrientedPDCode.orientation_adjoinKink_inl, horient,
        orientation_closure]
  · rw [crossinglessComponents_closure, OrientedPDCode.relabel_crossinglessComponents,
      OrientedPDCode.crossinglessComponents_adjoinKink, hcc]

/-! ### Stabilization is a first Reidemeister move -/

open OrientedPDCode in
/-- **Markov stabilization of a braid word is a first Reidemeister move on its closure.** Adding a
strand to a braid word and crossing it once with the previous last strand, in either sense, gives
a word whose closure is Reidemeister equivalent to the closure of the original word. -/
theorem reidemeisterEquiv_closure_stabilize (w : BraidWord (n + 1)) (ε : ℤˣ) :
    ReidemeisterEquiv (w.stabilize ε).closure w.closure := by
  rcases List.eq_nil_or_concat (w.crossingsAt (Fin.last n)) with hl | ⟨l, t, hl⟩
  · -- The last old position closes up to a crossing-free circle, to which a kink is added.
    have hmem : true ∈ w.closure.crossinglessComponents := by
      rw [crossinglessComponents_closure, Multiset.mem_replicate]
      exact ⟨Finset.card_ne_zero.2 ⟨Fin.last n, by simp [hl]⟩, rfl⟩
    obtain ⟨D₀, hD₀⟩ := exists_eq_adjoinCircle_of_mem hmem
    rw [closure_stabilize_eq_relabel_adjoinKink _ hl hD₀, hD₀]
    exact ((reidemeisterEquiv_adjoinKink _ _ _).trans (reidemeisterEquiv_relabel _ _ _)).symm
  · -- A kink is added to the arc running from the top of the last old position to its bottom.
    rw [List.concat_eq_append] at hl
    rw [closure_stabilize_eq_relabel_kinkCode _ hl, kinkCode]
    exact ((((reidemeisterEquiv_reidemeisterOne _ _ _).trans
      (reidemeisterEquiv_rotateCrossing _ _)).trans (reidemeisterEquiv_rotateCrossing _ _)).trans
      (reidemeisterEquiv_relabel _ _ _)).symm

end BraidWord

end TauCeti
