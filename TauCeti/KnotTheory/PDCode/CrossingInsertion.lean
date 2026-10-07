/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Kauffman
import TauCeti.GroupTheory.Perm.SumCongr

/-!
# Crossing insertion and the skein relation of the Kauffman bracket

Kauffman's bracket satisfies the skein relation: at a crossing of a diagram `D`,
`⟨D⟩ = A ⟨D_A⟩ + A⁻¹ ⟨D_B⟩`, where `D_A` and `D_B` are the diagrams obtained by smoothing that
crossing in its two ways. Together with its value on the unknot and its behaviour under adding a
disjoint circle, this determines the bracket. This file proves the relation for the state-sum
bracket `TauCeti.PDCode.kauffmanBracket` of PD-codes, at a crossing none of whose four arcs returns
to it.

On a PD-code `D` with `n` crossings, `TauCeti.PDCode.insertCrossing D p q b` adds such a crossing:
it cuts the arc `P` ending at the half-edge `p` and the arc `Q` ending at the half-edge `q`, and
routes them across each other through one new crossing, the last one, `Fin.last n`. With the slots
of a crossing in counterclockwise order, its slot `0` is joined to `p`, slot `1` to `q`, slot `2` to
the other end `D.edgePair.val p` of `P` and slot `3` to the other end `D.edgePair.val q` of `Q`, so
that `P` runs through slots `0` and `2` and `Q` through slots `1` and `3`. The Boolean `b` is the
over-pair indicator of the new crossing: with `b = false` the strand along `P` is over. The
insertion is meaningful for two distinct arcs, that is, for `q ≠ p` and `q ≠ D.edgePair.val p`,
and the results below assume this. Like `TauCeti.PDCode.insertClasp`, it is an algebraic operation
on the code: it makes no claim about planarity.

A smoothing of the new crossing joins the four cut ends in two pairs without crossing. One of them
joins `p` to `q` and `D.edgePair.val p` to `D.edgePair.val q`; this is the code
`TauCeti.PDCode.reconnect D p q`, in which only these two arcs of `D` change. The other joins `p`
to `D.edgePair.val q` and `q` to `D.edgePair.val p`, which is `D.reconnect p (D.edgePair.val q)`.
A state of the new code is a state of `D` together with a choice at the new crossing, and its
smoothed diagram is the smoothed diagram of the corresponding reconnection of `D`
(`TauCeti.PDCode.stateLoopCount_insertCrossing`). Summing over the states gives the **skein
relation** `TauCeti.PDCode.kauffmanBracket_insertCrossing`: the bracket of the new code is `a`
times the bracket of the reconnection by its `A`-smoothing plus `a⁻¹` times that of the
reconnection by its `B`-smoothing. Comparing the two crossings with opposite over-strands
eliminates one reconnection, `TauCeti.PDCode.kauffmanBracket_insertCrossing_sub`. Following the
strands instead of a smoothing, both of them go straight through the new crossing, so the
insertion keeps the number of components.

## Main definitions

* `TauCeti.PDCode.insertCrossing`: route two arcs across each other through a new crossing.

## Main results

* `TauCeti.PDCode.stateLoopCount_insertCrossing`: a state of the new code leaves as many circles
  as the corresponding reconnection of the old code.
* `TauCeti.PDCode.kauffmanBracket_insertCrossing`: the skein relation of the Kauffman bracket.
* `TauCeti.PDCode.kauffmanBracket_insertCrossing_sub`: `a` times the bracket with the strand along
  `Q` over, minus `a⁻¹` times the bracket with the strand along `P` over, is a multiple of the
  bracket of `D.reconnect p q`.
* `TauCeti.PDCode.crossingComponentCount_insertCrossing`: the insertion keeps the number of
  components.
* `TauCeti.PDCode.mirror_insertCrossing`: mirroring the new code inserts the crossing with the
  other strand over into the mirror code.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3,
  Definition 3.1 (the skein relation defining the bracket).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2-3 (the PD convention).
-/

public section

namespace TauCeti

open Equiv Equiv.Perm TemperleyLieb

namespace PDCode

variable {n : ℕ}

section Splice

/-! ### The arcs of an inserted crossing, on the old half-edges and the new slots

The arcs of a code with a crossing inserted are built as a perfect matching of `α ⊕ Fin 4`: `α`
holds the old half-edges and `Fin 4` the four slots of the new crossing. With `E` the old arcs, the
arcs from `p` to `E.val p` and from `q` to `E.val q` are cut and joined to the slots. These helpers
serve only the proofs in this file. -/

variable {α : Type*} [DecidableEq α] {p q : α}

/-- The old arcs together with the two local strands `0`-`2` and `1`-`3` of the new crossing. -/
private def strandMatching (E : PerfectMatching α) : PerfectMatching (α ⊕ Fin 4) :=
  PerfectMatching.mk (Perm.sumCongr E.val oppositeCrossingSlot)
    (fun x => by
      rcases x with x | t <;> simp only [Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr,
        E.apply_apply, oppositeCrossingSlot_apply_oppositeCrossingSlot])
    (fun x hx => by
      rcases x with x | t
      · exact E.apply_ne x (Sum.inl_injective hx)
      · exact Fin.oppositeCrossingSlot_ne t (Sum.inr_injective hx))

/-- The arcs of the code with a crossing inserted at the arcs ending at `p` and `q`: `p`, `q`,
`E.val p` and `E.val q` are joined to slots `0`, `1`, `2` and `3`, and every other half-edge to its
old partner. It is `TauCeti.PDCode.strandMatching` transported along the transpositions exchanging
`E.val p` with slot `0` and `E.val q` with slot `1`. -/
private def crossingMatching (E : PerfectMatching α) (p q : α) : PerfectMatching (α ⊕ Fin 4) :=
  PerfectMatching.congr (swap (.inl (E.val p)) (.inr 0) * swap (.inl (E.val q)) (.inr 1))
    (strandMatching E)

section Values

variable {E : PerfectMatching α}

omit [DecidableEq α] in
/-- The four ends of two distinct arcs are distinct, in both orders. -/
private theorem ends_ne (hqp : q ≠ p) (hqe : q ≠ E.val p) :
    p ≠ q ∧ q ≠ p ∧ p ≠ E.val p ∧ E.val p ≠ p ∧ p ≠ E.val q ∧ E.val q ≠ p ∧
      q ≠ E.val p ∧ E.val p ≠ q ∧ q ≠ E.val q ∧ E.val q ≠ q ∧
      E.val p ≠ E.val q ∧ E.val q ≠ E.val p := by
  have hpe : p ≠ E.val q := fun h => hqe (by rw [h, E.apply_apply])
  have hee : E.val p ≠ E.val q := fun h => hqp (E.val.injective h).symm
  exact ⟨hqp.symm, hqp, (E.apply_ne p).symm, E.apply_ne p, hpe, hpe.symm, hqe, hqe.symm,
    (E.apply_ne q).symm, E.apply_ne q, hee, hee.symm⟩

private theorem crossingMatching_val_apply (y : α ⊕ Fin 4) :
    (crossingMatching E p q).val y =
      swap (.inl (E.val p)) (.inr 0) (swap (.inl (E.val q)) (.inr 1)
        (Perm.sumCongr E.val oppositeCrossingSlot
          (swap (.inl (E.val q)) (.inr 1) (swap (.inl (E.val p)) (.inr 0) y)))) := by
  simp [crossingMatching, strandMatching, PerfectMatching.val_mk, Perm.mul_apply]

omit [DecidableEq α] in
/-- Two permutations of the half-edges of an inserted crossing agree once they agree at the four
ends of the two cut arcs, at every other old half-edge, and at the four new slots. -/
private theorem crossing_ext {F G : Perm (α ⊕ Fin 4)}
    (hp : F (.inl p) = G (.inl p)) (hq : F (.inl q) = G (.inl q))
    (hep : F (.inl (E.val p)) = G (.inl (E.val p))) (heq : F (.inl (E.val q)) = G (.inl (E.val q)))
    (hx : ∀ x, x ≠ p → x ≠ q → x ≠ E.val p → x ≠ E.val q → E.val x ≠ p → E.val x ≠ q →
      E.val x ≠ E.val p → E.val x ≠ E.val q → F (.inl x) = G (.inl x))
    (hi : ∀ i, F (.inr i) = G (.inr i)) : F = G := by
  ext y
  rcases y with x | i
  · by_cases hxp : x = p
    · subst hxp; exact hp
    by_cases hxq : x = q
    · subst hxq; exact hq
    by_cases hxe : x = E.val p
    · subst hxe; exact hep
    by_cases hxe' : x = E.val q
    · subst hxe'; exact heq
    refine hx x hxp hxq hxe hxe' (fun h => hxe (by rw [← h, E.apply_apply]))
      (fun h => hxe' (by rw [← h, E.apply_apply])) (fun h => hxp (E.val.injective h))
      (fun h => hxq (E.val.injective h))
  · exact hi i

variable (hqp : q ≠ p) (hqe : q ≠ E.val p)
include hqp hqe

/-- Smoothing the new crossing by `slotSmoothing true` joins `p` to `q` and `E.val p` to `E.val q`:
it is the traversal reconnected that way, with the four new slots spliced in. -/
private theorem sumCongr_slotSmoothing_true_mul_crossingMatching (T : Perm α) :
    Perm.sumCongr T (slotSmoothing true) * (crossingMatching E p q).val =
      Perm.sumCongr (T * (swap (E.val p) q).permCongr E.val) 1 * swap (.inl p) (.inr 1) *
        swap (.inl q) (.inr 0) * swap (.inl (E.val p)) (.inr 3) *
        swap (.inl (E.val q)) (.inr 2) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := ends_ne hqp hqe
  refine crossing_ext (E := E) (p := p) (q := q) ?_ ?_ ?_ ?_
    (fun x hxp hxq hxe hxe' _ hx₂ hx₃ hx₄ => ?_) (fun i => ?_)
  all_goals (try fin_cases i) <;> simp [crossingMatching_val_apply, swap_apply_def,
    oppositeCrossingSlot_eq_swap_mul_swap, *]

/-- Smoothing the new crossing by `slotSmoothing false` joins `p` to `E.val q` and `q` to `E.val p`:
it is the traversal reconnected that way, with the four new slots spliced in. -/
private theorem sumCongr_slotSmoothing_false_mul_crossingMatching (T : Perm α) :
    Perm.sumCongr T (slotSmoothing false) * (crossingMatching E p q).val =
      Perm.sumCongr (T * (swap (E.val p) (E.val q)).permCongr E.val) 1 * swap (.inl p) (.inr 3) *
        swap (.inl q) (.inr 2) * swap (.inl (E.val p)) (.inr 1) *
        swap (.inl (E.val q)) (.inr 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := ends_ne hqp hqe
  refine crossing_ext (E := E) (p := p) (q := q) ?_ ?_ ?_ ?_
    (fun x hxp hxq hxe hxe' _ _ hx₃ hx₄ => ?_) (fun i => ?_)
  all_goals (try fin_cases i) <;> simp [crossingMatching_val_apply, swap_apply_def,
    oppositeCrossingSlot_eq_swap_mul_swap, *]

/-- Following the strands through the new crossing restores the two cut arcs: it is the old
traversal `C * E.val` with the four new slots spliced in. -/
private theorem sumCongr_oppositeCrossingSlot_mul_crossingMatching (C : Perm α) :
    Perm.sumCongr C oppositeCrossingSlot * (crossingMatching E p q).val =
      Perm.sumCongr (C * E.val) 1 * swap (.inl p) (.inr 2) * swap (.inl q) (.inr 3) *
        swap (.inl (E.val p)) (.inr 0) * swap (.inl (E.val q)) (.inr 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := ends_ne hqp hqe
  refine crossing_ext (E := E) (p := p) (q := q) ?_ ?_ ?_ ?_
    (fun x hxp hxq hxe hxe' _ _ hx₃ hx₄ => ?_) (fun i => ?_)
  all_goals (try fin_cases i) <;> simp [crossingMatching_val_apply, swap_apply_def,
    oppositeCrossingSlot_eq_swap_mul_swap, *]

end Values

end Splice

section Insert

/-- **Crossing insertion**: route the arc of `D` ending at the half-edge `p` and the arc ending at
`q` across each other through a new crossing, with over-pair indicator `b`. The new crossing is
`Fin.last n`; its slots `0`, `1`, `2` and `3` are joined to `p`, `q`, `D.edgePair.val p` and
`D.edgePair.val q`, so the first arc runs through slots `0` and `2`, and the second through slots
`1` and `3`. With `b = false` the strand along the first arc is over, with `b = true` the strand
along the second. The insertion is meaningful for two distinct arcs, `q ≠ p` and
`q ≠ D.edgePair.val p`. -/
def insertCrossing (D : PDCode n) (p q : Fin (4 * n)) (b : Bool) : PDCode (n + 1) where
  halfEdge := (halfEdgeSuccEquiv n).permCongr (Perm.sumCongr D.halfEdge 1)
  edgePair := PerfectMatching.congr (halfEdgeSuccEquiv n) (crossingMatching D.edgePair p q)
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := Fin.snoc (α := fun _ => Bool) D.overPair b

variable (D : PDCode n) (p q : Fin (4 * n)) (b : Bool)

/-- The old crossings keep their half-edges. -/
@[simp] theorem insertCrossing_crossing_castSucc (i : Fin n) (slot : Fin 4) :
    (D.insertCrossing p q b).halfEdge
        (halfEdgeSuccEquiv n (.inl (crossingSlotEquiv n (i, slot)))) =
      halfEdgeSuccEquiv n (.inl (D.crossing i slot)) := by
  simp [insertCrossing, Equiv.permCongr_apply]

/-- The slots of the new crossing are the four new half-edges. -/
@[simp] theorem insertCrossing_crossing_last (slot : Fin 4) :
    (D.insertCrossing p q b).halfEdge (halfEdgeSuccEquiv n (.inr slot)) =
      halfEdgeSuccEquiv n (.inr slot) := by
  simp [insertCrossing, Equiv.permCongr_apply]

/-- The old crossings keep their over-strands. -/
@[simp] theorem insertCrossing_overPair_castSucc (i : Fin n) :
    (D.insertCrossing p q b).overPair i.castSucc = D.overPair i := by
  simp [insertCrossing]

/-- The over-pair indicator of the new crossing is `b`. -/
@[simp] theorem insertCrossing_overPair_last :
    (D.insertCrossing p q b).overPair (Fin.last n) = b := by
  simp [insertCrossing]

/-- The insertion keeps the crossing-free circles. -/
@[simp] theorem insertCrossing_crossinglessComponentCount :
    (D.insertCrossing p q b).crossinglessComponentCount = D.crossinglessComponentCount := (rfl)

private theorem insertCrossing_halfEdge :
    (D.insertCrossing p q b).halfEdge =
      (halfEdgeSuccEquiv n).permCongr (Perm.sumCongr D.halfEdge 1) := (rfl)

private theorem insertCrossing_overPair :
    (D.insertCrossing p q b).overPair = Fin.snoc (α := fun _ => Bool) D.overPair b := (rfl)

private theorem insertCrossing_edgePair_val :
    (D.insertCrossing p q b).edgePair.val =
      (halfEdgeSuccEquiv n).permCongr (crossingMatching D.edgePair p q).val :=
  PerfectMatching.congr_val _ _

/-- The values of the arcs of the new code at the old half-edges and the new slots. -/
private theorem insertCrossing_edgePair_apply (y : Fin (4 * n) ⊕ Fin 4) :
    (D.insertCrossing p q b).edgePair.val (halfEdgeSuccEquiv n y) =
      halfEdgeSuccEquiv n ((crossingMatching D.edgePair p q).val y) := by
  rw [insertCrossing_edgePair_val, Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- Mirroring the new code inserts the crossing with the other strand over into the mirror
code. -/
@[simp] theorem mirror_insertCrossing :
    (D.insertCrossing p q b).mirror = D.mirror.insertCrossing p q !b := by
  apply PDCode.ext
  · simp [insertCrossing]
  · simp [insertCrossing]
  · simp [insertCrossing]
  · funext i
    induction i using Fin.lastCases <;> simp

section EdgePair

variable {D p q} (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p)
include hqp hqe

/-- The half-edge `p` is joined to slot `0` of the new crossing. -/
@[simp] theorem insertCrossing_edgePair_inl_self :
    (D.insertCrossing p q b).edgePair.val (halfEdgeSuccEquiv n (.inl p)) =
      halfEdgeSuccEquiv n (.inr 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := ends_ne hqp hqe
  rw [insertCrossing_edgePair_apply, crossingMatching_val_apply]
  simp [swap_apply_def, oppositeCrossingSlot_eq_swap_mul_swap, *]

/-- Slot `0` of the new crossing is joined to the half-edge `p`. -/
@[simp] theorem insertCrossing_edgePair_inr_zero :
    (D.insertCrossing p q b).edgePair.val (halfEdgeSuccEquiv n (.inr 0)) =
      halfEdgeSuccEquiv n (.inl p) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := ends_ne hqp hqe
  rw [insertCrossing_edgePair_apply, crossingMatching_val_apply]
  simp [swap_apply_def, oppositeCrossingSlot_eq_swap_mul_swap, *]

/-- The half-edge `q` is joined to slot `1` of the new crossing. -/
@[simp] theorem insertCrossing_edgePair_inl_right :
    (D.insertCrossing p q b).edgePair.val (halfEdgeSuccEquiv n (.inl q)) =
      halfEdgeSuccEquiv n (.inr 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := ends_ne hqp hqe
  rw [insertCrossing_edgePair_apply, crossingMatching_val_apply]
  simp [swap_apply_def, oppositeCrossingSlot_eq_swap_mul_swap, *]

/-- Slot `1` of the new crossing is joined to the half-edge `q`. -/
@[simp] theorem insertCrossing_edgePair_inr_one :
    (D.insertCrossing p q b).edgePair.val (halfEdgeSuccEquiv n (.inr 1)) =
      halfEdgeSuccEquiv n (.inl q) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := ends_ne hqp hqe
  rw [insertCrossing_edgePair_apply, crossingMatching_val_apply]
  simp [swap_apply_def, oppositeCrossingSlot_eq_swap_mul_swap, *]

/-- The other end of the first cut arc is joined to slot `2` of the new crossing. -/
@[simp] theorem insertCrossing_edgePair_inl_edgePair_self :
    (D.insertCrossing p q b).edgePair.val (halfEdgeSuccEquiv n (.inl (D.edgePair.val p))) =
      halfEdgeSuccEquiv n (.inr 2) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := ends_ne hqp hqe
  rw [insertCrossing_edgePair_apply, crossingMatching_val_apply]
  simp [swap_apply_def, oppositeCrossingSlot_eq_swap_mul_swap, *]

/-- Slot `2` of the new crossing is joined to the other end of the first cut arc. -/
@[simp] theorem insertCrossing_edgePair_inr_two :
    (D.insertCrossing p q b).edgePair.val (halfEdgeSuccEquiv n (.inr 2)) =
      halfEdgeSuccEquiv n (.inl (D.edgePair.val p)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := ends_ne hqp hqe
  rw [insertCrossing_edgePair_apply, crossingMatching_val_apply]
  simp [swap_apply_def, oppositeCrossingSlot_eq_swap_mul_swap, *]

/-- The other end of the second cut arc is joined to slot `3` of the new crossing. -/
@[simp] theorem insertCrossing_edgePair_inl_edgePair_right :
    (D.insertCrossing p q b).edgePair.val (halfEdgeSuccEquiv n (.inl (D.edgePair.val q))) =
      halfEdgeSuccEquiv n (.inr 3) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := ends_ne hqp hqe
  rw [insertCrossing_edgePair_apply, crossingMatching_val_apply]
  simp [swap_apply_def, oppositeCrossingSlot_eq_swap_mul_swap, *]

/-- Slot `3` of the new crossing is joined to the other end of the second cut arc. -/
@[simp] theorem insertCrossing_edgePair_inr_three :
    (D.insertCrossing p q b).edgePair.val (halfEdgeSuccEquiv n (.inr 3)) =
      halfEdgeSuccEquiv n (.inl (D.edgePair.val q)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := ends_ne hqp hqe
  rw [insertCrossing_edgePair_apply, crossingMatching_val_apply]
  simp [swap_apply_def, oppositeCrossingSlot_eq_swap_mul_swap, *]

omit hqp hqe in
/-- Every half-edge off the two cut arcs keeps its old partner. -/
@[simp] theorem insertCrossing_edgePair_inl_of_ne {x : Fin (4 * n)} (hxp : x ≠ p) (hxq : x ≠ q)
    (hxe : x ≠ D.edgePair.val p) (hxe' : x ≠ D.edgePair.val q) :
    (D.insertCrossing p q b).edgePair.val (halfEdgeSuccEquiv n (.inl x)) =
      halfEdgeSuccEquiv n (.inl (D.edgePair.val x)) := by
  have h₁ : D.edgePair.val x ≠ D.edgePair.val p := fun h => hxp (D.edgePair.val.injective h)
  have h₂ : D.edgePair.val x ≠ D.edgePair.val q := fun h => hxq (D.edgePair.val.injective h)
  rw [insertCrossing_edgePair_apply, crossingMatching_val_apply]
  simp [swap_apply_def, hxe, hxe', h₁, h₂]

end EdgePair

variable {D p q b} (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p)
include hqp hqe

/-- **Circles after a crossing insertion.** A state of the new code leaves as many circles as its
restriction to the old crossings leaves in the reconnection of the old code by its smoothing at
the new crossing: `D.reconnect p q` when that choice is `b`, and
`D.reconnect p (D.edgePair.val q)` otherwise. -/
@[simp] theorem stateLoopCount_insertCrossing (s : Fin (n + 1) → Bool) :
    (D.insertCrossing p q b).stateLoopCount s =
      (D.reconnect p (if s (Fin.last n) = b then q else D.edgePair.val q)).stateLoopCount
        (Fin.init s) := by
  rw [stateLoopCount_def, stateLoopCount_def, statePerm_def, statePerm_def,
    smoothingTurn_eq_permCongr_sumCongr (insertCrossing_halfEdge D p q b),
    init_smoothingChoice_of_overPair_eq (insertCrossing_overPair D p q b),
    smoothingChoice_last_of_overPair_eq (insertCrossing_overPair D p q b),
    insertCrossing_edgePair_val, ← Equiv.permCongr_mul, Equiv.orbitCount_permCongr,
    smoothingTurn_reconnect, smoothingChoice_reconnect,
    reconnect_edgePair_val, reconnect_crossinglessComponentCount,
    insertCrossing_crossinglessComponentCount]
  by_cases hs : s (Fin.last n) = b
  · simp only [hs, ↓reduceIte, beq_self_eq_true]
    rw [sumCongr_slotSmoothing_true_mul_crossingMatching hqp hqe,
      Perm.orbitCount_sumCongr_one_mul_swap_mul_swap_mul_swap_mul_swap _ _ _ _ _ (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]
  · have hbne : (s (Fin.last n) == b) = false := by simpa using hs
    rw [hbne]
    simp only [hs, ↓reduceIte]
    rw [sumCongr_slotSmoothing_false_mul_crossingMatching hqp hqe,
      Perm.orbitCount_sumCongr_one_mul_swap_mul_swap_mul_swap_mul_swap _ _ _ _ _ (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]

/-- **The skein relation of the Kauffman bracket.** The bracket of a code with a crossing
inserted is `a` times the bracket of the reconnection by the `A`-smoothing of the new crossing plus
`a⁻¹` times the bracket of the reconnection by its `B`-smoothing. With `b = true` the
`A`-smoothing joins `p` to `q`, with `b = false` it joins `p` to `D.edgePair.val q`. -/
theorem kauffmanBracket_insertCrossing {R : Type*} [CommRing R] (a : Rˣ) :
    (D.insertCrossing p q b).kauffmanBracket a =
      a * (D.reconnect p (bif b then q else D.edgePair.val q)).kauffmanBracket a +
        ((a⁻¹ : Rˣ) : R) *
          (D.reconnect p (bif b then D.edgePair.val q else q)).kauffmanBracket a := by
  -- Split each state of the new code into a state of the old code and a choice at the new
  -- crossing; the two choices give one term of each reconnected bracket.
  rw [kauffmanBracket_def, kauffmanBracket_def, kauffmanBracket_def,
    ← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, stateLoopCount_insertCrossing hqp hqe, Fin.init_snoc,
    Fin.snoc_last, stateWeight_snoc, Units.val_mul]
  cases b <;> simp only [Bool.cond_true, Bool.cond_false, Bool.true_eq_false, Bool.false_eq_true,
    ↓reduceIte] <;> ring

/-- **Comparing the two crossings.** `a` times the bracket of `D.insertCrossing p q true`, whose
new crossing has the strand along the second arc over, minus `a⁻¹` times the bracket of
`D.insertCrossing p q false`, whose new crossing has the strand along the first arc over, is
`a ^ 2 - a⁻¹ ^ 2` times the bracket of `D.reconnect p q`: the reconnection joining `p` to
`D.edgePair.val q` cancels. -/
theorem kauffmanBracket_insertCrossing_sub {R : Type*} [CommRing R] (a : Rˣ) :
    a * (D.insertCrossing p q true).kauffmanBracket a -
        ((a⁻¹ : Rˣ) : R) * (D.insertCrossing p q false).kauffmanBracket a =
      ((a : R) ^ 2 - ((a⁻¹ : Rˣ) : R) ^ 2) * (D.reconnect p q).kauffmanBracket a := by
  rw [kauffmanBracket_insertCrossing hqp hqe, kauffmanBracket_insertCrossing hqp hqe]
  simp only [Bool.cond_true, Bool.cond_false]
  ring

/-- **Crossing insertion keeps the number of components**: both strands go straight through the
new crossing. -/
@[simp] theorem crossingComponentCount_insertCrossing :
    (D.insertCrossing p q b).crossingComponentCount = D.crossingComponentCount := by
  rw [crossingComponentCount_def, crossingComponentCount_def, componentPerm_def,
    componentPerm_def, crossingTurn_eq_permCongr_sumCongr (insertCrossing_halfEdge D p q b),
    insertCrossing_edgePair_val, ← Equiv.permCongr_mul, Equiv.orbitCount_permCongr,
    sumCongr_oppositeCrossingSlot_mul_crossingMatching hqp hqe,
    Perm.orbitCount_sumCongr_one_mul_swap_mul_swap_mul_swap_mul_swap _ _ _ _ _ (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]

end Insert

end PDCode

end TauCeti
