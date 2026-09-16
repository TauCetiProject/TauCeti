/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Components
public import TauCeti.KnotTheory.TemperleyLieb
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.LinearCombination

/-!
# The Kauffman bracket of a PD-code

Smoothing every crossing of a diagram in one of its two ways turns the diagram into a disjoint
union of circles. A **state** of a PD-code with `n` crossings is such a choice at each crossing,
recorded as `s : Fin n → Bool`, with `s i = true` selecting the `A`-smoothing at crossing `i`:
the smoothing that turns left off the over-strand, equivalently the one joining the two regions
swept out when the over-strand is rotated counterclockwise. With the four slots of a crossing in
counterclockwise order that smoothing takes each over-slot to the preceding slot, which is
`TauCeti.PDCode.slotSmoothing` applied to the code's own over-pair indicator; the `B`-smoothing
is the same construction applied to the complementary indicator.

Reconnecting the half-edges accordingly gives `TauCeti.PDCode.statePerm`, the traversal of the
smoothed diagram: cross an arc, then follow the smoothing at the crossing reached. Exactly as for
`TauCeti.PDCode.componentPerm`, each circle of the smoothed diagram carries two of its orbits, one
for each direction of travel, so `TauCeti.PDCode.stateLoopCount` halves the orbit count and adds
the crossing-free circles that the code records separately.

The **Kauffman bracket** is the resulting state sum `∑ s, a ^ (A(s) - B(s)) * δ ^ loops s`, formed
over a commutative ring with a distinguished unit `a` at the loop value
`δ = -(a ^ 2 + a⁻¹ ^ 2)` (`TauCeti.TemperleyLieb.jonesDelta`), which is the value at which the
Kauffman-bracket expansion of a crossing is invertible. The normalisation used here is that the
empty diagram has bracket `1`, so a code with no crossings and `c` circles has bracket `δ ^ c`;
Kauffman's `⟨·⟩`, normalised by `⟨unknot⟩ = 1`, is this divided by `δ`.

The bracket depends on a PD-code only through its relabelling class, and mirroring a code inverts
the unit `a`. On the one-crossing kink diagram `TauCeti.PDCode.kink` it takes the value
`-a ^ 3 * δ`, the framing factor of the first Reidemeister move. Whether the bracket descends from
diagrams to knots is the question of its behaviour under the Reidemeister moves, which are a
separate construction on PD-codes and are not treated here.

## Main definitions

* `TauCeti.PDCode.slotSmoothing`: the two smoothings of the four slots at a crossing.
* `TauCeti.PDCode.smoothingTurn`: the reconnection of the half-edges smoothing every crossing.
* `TauCeti.PDCode.smoothingChoice`: the over-pair indicator a state selects at each crossing.
* `TauCeti.PDCode.statePerm`: the traversal of the smoothed diagram.
* `TauCeti.PDCode.stateLoopCount`: the number of circles of the smoothed diagram.
* `TauCeti.PDCode.stateWeight`: the weight `a ^ (A(s) - B(s))` of a state.
* `TauCeti.PDCode.kauffmanBracket`: the Kauffman bracket state sum.
* `TauCeti.PDCode.kink`: the one-crossing kink diagram.

## Main results

* `TauCeti.PDCode.kauffmanBracket_relabel`: the bracket is invariant under relabelling.
* `TauCeti.PDCode.kauffmanBracket_mirror`: mirroring the code inverts the unit.
* `TauCeti.PDCode.kauffmanBracket_eq_jonesDelta_pow`: a code with no crossings and `c` circles has
  bracket `δ ^ c`.
* `TauCeti.PDCode.stateLoopCount_kink_true`, `TauCeti.PDCode.stateLoopCount_kink_false`: the two
  smoothings of a kink leave two circles and one circle.
* `TauCeti.PDCode.kauffmanBracket_kink`: the kink diagram has bracket `-a ^ 3 * δ`.
* `TauCeti.PDCode.crossingComponentCount_kink`: the kink has one component, so it is a diagram of
  a knot.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3
  (the Kauffman bracket and the Jones polynomial).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2-3 (the PD convention).
-/


public section

namespace TauCeti

open Equiv Equiv.Perm TemperleyLieb

namespace PDCode

variable {n : ℕ}

/-- The two smoothings of the four slots at a crossing, indexed by an over-pair indicator.
`slotSmoothing false` pairs slot `0` with slot `3` and slot `1` with slot `2`, and
`slotSmoothing true` pairs slot `0` with slot `1` and slot `2` with slot `3`: in both cases each
slot of the pair indicated is joined to the slot preceding it in the counterclockwise order.
Applied to `D.overPair i` it is therefore the `A`-smoothing at crossing `i`, the one turning left
off the over-strand, and applied to `!D.overPair i` the `B`-smoothing. -/
def slotSmoothing (b : Bool) : Equiv.Perm (Fin 4) :=
  if b then Equiv.swap 0 1 * Equiv.swap 2 3 else Equiv.swap 0 3 * Equiv.swap 1 2

/-- A local smoothing is an involution of the four slots. -/
@[simp]
theorem slotSmoothing_apply_apply (b : Bool) (slot : Fin 4) :
    slotSmoothing b (slotSmoothing b slot) = slot := by
  revert slot
  cases b <;> decide

/-- A local smoothing moves every slot: it pairs the four slots off into two arcs. -/
theorem slotSmoothing_ne (b : Bool) (slot : Fin 4) : slotSmoothing b slot ≠ slot := by
  revert slot
  cases b <;> decide

/-- A local smoothing never joins a slot to the opposite slot: the two arcs of a smoothing cut
across the two local strands instead of following them, which is what distinguishes a smoothing
from `TauCeti.PDCode.crossingTurn`. -/
theorem slotSmoothing_ne_oppositeCrossingSlot (b : Bool) (slot : Fin 4) :
    slotSmoothing b slot ≠ oppositeCrossingSlot slot := by
  have key : ∀ (c : Bool) (t : Fin 4), (slotSmoothing c t).val ≠ (t + 2).val := by
    intro c
    cases c <;> decide
  intro h
  exact key b slot (by rw [h, oppositeCrossingSlot_apply])

/-- The two local smoothings at a crossing are distinct. -/
theorem slotSmoothing_ne_slotSmoothing_not (b : Bool) : slotSmoothing b ≠ slotSmoothing !b := by
  cases b <;> decide

/-- Smooth every crossing of a PD-code, using at crossing `i` the local smoothing
`slotSmoothing (b i)`. This is the smoothing counterpart of `TauCeti.PDCode.crossingTurn`, which
instead follows a local strand through a crossing. -/
def smoothingTurn (D : PDCode n) (b : Fin n → Bool) : Equiv.Perm (Fin (4 * n)) :=
  D.halfEdge.permCongr
    ((crossingSlotEquiv n).permCongr (Equiv.prodCongrRight fun i => slotSmoothing (b i)))

/-- Smoothing reconnects the slots at a crossing by the chosen local smoothing. -/
@[simp] theorem smoothingTurn_crossing (D : PDCode n) (b : Fin n → Bool) (i : Fin n)
    (slot : Fin 4) :
    D.smoothingTurn b (D.halfEdge (crossingSlotEquiv n (i, slot))) =
      D.crossing i (slotSmoothing (b i) slot) := by
  simp [smoothingTurn]

/-- Smoothing is an involution of the half-edges. -/
@[simp] theorem smoothingTurn_apply_apply (D : PDCode n) (b : Fin n → Bool) (h : Fin (4 * n)) :
    D.smoothingTurn b (D.smoothingTurn b h) = h := by
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective h
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  simp [smoothingTurn]

/-- Mirroring a code does not change how a prescribed family of local smoothings reconnects its
half-edges; only which of them is the `A`-smoothing changes. -/
@[simp] theorem smoothingTurn_mirror (D : PDCode n) (b : Fin n → Bool) :
    D.mirror.smoothingTurn b = D.smoothingTurn b := by
  simp [smoothingTurn]

/-- Relabelling conjugates smoothing by the half-edge relabelling, after transporting the family
of local smoothings along the crossing relabelling. -/
@[simp] theorem smoothingTurn_relabel (D : PDCode n) (b : Fin n → Bool)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).smoothingTurn b = half.permCongr (D.smoothingTurn (b ∘ cross)) := by
  ext h
  obtain ⟨x, rfl⟩ := half.surjective h
  obtain ⟨x, rfl⟩ := D.halfEdge.surjective x
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  have he : half (D.halfEdge (crossingSlotEquiv n (i, slot))) =
      (D.relabel half cross).halfEdge (crossingSlotEquiv n (cross i, slot)) := by
    rw [← D.crossing_apply, ← (D.relabel half cross).crossing_apply]
    simpa only [Equiv.symm_apply_apply] using (D.relabel_crossing half cross (cross i) slot).symm
  rw [he, smoothingTurn_crossing, relabel_crossing]
  simp

/-- The over-pair indicator of the local smoothing that a state selects at a crossing: the code's
own indicator where the state chooses the `A`-smoothing, and the complementary one where it
chooses the `B`-smoothing. -/
def smoothingChoice (D : PDCode n) (s : Fin n → Bool) (i : Fin n) : Bool :=
  bif s i then D.overPair i else !D.overPair i

/-- Where a state is `true` it selects the `A`-smoothing, the one built from the code's own
over-pair indicator. -/
@[simp] theorem smoothingChoice_of_true (D : PDCode n) {s : Fin n → Bool} {i : Fin n}
    (hs : s i = true) : D.smoothingChoice s i = D.overPair i := by
  simp [smoothingChoice, hs]

/-- Where a state is `false` it selects the `B`-smoothing, the one built from the complementary
over-pair indicator. -/
@[simp] theorem smoothingChoice_of_false (D : PDCode n) {s : Fin n → Bool} {i : Fin n}
    (hs : s i = false) : D.smoothingChoice s i = !D.overPair i := by
  simp [smoothingChoice, hs]

/-- Mirroring a code exchanges the `A`- and `B`-smoothings, so it acts on states by negation. -/
@[simp] theorem smoothingChoice_mirror (D : PDCode n) (s : Fin n → Bool) :
    D.mirror.smoothingChoice s = D.smoothingChoice fun j => !(s j) := by
  funext i
  cases hs : s i <;> simp [smoothingChoice, hs]

/-- Relabelling reads a state's choice at the old crossing name. -/
@[simp] theorem smoothingChoice_relabel (D : PDCode n) (s : Fin n → Bool)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).smoothingChoice s = D.smoothingChoice (s ∘ cross) ∘ cross.symm := by
  funext i
  simp [smoothingChoice]

/-- The traversal of the diagram smoothed according to the state `s`: cross an arc, then follow
the chosen smoothing at the crossing reached. Its orbits are the two directed traversals of each
circle of the smoothed diagram. -/
def statePerm (D : PDCode n) (s : Fin n → Bool) : Equiv.Perm (Fin (4 * n)) :=
  D.smoothingTurn (D.smoothingChoice s) * D.edgePair.val

/-- Smoothed traversal pairs the arc first, then follows the chosen smoothing. -/
@[simp] theorem statePerm_apply (D : PDCode n) (s : Fin n → Bool) (h : Fin (4 * n)) :
    D.statePerm s h = D.smoothingTurn (D.smoothingChoice s) (D.edgePair.val h) := by
  simp [statePerm, Equiv.Perm.mul_def]

/-- Mirroring a code negates the state that produces a given smoothed diagram. -/
@[simp] theorem statePerm_mirror (D : PDCode n) (s : Fin n → Bool) :
    D.mirror.statePerm s = D.statePerm fun i => !(s i) := by
  simp [statePerm]

/-- Relabelling conjugates smoothed traversal by the half-edge relabelling. -/
@[simp] theorem statePerm_relabel (D : PDCode n) (s : Fin n → Bool)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).statePerm s = half.permCongr (D.statePerm (s ∘ cross)) := by
  have hcomp : (D.smoothingChoice (s ∘ cross) ∘ cross.symm) ∘ cross
      = D.smoothingChoice (s ∘ cross) := by
    funext i
    simp
  rw [statePerm, statePerm, smoothingChoice_relabel, smoothingTurn_relabel, hcomp,
    relabel_edgePair, PerfectMatching.congr_val, ← Equiv.permCongr_mul]

/-- The number of circles of the diagram smoothed according to the state `s`, the crossing-free
circles of the code included. Each circle meeting a crossing is represented by the two directed
orbits of `TauCeti.PDCode.statePerm`, one for each direction of travel, exactly as for
`TauCeti.PDCode.crossingComponentCount`. -/
noncomputable def stateLoopCount (D : PDCode n) (s : Fin n → Bool) : ℕ :=
  orbitCount (D.statePerm s) / 2 + D.crossinglessComponentCount

/-- The number of circles of a smoothed diagram is half the number of directed traversal orbits,
plus the crossing-free circles. -/
theorem stateLoopCount_def (D : PDCode n) (s : Fin n → Bool) :
    D.stateLoopCount s = orbitCount (D.statePerm s) / 2 + D.crossinglessComponentCount := (rfl)

/-- A code with no crossings has one circle per crossing-free component, in every state. -/
@[simp] theorem stateLoopCount_eq_crossinglessComponentCount (D : PDCode 0) (s : Fin 0 → Bool) :
    D.stateLoopCount s = D.crossinglessComponentCount := by
  have h := Equiv.Perm.orbitCount_le_card (D.statePerm s)
  simp at h
  simp [stateLoopCount_def, h]

/-- Mirroring a code negates the state producing a given circle count. -/
@[simp] theorem stateLoopCount_mirror (D : PDCode n) (s : Fin n → Bool) :
    D.mirror.stateLoopCount s = D.stateLoopCount fun i => !(s i) := by
  simp [stateLoopCount_def]

/-- Relabelling preserves the circle count of every state. -/
@[simp] theorem stateLoopCount_relabel (D : PDCode n) (s : Fin n → Bool)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).stateLoopCount s = D.stateLoopCount (s ∘ cross) := by
  simp [stateLoopCount_def]

section Bracket

variable {R : Type*} [CommRing R]

/-- The weight of a state: the unit `a` at each `A`-smoothing and `a⁻¹` at each `B`-smoothing, so
that a state with `p` of the former and `q` of the latter has weight `a ^ (p - q)`. -/
def stateWeight (s : Fin n → Bool) (a : Rˣ) : Rˣ :=
  ∏ i, bif s i then a else a⁻¹

/-- Negating a state inverts its weight, since it exchanges the `A`- and `B`-smoothings. -/
@[simp] theorem stateWeight_not (s : Fin n → Bool) (a : Rˣ) :
    stateWeight (fun i => !(s i)) a = (stateWeight s a)⁻¹ := by
  rw [stateWeight, stateWeight, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases hs : s i <;> simp

/-- Inverting the unit inverts every state weight. -/
@[simp] theorem stateWeight_inv (s : Fin n → Bool) (a : Rˣ) :
    stateWeight s a⁻¹ = (stateWeight s a)⁻¹ := by
  rw [stateWeight, stateWeight, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases hs : s i <;> simp

/-- Transporting a state along a relabelling of the crossings preserves its weight. -/
@[simp] theorem stateWeight_comp (s : Fin n → Bool) (a : Rˣ) (cross : Equiv.Perm (Fin n)) :
    stateWeight (s ∘ cross) a = stateWeight s a :=
  Equiv.prod_comp cross fun i => bif s i then a else a⁻¹

/-- **The Kauffman bracket** of a PD-code at a unit `a`: the sum, over all `2 ^ n` states, of the
weight of the state times the loop value `TauCeti.TemperleyLieb.jonesDelta a` raised to the number
of circles of the smoothed diagram. The normalisation is that the empty diagram has bracket `1`,
so a code with no crossings and `c` circles has bracket `δ ^ c`, and Kauffman's `⟨·⟩` with
`⟨unknot⟩ = 1` is this divided by `δ`. -/
noncomputable def kauffmanBracket (D : PDCode n) (a : Rˣ) : R :=
  ∑ s : Fin n → Bool, (stateWeight s a : R) * jonesDelta a ^ D.stateLoopCount s

/-- The Kauffman bracket depends on a PD-code only through its relabelling class. -/
@[simp] theorem kauffmanBracket_relabel (D : PDCode n) (a : Rˣ)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).kauffmanBracket a = D.kauffmanBracket a := by
  refine Fintype.sum_bijective (fun s => s ∘ cross)
    (Function.bijective_iff_has_inverse.mpr ⟨fun s => s ∘ cross.symm, fun s => by
      funext i; simp, fun s => by funext i; simp⟩) _ _ fun s => ?_
  rw [stateLoopCount_relabel, stateWeight_comp]

/-- Mirroring a PD-code inverts the unit in its Kauffman bracket. -/
@[simp] theorem kauffmanBracket_mirror (D : PDCode n) (a : Rˣ) :
    D.mirror.kauffmanBracket a = D.kauffmanBracket a⁻¹ := by
  refine Fintype.sum_bijective (fun s i => !(s i))
    (Function.Involutive.bijective fun s => by funext i; simp) _ _ fun s => ?_
  rw [stateLoopCount_mirror, stateWeight_inv, stateWeight_not, inv_inv, jonesDelta_inv]

/-- A PD-code with no crossings and `c` crossing-free circles has Kauffman bracket `δ ^ c`. This
pins the normalisation of `TauCeti.PDCode.kauffmanBracket`: the empty diagram has bracket `1`, and
each further circle contributes one factor of the loop value. -/
theorem kauffmanBracket_eq_jonesDelta_pow (D : PDCode 0) (a : Rˣ) :
    D.kauffmanBracket a = jonesDelta a ^ D.crossinglessComponentCount := by
  rw [kauffmanBracket, Fintype.sum_unique]
  simp [stateWeight]

/-- The one-crossing knot diagram: a single kink. Its single crossing has the slot pair `1`-`3`
as its over-strand, and its two arcs join slot `0` to slot `1` and slot `2` to slot `3`, so the
strand doubles back on itself, as in the first Reidemeister move. -/
def kink : PDCode 1 where
  halfEdge := 1
  edgePair := PerfectMatching.congr (crossingSlotEquiv 1)
    (PerfectMatching.mk (Equiv.prodCongrRight fun _ => slotSmoothing true) (by decide) (by decide))
  crossinglessComponentCount := 0
  overPair := fun _ => true

/-- The kink numbers its half-edges by their crossing slots. -/
@[simp] theorem kink_halfEdge : kink.halfEdge = 1 := by simp [kink]

/-- The kink has no crossing-free component. -/
@[simp] theorem kink_crossinglessComponentCount : kink.crossinglessComponentCount = 0 := by
  simp [kink]

/-- The over-strand of the kink is the slot pair `1`-`3`. -/
@[simp] theorem kink_overPair (i : Fin 1) : kink.overPair i = true := by simp [kink]

/-- The half-edge of the kink in a given crossing slot is that slot. -/
@[simp] theorem kink_crossing (i : Fin 1) (t : Fin 4) :
    kink.crossing i t = crossingSlotEquiv 1 (i, t) := by
  rw [crossing_apply, kink_halfEdge]
  simp

/-- The two arcs of the kink join each slot of the over-pair to the slot preceding it. -/
@[simp] theorem kink_edgePair_apply (i : Fin 1) (t : Fin 4) :
    kink.edgePair.val (crossingSlotEquiv 1 (i, t))
      = crossingSlotEquiv 1 (i, slotSmoothing true t) := by
  simp [kink, PerfectMatching.congr_val, PerfectMatching.val_mk]

/-- Smoothing the kink reconnects its slots by the chosen local smoothing. -/
@[simp] theorem kink_smoothingTurn (b : Fin 1 → Bool) (i : Fin 1) (t : Fin 4) :
    kink.smoothingTurn b (crossingSlotEquiv 1 (i, t))
      = crossingSlotEquiv 1 (i, slotSmoothing (b i) t) := by
  have h := kink.smoothingTurn_crossing b i t
  rw [kink_halfEdge] at h
  simpa using h

/-- Following a strand of the kink through its crossing passes to the opposite slot. -/
@[simp] theorem kink_crossingTurn (i : Fin 1) (t : Fin 4) :
    kink.crossingTurn (crossingSlotEquiv 1 (i, t))
      = crossingSlotEquiv 1 (i, oppositeCrossingSlot t) := by
  have h := kink.crossingTurn_crossing i t
  rw [kink_halfEdge] at h
  simpa using h

/-- Traversing the kink alternates its arcs with the passage to the opposite slot. -/
private theorem kink_componentPerm : kink.componentPerm = (crossingSlotEquiv 1).permCongr
    (Equiv.prodCongrRight fun _ : Fin 1 => oppositeCrossingSlot * slotSmoothing true) := by
  refine Equiv.ext fun h => ?_
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv 1).surjective h
  rw [componentPerm_apply, kink_edgePair_apply, kink_crossingTurn]
  simp [Equiv.Perm.mul_apply]

/-- Following an arc of the kink and then passing to the opposite slot pairs slot `0` with slot
`3` and slot `1` with slot `2`. -/
private theorem oppositeCrossingSlot_mul_slotSmoothing_true :
    oppositeCrossingSlot * slotSmoothing true = Equiv.swap (0 : Fin 4) 3 * Equiv.swap 1 2 := by
  refine Equiv.ext fun t => ?_
  rw [← Fin.val_inj]
  simp only [Equiv.Perm.mul_apply, oppositeCrossingSlot_apply]
  revert t
  decide

/-- **The kink is a diagram of a knot**: it has a single component. -/
theorem crossingComponentCount_kink : kink.crossingComponentCount = 1 := by
  have h : orbitCount kink.componentPerm = 2 := by
    rw [kink_componentPerm, Equiv.orbitCount_permCongr,
      oppositeCrossingSlot_mul_slotSmoothing_true]
    have hperm : (Equiv.prodCongrRight fun _ : Fin 1 => Equiv.swap (0 : Fin 4) 3 * Equiv.swap 1 2)
        = Equiv.swap ((0 : Fin 1), (0 : Fin 4)) (0, 3) * Equiv.swap ((0 : Fin 1), (1 : Fin 4))
          (0, 2) := by
      decide
    have hcard : Nat.card (Fin 1 × Fin 4) = 4 := by simp
    have horbit := orbitCount_swap_mul_swap (x := ((0 : Fin 1), (0 : Fin 4))) (y := (0, 3))
      (z := (0, 1)) (w := (0, 2)) (by decide) (by decide) (by decide) (by decide)
    rw [hperm]
    omega
  rw [crossingComponentCount_def, h]

/-- The `A`-smoothing of the kink undoes its arcs, separating the strand into two circles. -/
private theorem kink_statePerm_true : kink.statePerm (fun _ => true) = 1 := by
  refine Equiv.ext fun h => ?_
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv 1).surjective h
  rw [statePerm_apply, kink_edgePair_apply, kink_smoothingTurn]
  simp

/-- The `B`-smoothing of the kink leaves a single circle. -/
private theorem kink_statePerm_false : kink.statePerm (fun _ => false) =
    (crossingSlotEquiv 1).permCongr
      (Equiv.prodCongrRight fun _ : Fin 1 => slotSmoothing false * slotSmoothing true) := by
  refine Equiv.ext fun h => ?_
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv 1).surjective h
  rw [statePerm_apply, kink_edgePair_apply, kink_smoothingTurn]
  simp [Equiv.Perm.mul_apply]

/-- **The `A`-smoothing of the kink leaves two circles.** -/
theorem stateLoopCount_kink_true : kink.stateLoopCount (fun _ => true) = 2 := by
  rw [stateLoopCount_def, kink_statePerm_true, orbitCount_one, kink_crossinglessComponentCount]
  simp

/-- **The `B`-smoothing of the kink leaves one circle.** -/
theorem stateLoopCount_kink_false : kink.stateLoopCount (fun _ => false) = 1 := by
  rw [stateLoopCount_def, kink_statePerm_false, Equiv.orbitCount_permCongr,
    kink_crossinglessComponentCount]
  have hperm : (Equiv.prodCongrRight fun _ : Fin 1 => slotSmoothing false * slotSmoothing true)
      = Equiv.swap ((0 : Fin 1), (1 : Fin 4)) (0, 3) * Equiv.swap ((0 : Fin 1), (0 : Fin 4))
        (0, 2) := by
    decide
  have hcard : Nat.card (Fin 1 × Fin 4) = 4 := by simp
  have horbit := orbitCount_swap_mul_swap (x := ((0 : Fin 1), (1 : Fin 4))) (y := (0, 3))
    (z := (0, 0)) (w := (0, 2)) (by decide) (by decide) (by decide) (by decide)
  rw [hperm]
  omega

/-- **The Kauffman bracket of the kink is `-a ^ 3` times that of the unknot.** The two smoothings
of the single crossing contribute `a * δ ^ 2` and `a⁻¹ * δ`, and the loop value collapses their
sum to `-a ^ 3 * δ`: this is the framing factor by which the bracket fails to be invariant under
the first Reidemeister move. -/
theorem kauffmanBracket_kink (a : Rˣ) :
    kink.kauffmanBracket a = -((a : R) ^ 3) * jonesDelta a := by
  have hbij : Function.Bijective (fun (b : Bool) (_ : Fin 1) => b) :=
    ⟨fun b c hbc => congrFun hbc 0, fun s => ⟨s 0, funext fun i => by
      rw [Subsingleton.elim i 0]⟩⟩
  rw [kauffmanBracket, ← Fintype.sum_bijective _ hbij
    (fun b => (stateWeight (fun _ : Fin 1 => b) a : R) * jonesDelta a ^
      kink.stateLoopCount fun _ => b) _ fun b => rfl, Fintype.sum_bool]
  simp only [stateLoopCount_kink_true, stateLoopCount_kink_false, stateWeight,
    Fin.prod_univ_one, Bool.cond_true, Bool.cond_false, jonesDelta_def]
  linear_combination (((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2) * ((a⁻¹ : Rˣ) : R)) * a.mul_inv

end Bracket

end PDCode

end TauCeti
