/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.FinCases

/-!
# PD-codes

A PD-code records finite combinatorial crossing data for a link. The `halfEdge` permutation lists
the four half-edges at each crossing, while the perfect matching `edgePair` joins the two
half-edges at the ends of each arc. Opposite slots form the two local strands, one of which is
selected by `overPair`. Crossing-free components are recorded separately.

`OrientedPDCode` decorates this data with compatible directions on the arcs and crossing-free
components. `FramedOrientedPDCode` further assigns an integer framing to every component. The
forgetful maps between these three presentation layers let results use only the data they need.

This is a code-level presentation: `PDCode` neither imposes planarity nor provides a geometric
realization, so these must be supplied separately. Keeping the code finite and explicit avoids
choosing a privileged geometric embedding.

The PD-code encoding adapts M. Mastin, *Links and Planar Diagram Codes*, Definitions 2--3,
which develops the Bar-Natan/KnotTheory PD convention. Mastin lists, at each crossing, the labels of
the four incident arcs counterclockwise from the incoming under-edge. Here `halfEdge` labels
half-edges rather than arcs, the four slots of a crossing are read counterclockwise from any
starting slot, the over-strand is recorded by the separate bit `overPair`, and crossing-free
components are counted separately. The diagram and crossing-sign conventions
follow W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175, Chapter 1. The framing
convention follows R. Gompf and A. Stipsicz, *4-Manifolds and Kirby Calculus*, GSM 20, Section 4.5,
especially Proposition 4.5.8.

## Main definitions

* `TauCeti.PDCode`: an unoriented PD-code with `n` crossings.
* `TauCeti.OrientedPDCode`: an orientation decoration of a PD-code.
* `TauCeti.FramedOrientedPDCode`: a framing decoration of an oriented PD-code.
* `TauCeti.PDCode.halfEdgeSuccEquiv`: the half-edge positions of a code with one crossing more.
* `TauCeti.PDCode.mirror` and `TauCeti.PDCode.relabel`: reflection and relabelling along
  equivalences of the finite index types.
* `TauCeti.PDCode.reconnect`: reconnect the arcs ending at two half-edges, joining them.
* `TauCeti.PDCode.slotSmoothing`: the two smoothings of the four slots at a crossing.
* `TauCeti.PDCode.kink`: the one-crossing kink diagram, and `TauCeti.OrientedPDCode.positiveKink`,
  its orientation with a positive crossing.
* `TauCeti.OrientedPDCode.reverse`: reversal of every component orientation.
* `TauCeti.OrientedPDCode.crossingSign`: the sign derived from the local oriented crossing data.
* `TauCeti.OrientedPDCode.writhe`: the sum of the crossing signs.

## Main results

* `TauCeti.OrientedPDCode.crossingSign_eq_one_iff` and
  `crossingSign_eq_neg_one_iff` characterize the two possible crossing signs.
* `TauCeti.PDCode.mirror_mirror` and `TauCeti.PDCode.relabel_relabel` give the basic operation
  laws.
* `TauCeti.OrientedPDCode.unlinkEquiv` classifies zero-crossing oriented PD-codes.
-/

public section

namespace TauCeti

namespace PDCode

/-- The standard equivalence between crossing-slot pairs and the `4 * n` half-edge positions. -/
def crossingSlotEquiv (n : ℕ) : Fin n × Fin 4 ≃ Fin (4 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 4))

/-- The crossing-slot equivalence numbers slot `s` at crossing `i` by `s + 4 * i`. -/
@[simp]
theorem crossingSlotEquiv_apply_val {n : ℕ} (i : Fin n) (slot : Fin 4) :
    (crossingSlotEquiv n (i, slot)).val = slot.val + 4 * i.val :=
  (rfl)

/-- The half-edge positions of a code with one crossing more: the `4 * n` positions of the first
`n` crossings, followed by the four slots of the new last crossing. -/
def halfEdgeSuccEquiv (n : ℕ) : Fin (4 * n) ⊕ Fin 4 ≃ Fin (4 * (n + 1)) :=
  finSumFinEquiv.trans (finCongr (by omega))

/-- A slot of one of the first `n` crossings keeps its half-edge position when a crossing is
added last. -/
@[simp]
theorem crossingSlotEquiv_succ_castSucc {n : ℕ} (i : Fin n) (slot : Fin 4) :
    crossingSlotEquiv (n + 1) (i.castSucc, slot) =
      halfEdgeSuccEquiv n (.inl (crossingSlotEquiv n (i, slot))) :=
  (rfl)

/-- The slots of the last crossing occupy the last four half-edge positions. -/
@[simp]
theorem crossingSlotEquiv_succ_last {n : ℕ} (slot : Fin 4) :
    crossingSlotEquiv (n + 1) (Fin.last n, slot) = halfEdgeSuccEquiv n (.inr slot) :=
  Fin.ext (Nat.add_comm _ _)

-- Not `@[simp]`: `crossingSlotEquiv_apply_val` already rewrites the left-hand side.
/-- The slot of a half-edge is recovered from its position modulo four. -/
theorem crossingSlotEquiv_apply_val_mod_four {n : ℕ} (i : Fin n) (slot : Fin 4) :
    (crossingSlotEquiv n (i, slot)).val % 4 = slot.val := by
  rw [crossingSlotEquiv_apply_val]
  omega

/-- A half-edge position of the first `n` crossings keeps its value when a crossing is added. -/
@[simp]
theorem halfEdgeSuccEquiv_apply_inl_val {n : ℕ} (x : Fin (4 * n)) :
    (halfEdgeSuccEquiv n (.inl x)).val = x.val :=
  (rfl)

/-- The slots of the added crossing follow the `4 * n` positions of the first `n` crossings. -/
@[simp]
theorem halfEdgeSuccEquiv_apply_inr_val {n : ℕ} (slot : Fin 4) :
    (halfEdgeSuccEquiv n (.inr slot)).val = slot.val + 4 * n :=
  Nat.add_comm _ _

/-- The slot opposite a given slot in the cyclic order at a crossing. -/
def oppositeCrossingSlot : Equiv.Perm (Fin 4) :=
  finCycle 2

-- Not `@[simp]`: the simp normal form keeps `oppositeCrossingSlot`, which the simp lemmas about
-- opposite slots match.
/-- The opposite crossing slot is obtained by adding two cyclically. -/
theorem oppositeCrossingSlot_apply (slot : Fin 4) : oppositeCrossingSlot slot = slot + 2 :=
  finCycle_apply 2 slot

/-- The value of the opposite crossing slot. -/
@[simp]
theorem oppositeCrossingSlot_apply_val (slot : Fin 4) :
    (oppositeCrossingSlot slot).val = (slot + 2).val := by
  rw [oppositeCrossingSlot_apply]

/-- The opposite-slot permutation swaps slots `0`, `2` and slots `1`, `3`. -/
theorem oppositeCrossingSlot_eq_swap_mul_swap :
    oppositeCrossingSlot = Equiv.swap 0 2 * Equiv.swap 1 3 := by
  decide

-- Not `@[simp]`: `oppositeCrossingSlot_apply_val` already rewrites the left-hand side.
/-- Exactly one of a slot and its opposite slot is one of the last two slots `2`, `3`. -/
theorem two_le_oppositeCrossingSlot_val_iff (slot : Fin 4) :
    2 ≤ (oppositeCrossingSlot slot).val ↔ ¬2 ≤ slot.val := by
  fin_cases slot <;> decide

/-- Taking the opposite crossing slot twice returns to the original slot. -/
@[simp]
theorem oppositeCrossingSlot_apply_oppositeCrossingSlot (slot : Fin 4) :
    oppositeCrossingSlot (oppositeCrossingSlot slot) = slot := by
  fin_cases slot <;> decide

/-- The two smoothings of the four slots at a crossing, indexed by an over-pair indicator.
`slotSmoothing false` pairs slot `0` with slot `3` and slot `1` with slot `2`, and
`slotSmoothing true` pairs slot `0` with slot `1` and slot `2` with slot `3`: in both cases each
slot of the pair indicated is joined to the slot preceding it in the counterclockwise order.
Applied to `D.overPair i` it is therefore the `A`-smoothing at crossing `i`, the one turning left
off the over-strand, and applied to `!D.overPair i` the `B`-smoothing. -/
def slotSmoothing (b : Bool) : Equiv.Perm (Fin 4) :=
  if b then Equiv.swap 0 1 * Equiv.swap 2 3 else Equiv.swap 0 3 * Equiv.swap 1 2

/-- The `true` smoothing pairs slots `0`-`1` and `2`-`3`. -/
@[simp] theorem slotSmoothing_true :
    slotSmoothing true = Equiv.swap 0 1 * Equiv.swap 2 3 := (rfl)

/-- The `false` smoothing pairs slots `0`-`3` and `1`-`2`. -/
@[simp] theorem slotSmoothing_false :
    slotSmoothing false = Equiv.swap 0 3 * Equiv.swap 1 2 := (rfl)

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

end PDCode

end TauCeti

namespace Fin

/-- The opposite crossing slot is different from the original slot. -/
theorem oppositeCrossingSlot_ne (slot : Fin 4) :
    TauCeti.PDCode.oppositeCrossingSlot slot ≠ slot := by
  fin_cases slot <;> decide

end Fin

namespace TauCeti

/-- A finite unoriented PD-code with `n` crossings.

The `4 * n` half-edges are grouped into four slots for each crossing by `halfEdge`, listed
counterclockwise around the crossing. The perfect matching `edgePair` joins the two half-edges at
the ends of each arc. Slots `0` and `2` form one local strand, while slots `1` and `3` form the
other. `crossinglessComponentCount` counts circle components which meet no crossing.
`overPair i = false` selects the `0`-`2` strand as over, while `true` selects the `1`-`3` strand. -/
@[ext]
structure PDCode (n : ℕ) where
  /-- The half-edge labels occupying the four slots of each crossing. -/
  halfEdge : Equiv.Perm (Fin (4 * n))
  /-- The perfect matching pairing the two half-edges at the ends of each arc. -/
  edgePair : PerfectMatching (Fin (4 * n))
  /-- The number of circle components which meet no crossing. -/
  crossinglessComponentCount : ℕ
  /-- Which of the two opposite-slot strands is over at each crossing. -/
  overPair : Fin n → Bool

/-- An oriented PD-code, consisting of an unoriented code and compatible component directions. -/
@[ext (flat := false)]
structure OrientedPDCode (n : ℕ) extends PDCode n where
  /-- Whether an arc points away from its incident crossing (`true`) or toward it (`false`). -/
  orientation : Fin (4 * n) → Bool
  /-- The direction on an arc reverses at its paired half-edge. -/
  orientation_edgePair : ∀ h, orientation (edgePair.val h) = !orientation h
  /-- The orientation reverses between the opposite slots belonging to each local strand. -/
  orientation_oppositeCrossingSlot : ∀ i slot,
    orientation (halfEdge (PDCode.crossingSlotEquiv n (i, PDCode.oppositeCrossingSlot slot))) =
      !orientation (halfEdge (PDCode.crossingSlotEquiv n (i, slot)))
  /-- The orientations of the circle components which meet no crossing, one entry per component.
  For such a circle, `true` and `false` simply label its two orientations, which
  `TauCeti.OrientedPDCode.reverse` exchanges. -/
  crossinglessComponents : Multiset Bool
  /-- The orientation multiset has one entry per crossing-free component of the underlying code. -/
  card_crossinglessComponents : crossinglessComponents.card = crossinglessComponentCount

/-- A framed oriented PD-code.

On a component meeting a crossing, `framing` is an integer constant along arc pairings and local
strands. For crossing-free components, `crossinglessFramings` keeps each orientation paired with
its framing integer. These integers measure the chosen framing relative to the Seifert (`0`-)
framing. The diagram's blackboard framing instead has coefficient equal to the component writhe. -/
@[ext (flat := false)]
structure FramedOrientedPDCode (n : ℕ) extends OrientedPDCode n where
  /-- The Seifert-relative framing coefficient of the component through each half-edge. -/
  framing : Fin (4 * n) → ℤ
  /-- Framing is constant along an arc. -/
  framing_edgePair : ∀ h, framing (edgePair.val h) = framing h
  /-- Framing is constant along a local strand through a crossing. -/
  framing_oppositeCrossingSlot : ∀ i slot,
    framing (halfEdge (PDCode.crossingSlotEquiv n (i, PDCode.oppositeCrossingSlot slot))) =
      framing (halfEdge (PDCode.crossingSlotEquiv n (i, slot)))
  /-- The orientation and Seifert-relative framing coefficient of each crossing-free component. -/
  crossinglessFramings : Multiset (Bool × ℤ)
  /-- Forgetting framings recovers the oriented crossing-free components. -/
  map_fst_crossinglessFramings : crossinglessFramings.map Prod.fst = crossinglessComponents

attribute [simp] OrientedPDCode.orientation_edgePair
  OrientedPDCode.orientation_oppositeCrossingSlot
  OrientedPDCode.card_crossinglessComponents
  FramedOrientedPDCode.framing_edgePair FramedOrientedPDCode.framing_oppositeCrossingSlot
  FramedOrientedPDCode.map_fst_crossinglessFramings

namespace PDCode

variable {n : ℕ}

/-- The four half-edge labels at a crossing, in counterclockwise cyclic order. -/
def crossing (D : PDCode n) (i : Fin n) (slot : Fin 4) : Fin (4 * n) :=
  D.halfEdge (crossingSlotEquiv n (i, slot))

/-- The explicit formula for the half-edge in a specified crossing slot. -/
@[simp]
theorem crossing_apply (D : PDCode n) (i : Fin n) (slot : Fin 4) :
    D.crossing i slot = D.halfEdge (crossingSlotEquiv n (i, slot)) :=
  crossing.eq_1 D i slot

/-- Let `D'` be a code with one crossing more than `D`, whose first `n` crossings keep the
half-edges of `D` and whose last crossing takes the four new half-edge positions. A permutation of
the half-edges of `D'` that acts at each crossing `i` by the local permutation `f i` of its slots
is the permutation of the half-edges of `D` acting at each crossing `i` by `f i.castSucc`,
together with `f (Fin.last n)` on the four new slots. -/
theorem eq_permCongr_sumCongr_of_halfEdge_eq {D : PDCode n} {D' : PDCode (n + 1)}
    (hD : D'.halfEdge = (halfEdgeSuccEquiv n).permCongr (Equiv.Perm.sumCongr D.halfEdge 1))
    {σ : Equiv.Perm (Fin (4 * n))} {τ : Equiv.Perm (Fin (4 * (n + 1)))}
    (f : Fin (n + 1) → Equiv.Perm (Fin 4))
    (hσ : ∀ i slot, σ (D.halfEdge (crossingSlotEquiv n (i, slot))) =
      D.crossing i (f i.castSucc slot))
    (hτ : ∀ i slot, τ (D'.halfEdge (crossingSlotEquiv (n + 1) (i, slot))) =
      D'.crossing i (f i slot)) :
    τ = (halfEdgeSuccEquiv n).permCongr (Equiv.Perm.sumCongr σ (f (Fin.last n))) := by
  have hold (i : Fin n) (slot : Fin 4) :
      D'.crossing i.castSucc slot = halfEdgeSuccEquiv n (.inl (D.crossing i slot)) := by
    simp [hD, Equiv.permCongr_apply]
  have hnew (slot : Fin 4) : D'.crossing (Fin.last n) slot = halfEdgeSuccEquiv n (.inr slot) := by
    simp [hD, Equiv.permCongr_apply]
  refine Equiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
  rcases y with y | slot
  · obtain ⟨z, rfl⟩ := D.halfEdge.surjective y
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective z
    have hx := hτ i.castSucc slot
    rw [← crossing_apply D' i.castSucc slot, hold, hold] at hx
    rw [← crossing_apply D i slot, hx, Equiv.permCongr_apply, Equiv.symm_apply_apply,
      Equiv.Perm.sumCongr_apply, Sum.map_inl, crossing_apply D i slot, hσ]
  · have hx := hτ (Fin.last n) slot
    rw [← crossing_apply D' (Fin.last n) slot, hnew, hnew] at hx
    rw [hx, Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply,
      Sum.map_inr]

/-- Whether a slot belongs to the over-strand at its crossing. -/
def isOver (D : PDCode n) (i : Fin n) (slot : Fin 4) : Bool :=
  D.overPair i == decide (slot = 1 ∨ slot = 3)

/-- The defining equation for the over-strand indicator of a slot: it compares the over-pair
indicator with the parity of the slot. -/
theorem isOver_def (D : PDCode n) (i : Fin n) (slot : Fin 4) :
    D.isOver i slot = (D.overPair i == decide (slot = 1 ∨ slot = 3)) := (rfl)

/-- Slot zero is over exactly when the second opposite-slot pair was not selected. -/
@[simp]
theorem isOver_zero (D : PDCode n) (i : Fin n) : D.isOver i 0 = !D.overPair i := by
  simp [isOver]

/-- Slot one is over exactly when the second opposite-slot pair was selected. -/
@[simp]
theorem isOver_one (D : PDCode n) (i : Fin n) : D.isOver i 1 = D.overPair i := by
  simp [isOver]

/-- Slot two is over exactly when the second opposite-slot pair was not selected. -/
@[simp]
theorem isOver_two (D : PDCode n) (i : Fin n) : D.isOver i 2 = !D.overPair i := by
  simp [isOver]

/-- Slot three is over exactly when the second opposite-slot pair was selected. -/
@[simp]
theorem isOver_three (D : PDCode n) (i : Fin n) : D.isOver i 3 = D.overPair i := by
  simp [isOver]

/-- Opposite slots belong to the same over- or under-strand. -/
@[simp]
theorem isOver_oppositeCrossingSlot (D : PDCode n) (i : Fin n) (slot : Fin 4) :
    D.isOver i (oppositeCrossingSlot slot) = D.isOver i slot := by
  fin_cases slot <;> simp [oppositeCrossingSlot, isOver]

/-- Reflect a diagram by swapping the over- and under-strands. -/
def mirror (D : PDCode n) : PDCode n where
  halfEdge := D.halfEdge
  edgePair := D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := fun i => !D.overPair i

/-- Reflection leaves the half-edge order unchanged. -/
@[simp] theorem mirror_halfEdge (D : PDCode n) : D.mirror.halfEdge = D.halfEdge := (rfl)

/-- Reflection leaves the arc matching unchanged. -/
@[simp] theorem mirror_edgePair (D : PDCode n) : D.mirror.edgePair = D.edgePair := (rfl)

/-- Reflection preserves the number of crossing-free components. -/
@[simp] theorem mirror_crossinglessComponentCount (D : PDCode n) :
    D.mirror.crossinglessComponentCount = D.crossinglessComponentCount := (rfl)

/-- Reflection complements each over-strand choice. -/
@[simp] theorem mirror_overPair (D : PDCode n) (i : Fin n) :
    D.mirror.overPair i = !D.overPair i := (rfl)

/-- Reflection leaves every labelled crossing slot unchanged. -/
theorem crossing_mirror (D : PDCode n) (i : Fin n) (slot : Fin 4) :
    D.mirror.crossing i slot = D.crossing i slot := (rfl)

/-- Reflection interchanges over- and under-slots. -/
@[simp]
theorem isOver_mirror (D : PDCode n) (i : Fin n) (slot : Fin 4) :
    D.mirror.isOver i slot = !D.isOver i slot := by
  fin_cases slot <;> simp [mirror, isOver]

/-- Reflecting a PD-code twice gives the original code. -/
@[simp]
theorem mirror_mirror (D : PDCode n) : D.mirror.mirror = D := by
  ext <;> simp

/-- Reflection fixes every PD-code without crossings. -/
@[simp]
theorem mirror_eq_self_of_zero_crossings (D : PDCode 0) : D.mirror = D :=
  PDCode.ext rfl rfl rfl (funext fun i => i.elim0)

section Reconnect

/-- **Reconnecting two arcs.** Cut the arc of `D` ending at the half-edge `p` and the arc ending
at `q`, and join `p` to `q` and the other end `D.edgePair.val p` of the first arc to the other end
`D.edgePair.val q` of the second (`TauCeti.PerfectMatching.reconnect`). The crossings, their
over-strands and the crossing-free circles are unchanged. This is how a smoothing of a crossing
added by `TauCeti.PDCode.insertCrossing` reconnects the cut arcs. The two arcs are distinct when
`q ≠ p` and `q ≠ D.edgePair.val p`; when `q = D.edgePair.val p` both choices name the same arc and
the code is left unchanged. -/
def reconnect (D : PDCode n) (p q : Fin (4 * n)) : PDCode n where
  halfEdge := D.halfEdge
  edgePair := D.edgePair.reconnect p q
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := D.overPair

variable (D : PDCode n) (p q : Fin (4 * n))

/-- Reconnecting arcs keeps the half-edges at the crossings. -/
@[simp] theorem reconnect_halfEdge : (D.reconnect p q).halfEdge = D.halfEdge := (rfl)

/-- Reconnecting arcs keeps the over-strands. -/
@[simp] theorem reconnect_overPair : (D.reconnect p q).overPair = D.overPair := (rfl)

/-- Reconnecting arcs keeps the crossing-free circles. -/
@[simp] theorem reconnect_crossinglessComponentCount :
    (D.reconnect p q).crossinglessComponentCount = D.crossinglessComponentCount := (rfl)

/-- Reconnecting arcs of the code reconnects its perfect matching of half-edges. -/
@[simp] theorem reconnect_edgePair : (D.reconnect p q).edgePair = D.edgePair.reconnect p q := (rfl)

/-- Reconnecting the two ends of one arc leaves the code unchanged. -/
@[simp] theorem reconnect_partner : D.reconnect p (D.edgePair.val p) = D := by
  apply PDCode.ext <;> simp

/-- Reconnecting a half-edge with itself leaves the code unchanged. -/
@[simp] theorem reconnect_self : D.reconnect p p = D := by
  apply PDCode.ext <;> simp

/-- The arcs of the reconnected code are the old arcs conjugated by the transposition of
`D.edgePair.val p` with `q`. -/
theorem reconnect_edgePair_val :
    (D.reconnect p q).edgePair.val = (Equiv.swap (D.edgePair.val p) q).permCongr D.edgePair.val :=
  PerfectMatching.reconnect_val _ _ _

/-- Mirroring commutes with reconnecting arcs. -/
@[simp] theorem mirror_reconnect : (D.reconnect p q).mirror = D.mirror.reconnect p q := by
  apply PDCode.ext
  · simp [reconnect]
  · simp [reconnect]
  · simp [reconnect]
  · funext i
    simp [reconnect]

end Reconnect

/-- The equivalence of half-edge positions induced by an equivalence of crossing names. It changes
the crossing coordinate and preserves the slot coordinate. -/
def crossingBlockEquiv {m : ℕ} (cross : Fin n ≃ Fin m) : Fin (4 * n) ≃ Fin (4 * m) :=
  (crossingSlotEquiv n).symm.trans ((cross.prodCongr (.refl _)).trans (crossingSlotEquiv m))

/-- A crossing-block equivalence changes the crossing coordinate and preserves its slot. -/
@[simp]
theorem crossingBlockEquiv_apply_crossingSlotEquiv {m : ℕ} (cross : Fin n ≃ Fin m)
    (i : Fin n) (slot : Fin 4) :
    crossingBlockEquiv cross (crossingSlotEquiv n (i, slot)) =
      crossingSlotEquiv m (cross i, slot) := by
  simp [crossingBlockEquiv]

/-- The inverse of a crossing-block equivalence is induced by the inverse crossing
equivalence. -/
@[simp]
theorem crossingBlockEquiv_symm {m : ℕ} (cross : Fin n ≃ Fin m) :
    (crossingBlockEquiv cross).symm = crossingBlockEquiv cross.symm := by
  refine Equiv.ext fun h ↦ ?_
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv m).surjective h
  apply (crossingBlockEquiv cross).injective
  simp

/-- The identity equivalence of crossing names induces the identity equivalence of half-edges. -/
@[simp]
theorem crossingBlockEquiv_refl : crossingBlockEquiv (Equiv.refl (Fin n)) = Equiv.refl _ := by
  ext h
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective h
  simp

/-- Crossing-block equivalences preserve composition. -/
@[simp]
theorem crossingBlockEquiv_trans {m r : ℕ} (cross₁ : Fin n ≃ Fin m) (cross₂ : Fin m ≃ Fin r) :
    crossingBlockEquiv (cross₁.trans cross₂) =
      (crossingBlockEquiv cross₁).trans (crossingBlockEquiv cross₂) := by
  ext h
  obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective h
  simp

/-- Relabel the half-edges and crossings of a code along equivalences of their index types: the
half-edge `h` becomes `half h` and the crossing `j` becomes `cross j`. Slots are kept, so the
half-edge in slot `s` of crossing `cross j` is `half` of the half-edge in slot `s` of crossing `j`;
arcs join the images of the half-edges they joined, the over-strand choice at `cross j` is the one
at `j`, and the number of crossing-free components is unchanged. The half-edge equivalence need
not be the one induced by the crossing equivalence. -/
def relabel {m : ℕ} (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) : PDCode m where
  halfEdge := (crossingBlockEquiv cross).equivCongr half D.halfEdge
  edgePair := PerfectMatching.congr half D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := D.overPair ∘ cross.symm

section Relabel

variable {m : ℕ} (D : PDCode n) (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m)

/-- The half-edge permutation of a relabelled code is
`half ∘ D.halfEdge ∘ (crossingBlockEquiv cross).symm`: the half-edge in slot `s` of crossing
`cross j` is `half` of the half-edge of `D` in slot `s` of crossing `j`. -/
@[simp] theorem relabel_halfEdge : (D.relabel half cross).halfEdge =
    (crossingBlockEquiv cross).equivCongr half D.halfEdge := (rfl)

/-- Relabelling transports the perfect matching along the half-edge equivalence. -/
@[simp] theorem relabel_edgePair : (D.relabel half cross).edgePair =
    PerfectMatching.congr half D.edgePair := (rfl)

/-- Relabelling preserves the number of crossing-free components. -/
@[simp] theorem relabel_crossinglessComponentCount :
    (D.relabel half cross).crossinglessComponentCount = D.crossinglessComponentCount := (rfl)

/-- Relabelling reads the over-strand choice at the old crossing name. -/
@[simp] theorem relabel_overPair (i : Fin m) :
    (D.relabel half cross).overPair i = D.overPair (cross.symm i) := (rfl)

-- Not `@[simp]`: `crossing_apply` already rewrites the left-hand side, and `simp` proves this
-- from `crossing_apply`, `relabel_halfEdge` and `crossingBlockEquiv_apply_crossingSlotEquiv`.
/-- Relabelling transports every crossing block together with its slot order. -/
theorem crossing_relabel (i : Fin m) (slot : Fin 4) :
    (D.relabel half cross).crossing i slot = half (D.crossing (cross.symm i) slot) := by
  rw [crossing_apply, relabel_halfEdge, Equiv.equivCongr_apply_apply, crossingBlockEquiv_symm,
    crossingBlockEquiv_apply_crossingSlotEquiv, crossing_apply]

/-- The over/under status after relabelling is read at the old crossing name. -/
@[simp]
theorem isOver_relabel (i : Fin m) (slot : Fin 4) :
    (D.relabel half cross).isOver i slot = D.isOver (cross.symm i) slot := (rfl)

/-- Relabelling by identity equivalences does nothing. -/
@[simp]
theorem relabel_refl : D.relabel (Equiv.refl _) (Equiv.refl _) = D := by
  ext <;> simp

/-- Consecutive relabellings compose their half-edge and crossing equivalences. -/
@[simp]
theorem relabel_relabel {r : ℕ} (half₂ : Fin (4 * m) ≃ Fin (4 * r)) (cross₂ : Fin m ≃ Fin r) :
    (D.relabel half cross).relabel half₂ cross₂ =
      D.relabel (half.trans half₂) (cross.trans cross₂) := by
  ext <;> simp

/-- Reflection commutes with relabelling. -/
@[simp]
theorem mirror_relabel : (D.relabel half cross).mirror = D.mirror.relabel half cross := by
  ext <;> simp

end Relabel

/-- The one-crossing knot diagram: a single kink. Its single crossing has the slot pair `1`-`3`
as its over-strand, and its two arcs join slot `0` to slot `1` and slot `2` to slot `3`, so the
strand doubles back on itself, as in the first Reidemeister move. -/
def kink : PDCode 1 where
  halfEdge := 1
  edgePair := PerfectMatching.congr (crossingSlotEquiv 1)
    (PerfectMatching.mk (Equiv.prodCongrRight fun _ ↦ slotSmoothing true)
      (fun p ↦ Prod.ext rfl (slotSmoothing_apply_apply true p.2))
      (fun p h ↦ slotSmoothing_ne true p.2 (congrArg Prod.snd h)))
  crossinglessComponentCount := 0
  overPair := fun _ ↦ true

/-- The kink numbers its half-edges by their crossing slots. -/
@[simp] theorem kink_halfEdge : kink.halfEdge = 1 := (rfl)

/-- The kink has no crossing-free component. -/
@[simp] theorem kink_crossinglessComponentCount : kink.crossinglessComponentCount = 0 := (rfl)

/-- The over-strand of the kink is the slot pair `1`-`3`. -/
@[simp] theorem kink_overPair (i : Fin 1) : kink.overPair i = true := (rfl)

/-- The half-edge of the kink in a given crossing slot is that slot. -/
theorem kink_crossing (i : Fin 1) (t : Fin 4) :
    kink.crossing i t = crossingSlotEquiv 1 (i, t) := by
  rw [crossing_apply, kink_halfEdge]
  simp

/-- The two arcs of the kink join each slot of the over-pair to the slot preceding it. -/
@[simp] theorem kink_edgePair_apply (i : Fin 1) (t : Fin 4) :
    kink.edgePair.val (crossingSlotEquiv 1 (i, t))
      = crossingSlotEquiv 1 (i, slotSmoothing true t) := by
  simp [kink, PerfectMatching.congr_val, PerfectMatching.val_mk]

end PDCode

namespace OrientedPDCode

variable {n : ℕ}

/-- The orientation reverses between two opposite slots `s` and `t = s + 2` of a crossing. -/
theorem orientation_crossing_of_add_two_eq (D : OrientedPDCode n) (i : Fin n) {s t : Fin 4}
    (hst : s + 2 = t) :
    D.orientation (D.crossing i t) = !D.orientation (D.crossing i s) := by
  rw [← hst, ← PDCode.oppositeCrossingSlot_apply, PDCode.crossing_apply, PDCode.crossing_apply,
    D.orientation_oppositeCrossingSlot]

/-- The sign of crossing `i`:`1` if the crossing is right-handed and `-1` if it is left-handed,
as in Lickorish, Chapter 1. The slots are read counterclockwise in the oriented plane and
`orientation` is `true` at the half-edges where the strands leave the crossing. The crossing is
right-handed when a counterclockwise quarter turn takes the direction of the over-strand to that
of the under-strand; in terms of the code, the sign is `1` exactly when `overPair i` records
whether the orientations at slots `0` and `1` differ. -/
def crossingSign (D : OrientedPDCode n) (i : Fin n) : ℤ :=
  if Bool.xor (D.orientation (D.crossing i 0)) (D.orientation (D.crossing i 1)) =
      D.overPair i then 1 else -1

/-- The defining equation for an oriented crossing sign. -/
theorem crossingSign_def (D : OrientedPDCode n) (i : Fin n) :
    D.crossingSign i =
      if Bool.xor (D.orientation (D.crossing i 0)) (D.orientation (D.crossing i 1)) =
          D.overPair i then 1 else -1 := (rfl)

/-- A crossing is positive exactly when its orientation parity agrees with its over-strand. -/
@[simp]
theorem crossingSign_eq_one_iff (D : OrientedPDCode n) (i : Fin n) :
    D.crossingSign i = 1 ↔
      Bool.xor (D.orientation (D.crossing i 0)) (D.orientation (D.crossing i 1)) =
        D.overPair i := by
  simp [crossingSign]

/-- A crossing is negative exactly when its orientation parity disagrees with its over-strand. -/
@[simp]
theorem crossingSign_eq_neg_one_iff (D : OrientedPDCode n) (i : Fin n) :
    D.crossingSign i = -1 ↔
      Bool.xor (D.orientation (D.crossing i 0)) (D.orientation (D.crossing i 1)) ≠
        D.overPair i := by
  simp [crossingSign]

/-- Every crossing sign is either positive or negative. -/
theorem crossingSign_eq_one_or_neg_one (D : OrientedPDCode n) (i : Fin n) :
    D.crossingSign i = 1 ∨ D.crossingSign i = -1 :=
  (em _).imp (crossingSign_eq_one_iff D i).2 (crossingSign_eq_neg_one_iff D i).2

/-- The writhe of an oriented code is the sum of its crossing signs. -/
def writhe (D : OrientedPDCode n) : ℤ :=
  ∑ i : Fin n, D.crossingSign i

/-- Expand the writhe as the sum of the crossing signs. -/
theorem writhe_def (D : OrientedPDCode n) : D.writhe = ∑ i : Fin n, D.crossingSign i := (rfl)

/-- Reverse every component orientation while preserving the underlying unoriented code. -/
def reverse (D : OrientedPDCode n) : OrientedPDCode n where
  toPDCode := D.toPDCode
  orientation := fun h => !D.orientation h
  orientation_edgePair := by simp
  orientation_oppositeCrossingSlot := by simp
  crossinglessComponents := D.crossinglessComponents.map (!·)
  card_crossinglessComponents := by simp

/-- Forgetting orientation after reversal leaves the underlying code unchanged. -/
@[simp] theorem reverse_toPDCode (D : OrientedPDCode n) :
    D.reverse.toPDCode = D.toPDCode := (rfl)

/-- Reversal complements the direction at every half-edge. -/
@[simp] theorem reverse_orientation (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.reverse.orientation h = !D.orientation h := (rfl)

/-- Reversal complements the orientations of all crossing-free components. -/
@[simp] theorem reverse_crossinglessComponents (D : OrientedPDCode n) :
    D.reverse.crossinglessComponents = D.crossinglessComponents.map (!·) := (rfl)

/-- Reversing every component orientation preserves each crossing sign. -/
@[simp] theorem crossingSign_reverse (D : OrientedPDCode n) (i : Fin n) :
    D.reverse.crossingSign i = D.crossingSign i := by
  simp [crossingSign]

/-- Reversing every component orientation twice gives the original code. -/
@[simp] theorem reverse_reverse (D : OrientedPDCode n) : D.reverse.reverse = D := by
  ext <;> simp

/-- Reflect an oriented diagram, preserving all component orientations. -/
def mirror (D : OrientedPDCode n) : OrientedPDCode n where
  toPDCode := D.toPDCode.mirror
  orientation := D.orientation
  orientation_edgePair := by simp
  orientation_oppositeCrossingSlot := by simp
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := by simp

/-- Forgetting orientation after reflection gives reflection of the underlying code. -/
@[simp] theorem mirror_toPDCode (D : OrientedPDCode n) :
    D.mirror.toPDCode = D.toPDCode.mirror := (rfl)

/-- Reflection preserves the orientation of every arc. -/
@[simp] theorem mirror_orientation (D : OrientedPDCode n) :
    D.mirror.orientation = D.orientation := (rfl)

/-- Reflection preserves the oriented crossing-free components. -/
@[simp] theorem mirror_crossinglessComponents (D : OrientedPDCode n) :
    D.mirror.crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Reflection reverses the sign of every crossing. -/
@[simp]
theorem crossingSign_mirror (D : OrientedPDCode n) (i : Fin n) :
    D.mirror.crossingSign i = -D.crossingSign i := by
  rw [crossingSign_def, crossingSign_def]
  split_ifs <;> simp_all

/-- Reflecting an oriented PD-code twice gives the original code. -/
@[simp]
theorem mirror_mirror (D : OrientedPDCode n) : D.mirror.mirror = D := by
  ext <;> simp

/-- Relabel half-edges and crossings along equivalences of their finite index types. -/
def relabel {m : ℕ} (D : OrientedPDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) : OrientedPDCode m where
  toPDCode := D.toPDCode.relabel half cross
  orientation := D.orientation ∘ half.symm
  orientation_edgePair := by simp
  orientation_oppositeCrossingSlot := by simp
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := by simp

section Relabel

variable {m : ℕ} (D : OrientedPDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
  (cross : Fin n ≃ Fin m)

/-- Forgetting orientation after relabelling gives relabelling of the underlying code. -/
@[simp] theorem relabel_toPDCode :
    (D.relabel half cross).toPDCode = D.toPDCode.relabel half cross := (rfl)

/-- Relabelling transports arc orientations along the half-edge equivalence. -/
@[simp] theorem relabel_orientation (h : Fin (4 * m)) :
    (D.relabel half cross).orientation h = D.orientation (half.symm h) := (rfl)

/-- Relabelling leaves crossing-free oriented components unchanged. -/
@[simp] theorem relabel_crossinglessComponents :
    (D.relabel half cross).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- The crossing sign after relabelling is read at the old crossing name. -/
@[simp]
theorem crossingSign_relabel (i : Fin m) :
    (D.relabel half cross).crossingSign i = D.crossingSign (cross.symm i) := by
  simp only [crossingSign_def, relabel_toPDCode, PDCode.crossing_relabel, relabel_orientation,
    PDCode.relabel_overPair, Equiv.symm_apply_apply]

/-- Relabelling by identity equivalences does nothing. -/
@[simp]
theorem relabel_refl : D.relabel (Equiv.refl _) (Equiv.refl _) = D := by
  ext <;> simp

/-- Consecutive relabellings compose their half-edge and crossing equivalences. -/
@[simp]
theorem relabel_relabel {r : ℕ} (half₂ : Fin (4 * m) ≃ Fin (4 * r)) (cross₂ : Fin m ≃ Fin r) :
    (D.relabel half cross).relabel half₂ cross₂ =
      D.relabel (half.trans half₂) (cross.trans cross₂) := by
  ext <;> simp

/-- Relabelling matches the crossings bijectively, so it preserves the writhe. -/
@[simp] theorem writhe_relabel : (D.relabel half cross).writhe = D.writhe := by
  simp only [writhe_def, crossingSign_relabel]
  exact Equiv.sum_comp cross.symm D.crossingSign

end Relabel

/-- Reflection negates the writhe. -/
@[simp] theorem writhe_mirror (D : OrientedPDCode n) : D.mirror.writhe = -D.writhe := by
  simp [writhe_def]

/-- Reversing every component orientation preserves the writhe. -/
@[simp] theorem writhe_reverse (D : OrientedPDCode n) : D.reverse.writhe = D.writhe := by
  simp [writhe_def]

/-- Reflection and orientation reversal commute. -/
@[simp]
theorem mirror_reverse (D : OrientedPDCode n) : D.reverse.mirror = D.mirror.reverse := by
  ext <;> simp

/-- Reflection commutes with relabelling. -/
@[simp]
theorem mirror_relabel {m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).mirror = D.mirror.relabel half cross := by
  ext <;> simp

/-- Orientation reversal commutes with relabelling. -/
@[simp]
theorem reverse_relabel {m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).reverse = D.reverse.relabel half cross := by
  ext <;> simp

end OrientedPDCode

namespace FramedOrientedPDCode

variable {n : ℕ}

/-- Reflect a framed oriented diagram, negating its Seifert-relative framing coefficients. -/
def mirror (D : FramedOrientedPDCode n) : FramedOrientedPDCode n where
  toOrientedPDCode := D.toOrientedPDCode.mirror
  framing := fun h => -D.framing h
  framing_edgePair := by simp
  framing_oppositeCrossingSlot := by simp
  crossinglessFramings := D.crossinglessFramings.map fun component =>
    (component.1, -component.2)
  map_fst_crossinglessFramings := by simp

/-- Forgetting framing after reflection gives reflection of the underlying oriented code. -/
@[simp] theorem mirror_toOrientedPDCode (D : FramedOrientedPDCode n) :
    D.mirror.toOrientedPDCode = D.toOrientedPDCode.mirror := (rfl)

/-- Reflection negates the Seifert-relative framing coefficient at every half-edge. -/
@[simp] theorem mirror_framing (D : FramedOrientedPDCode n) :
    D.mirror.framing = -D.framing := (rfl)

/-- Reflection preserves orientation and negates framing on every crossing-free component. -/
@[simp] theorem mirror_crossinglessFramings (D : FramedOrientedPDCode n) :
    D.mirror.crossinglessFramings =
      D.crossinglessFramings.map (fun component => (component.1, -component.2)) := (rfl)

/-- Reflecting a framed oriented PD-code twice gives the original code. -/
@[simp] theorem mirror_mirror (D : FramedOrientedPDCode n) : D.mirror.mirror = D := by
  apply FramedOrientedPDCode.ext <;> simp

/-- Relabel half-edges and crossings along equivalences of their finite index types while
transporting the framing function. -/
def relabel {m : ℕ} (D : FramedOrientedPDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
    (cross : Fin n ≃ Fin m) : FramedOrientedPDCode m where
  toOrientedPDCode := D.toOrientedPDCode.relabel half cross
  framing := D.framing ∘ half.symm
  framing_edgePair := by simp
  framing_oppositeCrossingSlot := by simp
  crossinglessFramings := D.crossinglessFramings
  map_fst_crossinglessFramings := by simp

section Relabel

variable {m : ℕ} (D : FramedOrientedPDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
  (cross : Fin n ≃ Fin m)

/-- Forgetting framing after relabelling gives relabelling of the underlying oriented code. -/
@[simp] theorem relabel_toOrientedPDCode :
    (D.relabel half cross).toOrientedPDCode = D.toOrientedPDCode.relabel half cross := (rfl)

/-- Relabelling transports framing values along the half-edge equivalence. -/
@[simp] theorem relabel_framing (h : Fin (4 * m)) :
    (D.relabel half cross).framing h = D.framing (half.symm h) := (rfl)

/-- Relabelling preserves all crossing-free orientation-framing pairs. -/
@[simp] theorem relabel_crossinglessFramings :
    (D.relabel half cross).crossinglessFramings = D.crossinglessFramings := (rfl)

/-- Relabelling by identity equivalences does nothing to a framed oriented code. -/
@[simp] theorem relabel_refl : D.relabel (Equiv.refl _) (Equiv.refl _) = D := by
  ext <;> simp

/-- Consecutive framed relabellings compose their half-edge and crossing equivalences. -/
@[simp]
theorem relabel_relabel {r : ℕ} (half₂ : Fin (4 * m) ≃ Fin (4 * r)) (cross₂ : Fin m ≃ Fin r) :
    (D.relabel half cross).relabel half₂ cross₂ =
      D.relabel (half.trans half₂) (cross.trans cross₂) := by
  ext <;> simp

end Relabel

/-- Reverse every component orientation of a framed code, preserving all framing integers. -/
def reverse (D : FramedOrientedPDCode n) : FramedOrientedPDCode n where
  toOrientedPDCode := D.toOrientedPDCode.reverse
  framing := D.framing
  framing_edgePair := by simp
  framing_oppositeCrossingSlot := by simp
  crossinglessFramings := D.crossinglessFramings.map fun component =>
    (!component.1, component.2)
  map_fst_crossinglessFramings := by
    rw [Multiset.map_map, OrientedPDCode.reverse_crossinglessComponents]
    rw [← D.map_fst_crossinglessFramings, Multiset.map_map]
    rfl

/-- Forgetting framing after reversal gives reversal of the underlying oriented code. -/
@[simp] theorem reverse_toOrientedPDCode (D : FramedOrientedPDCode n) :
    D.reverse.toOrientedPDCode = D.toOrientedPDCode.reverse := (rfl)

/-- Reversal preserves the framing at every half-edge. -/
@[simp] theorem reverse_framing (D : FramedOrientedPDCode n) :
    D.reverse.framing = D.framing := (rfl)

/-- Reversal complements only the orientation in each crossing-free framing pair. -/
@[simp] theorem reverse_crossinglessFramings (D : FramedOrientedPDCode n) :
    D.reverse.crossinglessFramings =
      D.crossinglessFramings.map (fun component => (!component.1, component.2)) := (rfl)

/-- Reversing every component orientation twice gives the original framed code. -/
@[simp] theorem reverse_reverse (D : FramedOrientedPDCode n) : D.reverse.reverse = D := by
  ext <;> simp

/-- Reflection and orientation reversal commute. -/
@[simp]
theorem mirror_reverse (D : FramedOrientedPDCode n) : D.reverse.mirror = D.mirror.reverse := by
  ext <;> simp

/-- Reflection commutes with relabelling. -/
@[simp]
theorem mirror_relabel {m : ℕ} (D : FramedOrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).mirror = D.mirror.relabel half cross := by
  ext <;> simp

/-- Orientation reversal commutes with relabelling. -/
@[simp]
theorem reverse_relabel {m : ℕ} (D : FramedOrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (D.relabel half cross).reverse = D.reverse.relabel half cross := by
  ext <;> simp

end FramedOrientedPDCode

namespace OrientedPDCode

/-- A zero-crossing oriented PD-code consisting of crossing-free circles with the specified
orientations. Multiplicity records distinct components without imposing an ordering on them. -/
def unlink (orientations : Multiset Bool) : OrientedPDCode 0 where
  halfEdge := Equiv.refl _
  edgePair := PerfectMatching.mk (Equiv.refl _) (fun _ ↦ rfl) (fun h ↦ h.elim0)
  crossinglessComponentCount := orientations.card
  overPair := fun h => nomatch h
  orientation := fun h => nomatch h
  orientation_edgePair h := h.elim0
  orientation_oppositeCrossingSlot i := i.elim0
  crossinglessComponents := orientations
  card_crossinglessComponents := rfl

/-- The unlink constructor retains exactly its component-orientation multiset. -/
@[simp]
theorem crossinglessComponents_unlink (orientations : Multiset Bool) :
    (unlink orientations).crossinglessComponents = orientations :=
  (rfl)

/-- Every zero-crossing oriented PD-code is its canonical crossing-free unlink code. -/
theorem eq_unlink (D : OrientedPDCode 0) :
    D = unlink D.crossinglessComponents :=
  OrientedPDCode.ext (PDCode.ext (Equiv.ext (·.elim0)) (Subtype.ext (Equiv.ext (·.elim0)))
    D.card_crossinglessComponents.symm (funext (·.elim0))) (funext (·.elim0)) rfl

/-- Multisets of orientations are equivalent to zero-crossing oriented PD-codes. -/
def unlinkEquiv : Multiset Bool ≃ OrientedPDCode 0 where
  toFun := unlink
  invFun := OrientedPDCode.crossinglessComponents
  left_inv := crossinglessComponents_unlink
  right_inv := fun D => (eq_unlink D).symm

/-- The inverse of `unlinkEquiv` reads off the orientations of the crossing-free components. -/
@[simp]
theorem unlinkEquiv_symm_apply (D : OrientedPDCode 0) :
    unlinkEquiv.symm D = D.crossinglessComponents :=
  (rfl)

/-- The empty oriented PD-code. -/
def empty : OrientedPDCode 0 := unlink 0

/-- The empty diagram has no crossing-free components. -/
@[simp]
theorem crossinglessComponents_empty : empty.crossinglessComponents = 0 :=
  (rfl)

/-- A crossing-free oriented unknot with the specified choice of orientation. -/
def unknot (orientation : Bool) : OrientedPDCode 0 :=
  unlink {orientation}

/-- The oriented unknot retains its specified component orientation. -/
@[simp]
theorem crossinglessComponents_unknot (orientation : Bool) :
    (unknot orientation).crossinglessComponents = {orientation} :=
  (rfl)

/-- A crossing-free oriented circle is distinct from the empty diagram. -/
theorem unknot_ne_empty (orientation : Bool) :
    unknot orientation ≠ empty :=
  unlinkEquiv.injective.ne (Multiset.singleton_ne_zero orientation)

/-- Distinct orientation choices give distinct crossing-free circle presentations. -/
theorem unknot_injective : Function.Injective unknot := fun _ _ h =>
  Multiset.singleton_inj.1 (congrArg crossinglessComponents h)

/-- Reflection fixes every zero-crossing oriented PD-code. -/
@[simp]
theorem mirror_eq_self_of_zero_crossings (D : OrientedPDCode 0) :
    D.mirror = D :=
  OrientedPDCode.ext (by simp) (by simp) (by simp)

/-- The kink `TauCeti.PDCode.kink`, oriented so that its crossing is positive.

This concrete code is a semantic witness that the presentation permits a genuine positive
crossing, not only crossing-free links. -/
def positiveKink : OrientedPDCode 1 where
  toPDCode := PDCode.kink
  orientation := fun h => decide (h = 1 ∨ h = 2)
  orientation_edgePair := by
    intro h
    obtain ⟨⟨i, t⟩, rfl⟩ := (PDCode.crossingSlotEquiv 1).surjective h
    rw [PDCode.kink_edgePair_apply]
    fin_cases i
    fin_cases t <;> decide
  orientation_oppositeCrossingSlot := by decide
  crossinglessComponents := 0
  card_crossinglessComponents := by simp

/-- The underlying PD-code of `positiveKink` is the kink. -/
@[simp]
theorem toPDCode_positiveKink : positiveKink.toPDCode = PDCode.kink :=
  (rfl)

/-- The arcs of `positiveKink` point away from the crossing exactly at slots `1` and `2`. -/
@[simp]
theorem orientation_positiveKink (h : Fin (4 * 1)) :
    positiveKink.orientation h = decide (h = 1 ∨ h = 2) :=
  (rfl)

/-- The positive kink has no crossing-free components. -/
@[simp]
theorem crossinglessComponents_positiveKink : positiveKink.crossinglessComponents = 0 :=
  (rfl)

/-- The crossing of `positiveKink` has positive sign. -/
@[simp]
theorem crossingSign_positiveKink (i : Fin 1) :
    positiveKink.crossingSign i = 1 := by
  fin_cases i
  decide

end OrientedPDCode

end TauCeti
