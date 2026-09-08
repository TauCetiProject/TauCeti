/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Oriented PD-codes

An oriented PD-code records the finite combinatorial data at the crossings of a link.  The
`halfEdge` permutation lists the four visits at each crossing, `edgePair` joins the two visits
belonging to one arc, and `orientation` records the direction of every arc.  Opposite slots form
the two local strands, one of which is selected by `overPair`; the crossing sign is then derived
from this local oriented crossing data.

This is a code-level presentation: planarity and the realization in the plane are intentionally
separate predicates.  Keeping the code finite and explicit makes it the hub for later
Reidemeister moves and for the conversion to Gauss codes, without choosing a privileged geometric
embedding.  The code also carries orientation, as required for oriented knot invariants.

The encoding follows Lickorish, *An Introduction to Knot Theory*, GTM 175, Chapter 1.  No planar
realization theorem is asserted here; that is the subsequent geometric-to-combinatorial step.

## Main definitions

* `TauCeti.OrientedPDCode`: an oriented PD-code with `n` crossings.
* `TauCeti.OrientedPDCode.mirror`: reflection, which swaps the over- and under-strands.
* `TauCeti.OrientedPDCode.relabel`: relabelling of the half-edge and crossing indices.

## Main results

* `TauCeti.OrientedPDCode.crossingSign_eq_one_or_neg_one` records that every crossing sign
  is genuinely positive or negative.
* `TauCeti.OrientedPDCode.mirror_mirror` and `relabel_relabel` show respectively that reflection
  is involutive and that relabelling is an action.
* `TauCeti.orientedPDCodeZero` is the empty oriented diagram, providing a nontrivial
  witness for the finite presentation at zero crossings.
-/

public section

namespace TauCeti

open Function

namespace OrientedPDCode

/-- The standard equivalence between crossing-slot pairs and the `4 * n` half-edge positions. -/
@[expose] def crossingSlotEquiv (n : ℕ) : Fin n × Fin 4 ≃ Fin (4 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 4))

/-- The slot opposite a given slot in the cyclic order at a crossing. -/
@[expose] def oppositeCrossingSlot : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2 * Equiv.swap 1 3

end OrientedPDCode

/-- A finite oriented PD-code with `n` crossings.

The `4 * n` half-edges are grouped into four slots for each crossing by `halfEdge`.  The
fixed-point-free involution `edgePair` joins the two visits of each arc.  `orientation` chooses a
direction on each arc, so its values are opposite both at paired visits and across each local
strand.  Slots `0` and `2` form one strand, while slots `1` and `3` form the other.
`overPair i = false` selects the `0`-`2` strand as over; `true` selects the `1`-`3` strand. -/
structure OrientedPDCode (n : ℕ) where
  /-- The half-edge labels occupying the four slots of each crossing. -/
  halfEdge : Equiv.Perm (Fin (4 * n))
  /-- The involution pairing the two visits of each arc. -/
  edgePair : Equiv.Perm (Fin (4 * n))
  /-- Pairing twice returns to the original visit. -/
  edgePair_sq : ∀ h, edgePair (edgePair h) = h
  /-- No visit is paired with itself. -/
  edgePair_ne : ∀ h, edgePair h ≠ h
  /-- Whether an arc points away from its incident crossing (`true`) or toward it (`false`). -/
  orientation : Fin (4 * n) → Bool
  /-- The direction on an arc reverses at its paired visit. -/
  orientation_pair : ∀ h, orientation (edgePair h) = !orientation h
  /-- The orientation reverses between the opposite slots belonging to each local strand. -/
  orientation_opposite : ∀ i slot,
    orientation (halfEdge (OrientedPDCode.crossingSlotEquiv n
      (i, OrientedPDCode.oppositeCrossingSlot slot))) =
      !orientation (halfEdge (OrientedPDCode.crossingSlotEquiv n (i, slot)))
  /-- Which of the two opposite-slot strands is over at each crossing. -/
  overPair : Fin n → Bool

namespace OrientedPDCode

variable {n : ℕ}

/-- An oriented PD-code is determined by its crossing order, arc pairing, orientations, and
over-strand choices. -/
@[ext]
theorem ext {D E : OrientedPDCode n}
    (hhalf : D.halfEdge = E.halfEdge) (hedge : D.edgePair = E.edgePair)
    (horient : D.orientation = E.orientation) (hover : D.overPair = E.overPair) : D = E := by
  cases D
  cases E
  simp_all

/-- The four half-edge labels at a crossing, in cyclic order. -/
@[expose] def crossing (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) : Fin (4 * n) :=
  D.halfEdge (crossingSlotEquiv n (i, slot))

/-- The explicit formula for the half-edge in a specified crossing slot. -/
@[simp]
theorem crossing_apply (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) :
    D.crossing i slot = D.halfEdge (crossingSlotEquiv n (i, slot)) :=
  by simp [crossing]

/-- Whether a slot belongs to the over-strand at its crossing. -/
@[expose] def isOver (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) : Bool :=
  D.overPair i == decide (slot = 1 ∨ slot = 3)

/-- The two opposite slot pairs are precisely the two complementary local strands. -/
theorem isOver_slots (D : OrientedPDCode n) (i : Fin n) :
    D.isOver i 0 = D.isOver i 2 ∧ D.isOver i 1 = D.isOver i 3 ∧
      D.isOver i 0 = !D.isOver i 1 := by
  cases h : D.overPair i <;> simp [isOver, h]

/-- The orientation reverses across each local strand at a crossing. -/
@[simp]
theorem orientation_oppositeCrossingSlot (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) :
    D.orientation (D.crossing i (oppositeCrossingSlot slot)) =
      !D.orientation (D.crossing i slot) :=
  D.orientation_opposite i slot

/-- The sign of an oriented crossing, with slots read counterclockwise in the oriented plane.

It is positive exactly when the parity of the outgoing directions in slots `0` and `1` agrees
with the choice of the `1`-`3` strand as the over-strand. -/
@[expose] def crossingSign (D : OrientedPDCode n) (i : Fin n) : ℤ :=
  if Bool.xor (D.orientation (D.crossing i 0)) (D.orientation (D.crossing i 1)) =
      D.overPair i then 1 else -1

/-- Every crossing sign is either positive or negative. -/
theorem crossingSign_eq_one_or_neg_one (D : OrientedPDCode n) (i : Fin n) :
    D.crossingSign i = 1 ∨ D.crossingSign i = -1 :=
  by simp only [crossingSign]; split <;> simp_all

/-- Pairing an arc visit twice returns to that visit. -/
@[simp]
theorem edgePair_apply_edgePair (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.edgePair (D.edgePair h) = h :=
  D.edgePair_sq h

/-- The pairing of arc visits is injective. -/
theorem edgePair_injective (D : OrientedPDCode n) :
    Function.Injective D.edgePair := by
  intro a b hab
  rw [← D.edgePair_sq a, ← D.edgePair_sq b, hab]

/-- An arc visit is never paired with itself. -/
theorem edgePair_ne_self (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.edgePair h ≠ h :=
  D.edgePair_ne h

/-- The two visits of an oriented arc have opposite directions. -/
@[simp]
theorem orientation_edgePair (D : OrientedPDCode n) (h : Fin (4 * n)) :
    D.orientation (D.edgePair h) = !D.orientation h :=
  D.orientation_pair h

/-- Reflect a diagram by swapping the over- and under-strands while preserving its oriented arcs. -/
@[expose] def mirror (D : OrientedPDCode n) : OrientedPDCode n where
  halfEdge := D.halfEdge
  edgePair := D.edgePair
  edgePair_sq := D.edgePair_sq
  edgePair_ne := D.edgePair_ne
  orientation := D.orientation
  orientation_pair := D.orientation_pair
  orientation_opposite := D.orientation_opposite
  overPair := fun i => !D.overPair i

/-- Reflection leaves the order of the half-edge labels unchanged. -/
@[simp]
theorem mirror_halfEdge (D : OrientedPDCode n) : D.mirror.halfEdge = D.halfEdge :=
  rfl

/-- Reflection leaves the labels in every crossing slot unchanged. -/
@[simp]
theorem mirror_crossing (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) :
    D.mirror.crossing i slot = D.crossing i slot :=
  rfl

/-- Reflection reverses the sign of every crossing. -/
@[simp]
theorem mirror_crossingSign (D : OrientedPDCode n) (i : Fin n) :
    D.mirror.crossingSign i = -D.crossingSign i :=
  by
    change (if Bool.xor (D.orientation (D.crossing i 0))
        (D.orientation (D.crossing i 1)) = !D.overPair i then 1 else -1) =
      -(if Bool.xor (D.orientation (D.crossing i 0))
        (D.orientation (D.crossing i 1)) = D.overPair i then 1 else -1)
    generalize Bool.xor (D.orientation (D.crossing i 0))
      (D.orientation (D.crossing i 1)) = parity
    generalize D.overPair i = ov
    cases parity <;> cases ov <;> norm_num

/-- Reflecting an oriented PD-code twice gives the original code. -/
@[simp]
theorem mirror_mirror (D : OrientedPDCode n) : D.mirror.mirror = D := by
  apply ext <;> simp [mirror]

/-- The permutation of half-edge positions induced by a permutation of crossing blocks. -/
@[expose] def crossingBlockPerm (cross : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (4 * n)) :=
  (crossingSlotEquiv n).symm.trans
    ((cross.prodCongr (Equiv.refl (Fin 4))).trans (crossingSlotEquiv n))

/-- A crossing-block permutation changes the crossing coordinate and preserves the slot. -/
@[simp]
theorem crossingBlockPerm_apply_crossingSlotEquiv (cross : Equiv.Perm (Fin n))
    (i : Fin n) (slot : Fin 4) :
    crossingBlockPerm cross (crossingSlotEquiv n (i, slot)) =
      crossingSlotEquiv n (cross i, slot) := by
  simp [crossingBlockPerm]

/-- Crossing-block permutations respect composition. -/
theorem crossingBlockPerm_mul (cross₁ cross₂ : Equiv.Perm (Fin n)) :
    crossingBlockPerm (cross₁ * cross₂) = crossingBlockPerm cross₁ * crossingBlockPerm cross₂ := by
  apply Equiv.ext
  intro h
  rw [← (crossingSlotEquiv n).apply_symm_apply h]
  rcases (crossingSlotEquiv n).symm h with ⟨i, slot⟩
  simp [Equiv.Perm.mul_apply]

/-- Relabel half-edge visits and crossings by permutations.

The relabelling is deliberately independent of the planar realization: it changes only the finite
names, so later equivalence relations can quotient out these bookkeeping choices. -/
@[expose] def relabel (D : OrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) : OrientedPDCode n where
  halfEdge := half * D.halfEdge * crossingBlockPerm cross.symm
  edgePair := half * D.edgePair * half.symm
  edgePair_sq := by
    intro h
    simp [mul_assoc, D.edgePair_sq]
  edgePair_ne := by
    intro h hh
    have := D.edgePair_ne (half.symm h)
    apply this
    simpa [mul_assoc] using congrArg (fun x => half.symm x) hh
  orientation := D.orientation ∘ half.symm
  orientation_pair := by
    intro h
    simp [Function.comp_apply, mul_assoc, D.orientation_pair]
  orientation_opposite := by
    intro i slot
    simp [Equiv.Perm.mul_apply, D.orientation_opposite]
  overPair := D.overPair ∘ cross.symm

/-- Relabelling transports the entire crossing block together with its metadata. -/
@[simp]
theorem relabel_crossing (D : OrientedPDCode n)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n))
    (i : Fin n) (slot : Fin 4) :
    (D.relabel half cross).crossing i slot = half (D.crossing (cross.symm i) slot) := by
  simp [relabel, crossing, Equiv.Perm.mul_apply]

/-- The crossing sign after relabelling is read at the old crossing name. -/
@[simp]
theorem relabel_crossingSign (D : OrientedPDCode n)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) (i : Fin n) :
    (D.relabel half cross).crossingSign i = D.crossingSign (cross.symm i) :=
  by simp [crossingSign, relabel, Function.comp_apply]

/-- Relabelling by identity permutations does nothing. -/
@[simp]
theorem relabel_refl (D : OrientedPDCode n) :
    D.relabel (Equiv.refl _) (Equiv.refl _) = D := by
  apply ext
  · ext x
    rw [← (crossingSlotEquiv n).apply_symm_apply x]
    simp [relabel, crossingBlockPerm, Equiv.Perm.mul_apply]
  · ext x
    rfl
  · rfl
  · rfl

/-- Consecutive relabellings compose their half-edge and crossing permutations. -/
@[simp]
theorem relabel_relabel (D : OrientedPDCode n)
    (half₁ half₂ : Equiv.Perm (Fin (4 * n))) (cross₁ cross₂ : Equiv.Perm (Fin n)) :
    (D.relabel half₁ cross₁).relabel half₂ cross₂ =
      D.relabel (half₂ * half₁) (cross₂ * cross₁) := by
  apply ext
  · change half₂ * (half₁ * D.halfEdge * crossingBlockPerm cross₁.symm) *
      crossingBlockPerm cross₂.symm =
        (half₂ * half₁) * D.halfEdge * crossingBlockPerm (cross₂ * cross₁).symm
    have hcross : (cross₂ * cross₁).symm = cross₁.symm * cross₂.symm := by
      simpa only [Equiv.Perm.inv_def] using (mul_inv_rev cross₂ cross₁)
    rw [hcross, crossingBlockPerm_mul]
    simp only [mul_assoc]
  · ext x
    rfl
  · rfl
  · rfl

end OrientedPDCode

/-- The empty oriented PD-code. -/
@[expose] def orientedPDCodeZero : OrientedPDCode 0 where
  halfEdge := Equiv.refl _
  edgePair := Equiv.refl _
  edgePair_sq := by intro h; exact rfl
  edgePair_ne := by intro h; exact Fin.elim0 h
  orientation := fun h => nomatch h
  orientation_pair := by intro h; exact nomatch h
  orientation_opposite := by intro i; exact Fin.elim0 i
  overPair := fun h => nomatch h

/-- Reflection fixes the empty PD-code. -/
@[simp]
theorem orientedPDCodeZero_mirror :
    orientedPDCodeZero.mirror = orientedPDCodeZero := by
  refine OrientedPDCode.ext (D := orientedPDCodeZero.mirror) (E := orientedPDCodeZero)
    rfl rfl rfl ?_
  funext i
  exact Fin.elim0 i

/-- A one-crossing positive PD-code whose two exterior arcs join adjacent crossing visits.

This concrete code is useful as a sanity check that the presentation permits genuine crossings,
not only the empty link. -/
@[expose] def orientedPDCodeOne : OrientedPDCode 1 where
  halfEdge := Equiv.refl _
  edgePair := Equiv.swap 0 1 * Equiv.swap 2 3
  edgePair_sq := by
    intro h
    fin_cases h <;> simp [Equiv.swap_apply_def]
  edgePair_ne := by
    intro h
    fin_cases h <;> simp [Equiv.swap_apply_def]
  orientation := fun h => decide (h = 1 ∨ h = 2)
  orientation_pair := by
    intro h
    fin_cases h <;> simp [Equiv.swap_apply_def]
  orientation_opposite := by
    intro i slot
    fin_cases i
    fin_cases slot <;> decide
  overPair := fun _ => true

@[simp]
theorem orientedPDCodeOne_crossingSign :
    orientedPDCodeOne.crossingSign 0 = 1 :=
  by decide

@[simp]
theorem orientedPDCodeOne_mirror_crossingSign :
    orientedPDCodeOne.mirror.crossingSign 0 = -1 := by
  simp

end TauCeti
