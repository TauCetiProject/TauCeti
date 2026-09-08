/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# Oriented PD-codes

An oriented PD-code records the finite combinatorial data at the crossings of a link.  The
`halfEdge` permutation lists the four visits at each crossing, `edgePair` joins the two visits
belonging to one arc, and `orientation` records the direction of every arc.  Crossing-free circle
components and their orientations are recorded separately.  Opposite slots form the two local
strands, one of which is selected by `overPair`; the crossing sign is then derived from this local
oriented crossing data.

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
* `TauCeti.orientedPDCodeUnlink` records any finite collection of oriented crossing-free circles;
  `orientedPDCodeZero` and `orientedPDCodeUnknot` are respectively the empty and one-circle cases.
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
  finCycle 2

end OrientedPDCode

/-- A finite oriented PD-code with `n` crossings.

The `4 * n` half-edges are grouped into four slots for each crossing by `halfEdge`.  The
fixed-point-free involution `edgePair` joins the two visits of each arc.  `orientation` chooses a
direction on each arc, so its values are opposite both at paired visits and across each local
strand.  Slots `0` and `2` form one strand, while slots `1` and `3` form the other.
`crossinglessComponents` records the chosen orientations of components with no crossing visits.
`overPair i = false` selects the `0`-`2` strand as over; `true` selects the `1`-`3` strand. -/
structure OrientedPDCode (n : ℕ) where
  /-- The half-edge labels occupying the four slots of each crossing. -/
  halfEdge : Equiv.Perm (Fin (4 * n))
  /-- The involution pairing the two visits of each arc. -/
  edgePair : Equiv.Perm (Fin (4 * n))
  /-- Pairing twice returns to the original visit. -/
  edgePair_apply_edgePair : ∀ h, edgePair (edgePair h) = h
  /-- No visit is paired with itself. -/
  edgePair_ne_self : ∀ h, edgePair h ≠ h
  /-- Whether an arc points away from its incident crossing (`true`) or toward it (`false`). -/
  orientation : Fin (4 * n) → Bool
  /-- The direction on an arc reverses at its paired visit. -/
  orientation_edgePair : ∀ h, orientation (edgePair h) = !orientation h
  /-- The orientation reverses between the opposite slots belonging to each local strand. -/
  orientation_oppositeCrossingSlot : ∀ i slot,
    orientation (halfEdge (OrientedPDCode.crossingSlotEquiv n
      (i, OrientedPDCode.oppositeCrossingSlot slot))) =
      !orientation (halfEdge (OrientedPDCode.crossingSlotEquiv n (i, slot)))
  /-- The chosen orientations of circle components which meet no crossing. -/
  crossinglessComponents : Multiset Bool
  /-- Which of the two opposite-slot strands is over at each crossing. -/
  overPair : Fin n → Bool

attribute [simp] OrientedPDCode.edgePair_apply_edgePair
  OrientedPDCode.orientation_edgePair OrientedPDCode.orientation_oppositeCrossingSlot

namespace OrientedPDCode

variable {n : ℕ}

/-- An oriented PD-code is determined by its crossing order, arc pairing, orientations, and
crossing-free components, and over-strand choices. -/
@[ext]
theorem ext {D E : OrientedPDCode n}
    (hhalf : D.halfEdge = E.halfEdge) (hedge : D.edgePair = E.edgePair)
    (horient : D.orientation = E.orientation)
    (hcrossingless : D.crossinglessComponents = E.crossinglessComponents)
    (hover : D.overPair = E.overPair) : D = E := by
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

/-- Reflect a diagram by swapping the over- and under-strands while preserving its oriented arcs. -/
@[expose] def mirror (D : OrientedPDCode n) : OrientedPDCode n where
  halfEdge := D.halfEdge
  edgePair := D.edgePair
  edgePair_apply_edgePair := D.edgePair_apply_edgePair
  edgePair_ne_self := D.edgePair_ne_self
  orientation := D.orientation
  orientation_edgePair := D.orientation_edgePair
  orientation_oppositeCrossingSlot := D.orientation_oppositeCrossingSlot
  crossinglessComponents := D.crossinglessComponents
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

/-- Reflection preserves the orientations of components which do not meet a crossing. -/
@[simp]
theorem mirror_crossinglessComponents (D : OrientedPDCode n) :
    D.mirror.crossinglessComponents = D.crossinglessComponents :=
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
  (crossingSlotEquiv n).permCongr (cross.prodCongr (.refl _))

/-- A crossing-block permutation changes the crossing coordinate and preserves the slot. -/
@[simp]
theorem crossingBlockPerm_apply_crossingSlotEquiv (cross : Equiv.Perm (Fin n))
    (i : Fin n) (slot : Fin 4) :
    crossingBlockPerm cross (crossingSlotEquiv n (i, slot)) =
      crossingSlotEquiv n (cross i, slot) := by
  simp [crossingBlockPerm]

/-- The inverse crossing-block permutation changes only the crossing coordinate. -/
@[simp]
theorem crossingBlockPerm_symm_apply_crossingSlotEquiv (cross : Equiv.Perm (Fin n))
    (i : Fin n) (slot : Fin 4) :
    (crossingBlockPerm cross).symm (crossingSlotEquiv n (i, slot)) =
      crossingSlotEquiv n (cross.symm i, slot) := by
  apply (crossingBlockPerm cross).injective
  simp

/-- The identity crossing permutation induces the identity block permutation. -/
@[simp]
theorem crossingBlockPerm_refl :
    crossingBlockPerm (Equiv.refl (Fin n)) = Equiv.refl _ := by
  apply Equiv.ext
  intro h
  rw [← (crossingSlotEquiv n).apply_symm_apply h]
  rcases (crossingSlotEquiv n).symm h with ⟨i, slot⟩
  simp

/-- Crossing-block permutations respect composition. -/
theorem crossingBlockPerm_mul (cross₁ cross₂ : Equiv.Perm (Fin n)) :
    crossingBlockPerm (cross₁ * cross₂) = crossingBlockPerm cross₁ * crossingBlockPerm cross₂ := by
  unfold crossingBlockPerm
  rw [← Equiv.permCongr_mul]
  congr 1

/-- Relabel half-edge visits and crossings by permutations.

The relabelling is deliberately independent of the planar realization: it changes only the finite
names, so later equivalence relations can quotient out these bookkeeping choices. -/
@[expose] def relabel (D : OrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) : OrientedPDCode n where
  halfEdge := (crossingBlockPerm cross).equivCongr half D.halfEdge
  edgePair := half.permCongr D.edgePair
  edgePair_apply_edgePair := by
    intro h
    simp
  edgePair_ne_self := by
    intro h hh
    have := D.edgePair_ne_self (half.symm h)
    apply this
    simpa using congrArg (fun x => half.symm x) hh
  orientation := D.orientation ∘ half.symm
  orientation_edgePair := by
    intro h
    simp [Function.comp_apply]
  orientation_oppositeCrossingSlot := by
    intro i slot
    simp
  crossinglessComponents := D.crossinglessComponents
  overPair := D.overPair ∘ cross.symm

/-- Relabelling transports the entire crossing block together with its metadata. -/
@[simp]
theorem relabel_crossing (D : OrientedPDCode n)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n))
    (i : Fin n) (slot : Fin 4) :
    (D.relabel half cross).halfEdge (crossingSlotEquiv n (i, slot)) =
      half (D.crossing (cross.symm i) slot) := by
  simp [relabel, crossing]

/-- Relabelling crossing and half-edge names leaves crossing-free components unchanged. -/
@[simp]
theorem relabel_crossinglessComponents (D : OrientedPDCode n)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).crossinglessComponents = D.crossinglessComponents :=
  rfl

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
    simp [relabel]
  · ext x
    rfl
  · rfl
  · rfl
  · rfl

/-- Consecutive relabellings compose their half-edge and crossing permutations. -/
@[simp]
theorem relabel_relabel (D : OrientedPDCode n)
    (half₁ half₂ : Equiv.Perm (Fin (4 * n))) (cross₁ cross₂ : Equiv.Perm (Fin n)) :
    (D.relabel half₁ cross₁).relabel half₂ cross₂ =
      D.relabel (half₂ * half₁) (cross₂ * cross₁) := by
  apply ext
  · change (crossingBlockPerm cross₂).equivCongr half₂
        ((crossingBlockPerm cross₁).equivCongr half₁ D.halfEdge) =
      (crossingBlockPerm (cross₂ * cross₁)).equivCongr (half₂ * half₁) D.halfEdge
    have htransport := congrArg (fun e => e D.halfEdge)
      (Equiv.equivCongr_trans (crossingBlockPerm cross₁) half₁
        (crossingBlockPerm cross₂) half₂)
    change _ = _ at htransport
    rw [crossingBlockPerm_mul]
    exact htransport
  · ext x
    rfl
  · rfl
  · rfl
  · rfl

end OrientedPDCode

/-- A zero-crossing oriented PD-code consisting of crossing-free circles with the specified
orientations.  Multiplicity records distinct components without imposing an ordering on them. -/
@[expose] def orientedPDCodeUnlink (orientations : Multiset Bool) : OrientedPDCode 0 where
  halfEdge := Equiv.refl _
  edgePair := Equiv.refl _
  edgePair_apply_edgePair := by intro h; exact rfl
  edgePair_ne_self := by intro h; exact Fin.elim0 h
  orientation := fun h => nomatch h
  orientation_edgePair := by intro h; exact nomatch h
  orientation_oppositeCrossingSlot := by intro i; exact Fin.elim0 i
  crossinglessComponents := orientations
  overPair := fun h => nomatch h

/-- The empty oriented PD-code. -/
@[expose] def orientedPDCodeZero : OrientedPDCode 0 :=
  orientedPDCodeUnlink 0

/-- A crossing-free oriented unknot with the specified choice of orientation. -/
@[expose] def orientedPDCodeUnknot (orientation : Bool) : OrientedPDCode 0 :=
  orientedPDCodeUnlink {orientation}

/-- Zero-crossing unlink codes retain exactly their multiset of component orientations. -/
theorem orientedPDCodeUnlink_injective : Function.Injective orientedPDCodeUnlink := by
  intro orientations₁ orientations₂ h
  exact congrArg OrientedPDCode.crossinglessComponents h

/-- A crossing-free oriented circle is distinct from the empty diagram. -/
theorem orientedPDCodeUnknot_ne_zero (orientation : Bool) :
    orientedPDCodeUnknot orientation ≠ orientedPDCodeZero := by
  intro h
  have := congrArg OrientedPDCode.crossinglessComponents h
  simp [orientedPDCodeUnknot, orientedPDCodeZero, orientedPDCodeUnlink] at this

/-- The two explicit orientation choices give distinct crossing-free circle presentations. -/
theorem orientedPDCodeUnknot_true_ne_false :
    orientedPDCodeUnknot true ≠ orientedPDCodeUnknot false := by
  intro h
  have := congrArg OrientedPDCode.crossinglessComponents h
  simp [orientedPDCodeUnknot, orientedPDCodeUnlink] at this

/-- Reflection fixes the empty PD-code. -/
@[simp]
theorem orientedPDCodeZero_mirror :
    orientedPDCodeZero.mirror = orientedPDCodeZero := by
  refine OrientedPDCode.ext (D := orientedPDCodeZero.mirror) (E := orientedPDCodeZero)
    rfl rfl rfl rfl ?_
  funext i
  exact Fin.elim0 i

/-- A one-crossing positive PD-code whose two exterior arcs join adjacent crossing visits.

This concrete code is useful as a sanity check that the presentation permits genuine crossings,
not only the empty link. -/
@[expose] def orientedPDCodeOne : OrientedPDCode 1 where
  halfEdge := Equiv.refl _
  edgePair := Equiv.swap 0 1 * Equiv.swap 2 3
  edgePair_apply_edgePair := by
    intro h
    fin_cases h <;> simp [Equiv.swap_apply_def]
  edgePair_ne_self := by
    intro h
    fin_cases h <;> simp [Equiv.swap_apply_def]
  orientation := fun h => decide (h = 1 ∨ h = 2)
  orientation_edgePair := by
    intro h
    fin_cases h <;> simp [Equiv.swap_apply_def]
  orientation_oppositeCrossingSlot := by
    intro i slot
    fin_cases i
    fin_cases slot <;> decide
  crossinglessComponents := 0
  overPair := fun _ => true

@[simp]
theorem orientedPDCodeOne_crossingSign :
    orientedPDCodeOne.crossingSign 0 = 1 :=
  by decide

end TauCeti
