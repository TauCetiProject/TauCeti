/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# PD-codes

A PD-code records finite combinatorial crossing data for a link. The `halfEdge` permutation lists
the four visits at each crossing, while the perfect matching `edgePair` joins the two visits of
each arc. Opposite slots form the two local strands, one of which is selected by `overPair`.
Crossing-free components are recorded separately.

`OrientedPDCode` decorates this data with compatible directions on the arcs and crossing-free
components. `FramedOrientedPDCode` further assigns an integer framing to every component. The
forgetful maps between these three presentation layers let results use only the data they need.

This is a code-level presentation: planarity and realization in the plane are intentionally
separate predicates. Keeping the code finite and explicit makes it a hub for later Reidemeister
moves and conversions to Gauss codes, without choosing a privileged geometric embedding.

The encoding follows Lickorish, *An Introduction to Knot Theory*, GTM 175, Chapter 1. No planar
realization theorem is asserted here; that is the subsequent geometric-to-combinatorial step.

## Main definitions

* `TauCeti.PDCode`: an unoriented PD-code with `n` crossings.
* `TauCeti.OrientedPDCode`: an orientation decoration of a PD-code.
* `TauCeti.FramedOrientedPDCode`: a framing decoration of an oriented PD-code.
* `TauCeti.PDCode.mirror` and `TauCeti.PDCode.relabel`: reflection and relabelling.
* `TauCeti.OrientedPDCode.crossingSign`: the sign derived from the local oriented crossing data.

## Main results

* `TauCeti.OrientedPDCode.crossingSign_eq_one_iff` and
  `crossingSign_eq_neg_one_iff` characterize the two possible crossing signs.
* `TauCeti.PDCode.mirror_mirror` and `relabel_relabel` give the basic operation laws.
* `TauCeti.orientedPDCodeUnlinkEquiv` classifies zero-crossing oriented PD-codes.
-/

public section

namespace TauCeti

open Function

namespace PDCode

/-- The standard equivalence between crossing-slot pairs and the `4 * n` half-edge positions. -/
@[expose] def crossingSlotEquiv (n : ℕ) : Fin n × Fin 4 ≃ Fin (4 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 4))

/-- The slot opposite a given slot in the cyclic order at a crossing. -/
@[expose] def oppositeCrossingSlot : Equiv.Perm (Fin 4) :=
  finCycle 2

end PDCode

/-- A finite unoriented PD-code with `n` crossings.

The `4 * n` half-edges are grouped into four slots for each crossing by `halfEdge`. The perfect
matching `edgePair` joins the two visits of each arc. Slots `0` and `2` form one local strand,
while slots `1` and `3` form the other. `crossinglessComponentCount` counts circle components
with no crossing visits. `overPair i = false` selects the `0`-`2` strand as over, while `true`
selects the `1`-`3` strand. -/
structure PDCode (n : ℕ) where
  /-- The half-edge labels occupying the four slots of each crossing. -/
  halfEdge : Equiv.Perm (Fin (4 * n))
  /-- The perfect matching pairing the two visits of each arc. -/
  edgePair : PerfectMatching (Fin (4 * n))
  /-- The number of circle components which meet no crossing. -/
  crossinglessComponentCount : ℕ
  /-- Which of the two opposite-slot strands is over at each crossing. -/
  overPair : Fin n → Bool

/-- An oriented PD-code, consisting of an unoriented code and compatible component directions. -/
structure OrientedPDCode (n : ℕ) extends PDCode n where
  /-- Whether an arc points away from its incident crossing (`true`) or toward it (`false`). -/
  orientation : Fin (4 * n) → Bool
  /-- The direction on an arc reverses at its paired visit. -/
  orientation_edgePair : ∀ h, orientation (edgePair.val h) = !orientation h
  /-- The orientation reverses between the opposite slots belonging to each local strand. -/
  orientation_oppositeCrossingSlot : ∀ i slot,
    orientation (halfEdge (PDCode.crossingSlotEquiv n (i, PDCode.oppositeCrossingSlot slot))) =
      !orientation (halfEdge (PDCode.crossingSlotEquiv n (i, slot)))
  /-- The chosen orientations of circle components which meet no crossing. -/
  crossinglessComponents : Multiset Bool
  /-- The orientation list accounts for exactly the crossing-free components of the base code. -/
  crossinglessComponents_card : crossinglessComponents.card = crossinglessComponentCount

/-- A framed oriented PD-code.

On a component meeting a crossing, `framing` is an integer constant along arc pairings and local
strands. For crossing-free components, `crossinglessFramings` keeps each orientation paired with
its framing integer. These integers measure the chosen framing relative to the diagram's
blackboard framing. -/
structure FramedOrientedPDCode (n : ℕ) extends OrientedPDCode n where
  /-- The integer framing of the component through each crossing visit. -/
  framing : Fin (4 * n) → ℤ
  /-- Framing is constant along an arc. -/
  framing_edgePair : ∀ h, framing (edgePair.val h) = framing h
  /-- Framing is constant along a local strand through a crossing. -/
  framing_oppositeCrossingSlot : ∀ i slot,
    framing (halfEdge (PDCode.crossingSlotEquiv n (i, PDCode.oppositeCrossingSlot slot))) =
      framing (halfEdge (PDCode.crossingSlotEquiv n (i, slot)))
  /-- The orientation and integer framing of each crossing-free component. -/
  crossinglessFramings : Multiset (Bool × ℤ)
  /-- Forgetting framings recovers the oriented crossing-free components. -/
  crossinglessFramings_map_fst : crossinglessFramings.map Prod.fst = crossinglessComponents

attribute [simp] OrientedPDCode.orientation_edgePair
  OrientedPDCode.orientation_oppositeCrossingSlot
  FramedOrientedPDCode.framing_edgePair FramedOrientedPDCode.framing_oppositeCrossingSlot

namespace PDCode

variable {n : ℕ}

/-- An unoriented PD-code is determined by its crossing order, arc pairing, crossing-free
component count, and over-strand choices. -/
@[ext]
theorem ext {D E : PDCode n} (hhalf : D.halfEdge = E.halfEdge)
    (hedge : D.edgePair = E.edgePair)
    (hcrossingless : D.crossinglessComponentCount = E.crossinglessComponentCount)
    (hover : D.overPair = E.overPair) : D = E := by
  cases D
  cases E
  simp_all

/-- The four half-edge labels at a crossing, in cyclic order. -/
@[expose] def crossing (D : PDCode n) (i : Fin n) (slot : Fin 4) : Fin (4 * n) :=
  D.halfEdge (crossingSlotEquiv n (i, slot))

/-- The explicit formula for the half-edge in a specified crossing slot. -/
@[simp]
theorem crossing_apply (D : PDCode n) (i : Fin n) (slot : Fin 4) :
    D.crossing i slot = D.halfEdge (crossingSlotEquiv n (i, slot)) :=
  rfl

/-- Whether a slot belongs to the over-strand at its crossing. -/
def isOver (D : PDCode n) (i : Fin n) (slot : Fin 4) : Bool :=
  D.overPair i == decide (slot = 1 ∨ slot = 3)

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

/-- The two opposite slot pairs are precisely the two complementary local strands. -/
theorem isOver_slots (D : PDCode n) (i : Fin n) :
    D.isOver i 0 = D.isOver i 2 ∧ D.isOver i 1 = D.isOver i 3 ∧
      D.isOver i 0 = !D.isOver i 1 := by
  simp

/-- Reflect a diagram by swapping the over- and under-strands. -/
def mirror (D : PDCode n) : PDCode n where
  halfEdge := D.halfEdge
  edgePair := D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := fun i => !D.overPair i

/-- Reflection leaves the half-edge order unchanged. -/
@[simp] theorem mirror_halfEdge (D : PDCode n) : D.mirror.halfEdge = D.halfEdge := by
  simp [mirror]
/-- Reflection leaves the arc matching unchanged. -/
@[simp] theorem mirror_edgePair (D : PDCode n) : D.mirror.edgePair = D.edgePair := by
  simp [mirror]
/-- Reflection preserves the number of crossing-free components. -/
@[simp] theorem mirror_crossinglessComponentCount (D : PDCode n) :
    D.mirror.crossinglessComponentCount = D.crossinglessComponentCount := by simp [mirror]
/-- Reflection complements each over-strand choice. -/
@[simp] theorem mirror_overPair (D : PDCode n) (i : Fin n) :
    D.mirror.overPair i = !D.overPair i := by simp [mirror]
/-- Reflection leaves every labelled crossing slot unchanged. -/
theorem mirror_crossing (D : PDCode n) (i : Fin n) (slot : Fin 4) :
    D.mirror.crossing i slot = D.crossing i slot := by simp [mirror, crossing]

/-- Reflection interchanges over- and under-slots. -/
@[simp]
theorem mirror_isOver (D : PDCode n) (i : Fin n) (slot : Fin 4) :
    D.mirror.isOver i slot = !D.isOver i slot := by
  fin_cases slot <;> simp [mirror, isOver]

/-- Reflecting a PD-code twice gives the original code. -/
@[simp]
theorem mirror_mirror (D : PDCode n) : D.mirror.mirror = D := by
  apply ext
  · simp
  · simp
  · simp
  · funext i
    simp [mirror]

/-- The permutation of half-edge positions induced by a permutation of crossing blocks. -/
@[expose] def crossingBlockPerm (cross : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (4 * n)) :=
  (crossingSlotEquiv n).permCongr (cross.prodCongr (.refl _))

/-- A crossing-block permutation changes the crossing coordinate and preserves its slot. -/
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

/-- The identity crossing permutation induces the identity half-edge permutation. -/
@[simp]
theorem crossingBlockPerm_refl :
    crossingBlockPerm (Equiv.refl (Fin n)) = Equiv.refl _ := by
  apply Equiv.ext
  intro h
  rw [← (crossingSlotEquiv n).apply_symm_apply h]
  rcases (crossingSlotEquiv n).symm h with ⟨i, slot⟩
  simp

/-- Crossing-block permutations preserve permutation multiplication. -/
theorem crossingBlockPerm_mul (cross₁ cross₂ : Equiv.Perm (Fin n)) :
    crossingBlockPerm (cross₁ * cross₂) = crossingBlockPerm cross₁ * crossingBlockPerm cross₂ := by
  unfold crossingBlockPerm
  rw [← Equiv.permCongr_mul]
  congr 1

/-- Relabel half-edge visits and crossings by permutations. -/
def relabel (D : PDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) : PDCode n where
  halfEdge := (crossingBlockPerm cross).equivCongr half D.halfEdge
  edgePair := PerfectMatching.congr half D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := D.overPair ∘ cross.symm

/-- Relabelling transports the half-edge order between the new finite names. -/
@[simp] theorem relabel_halfEdge (D : PDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) : (D.relabel half cross).halfEdge =
      (crossingBlockPerm cross).equivCongr half D.halfEdge := by simp [relabel]
/-- Relabelling transports the perfect matching along the half-edge permutation. -/
@[simp] theorem relabel_edgePair (D : PDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) : (D.relabel half cross).edgePair =
      PerfectMatching.congr half D.edgePair := by simp [relabel]
/-- Relabelling preserves the number of crossing-free components. -/
@[simp] theorem relabel_crossinglessComponentCount (D : PDCode n)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).crossinglessComponentCount = D.crossinglessComponentCount := by
  simp [relabel]
/-- Relabelling reads the over-strand choice at the old crossing name. -/
@[simp] theorem relabel_overPair (D : PDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) (i : Fin n) :
    (D.relabel half cross).overPair i = D.overPair (cross.symm i) := by simp [relabel]

/-- Relabelling transports every crossing block together with its slot order. -/
theorem relabel_crossing (D : PDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) (i : Fin n) (slot : Fin 4) :
    (D.relabel half cross).crossing i slot = half (D.crossing (cross.symm i) slot) := by
  simp [relabel, crossing]

/-- The over/under status after relabelling is read at the old crossing name. -/
@[simp]
theorem relabel_isOver (D : PDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) (i : Fin n) (slot : Fin 4) :
    (D.relabel half cross).isOver i slot = D.isOver (cross.symm i) slot := by
  simp [isOver]

/-- Relabelling by identity permutations does nothing. -/
@[simp]
theorem relabel_refl (D : PDCode n) :
    D.relabel (Equiv.refl _) (Equiv.refl _) = D := by
  apply ext
  · ext x
    rw [← (crossingSlotEquiv n).apply_symm_apply x]
    simp
  · exact PerfectMatching.congr_refl D.edgePair
  · simp
  · funext i
    simp [relabel]

/-- Consecutive relabellings compose their half-edge and crossing permutations. -/
@[simp]
theorem relabel_relabel (D : PDCode n)
    (half₁ half₂ : Equiv.Perm (Fin (4 * n))) (cross₁ cross₂ : Equiv.Perm (Fin n)) :
    (D.relabel half₁ cross₁).relabel half₂ cross₂ =
      D.relabel (half₂ * half₁) (cross₂ * cross₁) := by
  apply ext
  · rw [relabel_halfEdge, relabel_halfEdge, relabel_halfEdge, crossingBlockPerm_mul]
    have htransport := congrArg (fun e => e D.halfEdge)
      (Equiv.equivCongr_trans (crossingBlockPerm cross₁) half₁
        (crossingBlockPerm cross₂) half₂)
    exact htransport
  · simpa only [relabel_edgePair, Equiv.Perm.mul_def] using
      PerfectMatching.congr_trans half₁ half₂ D.edgePair
  · simp
  · funext i
    simp only [relabel_overPair]
    have hinv : (cross₂ * cross₁).symm = cross₁.symm * cross₂.symm := by
      simpa only [Equiv.Perm.inv_def] using (mul_inv_rev cross₂ cross₁)
    rw [hinv]
    rfl

end PDCode

namespace OrientedPDCode

variable {n : ℕ}

/-- An oriented PD-code is determined by its underlying code, arc directions, and the
orientations of its crossing-free components. -/
@[ext]
theorem ext {D E : OrientedPDCode n} (hcode : D.toPDCode = E.toPDCode)
    (horient : D.orientation = E.orientation)
    (hcrossingless : D.crossinglessComponents = E.crossinglessComponents) : D = E := by
  cases D
  cases E
  simp_all

/-- Forget the orientation of a PD-code. -/
def forgetOrientation (D : OrientedPDCode n) : PDCode n := D.toPDCode

/-- The named forgetful map is the underlying-code projection. -/
@[simp] theorem forgetOrientation_eq_toPDCode (D : OrientedPDCode n) :
    D.forgetOrientation = D.toPDCode := by simp [forgetOrientation]

/-- The four half-edge labels at a crossing, in cyclic order. -/
def crossing (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) : Fin (4 * n) :=
  D.toPDCode.crossing i slot

/-- The oriented crossing accessor agrees with the underlying half-edge order. -/
@[simp] theorem crossing_apply (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) :
    D.crossing i slot = D.halfEdge (PDCode.crossingSlotEquiv n (i, slot)) := by
  simp [crossing, PDCode.crossing]

/-- Whether a slot belongs to the over-strand at its crossing. -/
def isOver (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) : Bool :=
  D.toPDCode.isOver i slot

/-- Slot zero is over exactly when the second strand pair was not selected. -/
@[simp] theorem isOver_zero (D : OrientedPDCode n) (i : Fin n) :
    D.isOver i 0 = !D.overPair i := D.toPDCode.isOver_zero i
/-- Slot one is over exactly when the second strand pair was selected. -/
@[simp] theorem isOver_one (D : OrientedPDCode n) (i : Fin n) :
    D.isOver i 1 = D.overPair i := D.toPDCode.isOver_one i
/-- Slot two is over exactly when the second strand pair was not selected. -/
@[simp] theorem isOver_two (D : OrientedPDCode n) (i : Fin n) :
    D.isOver i 2 = !D.overPair i := D.toPDCode.isOver_two i
/-- Slot three is over exactly when the second strand pair was selected. -/
@[simp] theorem isOver_three (D : OrientedPDCode n) (i : Fin n) :
    D.isOver i 3 = D.overPair i := D.toPDCode.isOver_three i

/-- The sign of an oriented crossing, with slots read counterclockwise in the oriented plane. -/
def crossingSign (D : OrientedPDCode n) (i : Fin n) : ℤ :=
  if Bool.xor (D.orientation (D.crossing i 0)) (D.orientation (D.crossing i 1)) =
      D.overPair i then 1 else -1

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
    D.crossingSign i = 1 ∨ D.crossingSign i = -1 := by
  simp only [crossingSign]
  split <;> simp_all

/-- Reflect an oriented diagram, preserving all component orientations. -/
def mirror (D : OrientedPDCode n) : OrientedPDCode n where
  toPDCode := D.toPDCode.mirror
  orientation := D.orientation
  orientation_edgePair := by simp
  orientation_oppositeCrossingSlot := by simp
  crossinglessComponents := D.crossinglessComponents
  crossinglessComponents_card := by simpa using D.crossinglessComponents_card

/-- Forgetting orientation after reflection gives reflection of the underlying code. -/
@[simp] theorem mirror_toPDCode (D : OrientedPDCode n) :
    D.mirror.toPDCode = D.toPDCode.mirror := by simp [mirror]
/-- Reflection leaves the half-edge order unchanged. -/
theorem mirror_halfEdge (D : OrientedPDCode n) : D.mirror.halfEdge = D.halfEdge := by
  simp [mirror]
/-- Reflection leaves the arc matching unchanged. -/
theorem mirror_edgePair (D : OrientedPDCode n) : D.mirror.edgePair = D.edgePair := by
  simp [mirror]
/-- Reflection preserves the orientation of every arc. -/
@[simp] theorem mirror_orientation (D : OrientedPDCode n) :
    D.mirror.orientation = D.orientation := by simp [mirror]
/-- Reflection complements each over-strand choice. -/
theorem mirror_overPair (D : OrientedPDCode n) (i : Fin n) :
    D.mirror.overPair i = !D.overPair i := by simp [mirror]
/-- Reflection leaves every labelled crossing slot unchanged. -/
theorem mirror_crossing (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) :
    D.mirror.crossing i slot = D.crossing i slot := by simp [mirror, crossing]
/-- Reflection preserves the oriented crossing-free components. -/
@[simp] theorem mirror_crossinglessComponents (D : OrientedPDCode n) :
    D.mirror.crossinglessComponents = D.crossinglessComponents := by simp [mirror]

/-- Reflection interchanges the over- and under-slots of an oriented code. -/
@[simp]
theorem mirror_isOver (D : OrientedPDCode n) (i : Fin n) (slot : Fin 4) :
    D.mirror.isOver i slot = !D.isOver i slot := D.toPDCode.mirror_isOver i slot

/-- Reflection reverses the sign of every crossing. -/
@[simp]
theorem mirror_crossingSign (D : OrientedPDCode n) (i : Fin n) :
    D.mirror.crossingSign i = -D.crossingSign i := by
  rw [crossingSign, crossingSign]
  simp only [mirror_orientation, mirror_crossing, mirror_overPair]
  generalize Bool.xor (D.orientation (D.crossing i 0))
    (D.orientation (D.crossing i 1)) = parity
  generalize D.overPair i = ov
  cases parity <;> cases ov <;> norm_num

/-- Reflecting an oriented PD-code twice gives the original code. -/
@[simp]
theorem mirror_mirror (D : OrientedPDCode n) : D.mirror.mirror = D := by
  apply ext
  · exact PDCode.mirror_mirror D.toPDCode
  · simp
  · simp

/-- Relabel half-edge visits and crossings by permutations. -/
def relabel (D : OrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) : OrientedPDCode n where
  toPDCode := D.toPDCode.relabel half cross
  orientation := D.orientation ∘ half.symm
  orientation_edgePair := by
    intro h
    simp [PDCode.relabel, Function.comp_apply]
  orientation_oppositeCrossingSlot := by
    intro i slot
    simp [PDCode.relabel, Function.comp_apply]
  crossinglessComponents := D.crossinglessComponents
  crossinglessComponents_card := by simpa using D.crossinglessComponents_card

/-- Forgetting orientation after relabelling gives relabelling of the underlying code. -/
@[simp] theorem relabel_toPDCode (D : OrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) : (D.relabel half cross).toPDCode =
      D.toPDCode.relabel half cross := by simp [relabel]
/-- Relabelling transports the half-edge order between the new finite names. -/
theorem relabel_halfEdge (D : OrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) : (D.relabel half cross).halfEdge =
      (PDCode.crossingBlockPerm cross).equivCongr half D.halfEdge := by simp [relabel]
/-- Relabelling transports the perfect matching along the half-edge permutation. -/
theorem relabel_edgePair (D : OrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) : (D.relabel half cross).edgePair =
      PerfectMatching.congr half D.edgePair := by simp [relabel]
/-- Relabelling transports arc orientations along the half-edge permutation. -/
@[simp] theorem relabel_orientation (D : OrientedPDCode n)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) (h : Fin (4 * n)) :
    (D.relabel half cross).orientation h = D.orientation (half.symm h) := by simp [relabel]
/-- Relabelling reads the over-strand choice at the old crossing name. -/
theorem relabel_overPair (D : OrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) (i : Fin n) :
    (D.relabel half cross).overPair i = D.overPair (cross.symm i) := by simp [relabel]
/-- Relabelling leaves crossing-free oriented components unchanged. -/
@[simp] theorem relabel_crossinglessComponents (D : OrientedPDCode n)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) :
    (D.relabel half cross).crossinglessComponents = D.crossinglessComponents := by simp [relabel]

/-- Relabelling transports every oriented crossing block together with its slot order. -/
theorem relabel_crossing (D : OrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) (i : Fin n) (slot : Fin 4) :
    (D.relabel half cross).crossing i slot = half (D.crossing (cross.symm i) slot) :=
  D.toPDCode.relabel_crossing half cross i slot

/-- The over/under status after oriented relabelling is read at the old crossing name. -/
@[simp]
theorem relabel_isOver (D : OrientedPDCode n) (half : Equiv.Perm (Fin (4 * n)))
    (cross : Equiv.Perm (Fin n)) (i : Fin n) (slot : Fin 4) :
    (D.relabel half cross).isOver i slot = D.isOver (cross.symm i) slot :=
  D.toPDCode.relabel_isOver half cross i slot

/-- The crossing sign after relabelling is read at the old crossing name. -/
@[simp]
theorem relabel_crossingSign (D : OrientedPDCode n)
    (half : Equiv.Perm (Fin (4 * n))) (cross : Equiv.Perm (Fin n)) (i : Fin n) :
    (D.relabel half cross).crossingSign i = D.crossingSign (cross.symm i) := by
  simp [crossingSign]

/-- Relabelling by identity permutations does nothing. -/
@[simp]
theorem relabel_refl (D : OrientedPDCode n) :
    D.relabel (Equiv.refl _) (Equiv.refl _) = D := by
  apply ext
  · exact PDCode.relabel_refl D.toPDCode
  · funext h
    simp [relabel]
  · simp

/-- Consecutive relabellings compose their half-edge and crossing permutations. -/
@[simp]
theorem relabel_relabel (D : OrientedPDCode n)
    (half₁ half₂ : Equiv.Perm (Fin (4 * n))) (cross₁ cross₂ : Equiv.Perm (Fin n)) :
    (D.relabel half₁ cross₁).relabel half₂ cross₂ =
      D.relabel (half₂ * half₁) (cross₂ * cross₁) := by
  apply ext
  · exact PDCode.relabel_relabel D.toPDCode half₁ half₂ cross₁ cross₂
  · funext h
    simp only [relabel_orientation]
    have hinv : (half₂ * half₁).symm = half₁.symm * half₂.symm := by
      simpa only [Equiv.Perm.inv_def] using (mul_inv_rev half₂ half₁)
    rw [hinv]
    rfl
  · simp

end OrientedPDCode

namespace FramedOrientedPDCode

variable {n : ℕ}

/-- Forget the framing of a framed oriented PD-code. -/
def forgetFraming (D : FramedOrientedPDCode n) : OrientedPDCode n := D.toOrientedPDCode

/-- The named framing-forgetful map is the underlying oriented-code projection. -/
@[simp] theorem forgetFraming_eq_toOrientedPDCode (D : FramedOrientedPDCode n) :
    D.forgetFraming = D.toOrientedPDCode := by simp [forgetFraming]

/-- Forget both framing and orientation from a framed oriented PD-code. -/
def forgetFramingAndOrientation (D : FramedOrientedPDCode n) : PDCode n :=
  D.toOrientedPDCode.toPDCode

/-- Forgetting both decorations is the composite of the two forgetful maps. -/
@[simp] theorem forgetFramingAndOrientation_eq (D : FramedOrientedPDCode n) :
    D.forgetFramingAndOrientation = D.forgetFraming.forgetOrientation := by
  simp [forgetFramingAndOrientation, forgetFraming, OrientedPDCode.forgetOrientation]

end FramedOrientedPDCode

/-- A zero-crossing oriented PD-code consisting of crossing-free circles with the specified
orientations. Multiplicity records distinct components without imposing an ordering on them. -/
def orientedPDCodeUnlink (orientations : Multiset Bool) : OrientedPDCode 0 where
  halfEdge := Equiv.refl _
  edgePair := PerfectMatching.mk (Equiv.refl _) (by intro h; exact rfl)
    (by intro h; exact Fin.elim0 h)
  crossinglessComponentCount := orientations.card
  overPair := fun h => nomatch h
  orientation := fun h => nomatch h
  orientation_edgePair := by intro h; exact nomatch h
  orientation_oppositeCrossingSlot := by intro i; exact Fin.elim0 i
  crossinglessComponents := orientations
  crossinglessComponents_card := rfl

/-- The unlink constructor retains exactly its component-orientation multiset. -/
@[simp]
theorem orientedPDCodeUnlink_crossinglessComponents (orientations : Multiset Bool) :
    (orientedPDCodeUnlink orientations).crossinglessComponents = orientations := by
  simp [orientedPDCodeUnlink]

/-- Every zero-crossing oriented PD-code is its canonical crossing-free unlink code. -/
theorem orientedPDCode_eq_unlink (D : OrientedPDCode 0) :
    D = orientedPDCodeUnlink D.crossinglessComponents := by
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · ext h
      exact Fin.elim0 h
    · apply Subtype.ext
      ext h
      exact Fin.elim0 h
    · exact D.crossinglessComponents_card.symm
    · funext i
      exact Fin.elim0 i
  · funext h
    exact Fin.elim0 h
  · exact rfl

/-- Multisets of orientations are equivalent to zero-crossing oriented PD-codes. -/
def orientedPDCodeUnlinkEquiv : Multiset Bool ≃ OrientedPDCode 0 where
  toFun := orientedPDCodeUnlink
  invFun := OrientedPDCode.crossinglessComponents
  left_inv := orientedPDCodeUnlink_crossinglessComponents
  right_inv := fun D => (orientedPDCode_eq_unlink D).symm

/-- The zero-crossing unlink constructor is injective. -/
theorem orientedPDCodeUnlink_injective : Function.Injective orientedPDCodeUnlink :=
  orientedPDCodeUnlinkEquiv.injective

/-- The empty oriented PD-code. -/
def orientedPDCodeEmpty : OrientedPDCode 0 := orientedPDCodeUnlink 0

/-- A crossing-free oriented unknot with the specified choice of orientation. -/
def orientedPDCodeUnknot (orientation : Bool) : OrientedPDCode 0 :=
  orientedPDCodeUnlink {orientation}

/-- A crossing-free oriented circle is distinct from the empty diagram. -/
theorem orientedPDCodeUnknot_ne_empty (orientation : Bool) :
    orientedPDCodeUnknot orientation ≠ orientedPDCodeEmpty := by
  intro h
  have heq : ({orientation} : Multiset Bool) = 0 :=
    orientedPDCodeUnlink_injective (by
      simpa [orientedPDCodeUnknot, orientedPDCodeEmpty] using h)
  simpa using congrArg Multiset.card heq

/-- The two explicit orientation choices give distinct crossing-free circle presentations. -/
theorem orientedPDCodeUnknot_true_ne_false :
    orientedPDCodeUnknot true ≠ orientedPDCodeUnknot false := by
  intro h
  have heq : ({true} : Multiset Bool) = {false} :=
    orientedPDCodeUnlink_injective (by simpa [orientedPDCodeUnknot] using h)
  simp at heq

/-- Reflection fixes every zero-crossing oriented PD-code. -/
@[simp]
theorem OrientedPDCode.mirror_eq_self_of_zero_crossings (D : OrientedPDCode 0) :
    D.mirror = D := by
  rw [orientedPDCode_eq_unlink D]
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · simp
    · simp
    · simp
    · funext i
      exact Fin.elim0 i
  · simp
  · simp

/-- Reflection fixes the empty PD-code. -/
theorem orientedPDCodeEmpty_mirror :
    orientedPDCodeEmpty.mirror = orientedPDCodeEmpty :=
  OrientedPDCode.mirror_eq_self_of_zero_crossings _

/-- A one-crossing positive PD-code whose two exterior arcs join adjacent crossing visits.

This concrete code is a semantic witness that the presentation permits a genuine positive
crossing, not only crossing-free links. -/
def orientedPDCodeOneCrossingPositive : OrientedPDCode 1 where
  halfEdge := Equiv.refl _
  edgePair := PerfectMatching.mk (Equiv.swap 0 1 * Equiv.swap 2 3)
    (by intro h; fin_cases h <;> simp [Equiv.swap_apply_def])
    (by intro h; fin_cases h <;> simp [Equiv.swap_apply_def])
  crossinglessComponentCount := 0
  overPair := fun _ => true
  orientation := fun h => decide (h = 1 ∨ h = 2)
  orientation_edgePair := by
    intro h
    fin_cases h <;> simp [Equiv.swap_apply_def]
  orientation_oppositeCrossingSlot := by
    intro i slot
    fin_cases i
    fin_cases slot <;> decide
  crossinglessComponents := 0
  crossinglessComponents_card := rfl

/-- The distinguished crossing of `orientedPDCodeOneCrossingPositive` has positive sign. -/
@[simp]
theorem orientedPDCodeOneCrossingPositive_crossingSign :
    orientedPDCodeOneCrossingPositive.crossingSign 0 = 1 := by
  decide

end TauCeti
