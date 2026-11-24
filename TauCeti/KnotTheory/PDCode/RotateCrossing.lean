/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Kauffman
public import TauCeti.KnotTheory.PDCode.Oriented.Component
public import TauCeti.KnotTheory.PDCode.Planar

/-!
# Reading a crossing of a PD-code from another slot

A PD-code lists the four half-edges at each crossing counterclockwise, starting from an arbitrary
slot. Reading the crossing `i` from its next slot counterclockwise instead gives another code for
the same diagram, `TauCeti.PDCode.rotateCrossing D i`: slot `k` of crossing `i` in the new code is
slot `k + 1` in the old one, and every other crossing is read as before. The two local strands at
`i` exchange the parities of their slots, so the over-pair indicator of `i` flips. Relabelling
(`TauCeti.PDCode.relabel`) renames half-edges and crossings but keeps the slot of every
half-edge, so it cannot change where the reading of a crossing starts; relabellings and these
rotations together are the isomorphisms of PD-codes. Local moves such as the third Reidemeister
move fix the slots at which their tangle meets each crossing, and the rotations let them apply to
a tangle however its crossings happen to be read.

The rotation leaves the underlying `4`-valent graph unchanged: it keeps the crossing rotation, and
so the faces and planarity, and the crossing turn, and so the components. It exchanges the two
local smoothings at `i` exactly as it flips the over-pair indicator, so every state smooths the
diagram into the same circles, and the Kauffman bracket is unchanged. On an oriented code it keeps
the orientation of every half-edge and the sign of every crossing, so the writhe-normalized bracket
is unchanged too, and every link component keeps its half-edge representatives and crossing-free
label.

## Main definitions

* `TauCeti.PDCode.rotateCrossing`: read one crossing of a PD-code from its next slot.
* `TauCeti.OrientedPDCode.rotateCrossing`: the same for an oriented PD-code.
* `TauCeti.OrientedPDCode.rotateCrossingComponentEquiv`: the labelled component bijection across a
  crossing-slot rotation.

## Main results

* `TauCeti.PDCode.toPermutationTriple_rotateCrossing` and
  `TauCeti.PDCode.isPlanar_rotateCrossing`: the rotation keeps the underlying graph and planarity.
* `TauCeti.PDCode.componentCount_rotateCrossing`: the rotation keeps the number of components.
* `TauCeti.PDCode.kauffmanBracket_rotateCrossing`: the rotation keeps the Kauffman bracket.
* `TauCeti.OrientedPDCode.crossingSign_rotateCrossing` and
  `TauCeti.OrientedPDCode.normalizedKauffmanBracket_rotateCrossing`: the rotation keeps every
  crossing sign and the writhe-normalized bracket.

## References

* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2-3 (the PD convention, reading each
  crossing counterclockwise).
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PDCode

variable {n : ℕ}

/-- Read the crossing `i` of a PD-code from its next slot counterclockwise: slot `k` of `i` in the
new code is slot `k + 1` in `D`. The local strand on slots `0` and `2` becomes the one on slots
`1` and `3`, so the over-pair indicator of `i` flips. The new code describes the same diagram. -/
def rotateCrossing (D : PDCode n) (i : Fin n) : PDCode n where
  halfEdge := D.halfEdge * (crossingSlotEquiv n).permCongr
    (prodCongrRight fun j ↦ if j = i then finRotate 4 else 1)
  edgePair := D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := Function.update D.overPair i (!D.overPair i)

section RotateCrossing

variable (D : PDCode n) (i : Fin n)

/-- Slot `k` of the rotated crossing is slot `k + 1` of the old one. -/
@[simp] theorem rotateCrossing_crossing_self (slot : Fin 4) :
    (D.rotateCrossing i).halfEdge (crossingSlotEquiv n (i, slot)) =
      D.halfEdge (crossingSlotEquiv n (i, slot + 1)) := by
  simp [rotateCrossing, Perm.mul_apply, Equiv.permCongr_apply]

/-- The other crossings keep their slots. -/
@[simp] theorem rotateCrossing_crossing_of_ne {j : Fin n} (hj : j ≠ i) (slot : Fin 4) :
    (D.rotateCrossing i).halfEdge (crossingSlotEquiv n (j, slot)) =
      D.halfEdge (crossingSlotEquiv n (j, slot)) := by
  simp [rotateCrossing, Perm.mul_apply, Equiv.permCongr_apply, hj]

/-- The rotation keeps the arcs. -/
@[simp] theorem rotateCrossing_edgePair : (D.rotateCrossing i).edgePair = D.edgePair := (rfl)

/-- The rotation keeps the crossing-free circles. -/
@[simp] theorem rotateCrossing_crossinglessComponentCount :
    (D.rotateCrossing i).crossinglessComponentCount = D.crossinglessComponentCount := (rfl)

/-- The over-pair indicator of the rotated crossing flips. -/
@[simp] theorem rotateCrossing_overPair_self :
    (D.rotateCrossing i).overPair i = !D.overPair i := by
  simp [rotateCrossing]

/-- The other crossings keep their over-pair indicators. -/
@[simp] theorem rotateCrossing_overPair_of_ne {j : Fin n} (hj : j ≠ i) :
    (D.rotateCrossing i).overPair j = D.overPair j := by
  simp [rotateCrossing, hj]

/-- Every half-edge of the rotated code is the one in a slot of `D`, read at the same crossing;
the rotation only shifts the slots of `i`. -/
private theorem rotateCrossing_halfEdge (j : Fin n) (slot : Fin 4) :
    (D.rotateCrossing i).halfEdge (crossingSlotEquiv n (j, slot)) =
      D.halfEdge (crossingSlotEquiv n (j, if j = i then slot + 1 else slot)) := by
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- Mirroring commutes with reading a crossing from another slot. -/
@[simp] theorem mirror_rotateCrossing :
    (D.rotateCrossing i).mirror = D.mirror.rotateCrossing i := by
  ext1
  · simp [rotateCrossing]
  · simp
  · simp
  · funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]

/-- The rotation keeps the counterclockwise rotation of the slots at every crossing. -/
@[simp] theorem crossingRotation_rotateCrossing :
    (D.rotateCrossing i).crossingRotation = D.crossingRotation := by
  ext h
  obtain ⟨x, rfl⟩ := (D.rotateCrossing i).halfEdge.surjective h
  obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  rw [crossingRotation_crossing, crossing_apply, rotateCrossing_halfEdge, rotateCrossing_halfEdge,
    crossingRotation_crossing, crossing_apply]
  split_ifs <;> rfl

/-- The rotation keeps the face traversal. -/
@[simp] theorem facePerm_rotateCrossing : (D.rotateCrossing i).facePerm = D.facePerm := by
  simp [facePerm_def]

/-- The rotation keeps the permutation triple of the underlying graph. -/
@[simp] theorem toPermutationTriple_rotateCrossing :
    (D.rotateCrossing i).toPermutationTriple = D.toPermutationTriple :=
  PermutationTriple.ext_of_two (by simp) (by simp)

/-- The rotation keeps planarity. -/
@[simp] theorem isPlanar_rotateCrossing : (D.rotateCrossing i).IsPlanar ↔ D.IsPlanar := by
  simp [isPlanar_def]

/-- The rotation keeps the passage through each crossing to the opposite slot. -/
@[simp] theorem crossingTurn_rotateCrossing :
    (D.rotateCrossing i).crossingTurn = D.crossingTurn := by
  ext h
  obtain ⟨x, rfl⟩ := (D.rotateCrossing i).halfEdge.surjective h
  obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  rw [crossingTurn_crossing, crossing_apply, rotateCrossing_halfEdge, rotateCrossing_halfEdge,
    crossingTurn_crossing, crossing_apply]
  split_ifs
  · simp only [oppositeCrossingSlot_apply]
    abel_nf
  · rfl

/-- The rotation keeps the component traversal. -/
@[simp] theorem componentPerm_rotateCrossing :
    (D.rotateCrossing i).componentPerm = D.componentPerm := by
  simp [componentPerm_def]

/-- The rotation keeps the number of components. -/
@[simp] theorem componentCount_rotateCrossing :
    (D.rotateCrossing i).componentCount = D.componentCount := by
  simp [componentCount_eq, crossingComponentCount_def]

/-- Reading a crossing from its next slot exchanges its two local smoothings. -/
private theorem slotSmoothing_not_add_one (c : Bool) (slot : Fin 4) :
    slotSmoothing (!c) (slot + 1) = slotSmoothing c slot + 1 := by
  revert slot
  cases c <;> simp only [Bool.not_false, Bool.not_true, slotSmoothing_true, slotSmoothing_false] <;>
    decide

/-- Smoothing the rotated code by a family of local smoothings is smoothing `D` by the family with
the other local smoothing at `i`. -/
theorem smoothingTurn_rotateCrossing (b : Fin n → Bool) :
    (D.rotateCrossing i).smoothingTurn b = D.smoothingTurn (Function.update b i (!b i)) := by
  ext h
  obtain ⟨x, rfl⟩ := (D.rotateCrossing i).halfEdge.surjective h
  obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
  rw [smoothingTurn_crossing, crossing_apply, rotateCrossing_halfEdge, rotateCrossing_halfEdge,
    smoothingTurn_crossing, crossing_apply]
  by_cases hj : j = i
  · subst hj
    simp [slotSmoothing_not_add_one]
  · simp [hj]

/-- A state selects at the rotated crossing the other local smoothing of the rotated code. -/
theorem smoothingChoice_rotateCrossing (s : Fin n → Bool) :
    (D.rotateCrossing i).smoothingChoice s =
      Function.update (D.smoothingChoice s) i (!D.smoothingChoice s i) := by
  funext j
  by_cases hj : j = i
  · subst hj
    cases hs : s j <;> simp [hs]
  · cases hs : s j <;> simp [hs, hj]

/-- Every state smooths the rotated code into the same circles as `D`. -/
@[simp] theorem statePerm_rotateCrossing (s : Fin n → Bool) :
    (D.rotateCrossing i).statePerm s = D.statePerm s := by
  rw [statePerm_def, statePerm_def, smoothingTurn_rotateCrossing, smoothingChoice_rotateCrossing,
    rotateCrossing_edgePair]
  simp

/-- Every state leaves as many circles in the rotated code as in `D`. -/
@[simp] theorem stateLoopCount_rotateCrossing (s : Fin n → Bool) :
    (D.rotateCrossing i).stateLoopCount s = D.stateLoopCount s := by
  simp [stateLoopCount_def]

/-- **The rotation keeps the Kauffman bracket.** -/
@[simp] theorem kauffmanBracket_rotateCrossing {R : Type*} [CommRing R] (a : Rˣ) :
    (D.rotateCrossing i).kauffmanBracket a = D.kauffmanBracket a := by
  simp [kauffmanBracket_def]

end RotateCrossing

end PDCode

namespace OrientedPDCode

variable {n : ℕ}

/-- Shifting the slots of a crossing by one step commutes with passing to the opposite slot. -/
private theorem oppositeCrossingSlot_add_one (slot : Fin 4) :
    PDCode.oppositeCrossingSlot slot + 1 = PDCode.oppositeCrossingSlot (slot + 1) := by
  simp only [PDCode.oppositeCrossingSlot_apply]
  abel

/-- Read the crossing `i` of an oriented PD-code from its next slot counterclockwise, keeping the
orientation of every half-edge. -/
def rotateCrossing (D : OrientedPDCode n) (i : Fin n) : OrientedPDCode n where
  toPDCode := D.toPDCode.rotateCrossing i
  orientation := D.orientation
  orientation_edgePair := D.orientation_edgePair
  orientation_oppositeCrossingSlot j slot := by
    by_cases hj : j = i
    · subst hj
      simp [oppositeCrossingSlot_add_one]
    · simp [hj]
  crossinglessComponents := D.crossinglessComponents
  card_crossinglessComponents := D.card_crossinglessComponents

section RotateCrossing

variable (D : OrientedPDCode n) (i : Fin n)

/-- Forgetting orientation after the rotation gives the rotation of the underlying code. -/
@[simp] theorem toPDCode_rotateCrossing :
    (D.rotateCrossing i).toPDCode = D.toPDCode.rotateCrossing i := (rfl)

/-- The rotation keeps the orientation of every half-edge. -/
@[simp] theorem rotateCrossing_orientation :
    (D.rotateCrossing i).orientation = D.orientation := (rfl)

/-- The rotation keeps the oriented crossing-free circles. -/
@[simp] theorem rotateCrossing_crossinglessComponents :
    (D.rotateCrossing i).crossinglessComponents = D.crossinglessComponents := (rfl)

/-- Mirroring commutes with changing the starting slot of an oriented crossing. -/
@[simp] theorem mirror_rotateCrossing :
    (D.rotateCrossing i).mirror = D.mirror.rotateCrossing i := by
  apply OrientedPDCode.ext <;> simp

/-- Reversing component directions commutes with changing the starting slot of a crossing. -/
@[simp] theorem reverse_rotateCrossing :
    (D.rotateCrossing i).reverse = D.reverse.rotateCrossing i := by
  apply OrientedPDCode.ext
  · simp
  · funext x; simp
  · simp

/-- **The rotation keeps every crossing sign.** At the rotated crossing both the orientation
parity of slots `0` and `1` and the over-pair indicator flip. -/
@[simp] theorem crossingSign_rotateCrossing (j : Fin n) :
    (D.rotateCrossing i).crossingSign j = D.crossingSign j := by
  by_cases hj : j = i
  · subst hj
    have h := D.orientation_oppositeCrossingSlot j 0
    simp only [PDCode.oppositeCrossingSlot_apply, zero_add] at h
    simp only [crossingSign_def, PDCode.crossing_apply, toPDCode_rotateCrossing,
      PDCode.rotateCrossing_crossing_self, PDCode.rotateCrossing_overPair_self,
      rotateCrossing_orientation, zero_add]
    have h₁₂ : (1 : Fin 4) + 1 = 2 := by decide
    rw [h₁₂, h]
    cases D.orientation (D.halfEdge (PDCode.crossingSlotEquiv n (j, 0))) <;>
      cases D.orientation (D.halfEdge (PDCode.crossingSlotEquiv n (j, 1))) <;>
      cases D.overPair j <;> simp
  · simp [crossingSign_def, hj]

/-- The rotation keeps the writhe. -/
@[simp] theorem writhe_rotateCrossing : (D.rotateCrossing i).writhe = D.writhe := by
  simp [writhe_def]

/-- **The rotation keeps the writhe-normalized Kauffman bracket.** -/
@[simp] theorem normalizedKauffmanBracket_rotateCrossing {R : Type*} [CommRing R] (a : Rˣ) :
    (D.rotateCrossing i).normalizedKauffmanBracket a = D.normalizedKauffmanBracket a := by
  simp [normalizedKauffmanBracket_def]

/-- Reading a crossing from its next slot preserves outgoing half-edges while keeping every
half-edge label fixed. -/
abbrev rotateCrossingOutgoingEquiv :
    {h : Fin (4 * n) // D.orientation h = true} ≃
      {h : Fin (4 * n) // (D.rotateCrossing i).orientation h = true} :=
  Equiv.subtypeEquivRight fun _ ↦ by simp

/-- Reading a crossing from its next slot conjugates outgoing component traversal along the
identity on half-edge labels. -/
@[simp] theorem componentPermOutgoing_rotateCrossing :
    (D.rotateCrossing i).componentPermOutgoing =
      (D.rotateCrossingOutgoingEquiv i).permCongr D.componentPermOutgoing := by
  ext h
  simp

noncomputable section

/-- Reading a crossing from its next slot preserves every component's outgoing half-edge
representatives and every crossing-free circle label. -/
def rotateCrossingComponentEquiv : D.Component ≃ (D.rotateCrossing i).Component :=
  D.componentEquiv (D.rotateCrossing i) (D.rotateCrossingOutgoingEquiv i)
    (D.componentPermOutgoing_rotateCrossing i) (finCongr (by simp))

/-- Rotating a crossing slot preserves the component represented by each outgoing half-edge. -/
@[simp] theorem rotateCrossingComponentEquiv_componentOfOutgoing
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.rotateCrossingComponentEquiv i (D.componentOfOutgoing h) =
      (D.rotateCrossing i).componentOfOutgoing (D.rotateCrossingOutgoingEquiv i h) :=
  D.componentEquiv_componentOfOutgoing _ _ _ _ h

/-- Rotating a crossing slot preserves the component of every half-edge, incoming or outgoing. -/
@[simp] theorem rotateCrossingComponentEquiv_inl_halfEdge (x : Fin (4 * n)) :
    D.rotateCrossingComponentEquiv i (.inl (D.crossingComponentOfHalfEdge x)) =
      .inl ((D.rotateCrossing i).crossingComponentOfHalfEdge x) :=
  D.componentEquiv_inl_crossingComponentOfHalfEdge (D.rotateCrossing i)
    (D.rotateCrossingOutgoingEquiv i) (D.componentPermOutgoing_rotateCrossing i)
    (finCongr (by simp)) id (fun _ ↦ by simp) (fun _ ↦ by simp) x

/-- Rotating a crossing slot fixes every crossing-free component label. -/
@[simp] theorem rotateCrossingComponentEquiv_inr (j : Fin D.crossinglessComponentCount) :
    D.rotateCrossingComponentEquiv i (.inr j) = .inr (Fin.cast (by simp) j) := by
  simp [rotateCrossingComponentEquiv]

/-- Inverse component transport across a crossing-slot rotation fixes outgoing representatives. -/
@[simp] theorem rotateCrossingComponentEquiv_symm_componentOfOutgoing
    (h : {h : Fin (4 * n) // (D.rotateCrossing i).orientation h = true}) :
    (D.rotateCrossingComponentEquiv i).symm ((D.rotateCrossing i).componentOfOutgoing h) =
      D.componentOfOutgoing ((D.rotateCrossingOutgoingEquiv i).symm h) := by
  apply (D.rotateCrossingComponentEquiv i).injective
  simp

/-- Inverse component transport across a crossing-slot rotation preserves every half-edge's
component. -/
@[simp] theorem rotateCrossingComponentEquiv_symm_inl_halfEdge (x : Fin (4 * n)) :
    (D.rotateCrossingComponentEquiv i).symm
        (.inl ((D.rotateCrossing i).crossingComponentOfHalfEdge x)) =
      .inl (D.crossingComponentOfHalfEdge x) := by
  apply (D.rotateCrossingComponentEquiv i).injective
  simp

/-- Inverse component transport across a crossing-slot rotation fixes every crossing-free label. -/
@[simp] theorem rotateCrossingComponentEquiv_symm_inr
    (j : Fin (D.rotateCrossing i).crossinglessComponentCount) :
    (D.rotateCrossingComponentEquiv i).symm (.inr j) = .inr (Fin.cast (by simp) j) := by
  apply (D.rotateCrossingComponentEquiv i).injective
  simp

end

end RotateCrossing

end OrientedPDCode

end TauCeti
