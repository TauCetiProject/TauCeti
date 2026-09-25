/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Kauffman

/-!
# Adjoining a crossing-free circle to a PD-code

A `PDCode` records components that never visit a crossing by their count.  This file makes the
corresponding diagram operation explicit: `PDCode.adjoinCircle` adds one disjoint circle without
changing any crossing data.  The oriented and framed versions also record the orientation and
relative framing of the new component.

The component and state-circle formulas make the operation usable in local move calculations.
For a nonempty diagram, adjoining a circle multiplies the Kauffman bracket by the loop value
`jonesDelta`; the nonemptiness hypothesis is necessary because the empty code is normalised to
have bracket one rather than a negative power of the loop value.

`ClaspInsertion` applies to clasps whose arcs meet crossings and does not treat a clasp through a
crossing-free circle; this file supplies the separate operation of adjoining a disjoint
crossing-free circle, which local move calculations need alongside it.

The PD-code convention follows M. Mastin, *Links and Planar Diagram Codes*, Definitions 2--3.
The disjoint-circle Kauffman-bracket relation follows L. H. Kauffman, *State models and the Jones
polynomial*, and W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997),
Chapter 3.
-/

public section

namespace TauCeti

open TemperleyLieb

namespace PDCode

variable {n : ℕ}

/-! ### Unoriented codes -/

/-- Adjoin one disjoint circle to a PD-code.  The crossing data and all crossing-bearing
components are unchanged; only the explicit count of crossing-free components increases. -/
def adjoinCircle (D : PDCode n) : PDCode n where
  halfEdge := D.halfEdge
  edgePair := D.edgePair
  crossinglessComponentCount := D.crossinglessComponentCount + 1
  overPair := D.overPair

/-- Adjoining a circle leaves the crossing labels unchanged. -/
@[simp] theorem adjoinCircle_halfEdge (D : PDCode n) : D.adjoinCircle.halfEdge = D.halfEdge := by
  rfl

/-- Adjoining a circle leaves the arc matching unchanged. -/
@[simp] theorem adjoinCircle_edgePair (D : PDCode n) : D.adjoinCircle.edgePair = D.edgePair := by
  rfl

/-- Adjoining a circle leaves the over-strand choice at every crossing unchanged. -/
@[simp] theorem adjoinCircle_overPair (D : PDCode n) : D.adjoinCircle.overPair = D.overPair := by
  rfl

/-- The new circle contributes one crossing-free component. -/
@[simp] theorem adjoinCircle_crossinglessComponentCount (D : PDCode n) :
    D.adjoinCircle.crossinglessComponentCount = D.crossinglessComponentCount + 1 := by
  rfl

/-- Adjoining a circle leaves the crossing traversal unchanged. -/
@[simp] theorem crossingTurn_adjoinCircle (D : PDCode n) :
    D.adjoinCircle.crossingTurn = D.crossingTurn := by
  simp [crossingTurn_def]

/-- Adjoining a circle leaves the component traversal permutation unchanged. -/
@[simp] theorem componentPerm_adjoinCircle (D : PDCode n) :
    D.adjoinCircle.componentPerm = D.componentPerm := by
  rw [componentPerm_def, componentPerm_def, crossingTurn_adjoinCircle,
    adjoinCircle_edgePair]

/-- Adjoining a circle does not change the crossing-bearing components. -/
@[simp] theorem crossingComponentCount_adjoinCircle (D : PDCode n) :
    D.adjoinCircle.crossingComponentCount = D.crossingComponentCount := by
  rw [crossingComponentCount_def, crossingComponentCount_def, componentPerm_adjoinCircle]

/-- Adjoining a circle increases the total component count by one. -/
@[simp] theorem componentCount_adjoinCircle (D : PDCode n) :
    D.adjoinCircle.componentCount = D.componentCount + 1 := by
  simp only [componentCount_eq, crossingComponentCount_adjoinCircle,
    adjoinCircle_crossinglessComponentCount]
  omega

/-- Adjoining a circle leaves the smoothing traversal permutation unchanged. -/
@[simp] theorem smoothingTurn_adjoinCircle (D : PDCode n) (s : Fin n → Bool) :
    D.adjoinCircle.smoothingTurn s = D.smoothingTurn s := by
  simp [smoothingTurn_def]

/-- Adjoining a circle leaves the chosen local smoothing at every crossing unchanged. -/
@[simp] theorem smoothingChoice_adjoinCircle (D : PDCode n) (s : Fin n → Bool) :
    D.adjoinCircle.smoothingChoice s = D.smoothingChoice s := by
  funext i
  cases hs : s i <;> simp [hs]

/-- Adjoining a circle leaves the state traversal permutation unchanged. -/
@[simp] theorem statePerm_adjoinCircle (D : PDCode n) (s : Fin n → Bool) :
    D.adjoinCircle.statePerm s = D.statePerm s := by
  rw [statePerm_def, statePerm_def, smoothingTurn_adjoinCircle,
    smoothingChoice_adjoinCircle, adjoinCircle_edgePair]

/-- Every smoothing has exactly one additional circle after adjoining a circle. -/
@[simp] theorem stateLoopCount_adjoinCircle (D : PDCode n) (s : Fin n → Bool) :
    D.adjoinCircle.stateLoopCount s = D.stateLoopCount s + 1 := by
  simp [stateLoopCount_def]
  omega

/-- Adjoining a circle to a nonempty diagram multiplies its Kauffman bracket by the loop
value. The empty code is excluded because its bracket is normalized to one. -/
@[simp] theorem kauffmanBracket_adjoinCircle {R : Type*} [CommRing R] (D : PDCode n)
    (h : 0 < D.componentCount) (a : Rˣ) :
    D.adjoinCircle.kauffmanBracket a = jonesDelta a * D.kauffmanBracket a := by
  rw [kauffmanBracket_def, kauffmanBracket_def, Finset.mul_sum]
  refine Fintype.sum_congr _ _ ?_
  intro s
  have hstate := D.one_le_stateLoopCount_of_componentCount_pos h s
  rw [stateLoopCount_adjoinCircle]
  rw [Nat.add_sub_cancel, ← mul_pow_sub_one (Nat.ne_of_gt hstate) (jonesDelta a)]
  ring

/-- Mirroring commutes with adjoining an unoriented circle. -/
@[simp] theorem mirror_adjoinCircle (D : PDCode n) :
    D.adjoinCircle.mirror = D.mirror.adjoinCircle := by
  apply ext
  · simp
  · simp
  · simp
  · funext i
    simp [PDCode.mirror_overPair]

end PDCode

/-! ### Oriented codes -/

namespace OrientedPDCode

/-- Adjoin a crossing-free component with the specified orientation. -/
def adjoinCircle (D : OrientedPDCode n) (orientation : Bool) : OrientedPDCode n where
  toPDCode := D.toPDCode.adjoinCircle
  orientation := D.orientation
  orientation_edgePair := D.orientation_edgePair
  orientation_oppositeCrossingSlot := D.orientation_oppositeCrossingSlot
  crossinglessComponents := orientation ::ₘ D.crossinglessComponents
  crossinglessComponents_card := by simp

/-- Forgetting orientation leaves the added circle in the underlying code. -/
@[simp] theorem toPDCode_adjoinCircle (D : OrientedPDCode n) (orientation : Bool) :
    (OrientedPDCode.adjoinCircle D orientation).toPDCode = D.toPDCode.adjoinCircle := by
  rfl

/-- The directions at existing crossings remain unchanged. -/
@[simp] theorem orientation_adjoinCircle (D : OrientedPDCode n) (orientation : Bool) :
    (OrientedPDCode.adjoinCircle D orientation).orientation = D.orientation := by
  rfl

/-- The orientation of the new circle is added to the crossing-free orientation multiset. -/
@[simp] theorem crossinglessComponents_adjoinCircle (D : OrientedPDCode n) (orientation : Bool) :
    (OrientedPDCode.adjoinCircle D orientation).crossinglessComponents =
      orientation ::ₘ D.crossinglessComponents := by
  rfl

/-- Adjoining a circle leaves every existing crossing sign unchanged. -/
@[simp] theorem crossingSign_adjoinCircle (D : OrientedPDCode n) (orientation : Bool)
    (i : Fin n) :
    (OrientedPDCode.adjoinCircle D orientation).crossingSign i = D.crossingSign i := by
  simp [crossingSign_def]

/-- An isolated circle does not change the writhe. -/
@[simp] theorem writhe_adjoinCircle (D : OrientedPDCode n) (orientation : Bool) :
    (OrientedPDCode.adjoinCircle D orientation).writhe = D.writhe := by
  simp [writhe_def]

/-- Mirroring commutes with adjoining an oriented crossing-free circle. -/
@[simp] theorem mirror_adjoinCircle (D : OrientedPDCode n) (orientation : Bool) :
    (OrientedPDCode.adjoinCircle D orientation).mirror =
      OrientedPDCode.adjoinCircle D.mirror orientation := by
  apply ext <;> simp

/-- Adjoining a circle to a nonempty oriented diagram multiplies the normalized bracket by the
same loop value as the unoriented bracket, since the writhe is unchanged. -/
@[simp] theorem normalizedKauffmanBracket_adjoinCircle {R : Type*} [CommRing R]
    (D : OrientedPDCode n) (orientation : Bool) (h : 0 < D.toPDCode.componentCount)
    (a : Rˣ) :
    (OrientedPDCode.adjoinCircle D orientation).normalizedKauffmanBracket a =
      jonesDelta a * D.normalizedKauffmanBracket a := by
  simp only [OrientedPDCode.normalizedKauffmanBracket_def, writhe_adjoinCircle,
    toPDCode_adjoinCircle, PDCode.kauffmanBracket_adjoinCircle D.toPDCode h a]
  ring

end OrientedPDCode

/-! ### Framed oriented codes -/

namespace FramedOrientedPDCode

/-- Adjoin a crossing-free component with its orientation and Seifert-relative framing. -/
def adjoinCircle (D : FramedOrientedPDCode n) (orientation : Bool) (framing : ℤ) :
    FramedOrientedPDCode n where
  toOrientedPDCode := OrientedPDCode.adjoinCircle D.toOrientedPDCode orientation
  framing := D.framing
  framing_edgePair := D.framing_edgePair
  framing_oppositeCrossingSlot := D.framing_oppositeCrossingSlot
  crossinglessFramings := (orientation, framing) ::ₘ D.crossinglessFramings
  crossinglessFramings_map_fst := by simp [D.crossinglessFramings_map_fst]

/-- Forgetting framing retains the orientation of the added circle. -/
@[simp] theorem toOrientedPDCode_adjoinCircle (D : FramedOrientedPDCode n)
    (orientation : Bool) (framing : ℤ) :
    (FramedOrientedPDCode.adjoinCircle D orientation framing).toOrientedPDCode =
      OrientedPDCode.adjoinCircle D.toOrientedPDCode orientation := by
  rfl

/-- Existing framing coefficients are unchanged. -/
@[simp] theorem framing_adjoinCircle (D : FramedOrientedPDCode n)
    (orientation : Bool) (framing : ℤ) :
    (FramedOrientedPDCode.adjoinCircle D orientation framing).framing = D.framing := by
  rfl

/-- The new circle's orientation and framing are recorded together. -/
@[simp] theorem crossinglessFramings_adjoinCircle (D : FramedOrientedPDCode n)
    (orientation : Bool) (framing : ℤ) :
    (FramedOrientedPDCode.adjoinCircle D orientation framing).crossinglessFramings =
      (orientation, framing) ::ₘ D.crossinglessFramings := by
  rfl

/-- Mirroring commutes with adjoining a framed oriented crossing-free circle and negates its
framing. -/
@[simp] theorem mirror_adjoinCircle (D : FramedOrientedPDCode n) (orientation : Bool)
    (framing : ℤ) :
    (FramedOrientedPDCode.adjoinCircle D orientation framing).mirror =
      FramedOrientedPDCode.adjoinCircle D.mirror orientation (-framing) := by
  apply ext <;> simp

end FramedOrientedPDCode

end TauCeti
