/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Circle.Component
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.One.Component
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Path
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Three.Component
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Two.Component

/-!
# Component transport along Reidemeister moves and words

Every generating move `TauCeti.OrientedPDCode.ReidemeisterMove x y` carries a bijection between
the labelled link components of its two codes,
`TauCeti.OrientedPDCode.ReidemeisterMove.componentEquiv`. It is the transport of the generator
used, with the parameters the move retains: relabelling and reading a crossing from another slot
carry each outgoing half-edge to its image, the first and second moves include the old
half-edges and send a consumed crossing-free circle to the component through the new crossings,
and the third move follows the native rewire of its triangle.

A word of moves, `TauCeti.OrientedPDCode.ReidemeisterPath x y`, composes these bijections, using
the inverse bijection for a move applied backwards
(`TauCeti.OrientedPDCode.ReidemeisterPath.componentEquiv`). The empty word gives the identity,
concatenation of words gives composition, and reversing a word gives the inverse bijection.
These transports depend on the word, not only on its endpoints, so they are the data that lets
a marked component be followed along a chosen sequence of moves.

## Main definitions

* `TauCeti.OrientedPDCode.rotateCrossingComponentEquiv`: components under reading a crossing
  from its next slot.
* `TauCeti.OrientedPDCode.ReidemeisterMove.componentEquiv`: components along a single move.
* `TauCeti.OrientedPDCode.ReidemeisterPath.componentEquiv`: components along a word of moves.

## Main results

* `TauCeti.OrientedPDCode.ReidemeisterPath.componentEquiv_comp`: transport along concatenated
  words is the composite transport.
* `TauCeti.OrientedPDCode.ReidemeisterPath.componentEquiv_reverse`: transport along the reversed
  word is the inverse transport.
* `TauCeti.OrientedPDCode.ReidemeisterMove.componentEquiv_toPath`: the word of a single move
  transports components as the move does.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1 (Reidemeister moves).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3
  (oriented component traversal).
-/

public section

noncomputable section

namespace TauCeti.OrientedPDCode

open Equiv

variable {n : ℕ}

section RotateCrossing

variable (D : OrientedPDCode n) (i : Fin n)

/-- Reading a crossing from its next slot keeps every half-edge and its orientation, so it keeps
each component, including each crossing-free label. -/
def rotateCrossingComponentEquiv : D.Component ≃ (D.rotateCrossing i).Component :=
  D.componentEquiv _ ((Equiv.refl _).subtypeEquiv fun _ ↦ by simp)
    (by ext h; simp [Equiv.subtypeEquiv]) (finCongr (by simp))

/-- Reading a crossing from its next slot keeps the component of each outgoing half-edge. -/
@[simp] theorem rotateCrossingComponentEquiv_componentOfOutgoing
    (h : {h : Fin (4 * n) // D.orientation h = true}) :
    D.rotateCrossingComponentEquiv i (D.componentOfOutgoing h) =
      (D.rotateCrossing i).componentOfOutgoing ⟨h.val, by simpa using h.property⟩ := by
  simp [rotateCrossingComponentEquiv, Equiv.subtypeEquiv]

/-- Reading a crossing from its next slot fixes each crossing-free component label. -/
@[simp] theorem rotateCrossingComponentEquiv_inr (j : Fin D.crossinglessComponentCount) :
    D.rotateCrossingComponentEquiv i (.inr j) = .inr (finCongr (by simp) j) :=
  D.componentEquiv_inr _ _ _ _ j

end RotateCrossing

variable {x y z : Σ n, OrientedPDCode n}

namespace ReidemeisterMove

/-- **Component transport along a Reidemeister move**: the bijection of labelled link components
given by the generator of the move, with its retained parameters. -/
def componentEquiv : ReidemeisterMove x y → (x.2.Component ≃ y.2.Component)
  | .relabel D half cross => D.relabelComponentEquiv half cross
  | .rotateCrossing D i => D.rotateCrossingComponentEquiv i
  | .reidemeisterOne D h b => D.reidemeisterOneComponentEquiv h b
  | .adjoinKink D o b => D.adjoinKinkComponentEquiv o b
  | .insertClasp D p q b hqp hqe _ => D.insertClaspComponentEquiv p q b hqp hqe
  | .insertCircleClasp D p o b => D.insertCircleClaspComponentEquiv p o b
  | .adjoinTwoCircleClasp D o₁ o₂ b => D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
  | .reidemeisterThree D c _ => D.reidemeisterThreeComponentEquiv c

/-- A relabelling transports components as `relabelComponentEquiv`. -/
@[simp] theorem componentEquiv_relabel {m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (relabel D half cross).componentEquiv = D.relabelComponentEquiv half cross := (rfl)

/-- Reading a crossing from its next slot transports components as
`rotateCrossingComponentEquiv`. -/
@[simp] theorem componentEquiv_rotateCrossing (D : OrientedPDCode n) (i : Fin n) :
    (rotateCrossing D i).componentEquiv = D.rotateCrossingComponentEquiv i := (rfl)

/-- A kink on an arc transports components as `reidemeisterOneComponentEquiv`. -/
@[simp] theorem componentEquiv_reidemeisterOne (D : OrientedPDCode n) (h : Fin (4 * n))
    (b : Bool) :
    (reidemeisterOne D h b).componentEquiv = D.reidemeisterOneComponentEquiv h b := (rfl)

/-- A kink on a crossing-free circle transports components as `adjoinKinkComponentEquiv`. -/
@[simp] theorem componentEquiv_adjoinKink (D : OrientedPDCode n) (o b : Bool) :
    (adjoinKink D o b).componentEquiv = D.adjoinKinkComponentEquiv o b := (rfl)

/-- A clasp between two arcs transports components as `insertClaspComponentEquiv`. -/
@[simp] theorem componentEquiv_insertClasp (D : OrientedPDCode n) (p q : Fin (4 * n))
    (b : Bool) (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p)
    (hpq : D.face (D.edgePair.val p) = D.face q ∨
      q ∉ MulAction.orbit D.toPermutationTriple.monodromyGroup p) :
    (insertClasp D p q b hqp hqe hpq).componentEquiv =
      D.insertClaspComponentEquiv p q b hqp hqe := (rfl)

/-- A clasp between an arc and a crossing-free circle transports components as
`insertCircleClaspComponentEquiv`. -/
@[simp] theorem componentEquiv_insertCircleClasp (D : OrientedPDCode n) (p : Fin (4 * n))
    (o b : Bool) :
    (insertCircleClasp D p o b).componentEquiv = D.insertCircleClaspComponentEquiv p o b := (rfl)

/-- A clasp between two crossing-free circles transports components as
`adjoinTwoCircleClaspComponentEquiv`. -/
@[simp] theorem componentEquiv_adjoinTwoCircleClasp (D : OrientedPDCode n) (o₁ o₂ b : Bool) :
    (adjoinTwoCircleClasp D o₁ o₂ b).componentEquiv =
      D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b := (rfl)

/-- A third move transports components as `reidemeisterThreeComponentEquiv`. -/
@[simp] theorem componentEquiv_reidemeisterThree (D : OrientedPDCode n) (c : Fin 3 ↪ Fin n)
    (h : D.HasReidemeisterThreeTriangle c) :
    (reidemeisterThree D c h).componentEquiv = D.reidemeisterThreeComponentEquiv c := (rfl)

end ReidemeisterMove

namespace ReidemeisterPath

/-- **Component transport along a word of Reidemeister moves**: the composite of the component
bijections of its moves, inverted for each move applied backwards. -/
def componentEquiv : ∀ {y : Σ n, OrientedPDCode n}, ReidemeisterPath x y →
    (x.2.Component ≃ y.2.Component)
  | _, .nil => Equiv.refl _
  | _, .cons p (.inl e) => (componentEquiv p).trans (ReidemeisterMove.componentEquiv e)
  | _, .cons p (.inr e) => (componentEquiv p).trans (ReidemeisterMove.componentEquiv e).symm

/-- The empty word transports each component to itself. -/
@[simp] theorem componentEquiv_nil :
    componentEquiv (Quiver.Path.nil : ReidemeisterPath x x) = Equiv.refl _ := (rfl)

/-- Appending a move applied forwards composes with its component transport. -/
@[simp] theorem componentEquiv_cons_toPos (p : ReidemeisterPath x y)
    (e : ReidemeisterMove y z) :
    componentEquiv (p.cons (Quiver.Hom.toPos (V := ReidemeisterQuiver) e)) =
      (componentEquiv p).trans e.componentEquiv := (rfl)

/-- Appending a move applied backwards composes with its inverse component transport. -/
@[simp] theorem componentEquiv_cons_toNeg (p : ReidemeisterPath x y)
    (e : ReidemeisterMove z y) :
    componentEquiv (p.cons (Quiver.Hom.toNeg (V := ReidemeisterQuiver) e)) =
      (componentEquiv p).trans e.componentEquiv.symm := (rfl)

/-- **Transport along concatenated words** is the composite of the two transports. -/
@[simp] theorem componentEquiv_comp (p : ReidemeisterPath x y) (q : ReidemeisterPath y z) :
    componentEquiv (p.comp q) = (componentEquiv p).trans (componentEquiv q) := by
  induction q with
  | nil => rfl
  | cons q e ih =>
    rcases e with e | e
    · exact (congrArg (·.trans (ReidemeisterMove.componentEquiv e)) ih).trans
        (Equiv.trans_assoc _ _ _)
    · exact (congrArg (·.trans (ReidemeisterMove.componentEquiv e).symm) ih).trans
        (Equiv.trans_assoc _ _ _)

end ReidemeisterPath

/-- The word of a single move transports components as the move does. -/
@[simp] theorem ReidemeisterMove.componentEquiv_toPath (e : ReidemeisterMove x y) :
    ReidemeisterPath.componentEquiv e.toPath = e.componentEquiv := by
  rw [ReidemeisterMove.toPath_def]
  exact Equiv.refl_trans _

namespace ReidemeisterPath

/-- **Transport along the reversed word** is the inverse transport. -/
@[simp] theorem componentEquiv_reverse (p : ReidemeisterPath x y) :
    componentEquiv p.reverse = (componentEquiv p).symm := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Quiver.Path.reverse, componentEquiv_comp, ih]
    -- The reversed arrow is a one-move word, whose transport is that of the arrow.
    rcases e with e | e <;> exact congrArg (·.trans (componentEquiv p).symm) (Equiv.refl_trans _)

end ReidemeisterPath

end TauCeti.OrientedPDCode
