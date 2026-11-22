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
# Component bijections along Reidemeister moves and paths

Each generating move `e : ReidemeisterMove x y` between oriented PD-codes carries an explicit
bijection `e.componentEquiv : x.2.Component ≃ y.2.Component` between the labelled link components
of its source and target diagrams. Unlike the proposition-valued relation `IsReidemeisterMove`, the
move datum retains the relabelling permutations, rotated crossing index, cut half-edges, over-strand
choice, adjoined circle orientations, or Reidemeister-III triangle needed to identify individual
components unambiguously — including across moves that convert crossing-free circle labels into
crossing-bearing traversal classes (`adjoinKink`, `insertCircleClasp`, `adjoinTwoCircleClasp`).

Extending `ReidemeisterMove.componentEquiv` to forward and backward steps in the symmetrized quiver
`Quiver.Symmetrify ReidemeisterQuiver` yields `ReidemeisterPath.componentEquiv`, which transports
labelled components along any finite word `p : ReidemeisterPath x y`. Empty words act by the
identity equivalence, path concatenation acts by `Equiv.trans`, and path reversal acts by
`Equiv.symm`.

## Main definitions

* `TauCeti.OrientedPDCode.ReidemeisterMove.componentEquiv`: component bijection for a single
  generating Reidemeister move.
* `TauCeti.OrientedPDCode.ReidemeisterPath.componentEquiv`: component bijection along a finite word
  of forward and backward Reidemeister moves.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1 (oriented diagrams and
  Reidemeister moves).
* M. Mastin, *Links and Planar Diagram Codes*, Definitions 2–3 (oriented component traversal).
-/

public section

noncomputable section

namespace TauCeti.OrientedPDCode

/-- The bijection of labelled link components induced by a generating Reidemeister move.
Moves involving crossing-free circles send the consumed `Fin.last` circle labels to the
corresponding crossing-bearing strands of the new kink or clasp. -/
def ReidemeisterMove.componentEquiv :
    ∀ {x y : Σ n, OrientedPDCode n}, ReidemeisterMove x y → (x.2.Component ≃ y.2.Component)
  | _, _, .relabel D half cross => D.relabelComponentEquiv half cross
  | _, _, .rotateCrossing D i => D.rotateCrossingComponentEquiv i
  | _, _, .reidemeisterOne D h b => D.reidemeisterOneComponentEquiv h b
  | _, _, .adjoinKink D o b => D.adjoinKinkComponentEquiv o b
  | _, _, .insertClasp D p q b hqp hqe _ => D.insertClaspComponentEquiv p q b hqp hqe
  | _, _, .insertCircleClasp D p o b => D.insertCircleClaspComponentEquiv p o b
  | _, _, .adjoinTwoCircleClasp D o₁ o₂ b => D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b
  | _, _, .reidemeisterThree D c _ => D.reidemeisterThreeComponentEquiv c

/-- Component transport for a relabelling move is `relabelComponentEquiv`. -/
@[simp]
theorem ReidemeisterMove.componentEquiv_relabel {n m : ℕ} (D : OrientedPDCode n)
    (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m) :
    (ReidemeisterMove.relabel D half cross).componentEquiv =
      D.relabelComponentEquiv half cross :=
  (rfl)

/-- Component transport for a crossing-slot rotation is `rotateCrossingComponentEquiv`. -/
@[simp]
theorem ReidemeisterMove.componentEquiv_rotateCrossing {n : ℕ} (D : OrientedPDCode n)
    (i : Fin n) :
    (ReidemeisterMove.rotateCrossing D i).componentEquiv = D.rotateCrossingComponentEquiv i :=
  (rfl)

/-- Component transport for an arc first Reidemeister move is `reidemeisterOneComponentEquiv`. -/
@[simp]
theorem ReidemeisterMove.componentEquiv_reidemeisterOne {n : ℕ} (D : OrientedPDCode n)
    (h : Fin (4 * n)) (b : Bool) :
    (ReidemeisterMove.reidemeisterOne D h b).componentEquiv =
      D.reidemeisterOneComponentEquiv h b :=
  (rfl)

/-- Component transport for an isolated first Reidemeister move is `adjoinKinkComponentEquiv`. -/
@[simp]
theorem ReidemeisterMove.componentEquiv_adjoinKink {n : ℕ} (D : OrientedPDCode n)
    (o b : Bool) :
    (ReidemeisterMove.adjoinKink D o b).componentEquiv = D.adjoinKinkComponentEquiv o b :=
  (rfl)

/-- Component transport for a two-arc clasp insertion is `insertClaspComponentEquiv`, independent of
the face or graph-component witness. -/
@[simp]
theorem ReidemeisterMove.componentEquiv_insertClasp {n : ℕ} (D : OrientedPDCode n)
    (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p)
    (hpq : D.face (D.edgePair.val p) = D.face q ∨
      q ∉ MulAction.orbit D.toPermutationTriple.monodromyGroup p) :
    (ReidemeisterMove.insertClasp D p q b hqp hqe hpq).componentEquiv =
      D.insertClaspComponentEquiv p q b hqp hqe :=
  (rfl)

/-- Component transport for an arc-circle clasp move is `insertCircleClaspComponentEquiv`. -/
@[simp]
theorem ReidemeisterMove.componentEquiv_insertCircleClasp {n : ℕ} (D : OrientedPDCode n)
    (p : Fin (4 * n)) (o b : Bool) :
    (ReidemeisterMove.insertCircleClasp D p o b).componentEquiv =
      D.insertCircleClaspComponentEquiv p o b :=
  (rfl)

/-- Component transport for a two-circle clasp move is `adjoinTwoCircleClaspComponentEquiv`. -/
@[simp]
theorem ReidemeisterMove.componentEquiv_adjoinTwoCircleClasp {n : ℕ} (D : OrientedPDCode n)
    (o₁ o₂ b : Bool) :
    (ReidemeisterMove.adjoinTwoCircleClasp D o₁ o₂ b).componentEquiv =
      D.adjoinTwoCircleClaspComponentEquiv o₁ o₂ b :=
  (rfl)

/-- Component transport for a third Reidemeister move is `reidemeisterThreeComponentEquiv`,
independent of the `HasReidemeisterThreeTriangle` witness. -/
@[simp]
theorem ReidemeisterMove.componentEquiv_reidemeisterThree {n : ℕ} (D : OrientedPDCode n)
    (c : Fin 3 ↪ Fin n) (h : D.HasReidemeisterThreeTriangle c) :
    (ReidemeisterMove.reidemeisterThree D c h).componentEquiv =
      D.reidemeisterThreeComponentEquiv c :=
  (rfl)

/-- Transport labelled link components along a finite word of forward and backward Reidemeister
moves. Forward steps act by `ReidemeisterMove.componentEquiv` and backward steps act by its
inverse. -/
def ReidemeisterPath.componentEquiv {x : Σ n, OrientedPDCode n} :
    ∀ {y : Σ n, OrientedPDCode n}, ReidemeisterPath x y → (x.2.Component ≃ y.2.Component)
  | _, .nil => Equiv.refl x.2.Component
  | _, .cons p (.inl e) => (ReidemeisterPath.componentEquiv p).trans e.componentEquiv
  | _, .cons p (.inr e) => (ReidemeisterPath.componentEquiv p).trans e.componentEquiv.symm

/-- The empty word of moves induces the identity equivalence on components. -/
@[simp]
theorem ReidemeisterPath.componentEquiv_nil (x : Σ n, OrientedPDCode n) :
    ReidemeisterPath.componentEquiv (.nil : ReidemeisterPath x x) = Equiv.refl x.2.Component :=
  (rfl)

/-- Appending a forward move composes component transport with `e.componentEquiv`. -/
@[simp]
theorem ReidemeisterPath.componentEquiv_cons_toPos {x y z : Σ n, OrientedPDCode n}
    (p : ReidemeisterPath x y) (e : ReidemeisterMove y z) :
    ReidemeisterPath.componentEquiv (p.cons (Quiver.Hom.toPos (V := ReidemeisterQuiver) e)) =
      (ReidemeisterPath.componentEquiv p).trans e.componentEquiv :=
  (rfl)

/-- Appending a backward move composes component transport with `e.componentEquiv.symm`. -/
@[simp]
theorem ReidemeisterPath.componentEquiv_cons_toNeg {x y z : Σ n, OrientedPDCode n}
    (p : ReidemeisterPath x y) (e : ReidemeisterMove z y) :
    ReidemeisterPath.componentEquiv (p.cons (Quiver.Hom.toNeg (V := ReidemeisterQuiver) e)) =
      (ReidemeisterPath.componentEquiv p).trans e.componentEquiv.symm :=
  (rfl)

/-- A single forward arrow as a length-one path acts by `e.componentEquiv`. -/
@[simp]
theorem ReidemeisterPath.componentEquiv_toPath_toPos {x y : Σ n, OrientedPDCode n}
    (e : ReidemeisterMove x y) :
    ReidemeisterPath.componentEquiv (Quiver.Hom.toPos (V := ReidemeisterQuiver) e).toPath =
      e.componentEquiv := by
  simp [Quiver.Hom.toPath]

/-- A single backward arrow as a length-one path acts by `e.componentEquiv.symm`. -/
@[simp]
theorem ReidemeisterPath.componentEquiv_toPath_toNeg {x y : Σ n, OrientedPDCode n}
    (e : ReidemeisterMove y x) :
    ReidemeisterPath.componentEquiv (Quiver.Hom.toNeg (V := ReidemeisterQuiver) e).toPath =
      e.componentEquiv.symm := by
  simp [Quiver.Hom.toPath]

/-- Transporting along the single-move word `e.toPath` recovers `e.componentEquiv`. -/
@[simp]
theorem ReidemeisterMove.componentEquiv_toPath {x y : Σ n, OrientedPDCode n}
    (e : ReidemeisterMove x y) :
    e.toPath.componentEquiv = e.componentEquiv := by
  rw [ReidemeisterMove.toPath_def]
  exact ReidemeisterPath.componentEquiv_toPath_toPos e

/-- Concatenating two words of moves composes their component bijections in diagram order. -/
@[simp]
theorem ReidemeisterPath.componentEquiv_comp {x y z : Σ n, OrientedPDCode n}
    (p : ReidemeisterPath x y) (q : ReidemeisterPath y z) :
    ReidemeisterPath.componentEquiv (p.comp q) =
      (ReidemeisterPath.componentEquiv p).trans (ReidemeisterPath.componentEquiv q) := by
  induction q with
  | nil => exact (Equiv.trans_refl _).symm
  | cons q a ih =>
    rcases a with e | e <;>
      · dsimp only [Quiver.Path.comp, ReidemeisterPath.componentEquiv]
        rw [ih, Equiv.trans_assoc]

/-- Reversing a word of moves inverts its component bijection. -/
@[simp]
theorem ReidemeisterPath.componentEquiv_reverse {x y : Σ n, OrientedPDCode n}
    (p : ReidemeisterPath x y) :
    ReidemeisterPath.componentEquiv p.reverse = (ReidemeisterPath.componentEquiv p).symm := by
  induction p with
  | nil => simp [ReidemeisterPath.componentEquiv]
  | cons p a ih =>
    have hrev := Quiver.symmetrify_reverse (V := ReidemeisterQuiver) a
    rcases a with e | e <;>
      simp [ReidemeisterPath.componentEquiv, hrev, ih, Equiv.symm_trans]

end TauCeti.OrientedPDCode
