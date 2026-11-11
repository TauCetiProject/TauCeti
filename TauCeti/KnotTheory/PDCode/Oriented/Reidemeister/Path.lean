/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Reachable
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence

/-!
# Reidemeister moves as data, and words of moves

`TauCeti.OrientedPDCode.IsReidemeisterMove` records only that two oriented PD-codes are related by
a generating move. Constructions that act along a move, such as transporting link components or
the maps between invariants attached to the two codes, need the move itself: which generator
was used, and its parameters. `TauCeti.OrientedPDCode.ReidemeisterMove x y` is the type of these
moves. It has one constructor for each constructor of `IsReidemeisterMove`, with the same
arguments, so a move retains the relabelling, the crossing read from another slot, the half-edges
and over-strand choice of a kink or clasp, the orientations of crossing-free circles, and the
triangle of a third move, together with the hypotheses under which the generator applies.

The moves are the arrows of a quiver on the oriented PD-codes with any numbers of crossings,
`TauCeti.OrientedPDCode.ReidemeisterQuiver`. A finite word of moves, each applied forwards or
backwards, is a path in its symmetrization (`Quiver.Symmetrify`), and
`TauCeti.OrientedPDCode.ReidemeisterPath x y` is the type of these words. Concatenation, reversal
and length of words, and their laws, are those of `Quiver.Path`. Forgetting the data of a word
gives a Reidemeister equivalence, and every Reidemeister equivalence arises from a word.

## Main definitions

* `TauCeti.OrientedPDCode.ReidemeisterMove`: a generating move together with its parameters.
* `TauCeti.OrientedPDCode.ReidemeisterQuiver`: the oriented PD-codes with these moves as arrows.
* `TauCeti.OrientedPDCode.ReidemeisterPath`: a finite word of moves, each forwards or backwards.

## Main results

* `TauCeti.OrientedPDCode.isReidemeisterMove_iff_nonempty_reidemeisterMove`: two codes are
  related by a generating move exactly when there is a move between them.
* `TauCeti.OrientedPDCode.ReidemeisterPath.reidemeisterEquiv`: a word of moves relates
  Reidemeister equivalent codes.
* `TauCeti.OrientedPDCode.reidemeisterEquiv_iff_nonempty_reidemeisterPath`: two codes are
  Reidemeister equivalent exactly when a word of moves joins them.
-/

public section

namespace TauCeti

namespace OrientedPDCode

/-- A **Reidemeister move** between oriented PD-codes with any numbers of crossings, as data: the
generator of `TauCeti.OrientedPDCode.IsReidemeisterMove` used, together with its parameters and
the hypotheses under which it applies. The constructors are those of `IsReidemeisterMove`, with
the same arguments. A move that adds crossings goes in the direction that adds them. -/
inductive ReidemeisterMove : (Σ n, OrientedPDCode n) → (Σ n, OrientedPDCode n) → Type
  /-- Relabelling the half-edges and the crossings. -/
  | relabel {n m : ℕ} (D : OrientedPDCode n) (half : Fin (4 * n) ≃ Fin (4 * m))
      (cross : Fin n ≃ Fin m) : ReidemeisterMove ⟨n, D⟩ ⟨m, D.relabel half cross⟩
  /-- Reading a crossing from its next slot. -/
  | rotateCrossing {n : ℕ} (D : OrientedPDCode n) (i : Fin n) :
      ReidemeisterMove ⟨n, D⟩ ⟨n, D.rotateCrossing i⟩
  /-- The first move: a kink added to the arc ending at a half-edge. -/
  | reidemeisterOne {n : ℕ} (D : OrientedPDCode n) (h : Fin (4 * n)) (b : Bool) :
      ReidemeisterMove ⟨n, D⟩ ⟨n + 1, D.reidemeisterOne h b⟩
  /-- The first move on a crossing-free circle. -/
  | adjoinKink {n : ℕ} (D : OrientedPDCode n) (o b : Bool) :
      ReidemeisterMove ⟨n, D.adjoinCircle o⟩ ⟨n + 1, D.adjoinKink o b⟩
  /-- The second move between two distinct arcs: inside a face both arcs border on the sides the
  clasp uses, or between two connected components of the underlying graph. -/
  | insertClasp {n : ℕ} (D : OrientedPDCode n) (p q : Fin (4 * n)) (b : Bool) (hqp : q ≠ p)
      (hqe : q ≠ D.edgePair.val p)
      (hpq : D.face (D.edgePair.val p) = D.face q ∨
        q ∉ MulAction.orbit D.toPermutationTriple.monodromyGroup p) :
      ReidemeisterMove ⟨n, D⟩ ⟨n + 2, D.insertClasp p q b hqp hqe⟩
  /-- The second move between an arc and a crossing-free circle. -/
  | insertCircleClasp {n : ℕ} (D : OrientedPDCode n) (p : Fin (4 * n)) (o b : Bool) :
      ReidemeisterMove ⟨n, D.adjoinCircle o⟩ ⟨n + 2, D.insertCircleClasp p o b⟩
  /-- The second move between two crossing-free circles. -/
  | adjoinTwoCircleClasp {n : ℕ} (D : OrientedPDCode n) (o₁ o₂ b : Bool) :
      ReidemeisterMove ⟨n, (D.adjoinCircle o₁).adjoinCircle o₂⟩
        ⟨n + 2, D.adjoinTwoCircleClasp o₁ o₂ b⟩
  /-- The third move, across a triangle of three crossings with an acyclic height order. -/
  | reidemeisterThree {n : ℕ} (D : OrientedPDCode n) (c : Fin 3 ↪ Fin n)
      (h : D.HasReidemeisterThreeTriangle c) :
      ReidemeisterMove ⟨n, D⟩ ⟨n, D.reidemeisterThree c⟩

variable {x y : Σ n, OrientedPDCode n}

/-- Forgetting the data of a move: the two codes are related by a generating move. -/
theorem ReidemeisterMove.isReidemeisterMove (e : ReidemeisterMove x y) :
    IsReidemeisterMove x y := by
  cases e with
  | relabel D half cross => exact .relabel D half cross
  | rotateCrossing D i => exact .rotateCrossing D i
  | reidemeisterOne D h b => exact .reidemeisterOne D h b
  | adjoinKink D o b => exact .adjoinKink D o b
  | insertClasp D p q b hqp hqe hpq => exact .insertClasp D p q b hqp hqe hpq
  | insertCircleClasp D p o b => exact .insertCircleClasp D p o b
  | adjoinTwoCircleClasp D o₁ o₂ b => exact .adjoinTwoCircleClasp D o₁ o₂ b
  | reidemeisterThree D c h => exact .reidemeisterThree D c h

/-- Two codes related by a generating move are related by a move. -/
theorem IsReidemeisterMove.nonempty_reidemeisterMove (h : IsReidemeisterMove x y) :
    Nonempty (ReidemeisterMove x y) := by
  cases h with
  | relabel D half cross => exact ⟨.relabel D half cross⟩
  | rotateCrossing D i => exact ⟨.rotateCrossing D i⟩
  | reidemeisterOne D h b => exact ⟨.reidemeisterOne D h b⟩
  | adjoinKink D o b => exact ⟨.adjoinKink D o b⟩
  | insertClasp D p q b hqp hqe hpq => exact ⟨.insertClasp D p q b hqp hqe hpq⟩
  | insertCircleClasp D p o b => exact ⟨.insertCircleClasp D p o b⟩
  | adjoinTwoCircleClasp D o₁ o₂ b => exact ⟨.adjoinTwoCircleClasp D o₁ o₂ b⟩
  | reidemeisterThree D c h => exact ⟨.reidemeisterThree D c h⟩

/-- Two codes are related by a generating move exactly when there is a move between them. -/
theorem isReidemeisterMove_iff_nonempty_reidemeisterMove :
    IsReidemeisterMove x y ↔ Nonempty (ReidemeisterMove x y) :=
  ⟨IsReidemeisterMove.nonempty_reidemeisterMove, fun ⟨e⟩ ↦ e.isReidemeisterMove⟩

/-- The oriented PD-codes with any numbers of crossings, as the vertices of the quiver whose
arrows are the Reidemeister moves `TauCeti.OrientedPDCode.ReidemeisterMove`. This type synonym of
`Σ n, OrientedPDCode n` carries the quiver structure. -/
@[expose] def ReidemeisterQuiver : Type := Σ n, OrientedPDCode n

/-- The arrows from `x` to `y` are the Reidemeister moves from `x` to `y`. -/
instance : Quiver ReidemeisterQuiver := ⟨ReidemeisterMove⟩

/-- A **word of Reidemeister moves** from `x` to `y`: a finite sequence of moves, each applied
forwards or backwards, that starts at `x` and ends at `y`. It is a path in the symmetrization of
`TauCeti.OrientedPDCode.ReidemeisterQuiver`, so words are concatenated with `Quiver.Path.comp`,
reversed with `Quiver.Path.reverse` and measured with `Quiver.Path.length`. -/
abbrev ReidemeisterPath (x y : Σ n, OrientedPDCode n) : Type :=
  Quiver.Path (V := Quiver.Symmetrify ReidemeisterQuiver) x y

/-- The word consisting of a single move, applied forwards. Its reverse, `e.toPath.reverse`, is
the word applying the move backwards. -/
def ReidemeisterMove.toPath (e : ReidemeisterMove x y) : ReidemeisterPath x y :=
  (Quiver.Hom.toPos (V := ReidemeisterQuiver) e).toPath

/-- The word of a single move is the path consisting of that move as a forward arrow of the
symmetrized quiver. -/
theorem ReidemeisterMove.toPath_def (e : ReidemeisterMove x y) :
    e.toPath = (Quiver.Hom.toPos (V := ReidemeisterQuiver) e).toPath :=
  (rfl)

/-- A single move is a word of length one. -/
@[simp]
theorem ReidemeisterMove.length_toPath (e : ReidemeisterMove x y) : e.toPath.length = 1 :=
  (rfl)

/-- **Words of moves witness Reidemeister equivalence**: two codes are Reidemeister equivalent
exactly when some word of moves joins them. -/
theorem reidemeisterEquiv_iff_nonempty_reidemeisterPath {n m : ℕ} {D : OrientedPDCode n}
    {D' : OrientedPDCode m} :
    ReidemeisterEquiv D D' ↔ Nonempty (ReidemeisterPath ⟨n, D⟩ ⟨m, D'⟩) := by
  have h : (fun x y : ReidemeisterQuiver ↦ Nonempty (x ⟶ y)) = IsReidemeisterMove := by
    ext x y
    exact isReidemeisterMove_iff_nonempty_reidemeisterMove.symm
  rw [reidemeisterEquiv_def, ← h]
  exact (Quiver.nonempty_path_symmetrify_iff_eqvGen (V := ReidemeisterQuiver)).symm

/-- Forgetting the data of a word of moves: its endpoints are Reidemeister equivalent. -/
theorem ReidemeisterPath.reidemeisterEquiv (p : ReidemeisterPath x y) :
    ReidemeisterEquiv x.2 y.2 :=
  reidemeisterEquiv_iff_nonempty_reidemeisterPath.2 ⟨p⟩

end OrientedPDCode

end TauCeti
