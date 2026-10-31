/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Move.Basic
public import TauCeti.KnotTheory.Grid.Stabilization.Transpose

/-!
# Transposition on grid links

Diagonal reflection exchanges row and column moves and preserves stabilizations.
It therefore descends to an involution on grid links, not merely on their presenting
diagrams. No identification of a link with its transpose is imposed.

The grid move conventions follow Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

/-- Diagonal reflection sends an elementary grid move to an elementary grid move. -/
theorem IsMove.transpose {A B : Σ n, GridDiagram n} (h : IsMove A B) :
    IsMove ⟨A.1, A.2.transpose⟩ ⟨B.1, B.2.transpose⟩ := by
  cases h with
  | cyclicRows h =>
    apply IsMove.cyclicColumns
    simpa only [relabelRows_transpose] using h.imp
      (congrArg GridDiagram.transpose) (congrArg GridDiagram.transpose)
  | cyclicColumns h =>
    apply IsMove.cyclicRows
    simpa only [relabelColumns_transpose] using h.imp
      (congrArg GridDiagram.transpose) (congrArg GridDiagram.transpose)
  | commutation h => exact .commutation ((isCommutation_transpose _ _).mpr h)
  | stabilization h => exact .stabilization ((isStabilization_transpose _ _).mpr h)
  | destabilization h => exact .destabilization ((isDestabilization_transpose _ _).mpr h)

/-- Diagonal reflection transports a sequence of grid moves. -/
theorem MovesTo.transpose {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
    (h : MovesTo G G') : MovesTo G.transpose G'.transpose := by
  exact MovesTo.induction_on
    (motive := fun A B ↦ MovesTo A.2.transpose B.2.transpose) h
    (fun h ↦ h.transpose.movesTo) (fun _ ↦ .refl _)
    (fun _ ih ↦ ih.symm) (fun _ _ ih ih' ↦ ih.trans ih')

/-- Two transposed diagrams are move-equivalent exactly when the original diagrams are. -/
@[simp]
theorem movesTo_transpose_iff {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m} :
    MovesTo G.transpose G'.transpose ↔ MovesTo G G' :=
  ⟨fun h ↦ by simpa only [transpose_transpose] using h.transpose, MovesTo.transpose⟩

end GridDiagram

namespace GridLink

/-- Diagonal reflection of a grid link, defined independently of a presenting diagram. -/
def transpose : GridLink → GridLink :=
  GridLink.lift (fun _ G ↦ G.transpose.toGridLink)
    (fun G ↦ by
      rw [GridDiagram.relabelRows_transpose]
      exact G.transpose.cyclicColumns_toGridLink_eq)
    (fun G ↦ by
      rw [GridDiagram.relabelColumns_transpose]
      exact G.transpose.cyclicRows_toGridLink_eq)
    (fun h ↦ ((GridDiagram.isCommutation_transpose _ _).mpr h).toGridLink_eq)
    (fun h ↦ ((GridDiagram.isStabilization_transpose _ _).mpr h).toGridLink_eq)

/-- Transposition of a link presented by a diagram is presented by the transposed diagram. -/
@[simp]
theorem transpose_toGridLink {n : ℕ} (G : GridDiagram n) :
    G.toGridLink.transpose = G.transpose.toGridLink := by
  unfold transpose
  apply GridLink.lift_toGridLink
  · intro n G
    rw [GridDiagram.relabelRows_transpose]
    exact G.transpose.cyclicColumns_toGridLink_eq
  · intro n G
    rw [GridDiagram.relabelColumns_transpose]
    exact G.transpose.cyclicRows_toGridLink_eq
  · exact fun h ↦ ((GridDiagram.isCommutation_transpose _ _).mpr h).toGridLink_eq
  · exact fun h ↦ ((GridDiagram.isStabilization_transpose _ _).mpr h).toGridLink_eq

/-- Diagonal reflection is involutive on grid links. -/
@[simp]
theorem transpose_transpose (L : GridLink) : L.transpose.transpose = L := by
  induction L using GridLink.ind with
  | h G => simp

/-- Transposition as an equivalence of grid links. -/
def transposeEquiv : GridLink ≃ GridLink :=
  Function.Involutive.toPerm transpose transpose_transpose

/-- The transposition equivalence acts by diagonal reflection. -/
@[simp]
theorem transposeEquiv_apply (L : GridLink) : transposeEquiv L = L.transpose :=
  (rfl)

/-- The inverse transposition equivalence also acts by diagonal reflection. -/
@[simp]
theorem transposeEquiv_symm_apply (L : GridLink) : transposeEquiv.symm L = L.transpose :=
  (rfl)

/-- Equality of transposes is equality of grid links. -/
@[simp]
theorem transpose_inj {L L' : GridLink} : L.transpose = L'.transpose ↔ L = L' :=
  transposeEquiv.injective.eq_iff

end GridLink

end TauCeti
