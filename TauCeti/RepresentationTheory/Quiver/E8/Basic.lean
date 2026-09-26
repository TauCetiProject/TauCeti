/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Orientation

/-!
# The oriented `E₈` quiver

The vertices are the nodes of `CartanMatrix.E 8`, numbered as in Bourbaki shifted down by one.
Every edge is directed from its smaller node to its larger one. The arrows are
`0 ⟶ 2`, `1 ⟶ 3`, `2 ⟶ 3`, `3 ⟶ 4`, `4 ⟶ 5`, `5 ⟶ 6`, and `6 ⟶ 7`.

The Euler and Tits forms are computed in `TauCeti.RepresentationTheory.Quiver.E8.EulerForm`.

## Main definitions and results

* `TauCeti.Quiver.E8` and `TauCeti.Quiver.E8.vertexEquiv`: the quiver and its eight nodes.
* `TauCeti.Quiver.E8.homEquiv`: arrows are exactly the adjacent pairs directed upward.
* `TauCeti.Quiver.E8.card_hom` and `TauCeti.Quiver.E8.isAcyclic`: the arrow count and acyclicity,
  derived from the linear-order orientation.

## References

* N. Bourbaki, *Lie groups and Lie algebras, Chapters 4–6*, Plate VII, for the numbering of the
  `E₈` diagram and its Cartan matrix.
-/

public section

namespace TauCeti

open _root_.Quiver DoubledQuiver

namespace Quiver

/-- **The oriented `E₈` quiver.** Its vertices are the nodes of `CartanMatrix.E 8` and its
arrows run from smaller to larger adjacent nodes. It is the oriented quiver of the `E₈` diagram
for the linear-order orientation, as a definition rather than an abbreviation: consumers use
`vertexEquiv`, `homEquiv`, `card_hom`, and `isAcyclic` instead of unfolding it. -/
@[expose]
def E8 : Type :=
  OrientedQuiver (diagramGraph (CartanMatrix.E 8)) (Orientation.ofLinearOrder _)

namespace E8

instance : _root_.Quiver E8 :=
  inferInstanceAs (_root_.Quiver
    (OrientedQuiver (diagramGraph (CartanMatrix.E 8)) (Orientation.ofLinearOrder _)))

instance : _root_.Quiver.IsThin E8 :=
  inferInstanceAs (_root_.Quiver.IsThin
    (OrientedQuiver (diagramGraph (CartanMatrix.E 8)) (Orientation.ofLinearOrder _)))

/-- The vertices of the `E₈` quiver are the eight nodes of the diagram. -/
def vertexEquiv : Fin 8 ≃ E8 :=
  OrientedQuiver.vertexEquiv _ _

private theorem vertexEquiv_eq (i : Fin 8) :
    vertexEquiv i =
      (OrientedQuiver.vertex (diagramGraph (CartanMatrix.E 8)) (Orientation.ofLinearOrder _) i :
        E8) :=
  OrientedQuiver.vertexEquiv_apply _ _ i

instance : Fintype E8 :=
  Fintype.ofEquiv (Fin 8) vertexEquiv

instance : DecidableEq E8 :=
  vertexEquiv.symm.decidableEq

/-- Each arrow space of the `E₈` quiver is finite. -/
noncomputable instance (i j : E8) : Fintype (i ⟶ j) :=
  Fintype.ofFinite _

/-- The arrows of the `E₈` quiver from node `i` to node `j` are exactly the edges with `i < j`.
This characterizes the hom spaces without unfolding the quiver instance. -/
def homEquiv (i j : Fin 8) :
    (vertexEquiv i ⟶ vertexEquiv j) ≃
      {_h : (diagramGraph (CartanMatrix.E 8)).Adj i j // i < j} :=
  (Equiv.cast (congrArg₂ (fun a b : E8 ↦ a ⟶ b) (vertexEquiv_eq i) (vertexEquiv_eq j))).trans <|
    (OrientedQuiver.homEquiv _ _ i j).trans <|
      Equiv.subtypeEquivRight fun _ ↦ Orientation.mem_ofLinearOrder_iff _ _

/-- **The arrows of the `E₈` quiver**: there is exactly one arrow `i ⟶ j` when the nodes `i < j`
are joined by an edge of the `E₈` diagram, and there are no others. -/
@[simp]
theorem card_hom (i j : Fin 8) :
    Fintype.card (vertexEquiv i ⟶ vertexEquiv j) =
      if i < j ∧ (diagramGraph (CartanMatrix.E 8)).Adj i j then 1 else 0 := by
  rw [Fintype.card_eq_nat_card, vertexEquiv_eq, vertexEquiv_eq]
  exact OrientedQuiver.card_hom_ofLinearOrder (diagramGraph (CartanMatrix.E 8)) i j

/-- The orientation of the `E₈` quiver is acyclic. -/
theorem isAcyclic : Quiver.IsAcyclic E8 :=
  OrientedQuiver.isAcyclic_ofLinearOrder _

end E8

end Quiver

end TauCeti
