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
* `TauCeti.Quiver.E8.arrow` and `TauCeti.Quiver.E8.exists_eq_arrow`: construction and elimination
  of arrows from directed edges.
* `TauCeti.Quiver.E8.card_hom` and `TauCeti.Quiver.E8.isAcyclic`: the arrow count and acyclicity,
  derived from the linear-order orientation.

## References

* “An oriented `E₈` quiver” in `TauCetiRoadmap/GrothendieckEulerForms/README.md`.
* N. Bourbaki, *Lie groups and Lie algebras, Chapters 4–6*, Plate VII, for the numbering of the
  `E₈` diagram and its Cartan matrix.
-/

public section

namespace TauCeti

open _root_.Quiver DoubledQuiver

namespace Quiver

/-- **The oriented `E₈` quiver.** Its vertices are the nodes of `CartanMatrix.E 8` and its
arrows run from smaller to larger adjacent nodes. -/
inductive E8 : Type
  | /-- The vertex at node `i` of the `E₈` Dynkin diagram. -/ vertex (i : Fin 8) : E8
  deriving DecidableEq

namespace E8

/-- The vertices of the `E₈` quiver are the eight nodes of the diagram. -/
def vertexEquiv : Fin 8 ≃ E8 where
  toFun := vertex
  invFun | .vertex i => i
  left_inv _ := rfl
  right_inv | .vertex _ => rfl

@[simp]
theorem vertexEquiv_apply (i : Fin 8) : vertexEquiv i = vertex i := (rfl)

instance : Fintype E8 :=
  Fintype.ofEquiv (Fin 8) vertexEquiv

instance : _root_.Quiver E8 where
  Hom a b := match a, b with
    | .vertex i, .vertex j =>
      OrientedQuiver.vertex (diagramGraph (CartanMatrix.E 8))
        (Orientation.ofLinearOrder _) i ⟶
      OrientedQuiver.vertex (diagramGraph (CartanMatrix.E 8))
        (Orientation.ofLinearOrder _) j

instance : _root_.Quiver.IsThin E8 := by
  intro a b
  cases a with | vertex i =>
  cases b with | vertex j =>
  change Subsingleton (OrientedQuiver.vertex (diagramGraph (CartanMatrix.E 8))
    (Orientation.ofLinearOrder _) i ⟶
    OrientedQuiver.vertex (diagramGraph (CartanMatrix.E 8))
    (Orientation.ofLinearOrder _) j)
  infer_instance

/-- Each arrow space of the `E₈` quiver is finite. -/
noncomputable instance (i j : E8) : Fintype (i ⟶ j) :=
  Fintype.ofFinite _

/-- **The arrows of the `E₈` quiver**: there is exactly one arrow `i ⟶ j` when the nodes `i < j`
are joined by an edge of the `E₈` diagram, and there are no others. -/
theorem card_hom (i j : Fin 8) :
    Fintype.card (vertexEquiv i ⟶ vertexEquiv j) =
      if i < j ∧ (diagramGraph (CartanMatrix.E 8)).Adj i j then 1 else 0 := by
  rw [Fintype.card_eq_nat_card, vertexEquiv_apply, vertexEquiv_apply]
  exact OrientedQuiver.card_hom_ofLinearOrder _ i j

/-- Construct the arrow from `i` to `j` when they are adjacent and `i < j`. -/
def arrow {i j : Fin 8} (h : (diagramGraph (CartanMatrix.E 8)).Adj i j) (hij : i < j) :
    vertexEquiv i ⟶ vertexEquiv j := by
  change OrientedQuiver.vertex (diagramGraph (CartanMatrix.E 8))
    (Orientation.ofLinearOrder _) i ⟶
    OrientedQuiver.vertex (diagramGraph (CartanMatrix.E 8)) (Orientation.ofLinearOrder _) j
  exact OrientedQuiver.arrow _ _ h (by simpa only [Orientation.mem_ofLinearOrder_iff] using hij)

/-- Every arrow of the oriented `E₈` quiver comes from an edge directed from its smaller node to
its larger node. -/
theorem exists_eq_arrow {i j : Fin 8} (e : vertexEquiv i ⟶ vertexEquiv j) :
    ∃ (h : (diagramGraph (CartanMatrix.E 8)).Adj i j) (hij : i < j), e = arrow h hij := by
  have e' : OrientedQuiver.vertex (diagramGraph (CartanMatrix.E 8))
      (Orientation.ofLinearOrder _) i ⟶
      OrientedQuiver.vertex (diagramGraph (CartanMatrix.E 8))
        (Orientation.ofLinearOrder _) j := e
  obtain ⟨h, ho⟩ := OrientedQuiver.homEquiv _ _ i j e'
  exact ⟨h, (by simpa only [Orientation.mem_ofLinearOrder_iff] using ho),
    Subsingleton.elim _ _⟩

/-- The orientation of the `E₈` quiver is acyclic. -/
theorem isAcyclic : Quiver.IsAcyclic E8 := by
  let F : E8 ⥤q OrientedQuiver (diagramGraph (CartanMatrix.E 8)) (Orientation.ofLinearOrder _) := {
    obj := fun | .vertex i => OrientedQuiver.vertex _ _ i
    map := fun {a b} e => by
      cases a with | vertex i =>
      cases b with | vertex j =>
      exact e
  }
  apply Quiver.isAcyclic_def.mpr
  intro a p
  have hlen : ∀ {b : E8} (q : Path a b), (F.mapPath q).length = q.length := by
    intro b q
    induction q with
    | nil => rfl
    | cons p e ih => simp only [Prefunctor.mapPath_cons, Path.length_cons, ih]
  exact p.eq_nil_of_length_zero ((hlen p).symm ▸
    (OrientedQuiver.isAcyclic_ofLinearOrder _).length_eq_zero (F.mapPath p))

end E8

end Quiver

end TauCeti
