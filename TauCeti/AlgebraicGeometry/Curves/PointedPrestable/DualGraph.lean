/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph.Iso
public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Category

/-!
# The dual graph of a pointed prestable curve

Over a separably closed field `K`, the dual graph `AlgebraicGeometry.Scheme.dualGraph` of a
prestable curve records the irreducible components of its normalization, their genera and the
branches over the nodes, and places markings at given points of the smooth locus. For a pointed
prestable curve over `K`, the markings are the values of its sections at the point of `Spec K`
(`TauCeti.AlgebraicGeometry.PointedPrestableFamily.markingPoint`).

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraph`: the dual graph of a pointed
  prestable curve over a separably closed field, with its markings.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraphIsoOfIso`: the isomorphism of dual
  graphs induced by an isomorphism of pointed prestable curves.

## Main results

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraph_reindex`: reindexing the markings
  of the curve reindexes the markings of its dual graph.

In the namespace `TauCeti.AlgebraicGeometry.PointedPrestableFamily`:

* `coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv`: the isomorphism of dual graphs
  carries a component of the blowup to its image under the induced isomorphism of blowups.
* `image_blowupToBase_comp_dualGraphIsoOfIso_vertexEquiv`: it therefore matches the images of
  the components in the curves.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PointedPrestableFamily

variable {K : Type u} [Field K] {m n : ℕ} (P : PointedPrestableFamily (Spec (.of K)) n)

/-- The **dual graph** of a pointed prestable curve over a separably closed field: the dual graph
`AlgebraicGeometry.Scheme.dualGraph` of its total space, with the `i`th marking at the point of
the `i`th section. -/
abbrev dualGraph [IsSepClosed K] : DualGraph.{u} (Fin n) :=
  P.total.dualGraph P.markingPoint

/-- The dual graph of a reindexed pointed prestable curve is the dual graph with reindexed
markings. -/
@[simp]
theorem dualGraph_reindex [IsSepClosed K] (e : Fin m ↪ Fin n) :
    (P.reindex e).dualGraph = P.dualGraph.reindex e := by
  rw [dualGraph, show (P.reindex e).markingPoint = P.markingPoint ∘ e from
    funext (P.markingPoint_reindex e)]
  exact P.total.dualGraph_comp P.markingPoint e

/-- An isomorphism of pointed prestable curves over a separably closed field induces an
isomorphism of their dual graphs: the isomorphism `AlgebraicGeometry.Scheme.dualGraphIsoOfIso`
induced by the isomorphism of total spaces, which lies over `Spec K` and matches the markings. -/
def dualGraphIsoOfIso [IsSepClosed K] {P Q : PointedPrestableFamily (Spec (.of K)) n}
    (e : P ≅ Q) : P.dualGraph.Iso Q.dualGraph :=
  Scheme.dualGraphIsoOfIso (K := K) (totalIso e) (totalIso_hom_comp_toBase e) _ _ fun i ↦ by
    rw [totalIso_hom]
    exact e.hom.hom_markingPoint i

/-- The isomorphism of dual graphs carries a component of the blowup of the total space of `P`
to its image under the induced isomorphism of blowups. -/
@[simp]
theorem coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv [IsSepClosed K]
    {P Q : PointedPrestableFamily (Spec (.of K)) n} (e : P ≅ Q) (v : P.dualGraph.Vertex) :
    (Q.total.dualGraphVertexEquiv Q.markingPoint ((dualGraphIsoOfIso e).vertexEquiv v) :
        Set (Q.total.singularLocus K).blowup) =
      (Scheme.singularLocusBlowupIso (R := K) (totalIso e) (totalIso_hom_comp_toBase e)).hom ''
        (P.total.dualGraphVertexEquiv P.markingPoint v) :=
  Scheme.coe_dualGraphVertexEquiv_dualGraphIsoOfIso_vertexEquiv ..

/-- The image of the component of the blowup of the total space of `Q` corresponding to a vertex
`v`, under the blowup morphism followed by a morphism `f` out of the total space, is the image of
the component `v` of the blowup of the total space of `P` under the blowup morphism followed by
the map of total spaces `e.hom.hom` and `f`. -/
theorem image_blowupToBase_comp_dualGraphIsoOfIso_vertexEquiv [IsSepClosed K]
    {P Q : PointedPrestableFamily (Spec (.of K)) n} (e : P ≅ Q) {Z : Scheme.{u}}
    (f : Q.total ⟶ Z) (v : P.dualGraph.Vertex) :
    ((Q.total.singularLocus K).blowupToBase ≫ f) ''
        (Q.total.dualGraphVertexEquiv Q.markingPoint ((dualGraphIsoOfIso e).vertexEquiv v) :
          Set (Q.total.singularLocus K).blowup) =
      ((P.total.singularLocus K).blowupToBase ≫ e.hom.hom ≫ f) ''
        (P.total.dualGraphVertexEquiv P.markingPoint v : Set (P.total.singularLocus K).blowup) := by
  rw [← totalIso_hom]
  exact Scheme.image_blowupToBase_comp_dualGraphIsoOfIso_vertexEquiv ..

end PointedPrestableFamily

end TauCeti.AlgebraicGeometry
