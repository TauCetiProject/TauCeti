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
@[expose]
def dualGraphIsoOfIso [IsSepClosed K] {P Q : PointedPrestableFamily (Spec (.of K)) n}
    (e : P ≅ Q) : P.dualGraph.Iso Q.dualGraph :=
  Scheme.dualGraphIsoOfIso (K := K) (totalIso e) e.hom.hom_comp_toBase _ _
    (totalIso_hom_markingPoint e)

end PointedPrestableFamily

end TauCeti.AlgebraicGeometry
