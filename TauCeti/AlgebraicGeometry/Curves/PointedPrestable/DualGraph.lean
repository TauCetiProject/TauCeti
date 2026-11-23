/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph
public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Basic

/-!
# The dual graph of a pointed prestable curve

Over a separably closed field `K`, the dual graph `AlgebraicGeometry.Scheme.dualGraph` of a
prestable curve records the irreducible components of its normalization, their genera and the
branches over the nodes, and places markings at given points of the smooth locus. For a pointed
prestable curve over `K`, the markings are the values of its sections at the point of `Spec K`.

## Main definitions

* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.markingPoint`: the point of a pointed
  prestable curve over a field at a marking, as a point of the smooth locus.
* `TauCeti.AlgebraicGeometry.PointedPrestableFamily.dualGraph`: the dual graph of a pointed
  prestable curve over a separably closed field, with its markings.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PointedPrestableFamily

variable {K : Type u} [Field K] {n : ℕ} (P : PointedPrestableFamily (Spec (.of K)) n)

/-- The point of a pointed prestable curve over a field at its `i`th marking, as a point of the
smooth locus. -/
def markingPoint (i : Fin n) : (P.total ↘ Spec (.of K)).smoothLocus :=
  ⟨P.marking i default, P.range_marking_subset_smoothLocus i ⟨default, rfl⟩⟩

/-- The point at the `i`th marking is the value of the `i`th section at the point of `Spec K`. -/
@[simp]
theorem coe_markingPoint (i : Fin n) : (P.markingPoint i : P.total) = P.marking i default :=
  (rfl)

/-- The **dual graph** of a pointed prestable curve over a separably closed field: the dual graph
`AlgebraicGeometry.Scheme.dualGraph` of its total space, with the `i`th marking at the point of
the `i`th section. -/
abbrev dualGraph [IsSepClosed K] : DualGraph.{u} (Fin n) :=
  P.total.dualGraph P.markingPoint

end PointedPrestableFamily

end TauCeti.AlgebraicGeometry
