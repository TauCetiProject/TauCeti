/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Disjoint

/-!
# Pairing rectangle--pentagon and pentagon--rectangle decompositions

The chain-map equation for a grid column commutation compares two sums over composite domains:
a rectangle followed by a pentagon, and a pentagon followed by a rectangle. This file constructs
the bijection between the disjoint parts of these two finite sets.

When the rectangle and pentagon have disjoint vertical side pairs, they commute: swapping the
order gives a bijection between the disjoint parts of the two composite domains. This is the
disjoint-domain case of the pentagon--rectangle juxtaposition argument; establishing that this
bijection preserves weights is left to the weight-identity argument, not claimed here.

## Main results

* `TauCeti.GridDiagram.disjointCommuteEquiv`: commuting gives an equivalence between disjoint
  rectangle--pentagon and pentagon--rectangle decompositions.
* `TauCeti.GridDiagram.disjointCommuteEquiv_apply`: the forward map acts by `commute`.
* `TauCeti.GridDiagram.disjointCommuteEquiv_symm_apply`: the inverse map acts by `commute`.

## References

The pentagon--rectangle juxtaposition argument in Ozsvath--Stipsicz--Szabo,
*Grid Homology for Knots and Links*, Section 5.1.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "b" => finRotate n C.column

variable (R : Type*) [CommSemiring R]

/-- Commuting gives an equivalence between disjoint rectangle--pentagon and pentagon--rectangle
decompositions. This is the bijection underlying the disjoint-domain case of the pentagon
chain-map weight identity. -/
def disjointCommuteEquiv (x z : GridState n) :
    {D : GridRectanglePentagonDecomposition C.column C.turnRow x z // D.HasDisjointSides} ≃
    {D : GridPentagonRectangleDecomposition C.column C.turnRow x z // D.HasDisjointSides} where
  toFun D := ⟨D.1.commute D.2, D.1.hasDisjointSides_commute D.2⟩
  invFun E := ⟨E.1.commute E.2, E.1.hasDisjointSides_commute E.2⟩
  left_inv D := Subtype.ext (D.1.commute_commute D.2)
  right_inv E := Subtype.ext (E.1.commute_commute E.2)

/-- The forward map of `disjointCommuteEquiv` acts by `commute`. -/
@[simp]
theorem disjointCommuteEquiv_apply (x z : GridState n)
    (D : {D : GridRectanglePentagonDecomposition C.column C.turnRow x z // D.HasDisjointSides}) :
    (disjointCommuteEquiv G C x z D : GridPentagonRectangleDecomposition C.column C.turnRow x z) =
      D.1.commute D.2 := by
  unfold disjointCommuteEquiv
  rfl

/-- The inverse map of `disjointCommuteEquiv` acts by `commute`. -/
@[simp]
theorem disjointCommuteEquiv_symm_apply (x z : GridState n)
    (E : {D : GridPentagonRectangleDecomposition C.column C.turnRow x z // D.HasDisjointSides}) :
    ((disjointCommuteEquiv G C x z).symm E :
      GridRectanglePentagonDecomposition C.column C.turnRow x z) =
      E.1.commute E.2 := by
  unfold disjointCommuteEquiv
  rfl

end GridDiagram

end TauCeti
