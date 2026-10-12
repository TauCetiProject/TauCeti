/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Decomposition
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Decomposition

/-!
# The chain-map equation of the grid commutation map

Let `C` be a validated column commutation of a grid diagram `G`, write `G'` for the commuted
diagram `G.swapColumns C.column (finRotate n C.column)`, `∂` and `∂'` for the unblocked
differentials of `G` and `G'`, and `Φ` for the commutation map `GridDiagram.commutationMap`,
which counts pentagons turning on either side. This file writes the equation `Φ ∘ ∂ = ∂' ∘ Φ`
as a finite combinatorial identity.

The `(x, z)` matrix coefficient of `Φ ∘ ∂` is the total weight of the counted domains made of a
rectangle of `G` followed by a pentagon, of either kind. That of `∂' ∘ Φ` is the total weight of
the counted domains made of a pentagon, of either kind, followed by a rectangle of `G'`. Since
both composites are semilinear over the same renaming of the variables, they agree exactly when
these four-term coefficient identities hold for all pairs of grid states.

## Main results

* `TauCeti.GridDiagram.commutationMap_unblockedDifferential_single_apply` and
  `TauCeti.GridDiagram.unblockedDifferential_commutationMap_single_apply`: the coefficients of
  the two composites on a grid-state generator.
* `TauCeti.GridDiagram.commutationMap_comp_unblockedDifferential_eq_iff`: the commutation map
  commutes with the differentials exactly when the composite-domain sums agree.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  (R : Type*) [CommSemiring R]

/-- On a grid-state generator, the coefficient of the commutation map after the original
differential is the total weight of the counted rectangle--pentagon decompositions, with
pentagons turning on either side. -/
theorem commutationMap_unblockedDifferential_single_apply (x z : GridState n) :
    G.commutationMap R C (G.unblockedDifferential R (Finsupp.single x 1)) z =
      (∑ D ∈ G.rectanglePentagonDecompositions C x z, G.rectanglePentagonWeight C R D) +
        ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z,
          G.rectangleInitialPentagonWeight C R D := by
  rw [commutationMap_apply, Finsupp.add_apply,
    G.pentagonMap_unblockedDifferential_single_apply C R x z,
    G.initialPentagonMap_unblockedDifferential_single_apply C R x z]

/-- On a grid-state generator, the coefficient of the commuted differential after the
commutation map is the total weight of the counted pentagon--rectangle decompositions, with
pentagons turning on either side. -/
theorem unblockedDifferential_commutationMap_single_apply (x z : GridState n) :
    (G.swapColumns C.column (finRotate n C.column)).unblockedDifferential R
        (G.commutationMap R C (Finsupp.single x 1)) z =
      (∑ D ∈ G.pentagonRectangleDecompositions C x z, G.pentagonRectangleWeight C R D) +
        ∑ D ∈ G.initialPentagonRectangleDecompositions C x z,
          G.initialPentagonRectangleWeight C R D := by
  rw [commutationMap_apply, map_add, Finsupp.add_apply,
    G.unblockedDifferential_pentagonMap_single_apply C R x z,
    G.unblockedDifferential_initialPentagonMap_single_apply C R x z]

/-- The commutation map commutes with the unblocked differentials exactly when, for all grid
states `x` and `z`, the counted rectangle--pentagon and pentagon--rectangle decompositions from
`x` to `z`, with pentagons turning on either side, have the same total weight. -/
theorem commutationMap_comp_unblockedDifferential_eq_iff :
    (G.commutationMap R C).comp (G.unblockedDifferential R) =
        ((G.swapColumns C.column (finRotate n C.column)).unblockedDifferential R).comp
          (G.commutationMap R C) ↔
      ∀ x z : GridState n,
        (∑ D ∈ G.rectanglePentagonDecompositions C x z, G.rectanglePentagonWeight C R D) +
            ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z,
              G.rectangleInitialPentagonWeight C R D =
          (∑ D ∈ G.pentagonRectangleDecompositions C x z, G.pentagonRectangleWeight C R D) +
            ∑ D ∈ G.initialPentagonRectangleDecompositions C x z,
              G.initialPentagonRectangleWeight C R D := by
  simp_rw [← G.commutationMap_unblockedDifferential_single_apply C R,
    ← G.unblockedDifferential_commutationMap_single_apply C R, ← Finsupp.ext_iff]
  constructor
  · intro h x
    exact LinearMap.congr_fun h (Finsupp.single x 1)
  · intro h
    exact Finsupp.lhom_ext' fun x => LinearMap.ext_ring (by
      simpa only [LinearMap.comp_apply, Finsupp.lsingle_apply] using h x)

end TauCeti.GridDiagram
