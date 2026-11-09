/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Retraction
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Restriction
public import Mathlib.Topology.Homotopy.Equiv

/-!
# The homotopy type of an open star

The open star of a set of vertices is homotopy equivalent to the realization of the full
subcomplex on those vertices. The forward map normalizes the retained barycentric coordinates;
the inverse is the simplicial inclusion. This packages `openStarDeformation` and
`restrictRealizationHomeomorph` for transporting CW-type witnesses.

The complement of a full subcomplex is the open star of the complementary vertex set. After
barycentric subdivision, this also computes the homotopy type of complements of arbitrary
subcomplexes.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 3 (full subcomplexes and simplicial neighbourhoods).
-/

public noncomputable section

open Set

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι) (s : Set ι)

attribute [local instance] Classical.decEq

/-- Normalizing the coordinates at the vertices of `s` gives a homotopy equivalence from
their open star to the realization of the full subcomplex on `s`. Its inverse is the
simplicial inclusion. -/
def openStarHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (K.openStarRealizationSet s) (Realization (K.restrict s)) := by
  let e : ContinuousMap.HomotopyEquiv (K.openStarRealizationSet s)
      {x : Realization K | (x.1.support : Set ι) ⊆ s} :=
    { toFun := K.openStarRetraction s
      invFun := ContinuousMap.inclusion (K.setOf_support_subset_subset_openStarRealizationSet s)
      left_inv := ⟨(K.openStarDeformation s).toHomotopy.symm⟩
      right_inv := by
        have h : (K.openStarRetraction s).comp
            (ContinuousMap.inclusion (K.setOf_support_subset_subset_openStarRealizationSet s)) =
              ContinuousMap.id _ :=
          ContinuousMap.ext (K.openStarRetraction_inclusion s)
        rw [h] }
  exact e.trans (K.restrictRealizationHomeomorph s).symm.toHomotopyEquiv

/-- The forward equivalence is the normalized open-star retraction, viewed in the
restricted realization. -/
@[simp]
theorem openStarHomotopyEquiv_apply (x : K.openStarRealizationSet s) :
    K.openStarHomotopyEquiv s x =
      (K.restrictRealizationHomeomorph s).symm (K.openStarRetraction s x) :=
  (rfl)

/-- The inverse equivalence is the simplicial inclusion, with its image in the open star. -/
@[simp]
theorem coe_openStarHomotopyEquiv_symm_apply (x : Realization (K.restrict s)) :
    ((K.openStarHomotopyEquiv s).symm x : Realization K) =
      (K.restrictInclusion s).realizationMap x := by
  -- Unfolding the inverse composition identifies it with the inclusion of the restricted
  -- realization homeomorphism; the inclusion does not change the underlying point.
  exact K.restrictRealizationHomeomorph_apply s x

end AbstractSimplicialComplex
