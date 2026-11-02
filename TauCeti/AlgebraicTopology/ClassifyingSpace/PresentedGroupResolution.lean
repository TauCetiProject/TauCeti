/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Resolution
public import TauCeti.AlgebraicTopology.UniversalCover.Action
public import TauCeti.Topology.Covering.Quotient

/-!
# The cellular resolution of a presented group

For a group presentation `⟨S | R⟩`, the cellular chains of the universal cover of the cellular
classifying space `TauCeti.cellularClassifyingSpace R` form a free resolution of the trivial
representation of `PresentedGroup R` (`TauCeti.cellularClassifyingSpaceResolution`). This is the
cellular counterpart of the resolution `TauCeti.universalGSpaceResolution` by the ordered chains of
Milnor's countable join: here the free generators in degree `n` are the `n`-cells of the cellular
model, one `0`-cell, one `1`-cell for each generator, one `2`-cell for each relator, and the cells
of dimension at least `3` that kill the higher homotopy groups.

The universal cover is the based-path model `TauCeti.UniversalCover` at the base point of the
cellular classifying space. Its fundamental group acts on it by deck transformations, a loop class
`γ` acting by prepending `γ⁻¹` to a path out of the base point (`TauCeti.UniversalCover.smul_mk`),
so that this is a left action of the fundamental group itself and not of its opposite. The
presented group acts through the identification
`TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv R` of the fundamental group with
`PresentedGroup R`: an element `g` acts as the loop class that this identification sends to `g`
(`TauCeti.cellularClassifyingSpace_universalCover_smul_def`). For instance, the generator `s` acts
by prepending the inverse of the image of the loop around the `s`-th circle of the presentation
complex (`TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv_symm_apply`). For
this action the endpoint projection is a quotient covering map
(`TauCeti.isQuotientCoveringMap_cellularClassifyingSpace_universalCover`).

The cellular classifying space is an aspherical Hausdorff CW complex and its universal cover is
simply connected, so the resolution is the cellular resolution of an aspherical CW complex
(`TauCeti.cellularResolutionOfIsAspherical`) for this covering.

## Main definitions

* `TauCeti.cellularClassifyingSpaceResolution`: the projective resolution of the trivial
  representation of `PresentedGroup R` by the lifted cellular chains of the universal cover of the
  cellular classifying space.

## Main results

* `TauCeti.isQuotientCoveringMap_cellularClassifyingSpace_universalCover`: the presented group
  acts on the universal cover of the cellular classifying space with quotient covering map the
  endpoint projection.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section I.4 and Section II.4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B.
-/

public section

noncomputable section

open CategoryTheory Set

namespace TauCeti

universe u

variable {S : Type u} (R : Set (FreeGroup S))

/-- The presented group acts on the universal cover of the cellular classifying space through the
identification `cellularClassifyingSpaceFundamentalGroupMulEquiv R` of the fundamental group with
`PresentedGroup R`: an element `g` acts as the loop class corresponding to it, by prepending the
inverse of that loop class to a path out of the base point. -/
instance : MulAction (PresentedGroup R) (UniversalCover (cellularClassifyingSpaceBasepoint R)) :=
  MulAction.compHom _ (cellularClassifyingSpaceFundamentalGroupMulEquiv R).symm.toMonoidHom

/-- An element of the presented group acts on the universal cover of the cellular classifying
space as the loop class that `cellularClassifyingSpaceFundamentalGroupMulEquiv R` sends to it. -/
@[simp]
theorem cellularClassifyingSpace_universalCover_smul_def (g : PresentedGroup R)
    (x : UniversalCover (cellularClassifyingSpaceBasepoint R)) :
    g • x = (cellularClassifyingSpaceFundamentalGroupMulEquiv R).symm g • x :=
  (rfl)

/-- **The presented group acts on the universal cover of the cellular classifying space as its
group of deck transformations**: for this action, the endpoint projection is a quotient covering
map. -/
theorem isQuotientCoveringMap_cellularClassifyingSpace_universalCover :
    IsQuotientCoveringMap
      (UniversalCover.proj :
        UniversalCover (cellularClassifyingSpaceBasepoint R) → cellularClassifyingSpace R)
      (PresentedGroup R) :=
  UniversalCover.isQuotientCoveringMap.of_smul_eq
    (cellularClassifyingSpaceFundamentalGroupMulEquiv R) fun {_ _} ↦ by
      rw [cellularClassifyingSpace_universalCover_smul_def, MulEquiv.symm_apply_apply]

/-- **The cellular resolution of a presented group**: the cellular chains of the universal cover of
the cellular classifying space of `⟨S | R⟩`, with its lifted CW structure, form a projective
resolution of the trivial representation of `PresentedGroup R` over `k`. In degree `n` they are
free over `k[PresentedGroup R]` with one generator for each `n`-cell of the cellular classifying
space (`TauCeti.cellularChainRepIsoFree`). The group acts by the deck transformations of
`isQuotientCoveringMap_cellularClassifyingSpace_universalCover`. This is
`TauCeti.cellularResolutionOfIsAspherical` for the cellular classifying space. -/
def cellularClassifyingSpaceResolution (k : Type u) [CommRing k] :
    ProjectiveResolution (Rep.trivial k (PresentedGroup R) k) :=
  cellularResolutionOfIsAspherical (isQuotientCoveringMap_cellularClassifyingSpace_universalCover R)
    (UniversalCover.proj_basepointLift _)
    (isEilenbergMacLaneSpaceOne_cellularClassifyingSpace R).isAspherical k

/-- The complex of `TauCeti.cellularClassifyingSpaceResolution` is the lifted cellular chain
complex of the universal cover of the cellular classifying space. -/
@[simp]
lemma cellularClassifyingSpaceResolution_complex (k : Type u) [CommRing k] :
    (cellularClassifyingSpaceResolution R k).complex =
      cellularChainComplexRep univ (isQuotientCoveringMap_cellularClassifyingSpace_universalCover R)
        k :=
  cellularResolutionOfIsAspherical_complex ..

-- As for `TauCeti.cellularResolution_π`, the public statement cannot unfold the unexposed body of
-- `TauCeti.cellularClassifyingSpaceResolution`, so it transports along
-- `cellularClassifyingSpaceResolution_complex`.
/-- The augmentation of `TauCeti.cellularClassifyingSpaceResolution` is that of the lifted cellular
chain complex. -/
@[simp]
lemma cellularClassifyingSpaceResolution_π (k : Type u) [CommRing k] :
    (cellularClassifyingSpaceResolution R k).π =
      eqToHom (cellularClassifyingSpaceResolution_complex R k) ≫
        cellularChainComplexRepAugmentation univ
          (isQuotientCoveringMap_cellularClassifyingSpace_universalCover R) k :=
  cellularResolutionOfIsAspherical_π ..

end TauCeti
