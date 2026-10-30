/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Cellular
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness
public import TauCeti.AlgebraicTopology.EilenbergMacLane.OneDimensional
import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv

/-!
# A wedge of circles is a classifying space of a free group

A wedge of circles indexed by `S` is a `K(F, 1)` for the free group `F = FreeGroup S`
(`TauCeti.WedgeSum.isEilenbergMacLaneSpaceOne_circle`), and it is a CW complex. By the uniqueness
of `K(G, 1)` spaces of CW type it is homotopy equivalent to Milnor's classifying space
`classifyingSpace (FreeGroup S)`, by a homotopy equivalence
`TauCeti.wedgeCirclesHomotopyEquivClassifyingSpace S` which induces the identity of `F` under the
two identifications of fundamental groups: the loop around the `i`-th circle goes to the
generator `i` (`TauCeti.classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCircles_expLoop`).

The equivalence need not preserve the base point; the path
`TauCeti.wedgeCirclesClassifyingSpaceBasepointPath` from the image of the wedge point to the base
point of the classifying space supplies the change of base point.

The wedge of circles is also homotopy equivalent to the cellular model of the free group. For the
presentation of `FreeGroup S` with no relators the presentation complex is the wedge of circles
itself (`TauCeti.TwoCellAttachment.inclHomeomorphOfIsEmpty`), and since it is already aspherical,
the cells of dimension at least `3` which build the cellular classifying space out of it change
nothing up to homotopy. So the inclusion of the wedge of circles into
`cellularClassifyingSpace (∅ : Set (FreeGroup S))` is a homotopy equivalence
`TauCeti.wedgeCirclesHomotopyEquivCellularClassifyingSpace S`, which is pointed and induces the
quotient map `PresentedGroup.mk ∅` on fundamental groups
(`TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv_mapOfEq_wedgeCircles`).

## Main definitions

* `TauCeti.wedgeCirclesHomotopyEquivClassifyingSpace`: the homotopy equivalence from the wedge of
  circles indexed by `S` to `classifyingSpace (FreeGroup S)`.
* `TauCeti.wedgeCirclesClassifyingSpaceBasepointPath`: the change of base point it requires.
* `TauCeti.wedgeCirclesHomotopyEquivCellularClassifyingSpace`: the inclusion of the wedge of
  circles into the cellular classifying space of the free presentation, as a homotopy
  equivalence.

## Main results

* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCirclesHomotopyEquivClassifyingSpace`:
  the equivalence induces the identification of both fundamental groups with `FreeGroup S`.
* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCircles_expLoop`: it sends the loop
  around the `i`-th circle to the generator `i`.
* `TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv_mapOfEq_wedgeCircles`: the inclusion
  of the wedge of circles into the cellular model induces the quotient map from the free group to
  the presented group without relators.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.B, Theorem 1B.8.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open scoped ContinuousMap
open FundamentalGroup

namespace TauCeti

open WedgeSum

variable (S : Type)

private theorem exists_wedgeCirclesHomotopyEquivClassifyingSpace :
    ∃ (e : (WedgeSum fun _ : S ↦ (1 : Circle)) ≃ₕ classifyingSpace (FreeGroup S))
      (γ : Path (e.toFun (base _)) (classifyingSpaceBasepoint (FreeGroup S))),
      ∀ a, classifyingSpaceFundamentalGroupMulEquiv (FreeGroup S)
        (fundamentalGroupMulEquivOfPath γ (map e.toFun (base _) a)) =
          circleFundamentalGroupMulEquiv S a :=
  (isEilenbergMacLaneSpaceOne_circle S).isAspherical.exists_homotopyEquiv_classifyingSpace
    (circleFundamentalGroupMulEquiv S)

/-- **A wedge of circles is homotopy equivalent to Milnor's classifying space of the free group
on its circles.** The equivalence induces the identity of `FreeGroup S` under the identifications
of both fundamental groups, after the change of base point along
`TauCeti.wedgeCirclesClassifyingSpaceBasepointPath`. -/
def wedgeCirclesHomotopyEquivClassifyingSpace :
    (WedgeSum fun _ : S ↦ (1 : Circle)) ≃ₕ classifyingSpace (FreeGroup S) :=
  (exists_wedgeCirclesHomotopyEquivClassifyingSpace S).choose

/-- The path from the image of the wedge point under
`TauCeti.wedgeCirclesHomotopyEquivClassifyingSpace` to the base point of the classifying space,
along which it induces the identity of `FreeGroup S`. -/
def wedgeCirclesClassifyingSpaceBasepointPath :
    Path ((wedgeCirclesHomotopyEquivClassifyingSpace S).toFun (base _))
      (classifyingSpaceBasepoint (FreeGroup S)) :=
  (exists_wedgeCirclesHomotopyEquivClassifyingSpace S).choose_spec.choose

/-- The homotopy equivalence `TauCeti.wedgeCirclesHomotopyEquivClassifyingSpace` induces the
identity of `FreeGroup S` under the identification `TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`
of the fundamental group of the wedge of circles and the identification
`TauCeti.classifyingSpaceFundamentalGroupMulEquiv` of that of the classifying space. -/
theorem classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCirclesHomotopyEquivClassifyingSpace
    (a : FundamentalGroup (WedgeSum fun _ : S ↦ (1 : Circle)) (base _)) :
    classifyingSpaceFundamentalGroupMulEquiv (FreeGroup S)
      (fundamentalGroupMulEquivOfPath (wedgeCirclesClassifyingSpaceBasepointPath S)
        (map (wedgeCirclesHomotopyEquivClassifyingSpace S).toFun (base _) a)) =
      circleFundamentalGroupMulEquiv S a :=
  (exists_wedgeCirclesHomotopyEquivClassifyingSpace S).choose_spec.choose_spec a

/-- The homotopy equivalence `TauCeti.wedgeCirclesHomotopyEquivClassifyingSpace` sends the loop
going once around the `i`-th circle to the generator `i` of the free group, under the
identification `TauCeti.classifyingSpaceFundamentalGroupMulEquiv`. -/
theorem classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCircles_expLoop (i : S) :
    classifyingSpaceFundamentalGroupMulEquiv (FreeGroup S)
      (fundamentalGroupMulEquivOfPath (wedgeCirclesClassifyingSpaceBasepointPath S)
        (map (wedgeCirclesHomotopyEquivClassifyingSpace S).toFun (base _)
          (mapOfEq (incl (fun _ : S ↦ (1 : Circle)) i) (incl_apply_self i)
            (fromPath (Path.Homotopic.Quotient.mk Circle.expLoop))))) =
      FreeGroup.of i := by
  rw [classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCirclesHomotopyEquivClassifyingSpace,
    circleFundamentalGroupMulEquiv_expLoop]

/-! ### The cellular model of a free group -/

/-- **The cellular classifying space of a free group is homotopy equivalent to a wedge of
circles.** For the presentation of `FreeGroup S` with generators `S` and no relators, the
presentation complex is the wedge of circles indexed by `S`
(`TauCeti.TwoCellAttachment.inclHomeomorphOfIsEmpty`), which is already aspherical, so the cells of
dimension at least `3` attached to it change nothing up to homotopy: the inclusion of the wedge of
circles into the cellular classifying space is a homotopy equivalence
(`TauCeti.wedgeCirclesHomotopyEquivCellularClassifyingSpace_apply`). -/
def wedgeCirclesHomotopyEquivCellularClassifyingSpace :
    (WedgeSum fun _ : S ↦ (1 : Circle)) ≃ₕ cellularClassifyingSpace (∅ : Set (FreeGroup S)) :=
  let e := TwoCellAttachment.inclHomeomorphOfIsEmpty
    fun r : (∅ : Set (FreeGroup S)) ↦ PresentationComplex.attachingLoop r.1
  e.toHomotopyEquiv.trans <| PresentationComplex.homotopyEquivCellularClassifyingSpace <|
    (isEilenbergMacLaneSpaceOne_circle S).isAspherical.of_homotopyEquiv e.toHomotopyEquiv _

/-- The homotopy equivalence `TauCeti.wedgeCirclesHomotopyEquivCellularClassifyingSpace` is the
inclusion of the wedge of circles, through the presentation complex. -/
@[simp]
theorem wedgeCirclesHomotopyEquivCellularClassifyingSpace_apply
    (y : WedgeSum fun _ : S ↦ (1 : Circle)) :
    (wedgeCirclesHomotopyEquivCellularClassifyingSpace S).toFun y =
      killHomotopyGroupsIncl 2 _ _ (PresentationComplex.incl (∅ : Set (FreeGroup S)) y) := by
  simp [wedgeCirclesHomotopyEquivCellularClassifyingSpace]

/-- The homotopy equivalence `TauCeti.wedgeCirclesHomotopyEquivCellularClassifyingSpace` sends the
wedge point to the base point of the cellular classifying space. -/
theorem wedgeCirclesHomotopyEquivCellularClassifyingSpace_base :
    (wedgeCirclesHomotopyEquivCellularClassifyingSpace S).toFun (base _) =
      cellularClassifyingSpaceBasepoint (∅ : Set (FreeGroup S)) :=
  wedgeCirclesHomotopyEquivCellularClassifyingSpace_apply S _

/-- The homotopy equivalence `TauCeti.wedgeCirclesHomotopyEquivCellularClassifyingSpace` induces
the quotient map `PresentedGroup.mk ∅` from the free group to the presented group without
relators, under the identification `TauCeti.WedgeSum.circleFundamentalGroupMulEquiv` of the
fundamental group of the wedge of circles and the identification
`TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv` of that of the cellular classifying
space. -/
@[simp]
theorem cellularClassifyingSpaceFundamentalGroupMulEquiv_mapOfEq_wedgeCircles
    (a : FundamentalGroup (WedgeSum fun _ : S ↦ (1 : Circle)) (base _)) :
    cellularClassifyingSpaceFundamentalGroupMulEquiv (∅ : Set (FreeGroup S))
      (mapOfEq (wedgeCirclesHomotopyEquivCellularClassifyingSpace S).toFun
        (wedgeCirclesHomotopyEquivCellularClassifyingSpace_base S) a) =
      PresentedGroup.mk ∅ (circleFundamentalGroupMulEquiv S a) := by
  let R : Set (FreeGroup S) := ∅
  let i := killHomotopyGroupsIncl 2 (TopCat.of (PresentationComplex R))
    (PresentationComplex.basepoint R)
  -- The equivalence is the inclusion of the wedge into the presentation complex followed by the
  -- inclusion `i` of the presentation complex into the cellular classifying space.
  rw [TauCeti.FundamentalGroup.mapOfEq_congr (f₂ := i.hom.comp (PresentationComplex.incl R))
      (ContinuousMap.ext (wedgeCirclesHomotopyEquivCellularClassifyingSpace_apply S)) _ rfl,
    ← TauCeti.FundamentalGroup.mapOfEq_comp _ _ rfl rfl, TauCeti.FundamentalGroup.mapOfEq_rfl,
    TauCeti.FundamentalGroup.mapOfEq_rfl,
    cellularClassifyingSpaceFundamentalGroupMulEquiv_map_killHomotopyGroupsIncl,
    PresentationComplex.fundamentalGroupMulEquiv_map_incl]

end TauCeti
