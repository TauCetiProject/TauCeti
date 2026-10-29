/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness
public import TauCeti.AlgebraicTopology.EilenbergMacLane.OneDimensional

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

## Main definitions

* `TauCeti.wedgeCirclesHomotopyEquivClassifyingSpace`: the homotopy equivalence from the wedge of
  circles indexed by `S` to `classifyingSpace (FreeGroup S)`.
* `TauCeti.wedgeCirclesClassifyingSpaceBasepointPath`: the change of base point it requires.

## Main results

* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCirclesHomotopyEquivClassifyingSpace`:
  the equivalence induces the identification of both fundamental groups with `FreeGroup S`.
* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCircles_expLoop`: it sends the loop
  around the `i`-th circle to the generator `i`.

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

end TauCeti
