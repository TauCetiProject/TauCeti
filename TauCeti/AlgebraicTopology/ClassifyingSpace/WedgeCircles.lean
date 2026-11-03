/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Cellular
public import TauCeti.AlgebraicTopology.ClassifyingSpace.FirstHomology
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Homology
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

Through Milnor's model, the singular homology of the wedge of circles with coefficients in a
commutative ring `k` is the group homology of the free group with trivial coefficients `k`, in
every degree (`TauCeti.wedgeCirclesSingularHomologyIsoGroupHomology`). The wedge has no cells of
dimension at least `2`, so its homology vanishes in those degrees
(`TauCeti.WedgeSum.isZero_singularHomology_circle`). Therefore so does the singular homology of
`classifyingSpace (FreeGroup S)`, with coefficients in any abelian category with exact coproducts
(`TauCeti.isZero_classifyingSpace_singularHomology_freeGroup`), and the group homology
`Hₙ(FreeGroup S, k)` for `n ≥ 2` (`TauCeti.isZero_groupHomology_freeGroup`). In degree one, the
Hurewicz class of a loop corresponds to the class of the element of the free group it represents,
both in the abelianization of the free group and in its first group homology
(`FundamentalGroup.classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles`); in
particular the loop around the `i`-th circle corresponds to the generator `i`
(`TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles_expLoop`). The
statements are for `S : Type`, the universe in which the wedge of circles is a `K(F, 1)`.

## Main definitions

* `TauCeti.wedgeCirclesHomotopyEquivClassifyingSpace`: the homotopy equivalence from the wedge of
  circles indexed by `S` to `classifyingSpace (FreeGroup S)`.
* `TauCeti.wedgeCirclesClassifyingSpaceBasepointPath`: the change of base point it requires.
* `TauCeti.wedgeCirclesHomotopyEquivCellularClassifyingSpace`: the inclusion of the wedge of
  circles into the cellular classifying space of the free presentation, as a homotopy
  equivalence.
* `TauCeti.wedgeCirclesSingularHomologyIsoGroupHomology`: the isomorphism
  `Hₙ(⋁ S¹; k) ≅ Hₙ(FreeGroup S, k)`.

## Main results

* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCirclesHomotopyEquivClassifyingSpace`:
  the equivalence induces the identification of both fundamental groups with `FreeGroup S`.
* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCircles_expLoop`: it sends the loop
  around the `i`-th circle to the generator `i`.
* `TauCeti.cellularClassifyingSpaceFundamentalGroupMulEquiv_mapOfEq_wedgeCircles`: the inclusion
  of the wedge of circles into the cellular model induces the quotient map from the free group to
  the presented group without relators.
* `TauCeti.isZero_classifyingSpace_singularHomology_freeGroup`: the singular homology of the
  classifying space of a free group vanishes in every degree at least `2`.
* `TauCeti.isZero_groupHomology_freeGroup`: the group homology of a free group with trivial
  coefficients in a commutative ring vanishes in every degree at least `2`.
* `TauCeti.classifyingSpaceFirstHomologyAddEquiv_map_wedgeCirclesHomotopyEquivClassifyingSpace`,
  `FundamentalGroup.classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles`: on first
  homology, the equivalence sends the class of a loop to the class of the element of the free
  group it represents.
* `TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles_expLoop`: the loop
  around the `i`-th circle goes to the class of the generator `i` in `H₁(FreeGroup S, ℤ)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.B, Theorem 1B.8.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section II.4.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

open scoped ContinuousMap
open CategoryTheory Limits FundamentalGroup Set TauCeti.HurewiczOne

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
  rw [mapOfEq_congr (f₂ := i.hom.comp (PresentationComplex.incl R))
      (ContinuousMap.ext (wedgeCirclesHomotopyEquivCellularClassifyingSpace_apply S)) _ rfl,
    ← mapOfEq_comp _ _ rfl rfl, mapOfEq_rfl,
    mapOfEq_rfl,
    cellularClassifyingSpaceFundamentalGroupMulEquiv_map_killHomotopyGroupsIncl,
    PresentationComplex.fundamentalGroupMulEquiv_map_incl]

/-! ### Homology -/

/-- **The homology of a wedge of circles is the group homology of the free group.** For every
commutative ring `k`, the singular homology `Hₙ(⋁ S¹; k)` of the wedge of circles indexed by `S`
is Mathlib's group homology `Hₙ(FreeGroup S, k)` of the trivial representation: the map induced by
`TauCeti.wedgeCirclesHomotopyEquivClassifyingSpace` followed by
`TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`. -/
def wedgeCirclesSingularHomologyIsoGroupHomology (k : Type) [CommRing k] (n : ℕ) :
    ((singularChains k).obj (TopCat.of (WedgeSum fun _ : S ↦ (1 : Circle)))).homology n ≅
      groupHomology (Rep.trivial k (FreeGroup S) k) n :=
  (wedgeCirclesHomotopyEquivClassifyingSpace S).singularHomologyIso (ModuleCat.of k k) n ≪≫
    classifyingSpaceSingularHomologyIsoGroupHomology k (FreeGroup S) n

/-- The identification `TauCeti.wedgeCirclesSingularHomologyIsoGroupHomology` is the map induced
on homology by `TauCeti.wedgeCirclesHomotopyEquivClassifyingSpace`, followed by
`TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`. -/
theorem wedgeCirclesSingularHomologyIsoGroupHomology_hom (k : Type) [CommRing k] (n : ℕ) :
    (wedgeCirclesSingularHomologyIsoGroupHomology S k n).hom =
      HomologicalComplex.homologyMap ((singularChains k).map
          (TopCat.ofHom (wedgeCirclesHomotopyEquivClassifyingSpace S).toFun)) n ≫
        (classifyingSpaceSingularHomologyIsoGroupHomology k (FreeGroup S) n).hom :=
  -- `Iso.trans_hom` does not rewrite here: the two isomorphisms are composed along a
  -- definitional equality of `singularHomologyFunctor` with the homology of `singularChains`.
  congrArg (· ≫ (classifyingSpaceSingularHomologyIsoGroupHomology k (FreeGroup S) n).hom)
    ((wedgeCirclesHomotopyEquivClassifyingSpace S).singularHomologyIso_hom (ModuleCat.of k k) n)

/-- **The homology of the classifying space of a free group vanishes in degrees at least `2`.**
Milnor's classifying space of `FreeGroup S` is homotopy equivalent to the wedge of circles indexed
by `S`, so its singular homology vanishes in every degree `n ≥ 2`, with coefficients in any
abelian category with exact coproducts. -/
theorem isZero_classifyingSpace_singularHomology_freeGroup {A : Type w} [Category.{v} A]
    [HasCoproducts.{0} A] [Abelian A] [AB4OfSize.{0} A] (R : A) {n : ℕ} (hn : 2 ≤ n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor.{0} A n).obj R).obj
      (TopCat.of (classifyingSpace (FreeGroup S)))) :=
  (WedgeSum.isZero_singularHomology_circle S R hn).of_iso
    ((wedgeCirclesHomotopyEquivClassifyingSpace S).singularHomologyIso R n).symm

/-- **The group homology of a free group vanishes in degrees at least `2`**, with trivial
coefficients in any commutative ring `k`: it is the homology of a wedge of circles. -/
theorem isZero_groupHomology_freeGroup (k : Type) [CommRing k] {n : ℕ} (hn : 2 ≤ n) :
    IsZero (groupHomology (Rep.trivial k (FreeGroup S) k) n) :=
  (isZero_classifyingSpace_singularHomology_freeGroup S (ModuleCat.of k k) hn).of_iso
    (classifyingSpaceSingularHomologyIsoGroupHomology k (FreeGroup S) n).symm

variable {S}

/-- On integral first homology, `TauCeti.wedgeCirclesHomotopyEquivClassifyingSpace` sends the
Hurewicz class of a loop at the wedge point to the class in `(FreeGroup S)ᵃᵇ` of the element of
the free group it represents under `TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`. -/
theorem classifyingSpaceFirstHomologyAddEquiv_map_wedgeCirclesHomotopyEquivClassifyingSpace
    (a : FundamentalGroup (WedgeSum fun _ : S ↦ (1 : Circle)) (base _)) :
    classifyingSpaceFirstHomologyAddEquiv (FreeGroup S)
      ((HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (wedgeCirclesHomotopyEquivClassifyingSpace S).toFun)) 1).hom
          (hurewiczHomologyAddEquiv (X := TopCat.of (WedgeSum fun _ : S ↦ (1 : Circle))) (base _)
            (Additive.ofMul (Abelianization.of a)))) =
      Additive.ofMul (Abelianization.of (circleFundamentalGroupMulEquiv S a)) := by
  rw [classifyingSpaceFirstHomologyAddEquiv_homologyMap_hurewiczHomologyAddEquiv _
      (wedgeCirclesClassifyingSpaceBasepointPath S),
    classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCirclesHomotopyEquivClassifyingSpace]

/-- **The first homology of a wedge of circles agrees with the first group homology of the free
group.** Under `TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology`, the Hurewicz class of
a loop `a` at the wedge point is the class in `H₁(FreeGroup S, ℤ)` of the `1`-cycle, with
coefficient `1`, at the element of the free group that `a` represents under
`TauCeti.WedgeSum.circleFundamentalGroupMulEquiv`. -/
-- Not a simp lemma: singularChainComplexFunctor_obj_map rewrites the chain map first.
theorem _root_.FundamentalGroup.classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles
    (a : FundamentalGroup (WedgeSum fun _ : S ↦ (1 : Circle)) (base _)) :
    classifyingSpaceFirstHomologyAddEquivGroupHomology (FreeGroup S)
      ((HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (wedgeCirclesHomotopyEquivClassifyingSpace S).toFun)) 1).hom
          (hurewiczHomologyAddEquiv (X := TopCat.of (WedgeSum fun _ : S ↦ (1 : Circle))) (base _)
            (Additive.ofMul (Abelianization.of a)))) =
      groupHomology.H1π (Rep.trivial ℤ (FreeGroup S) ℤ)
        ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ (FreeGroup S) ℤ)).inv
          (Finsupp.single (circleFundamentalGroupMulEquiv S a) 1)) := by
  rw [classifyingSpaceFirstHomologyAddEquivGroupHomology_apply,
    classifyingSpaceFirstHomologyAddEquiv_map_wedgeCirclesHomotopyEquivClassifyingSpace]
  exact groupHomology.H1AddEquivOfIsTrivial_symm_tmul
    (A := Rep.trivial ℤ (FreeGroup S) ℤ) _ 1

/-- The loop going once around the `i`-th circle of the wedge corresponds, under
`TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology`, to the class in `H₁(FreeGroup S, ℤ)`
of the `1`-cycle at the generator `i` with coefficient `1`. -/
theorem classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles_expLoop (i : S) :
    classifyingSpaceFirstHomologyAddEquivGroupHomology (FreeGroup S)
      ((HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (wedgeCirclesHomotopyEquivClassifyingSpace S).toFun)) 1).hom
          (hurewiczHomologyAddEquiv (X := TopCat.of (WedgeSum fun _ : S ↦ (1 : Circle))) (base _)
            (Additive.ofMul (Abelianization.of
              (mapOfEq (incl (fun _ : S ↦ (1 : Circle)) i) (incl_apply_self i)
                (fromPath (Path.Homotopic.Quotient.mk Circle.expLoop))))))) =
      groupHomology.H1π (Rep.trivial ℤ (FreeGroup S) ℤ)
        ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ (FreeGroup S) ℤ)).inv
          (Finsupp.single (FreeGroup.of i) 1)) := by
  rw [FundamentalGroup.classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles,
    circleFundamentalGroupMulEquiv_expLoop]

end TauCeti
