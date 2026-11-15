/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
public import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
public import TauCeti.AlgebraicTopology.ClassifyingSpace.FirstHomology
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Homology
public import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Homotopy.Whitehead
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy
public import TauCeti.Topology.CWComplex.Classical.Circle
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# The circle is the classifying space of `ℤ`

Milnor's classifying space `classifyingSpace (Multiplicative ℤ)` is homotopy equivalent to the
circle, by a homotopy equivalence that induces the identity of `ℤ` under the identifications of
both fundamental groups with `ℤ`.

The equivalence is the map `circleToClassifyingSpace`, which wraps the circle once around a loop
at the base point of the classifying space representing the generator `ofAdd 1` of `ℤ`. Under the
isomorphisms `Circle.fundamentalGroupMulEquiv`, the degree of a loop in the circle, and
`classifyingSpaceFundamentalGroupMulEquiv`, the map induces the identity of `ℤ`
(`classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_circleToClassifyingSpace`): both sides are
homomorphisms out of `ℤ` that agree on the counterclockwise loop. Both spaces are aspherical, so
the map is a weak homotopy equivalence (`TauCeti.IsAspherical.isWeakHomotopyEquivalence_iff`), and
both are CW complexes, so Whitehead's theorem makes it a homotopy equivalence.

Through this equivalence the homology of the circle is the group homology of `ℤ`. In every degree,
the singular homology of the circle with coefficients in a commutative ring `k` is Mathlib's group
homology of `ℤ` with trivial coefficients `k` (`TauCeti.circleSingularHomologyIsoGroupHomology`).
In degree one this identification agrees with the degree of loops: the integral homology class of
a loop `γ` at `1` goes to the class of its degree `Circle.degree γ`, both in the abelianization of
`ℤ` (`TauCeti.classifyingSpaceFirstHomologyAddEquiv_circleToClassifyingSpace_loopClass`) and
in Mathlib's first group homology
(`TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology_circleToClassifyingSpace_loopClass`).
Since `Circle.expLoop` has degree one (`Circle.degree_expLoop`), the counterclockwise loop goes to
the generator `ofAdd 1`.

## Main definitions

* `TauCeti.circleToClassifyingSpace`: the based map from the circle to the classifying space of
  `ℤ` around a loop representing the generator.
* `TauCeti.circleHomotopyEquivClassifyingSpace`: the homotopy equivalence
  `Circle ≃ₕ classifyingSpace (Multiplicative ℤ)` whose forward map is
  `circleToClassifyingSpace`.
* `TauCeti.circleSingularHomologyIsoGroupHomology`: the isomorphism `Hₙ(S¹; k) ≅ Hₙ(ℤ, k)`.

## Main results

* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_circleToClassifyingSpace`: the map
  induces the identity of `ℤ` on fundamental groups.
* `TauCeti.isWeakHomotopyEquivalence_circleToClassifyingSpace`: it is a weak homotopy equivalence.
* `TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology_circleToClassifyingSpace_loopClass`:
  in degree one, the class of a loop goes to the group-homology class of its degree.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B, Theorem 1B.8.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section II.4.
* J. Milnor, *Construction of universal bundles, II*, Ann. of Math. 63 (1956), 430--436.
-/

public section

noncomputable section

namespace TauCeti

open scoped Topology Topology.Homotopy

/-- The based map from the circle to the classifying space of `ℤ` that goes once around a loop at
the base point representing the generator `ofAdd 1` of `ℤ`. The point `exp (2πit)` goes to the
value of the loop at `t`. -/
def circleToClassifyingSpace : C(Circle, classifyingSpace (Multiplicative ℤ)) :=
  (Quotient.out (FundamentalGroup.toPath
    ((classifyingSpaceFundamentalGroupMulEquiv (Multiplicative ℤ)).symm
      (Multiplicative.ofAdd 1)))).toCircle

/-- The map from the circle preserves the base points. -/
@[simp]
theorem circleToClassifyingSpace_one :
    circleToClassifyingSpace 1 = classifyingSpaceBasepoint (Multiplicative ℤ) :=
  Path.toCircle_one _

/-- **The map from the circle induces the identity of `ℤ` on fundamental groups**, under the
identification `Circle.fundamentalGroupMulEquiv` of `π₁(S¹)` with `ℤ` by the degree, and the
identification `classifyingSpaceFundamentalGroupMulEquiv` of the fundamental group of the
classifying space with `ℤ`. -/
@[simp]
theorem classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_circleToClassifyingSpace
    (γ : FundamentalGroup Circle 1) :
    classifyingSpaceFundamentalGroupMulEquiv (Multiplicative ℤ)
        (FundamentalGroup.mapOfEq circleToClassifyingSpace circleToClassifyingSpace_one γ) =
      Circle.fundamentalGroupMulEquiv 1 γ :=
  Circle.apply_mapOfEq_toCircle_out_symm_ofAdd_one _ γ

/-- **The map from the circle to the classifying space of `ℤ` is a weak homotopy equivalence.**
Both spaces are aspherical and the map induces an isomorphism of fundamental groups. -/
theorem isWeakHomotopyEquivalence_circleToClassifyingSpace :
    circleToClassifyingSpace.IsWeakHomotopyEquivalence := by
  refine ((IsAspherical.mk inferInstance fun _ ↦ inferInstance).isWeakHomotopyEquivalence_iff
    (isEilenbergMacLaneSpaceOne_classifyingSpace (Multiplicative ℤ)).isAspherical
    circleToClassifyingSpace_one).2
    (Circle.bijective_mapOfEq_toCircle_out_symm_ofAdd_one _)

/-- **The circle is homotopy equivalent to the classifying space of `ℤ`**, by Whitehead's
theorem applied to `circleToClassifyingSpace`. Its forward map induces the identity of `ℤ` on
fundamental groups
(`classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_circleToClassifyingSpace`). -/
def circleHomotopyEquivClassifyingSpace :
    ContinuousMap.HomotopyEquiv Circle (classifyingSpace (Multiplicative ℤ)) :=
  isWeakHomotopyEquivalence_circleToClassifyingSpace.homotopyEquiv

/-- The forward map of the homotopy equivalence is `circleToClassifyingSpace`. -/
@[simp]
theorem circleHomotopyEquivClassifyingSpace_toFun :
    circleHomotopyEquivClassifyingSpace.toFun = circleToClassifyingSpace :=
  isWeakHomotopyEquivalence_circleToClassifyingSpace.homotopyEquiv_toFun

/-! ### Homology -/

section Homology

open CategoryTheory HurewiczOne groupHomology

/-- **The first homology of the circle, through the classifying space of `ℤ`, is the degree.** The
map induced on integral first homology by `circleToClassifyingSpace`, followed by the
identification `classifyingSpaceFirstHomologyAddEquiv` of `H₁(Bℤ; ℤ)` with the abelianization of
`ℤ`, sends the homology class of a loop `γ` at `1` to the class of its degree `Circle.degree γ`. -/
-- Not a simp lemma: `singularChainComplexFunctor_obj_map` rewrites the chain map first.
theorem classifyingSpaceFirstHomologyAddEquiv_circleToClassifyingSpace_loopClass
    (γ : Path (1 : Circle) 1) :
    classifyingSpaceFirstHomologyAddEquiv (Multiplicative ℤ)
      ((HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom circleToClassifyingSpace)) 1).hom
          (H₁AddEquivHomology _ (loopClass (X := TopCat.of Circle) γ))) =
      Additive.ofMul (Group.Abelianization.of (Multiplicative.ofAdd (Circle.degree γ))) := by
  rw [← hurewiczHomologyAddEquiv_ofMul_of_mk,
    homologyMap_hurewiczHomologyAddEquiv_mapOfEq _ circleToClassifyingSpace_one, toMul_ofMul,
    Group.Abelianization.map_of, classifyingSpaceFirstHomologyAddEquiv_hurewiczHomologyAddEquiv]
  -- `TopCat.ofHom circleToClassifyingSpace` has underlying map `circleToClassifyingSpace` by
  -- `TopCat.hom_ofHom`, which `rw` cannot reach under the dependent base point proof.
  simp only [TopCat.hom_ofHom,
    classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_circleToClassifyingSpace,
    Circle.fundamentalGroupMulEquiv_fromPath]

/-- **The first homology of the circle is the first group homology of `ℤ`, by the degree.** The map
induced on integral first homology by `circleToClassifyingSpace`, followed by the identification
`classifyingSpaceFirstHomologyAddEquivGroupHomology` of `H₁(Bℤ; ℤ)` with Mathlib's first group
homology, sends the homology class of a loop `γ` at `1` to the class of the cycle supported at its
degree `Circle.degree γ` with coefficient one. -/
-- Not a simp lemma: `singularChainComplexFunctor_obj_map` rewrites the chain map first.
theorem classifyingSpaceFirstHomologyAddEquivGroupHomology_circleToClassifyingSpace_loopClass
    (γ : Path (1 : Circle) 1) :
    classifyingSpaceFirstHomologyAddEquivGroupHomology (Multiplicative ℤ)
      ((HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom circleToClassifyingSpace)) 1).hom
          (H₁AddEquivHomology _ (loopClass (X := TopCat.of Circle) γ))) =
      H1π (Rep.trivial ℤ (Multiplicative ℤ) ℤ)
        ((cycles₁IsoOfIsTrivial (Rep.trivial ℤ (Multiplicative ℤ) ℤ)).inv
          (Finsupp.single (Multiplicative.ofAdd (Circle.degree γ)) 1)) := by
  rw [classifyingSpaceFirstHomologyAddEquivGroupHomology_apply,
    classifyingSpaceFirstHomologyAddEquiv_circleToClassifyingSpace_loopClass]
  exact H1AddEquivOfIsTrivial_symm_tmul (A := Rep.trivial ℤ (Multiplicative ℤ) ℤ) _ 1

variable (k : Type) [CommRing k]

/-- **The homology of the circle is the group homology of `ℤ`.** For every commutative ring `k`,
the singular homology `Hₙ(S¹; k)` of the circle is Mathlib's group homology `Hₙ(ℤ, k)` of the
trivial representation: the map induced by `TauCeti.circleHomotopyEquivClassifyingSpace` followed
by `TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`. -/
def circleSingularHomologyIsoGroupHomology (n : ℕ) :
    ((singularChains k).obj (TopCat.of Circle)).homology n ≅
      groupHomology (Rep.trivial k (Multiplicative ℤ) k) n :=
  circleHomotopyEquivClassifyingSpace.singularHomologyIso (ModuleCat.of k k) n ≪≫
    classifyingSpaceSingularHomologyIsoGroupHomology k (Multiplicative ℤ) n

/-- The identification `TauCeti.circleSingularHomologyIsoGroupHomology` is the map induced on
homology by `TauCeti.circleToClassifyingSpace`, followed by
`TauCeti.classifyingSpaceSingularHomologyIsoGroupHomology`. -/
theorem circleSingularHomologyIsoGroupHomology_hom (n : ℕ) :
    (circleSingularHomologyIsoGroupHomology k n).hom =
      HomologicalComplex.homologyMap ((singularChains k).map
          (TopCat.ofHom circleToClassifyingSpace)) n ≫
        (classifyingSpaceSingularHomologyIsoGroupHomology k (Multiplicative ℤ) n).hom := by
  rw [← circleHomotopyEquivClassifyingSpace_toFun]
  -- `Iso.trans_hom` does not rewrite here: the two isomorphisms are composed along a
  -- definitional equality of `singularHomologyFunctor` with the homology of `singularChains`.
  exact congrArg (· ≫ (classifyingSpaceSingularHomologyIsoGroupHomology k (Multiplicative ℤ) n).hom)
    (circleHomotopyEquivClassifyingSpace.singularHomologyIso_hom (ModuleCat.of k k) n)

end Homology

end TauCeti
