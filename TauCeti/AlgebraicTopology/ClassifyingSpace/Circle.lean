/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.CWComplex
public import TauCeti.AlgebraicTopology.ClassifyingSpace.EilenbergMacLane
public import TauCeti.AlgebraicTopology.EilenbergMacLane.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Homotopy.Whitehead
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy
public import TauCeti.Topology.CWComplex.Classical.Circle

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

## Main definitions

* `TauCeti.circleToClassifyingSpace`: the based map from the circle to the classifying space of
  `ℤ` around a loop representing the generator.
* `TauCeti.circleHomotopyEquivClassifyingSpace`: the homotopy equivalence
  `Circle ≃ₕ classifyingSpace (Multiplicative ℤ)` whose forward map is
  `circleToClassifyingSpace`.

## Main results

* `TauCeti.classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_circleToClassifyingSpace`: the map
  induces the identity of `ℤ` on fundamental groups.
* `TauCeti.isWeakHomotopyEquivalence_circleToClassifyingSpace`: it is a weak homotopy equivalence.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B, Theorem 1B.8.
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
      Circle.fundamentalGroupMulEquiv 1 γ := by
  -- Both sides are homomorphisms out of `π₁(S¹) ≅ ℤ`, so it suffices to compare them on the
  -- counterclockwise loop, which the circle identification sends to the generator.
  suffices h : ((classifyingSpaceFundamentalGroupMulEquiv (Multiplicative ℤ)).toMonoidHom.comp
        (FundamentalGroup.mapOfEq circleToClassifyingSpace circleToClassifyingSpace_one)).comp
          (Circle.fundamentalGroupMulEquiv 1).symm.toMonoidHom = MonoidHom.id _ by
    simpa using congrArg (· (Circle.fundamentalGroupMulEquiv 1 γ)) h
  refine MonoidHom.ext_mint ?_
  have hgen : (Circle.fundamentalGroupMulEquiv 1).symm (Multiplicative.ofAdd 1) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop) := by
    rw [MulEquiv.symm_apply_eq, Circle.fundamentalGroupMulEquiv_expLoop]
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, hgen,
    MonoidHom.id_apply]
  -- The loop wrapped around is a representative of the class sent to the generator.
  refine (congrArg (classifyingSpaceFundamentalGroupMulEquiv _)
    ((Circle.mapOfEq_toCircle_expLoop _).trans
      (FundamentalGroup.fromPath_mk_out _))).trans ?_
  exact MulEquiv.apply_symm_apply _ _

/-- **The map from the circle to the classifying space of `ℤ` is a weak homotopy equivalence.**
Both spaces are aspherical and the map induces an isomorphism of fundamental groups. -/
theorem isWeakHomotopyEquivalence_circleToClassifyingSpace :
    circleToClassifyingSpace.IsWeakHomotopyEquivalence := by
  refine ((IsAspherical.mk inferInstance fun _ ↦ inferInstance).isWeakHomotopyEquivalence_iff
    (isEilenbergMacLaneSpaceOne_classifyingSpace (Multiplicative ℤ)).isAspherical
    circleToClassifyingSpace_one).2 ?_
  have h : ⇑(FundamentalGroup.mapOfEq circleToClassifyingSpace circleToClassifyingSpace_one) =
      (classifyingSpaceFundamentalGroupMulEquiv (Multiplicative ℤ)).symm ∘
        Circle.fundamentalGroupMulEquiv 1 := by
    funext γ
    rw [Function.comp_apply, MulEquiv.eq_symm_apply,
      classifyingSpaceFundamentalGroupMulEquiv_mapOfEq_circleToClassifyingSpace]
  rw [h]
  exact (MulEquiv.bijective _).comp (MulEquiv.bijective _)

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

end TauCeti
