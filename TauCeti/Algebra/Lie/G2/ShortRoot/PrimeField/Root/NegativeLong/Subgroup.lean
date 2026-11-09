/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.NegativeLong.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.InnerConjugation

/-!
# Negative nonsimple long-root subgroups of the short-root G₂ carrier

The roots `-(3α₁ + α₂)` and `-(3α₁ + 2α₂)` have closed additive root subgroups in the
short-root carrier over `𝔽₃`. The parametrizations are obtained by conjugating the numbered
negative long simple-root subgroup by `negativeLongConjugator`, the same root words used to
normalize `negativeLongRootVector`. The coordinate maps are surjective, so these are closed
subgroup schemes, not merely subgroups of rational points. Their evaluation formulas hold over
all commutative `𝔽₃`-algebras.

These constructions concern the explicit carrier; it is not identified with the independently
pinned simply connected group scheme of type `G₂`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 5.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The coordinate construction follows
`TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup`.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.G2ShortRoot.PrimeField

universe v w

noncomputable section

/-- The negative nonsimple long-root point with the normalization of `negativeLongRootVector`.
Index zero denotes `-(3α₁ + α₂)` and index one denotes `-(3α₁ + 2α₂)`. -/
def negativeLongRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Multiplicative A →* points A :=
  (MulAut.conj (pointsMap (Algebra.ofId (ZMod 3) A) (negativeLongConjugator i))).toMonoidHom.comp
    (rootSubgroupPoints (.inr 1) A)

/-- The parametrization is conjugation of the numbered negative long simple-root subgroup. -/
theorem negativeLongRootSubgroupPoints_apply (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    negativeLongRootSubgroupPoints i A u =
      pointsMap (Algebra.ofId (ZMod 3) A) (negativeLongConjugator i) *
        rootSubgroupPoints (.inr 1) A u *
          (pointsMap (Algebra.ofId (ZMod 3) A) (negativeLongConjugator i))⁻¹ :=
  (rfl)

private theorem coe_negativeSimpleLong (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (u : Multiplicative A) :
    ((rootSubgroupPoints (.inr 1) A u : Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      1 + u.toAdd • (tangentMatrix (rootVector (.inr 1))).map (algebraMap (ZMod 3) A) := by
  rw [coe_rootSubgroupPoints, IntegralToralClosure.coe_rootSubgroupPoints,
    tangentMatrix_rootVector]
  simp [rootDividedSquareMatrix_inr, Matrix.map_map, Function.comp_def]

/-- The root parameter is linear, with exactly the matrix normalization of the previously
constructed negative long-root vector. This holds even over nonreduced coefficient algebras. -/
@[simp]
theorem coe_negativeLongRootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : Multiplicative A) :
    ((negativeLongRootSubgroupPoints i A u : Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      1 + u.toAdd • (tangentMatrix (negativeLongRootVector i)).map
        (algebraMap (ZMod 3) A) := by
  rw [negativeLongRootSubgroupPoints_apply,
    ← map_inv (pointsMap (Algebra.ofId (ZMod 3) A))]
  simp only [Subgroup.coe_mul, Units.val_mul, coe_pointsMap_ofId]
  rw [coe_negativeSimpleLong, negativeLongRootVector_def, tangentMatrix_conjugateTangent]
  simp [mul_add, add_mul, ← Matrix.map_mul]

/-- The root parameter is recovered faithfully over every coefficient algebra. -/
theorem negativeLongRootSubgroupPoints_injective (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] : Function.Injective (negativeLongRootSubgroupPoints i A) := by
  intro u v h
  have hm := congrArg (fun g : points A =>
    ((g : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) h
  rw [coe_negativeLongRootSubgroupPoints, coe_negativeLongRootSubgroupPoints,
    tangentMatrix_negativeLongRootVector] at hm
  apply Multiplicative.toAdd.injective
  fin_cases i
  · have he := congrFun (congrFun hm 4) 0
    simpa using he
  · have he := congrFun (congrFun hm 5) 0
    simpa using he

/-- Coefficient change preserves the negative long-root parameters. -/
@[simp]
theorem pointsMap_negativeLongRootSubgroupPoints {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] [Algebra (ZMod 3) A] [Algebra (ZMod 3) B]
    (f : A →ₐ[ZMod 3] B) (i : Fin 2) (u : Multiplicative A) :
    pointsMap f (negativeLongRootSubgroupPoints i A u) =
      negativeLongRootSubgroupPoints i B (Multiplicative.ofAdd (f u.toAdd)) := by
  simp only [negativeLongRootSubgroupPoints_apply, map_mul, map_inv,
    pointsMap_rootSubgroupPoints]
  have hcomp : f.comp (Algebra.ofId (ZMod 3) A) = Algebra.ofId (ZMod 3) B := by ext
  rw [← MonoidHom.comp_apply, ← pointsMap_comp, hcomp]

/-- Pullback of a negative nonsimple long-root subgroup: inner conjugation followed by the
negative long simple-root coordinate map. -/
def negativeLongRootSubgroupCoordinateMap (i : Fin 2) :
    carrierAlgebra ⟶ AdditiveGroup.coordinateHopfAlgebra (ZMod 3) :=
  (CommHopfAlgCat.innerConjugationIso carrierAlgebra
    ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm
      (negativeLongConjugator i))).hom ≫
    CommHopfAlgCat.commonKernelLift generator (.inl (.inr 1))

/-- The defining pullback of the negative nonsimple long-root parametrization. -/
theorem negativeLongRootSubgroupCoordinateMap_def (i : Fin 2) :
    negativeLongRootSubgroupCoordinateMap i =
      (CommHopfAlgCat.innerConjugationIso carrierAlgebra
        ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm
          (negativeLongConjugator i))).hom ≫
        CommHopfAlgCat.commonKernelLift generator (.inl (.inr 1)) := (rfl)

/-- The negative nonsimple long-root coordinate maps are surjective. -/
theorem negativeLongRootSubgroupCoordinateMap_surjective (i : Fin 2) :
    Function.Surjective (negativeLongRootSubgroupCoordinateMap i).hom := by
  rw [negativeLongRootSubgroupCoordinateMap, CommHopfAlgCat.hom_comp]
  exact (CommHopfAlgCat.commonKernelLift_surjective_of_surjective generator (.inl (.inr 1))
    (generator_surjective _)).comp
      (ConcreteCategory.bijective_of_isIso
        (CommHopfAlgCat.innerConjugationIso carrierAlgebra
          ((pointsMulEquiv (CommAlgCat.of (ZMod 3) (ZMod 3))).symm
            (negativeLongConjugator i))).hom).2

/-- The coordinate map evaluates to the displayed conjugate over every value algebra. -/
theorem pointsMulEquiv_negativeLongRootSubgroupCoordinateMap (i : Fin 2)
    (A : Type v) [CommRing A] [Algebra (ZMod 3) A]
    (q : HopfAlgebra.points (H := AdditiveGroup.coordinateHopfAlgebra (ZMod 3))
      (CommAlgCat.of (ZMod 3) A)) :
    pointsMulEquiv (CommAlgCat.of (ZMod 3) A)
        ((CommHopfAlgCat.Hom.mapPointsFunctor
          (negativeLongRootSubgroupCoordinateMap i)).app (CommAlgCat.of (ZMod 3) A) q) =
      negativeLongRootSubgroupPoints i A (AdditiveGroup.gaPointsMulEquiv q) := by
  rw [negativeLongRootSubgroupCoordinateMap,
    CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply,
    CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom]
  -- The composed functors use definitionally equal presentations of the point group.
  erw [HopfAlgebra.innerConjugationPointNatIso_hom_app_apply, map_mul, map_mul, map_inv]
  rw [pointsMulEquiv_extendPoint, MulEquiv.apply_symm_apply,
    pointsMulEquiv_commonKernelLift_root,
    negativeLongRootSubgroupPoints_apply]

/-- The closed additive subgroup scheme at either negative nonsimple long root. -/
def negativeLongRootSubgroup (i : Fin 2) :
    AdditiveGroup.groupScheme (ZMod 3) ⟶ groupScheme :=
  eqToHom (AdditiveGroup.groupScheme_def (ZMod 3)) ≫
    (hopfSpec (CommRingCat.of (ZMod 3))).map (negativeLongRootSubgroupCoordinateMap i).op ≫
      eqToHom (by rw [groupScheme_def, definingIdeal_def])

/-- The subgroup scheme is represented by its named coordinate pullback. -/
theorem negativeLongRootSubgroup_def (i : Fin 2) :
    negativeLongRootSubgroup i =
      eqToHom (AdditiveGroup.groupScheme_def (ZMod 3)) ≫
        (hopfSpec (CommRingCat.of (ZMod 3))).map (negativeLongRootSubgroupCoordinateMap i).op ≫
          eqToHom (by rw [groupScheme_def, definingIdeal_def]) := (rfl)

/-- Each negative nonsimple long-root parametrization is a closed immersion. -/
instance isClosedImmersion_negativeLongRootSubgroup (i : Fin 2) :
    IsClosedImmersion (negativeLongRootSubgroup i).hom.hom.left := by
  rw [negativeLongRootSubgroup]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (AdditiveGroup.groupScheme_def (ZMod 3))
    (by rw [groupScheme_def, definingIdeal_def]) (negativeLongRootSubgroupCoordinateMap i)).2
      (negativeLongRootSubgroupCoordinateMap_surjective i)

end

end TauCeti.G2ShortRoot.PrimeField
