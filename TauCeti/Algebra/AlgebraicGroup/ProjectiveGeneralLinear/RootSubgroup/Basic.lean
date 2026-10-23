/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Subgroup
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Basic
import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion
import TauCeti.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Closed elementary root subgroups of the projective general linear group

The elementary root map `xᵢⱼ : 𝔾ₐ → PGLₙ` acts on the matrix algebra by conjugation
with `1 + c Eᵢⱼ`. It is a closed immersion over any commutative base ring: the
coefficient of `Eᵢⱼ` in the image of `Eⱼⱼ` recovers the additive parameter. Thus
passing from `GLₙ` to its adjoint group does not collapse these root subgroups, even
in characteristics dividing `n` or over nonreduced rings.

The parametrized closed subgroups and their type-A Chevalley relations supply the
root maps used to normalize a pinning of the adjoint group. The construction follows
`GeneralLinear.rootSubgroupCoordinateMap` through `ProjectiveGeneralLinear.conjugationMap`;
the closed-subgroup packaging follows `GeneralLinear.Root.ClosedImmersion`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
-/

public section

open AlgebraicGeometry CategoryTheory Matrix WithConv
open scoped commutatorElement

namespace TauCeti.ProjectiveGeneralLinear

universe u w

noncomputable section

variable {R : Type u} [CommRing R] {n : ℕ} {i j k l : Fin n}

/-- The coordinate morphism of the elementary root map to `PGLₙ`: compose the
conjugation representation with the general-linear root map, contravariantly. -/
def rootSubgroupCoordinateMap (hij : i ≠ j) :
    coordinateHopfAlgebra n R ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  conjugationMap n R ≫ GeneralLinear.rootSubgroupCoordinateMap hij

/-- The projective root coordinate map factors through the general-linear root map. -/
theorem rootSubgroupCoordinateMap_def (hij : i ≠ j) :
    rootSubgroupCoordinateMap (R := R) hij =
      conjugationMap n R ≫ GeneralLinear.rootSubgroupCoordinateMap hij := (rfl)

/-- The map of convolution points induced by the elementary root coordinate map. -/
def rootSubgroupPoints (A : CommAlgCat.{w} R) (hij : i ≠ j) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra n R →ₐ[R] A) :=
  BialgHom.mapDomain (rootSubgroupCoordinateMap hij).hom

/-- The canonical map of points is the named elementary root homomorphism.
Use this as an explicit rewrite between the bundled point presentations. -/
theorem mapPointsFunctor_rootSubgroupCoordinateMap_app (A : CommAlgCat.{w} R)
    (hij : i ≠ j)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    (CommHopfAlgCat.Hom.mapPointsFunctor (rootSubgroupCoordinateMap hij)).app A f =
      rootSubgroupPoints A hij f := (rfl)

/-- In the matrix-unit representation, a root map is the conjugation matrix of
`1 + X Eᵢⱼ` and `1 - X Eᵢⱼ`. -/
theorem map_genericMatrix_rootSubgroupCoordinateMap (hij : i ≠ j) :
    (GeneralLinear.genericMatrix R (n * n)).map
        (CommHopfAlgCat.mkQuotient _ (definingHopfIdeal n R) ≫
          rootSubgroupCoordinateMap hij).hom =
      conjugationMatrix
        (Matrix.transvection i j (SymmetricAlgebra.ι R R 1))
        (Matrix.transvection i j (-SymmetricAlgebra.ι R R 1)) := by
  have hroot : (GeneralLinear.genericMatrix R n).map
      (GeneralLinear.rootSubgroupCoordinateMap (R := R) hij).hom =
        Matrix.transvection i j (SymmetricAlgebra.ι R R 1) := by
    ext a b
    rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply,
      GeneralLinear.rootSubgroupCoordinateMap_apply_X]
    rfl
  have hinv : (Matrix.transvection i j (SymmetricAlgebra.ι R R 1))⁻¹ =
      Matrix.transvection i j (-SymmetricAlgebra.ι R R 1) := by
    apply Matrix.inv_eq_left_inv
    simp [Matrix.transvection_mul_transvection_same i j hij]
  rw [rootSubgroupCoordinateMap_def, ← Category.assoc, CommHopfAlgCat.hom_comp,
    BialgHom.coe_comp, ← Matrix.map_map, map_genericMatrix_conjugationMap,
    conjugationMatrix_map]
  simp only [← BialgHom.coe_toAlgHom, GeneralLinear.map_inv_genericMatrix]
  simp only [BialgHom.coe_toAlgHom, hroot, hinv]

/-- The coefficient taking `Eⱼⱼ` to `Eᵢⱼ` pulls back to the additive parameter.
This is the coordinate that proves the root map is a closed immersion. -/
@[simp↓]
theorem rootSubgroupCoordinateMap_parameter (hij : i ≠ j) :
    (rootSubgroupCoordinateMap (R := R) hij).hom
      ((CommHopfAlgCat.mkQuotient _ (definingHopfIdeal n R)).hom
        (GeneralLinear.genericMatrix R (n * n)
          (finProdFinEquiv (i, j)) (finProdFinEquiv (j, j)))) =
      SymmetricAlgebra.ι R R 1 := by
  have h := congrFun (congrFun (map_genericMatrix_rootSubgroupCoordinateMap (R := R) hij)
    (finProdFinEquiv (i, j))) (finProdFinEquiv (j, j))
  simpa [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, hij, hij.symm] using h

/-- The coordinate map of each elementary projective root subgroup is surjective. -/
theorem rootSubgroupCoordinateMap_surjective (hij : i ≠ j) :
    Function.Surjective (rootSubgroupCoordinateMap (R := R) hij).hom := by
  apply (rootSubgroupCoordinateMap (R := R) hij).hom.toAlgHom.surjective_of_ι_one_mem_range
  exact ⟨_, rootSubgroupCoordinateMap_parameter hij⟩

/-- Evaluation of a root-subgroup point is precomposition with its coordinate map. -/
@[simp]
theorem rootSubgroupPoints_apply_apply (A : CommAlgCat.{w} R) (hij : i ≠ j)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A))
    (x : coordinateHopfAlgebra n R) :
    (rootSubgroupPoints A hij f).ofConv x = f.ofConv ((rootSubgroupCoordinateMap hij).hom x) :=
  CommHopfAlgCat.Hom.mapPointsFunctor_app_apply_apply _ _ _ _

/-- On every value algebra, the projective root map is conjugation by the
transvection of the additive parameter. Use `rw` with this formula; simplifier
matching of the bundled point presentations may require explicit arguments. -/
theorem pointsMulEquiv_rootSubgroupPoints (A : CommAlgCat.{w} R) (hij : i ≠ j)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv n R A (rootSubgroupPoints A hij f) =
      Matrix.GeneralLinearGroup.innerAut (transvectionUnit hij
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f))) := by
  -- Express the composite point as a general-linear root point followed by conjugation.
  -- Unfolding here only identifies precomposition with the composite coordinate map.
  simp only [rootSubgroupPoints, rootSubgroupCoordinateMap_def, BialgHom.mapDomain_apply,
    CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom, ← AlgHom.comp_assoc]
  rw [pointsMulEquiv_conjugationMap n R A
    (toConv (f.ofConv.comp (GeneralLinear.rootSubgroupCoordinateMap hij).hom.toAlgHom))]
  congr 1
  apply Units.ext
  ext a b
  simp only [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.pointToGeneralLinear_apply,
    AlgHom.comp_apply, BialgHom.coe_toAlgHom]
  rw [GeneralLinear.rootSubgroupCoordinateMap_apply_X]
  simp [coe_transvectionUnit, Matrix.transvection, Matrix.one_apply, Matrix.single_apply,
    AdditiveGroup.toAdd_gaPointsMulEquiv]
  split_ifs <;> simp_all

/-- Root-subgroup points are natural in the commutative value algebra. -/
theorem mapPoints_rootSubgroupPoints {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (hij : i ≠ j)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    HopfAlgebra.mapPoints φ (rootSubgroupPoints A hij f) =
      rootSubgroupPoints B hij (HopfAlgebra.mapPoints φ f) :=
  CommHopfAlgCat.Hom.mapPointsFunctor_naturality_apply _ _ _

/-- Distinct additive parameters give distinct projective root-subgroup points. -/
theorem rootSubgroupPoints_injective (A : CommAlgCat.{w} R) (hij : i ≠ j) :
    Function.Injective (rootSubgroupPoints A (R := R) hij) :=
  CommHopfAlgCat.Hom.mapPointsFunctor_app_injective_of_surjective _
    (rootSubgroupCoordinateMap_surjective hij) A

/-- Root-subgroup values at non-chaining index pairs commute. -/
theorem commute_rootSubgroupPoints (A : CommAlgCat.{w} R)
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    Commute (rootSubgroupPoints A hij f) (rootSubgroupPoints A hkl g) := by
  apply Commute.of_map (pointsMulEquiv n R A).injective
  rw [pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints]
  exact (commute_transvectionUnit hij hkl hjk hli
      (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f))
      (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv g))).map
        Matrix.GeneralLinearGroup.innerAut

/-- The type-A Chevalley relation in `PGLₙ`: the commutator of `xᵢⱼ(c)` and
`xⱼₗ(d)` is `xᵢₗ(cd)`. The parameter product is in the value algebra. -/
theorem commutatorElement_rootSubgroupPoints (A : CommAlgCat.{w} R)
    (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (f g : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    ⁅rootSubgroupPoints A hij f, rootSubgroupPoints A hjl g⁆ =
      rootSubgroupPoints A hil (AdditiveGroup.gaPointParamMul f g) := by
  apply (pointsMulEquiv n R A).injective
  rw [map_commutatorElement, pointsMulEquiv_rootSubgroupPoints,
    pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints,
    ← map_commutatorElement, commutatorElement_transvectionUnit hij hjl hil]
  simp only [AdditiveGroup.toAdd_gaPointsMulEquiv, AdditiveGroup.gaPointParamMul_apply_ι]

/-- The elementary root map `𝔾ₐ → PGLₙ`, acting by conjugation with `1 + c Eᵢⱼ`. -/
def rootSubgroup (hij : i ≠ j) : AdditiveGroup.groupScheme R ⟶ groupScheme n R :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (rootSubgroupCoordinateMap hij).op

/-- The root map is relative spectrum of its coordinate morphism, with the named
presentation of the additive group. -/
theorem rootSubgroup_def (hij : i ≠ j) :
    rootSubgroup (R := R) hij = eqToHom (AdditiveGroup.groupScheme_def R) ≫
      (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
        (rootSubgroupCoordinateMap hij).op := (rfl)

/-- Each elementary root map identifies the additive group with a closed subscheme
of `PGLₙ`, over every commutative base ring. -/
instance isClosedImmersion_rootSubgroup (hij : i ≠ j) :
    IsClosedImmersion (rootSubgroup (R := R) hij).hom.hom.left := by
  rw [rootSubgroup_def]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_iff
    (AdditiveGroup.groupScheme_def R) _).mpr (rootSubgroupCoordinateMap_surjective hij)

/-- The closed additive root subgroup of `PGLₙ` with its elementary parametrization. -/
def rootSubgroupClosedSubgroup (hij : i ≠ j) : ClosedSubgroupScheme (groupScheme n R) :=
  ClosedSubgroupScheme.mk (rootSubgroup hij)

/-- The closed root subgroup is represented by the elementary root map. -/
@[simp]
theorem coe_rootSubgroupClosedSubgroup (hij : i ≠ j) :
    (rootSubgroupClosedSubgroup (R := R) hij).1 = Subobject.mk (rootSubgroup hij) :=
  ClosedSubgroupScheme.coe_mk _

/-- The closed projective root subgroup is canonically isomorphic to the additive group. -/
def rootSubgroupClosedSubgroupIso (hij : i ≠ j) :
    ((rootSubgroupClosedSubgroup (R := R) hij).1 :
      Grp (Over (Spec (CommRingCat.of R)))) ≅ AdditiveGroup.groupScheme R :=
  ClosedSubgroupScheme.mkIso (rootSubgroup hij)

/-- The additive parametrization followed by the closed subgroup inclusion is the root map. -/
@[simp]
theorem rootSubgroupClosedSubgroupIso_inv_comp_arrow (hij : i ≠ j) :
    (rootSubgroupClosedSubgroupIso (R := R) hij).inv ≫
        (rootSubgroupClosedSubgroup (R := R) hij).1.arrow = rootSubgroup hij :=
  ClosedSubgroupScheme.mkIso_inv_comp_arrow _

end

end TauCeti.ProjectiveGeneralLinear
