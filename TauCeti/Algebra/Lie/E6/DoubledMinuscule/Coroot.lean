/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent.Map
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Root.Differential
public import TauCeti.Algebra.Lie.Matrix.IntegralCast
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# Simple-coroot differentials of the integral doubled E₆ carrier

The simple coroots in fundamental-weight coordinates define cocharacters of the integral
carrier on `V(ϖ₁) ⊕ V(ϖ₆)`. Their unit tangent vectors are exactly the brackets of the normalized
opposite simple-root differentials. This normalization holds over every commutative value ring,
including rings of characteristic three and nonreduced rings.

The six brackets form a basis of the tangent image of the weight torus. The calculation uses
the integral doubled minuscule Serre matrices, their reindexing into the carrier's `Fin 54`
coordinates, and the injective tangent inclusion into matrices. It does not identify the torus
with a maximal torus, assert that root lines exhaust weight spaces, or identify the carrier
with an independently pinned simply connected group scheme.

## Main declarations

* `corootCocharacter`: the cocharacters associated to the named simple coroots.
* `cartanVector_eq_derivationComp_corootCocharacter`: the opposite-root bracket normalization.
* `range_derivationCompLieHom_weightTorus_eq_span`: the toral tangent image.
* `cartanBasis`: the basis of that image given by the normalized Cartan vectors.

The cocharacter calculation adapts
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot` to the integral doubled carrier, using
its existing root differentials rather than differentials of a ground-ring-generated subgroup.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
-/

public section

open CategoryTheory

namespace TauCeti.E6DoubledMinuscule

noncomputable section

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

local notation "H" => CommHopfAlgCat.quotient
  (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal

variable {B : Type*} [CommRing B]

/-- The differential of the integral carrier's closed immersion into `GL₅₄`, in matrix form. -/
def tangentMatrixLieHom :
    Derivation ℤ H (Bialgebra.CounitAlgebra ℤ H B) →ₗ⁅B⁆ Matrix (Fin 54) (Fin 54) B :=
  GeneralLinear.tangentMatrixLieHom (Bialgebra.Quotient.mkBialgHom definingIdeal.toIdeal)

/-- The tangent inclusion evaluates a derivation on the generic matrix after the quotient map. -/
theorem tangentMatrixLieHom_apply (d : Derivation ℤ H (Bialgebra.CounitAlgebra ℤ H B)) :
    tangentMatrixLieHom d = GeneralLinear.tangentMatrix 54
      (HopfIdeal.quotientLieHom definingIdeal d) := by
  simpa only [tangentMatrixLieHom, HopfIdeal.quotientLieHom_apply] using
    GeneralLinear.tangentMatrixLieHom_apply
      (Bialgebra.Quotient.mkBialgHom definingIdeal.toIdeal) d

/-- The matrix realization of the tangent algebra is injective over every value ring. -/
theorem tangentMatrixLieHom_injective : Function.Injective (tangentMatrixLieHom (B := B)) :=
  GeneralLinear.tangentMatrixLieHom_injective_of_surjective _ Ideal.Quotient.mk_surjective

/-- The matrix of a normalized root differential is its integral root operator. -/
@[simp↓]
theorem tangentMatrixLieHom_rootVector (k : Fin 6 ⊕ Fin 6) :
    tangentMatrixLieHom (rootVector (B := B) k) =
      (rootIntMatrix k).map (Int.cast : ℤ → B) := by
  rw [tangentMatrixLieHom_apply, tangentMatrix_rootVector]

/-- The normalized Cartan vector is the bracket of the opposite numbered root vectors. -/
def cartanVector (i : Fin 6) : Derivation ℤ H (Bialgebra.CounitAlgebra ℤ H B) :=
  ⁅rootVector (B := B) (.inl i), rootVector (B := B) (.inr i)⁆

/-- The normalized Cartan vector is defined by its opposite-root bracket. -/
theorem cartanVector_def (i : Fin 6) :
    cartanVector (B := B) i = ⁅rootVector (B := B) (.inl i), rootVector (B := B) (.inr i)⁆ :=
  (rfl)

/-- The Cartan vector has the diagonal matrix of fundamental-weight coordinates. -/
@[simp↓]
theorem tangentMatrixLieHom_cartanVector (i : Fin 6) :
    tangentMatrixLieHom (cartanVector (B := B) i) =
      Matrix.diagonal fun a ↦ (matrixWeight a i : B) := by
  rw [cartanVector_def, LieHom.map_lie, tangentMatrixLieHom_rootVector,
    tangentMatrixLieHom_rootVector, rootIntMatrix_inl, rootIntMatrix_inr]
  have h := ((isSerreSystem.map
    (Matrix.reindexLieEquiv matrixIndexEquiv).toLieHom).map
      (matrixIntCastLieHom B)).lie_E_F_self i
  simp only [Function.comp_apply, LieEquiv.coe_toLieHom, Matrix.reindexLieEquiv_apply,
    matrixIntCastLieHom_eq_map] at h
  rw [h]
  ext a b
  simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    cartanGeneratorMatrix_apply, Matrix.diagonal_apply, matrixWeight_apply]
  split_ifs <;> simp_all

/-- The cocharacter obtained by evaluating the `i`th fundamental-weight coordinate in the
integral carrier's weight torus. -/
def corootCocharacter (i : Fin 6) : H →ₐc[ℤ] LaurentPolynomial ℤ :=
  weightTorusIntegralCoordinateMap.hom.cocharacter (Finsupp.applyAddHom i).toMultiplicative

/-- The simple-coroot cocharacter is evaluation at its fundamental-weight coordinate. -/
theorem corootCocharacter_def (i : Fin 6) :
    corootCocharacter i = weightTorusIntegralCoordinateMap.hom.cocharacter
      (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The coordinate cocharacter is the named simple coroot of the simply connected E₆ datum. -/
theorem corootCocharacter_eq_cocharacter_coroot_simpleIndex
    (ht : DynkinType.E6.Valid) (i : Fin 6) :
    corootCocharacter i = weightTorusIntegralCoordinateMap.hom.cocharacter
      (SplitTorus.cocharEquiv.symm
        ((DynkinType.E6.simplyConnectedRootDatum ht).coroot
          (DynkinType.E6.simpleIndex ht i))) := by
  rw [corootCocharacter_def]
  congr 1
  apply SplitTorus.cocharEquiv.eq_symm_apply.mpr
  have heval : SplitTorus.cocharEquiv (Finsupp.applyAddHom i).toMultiplicative =
      (Pi.single i 1 : Fin 6 → ℤ) := by
    ext j
    simp [SplitTorus.cocharEquiv_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  exact heval.trans (DynkinType.coroot_simpleIndex DynkinType.E6 ht i).symm

/-- The matrix of a simple-coroot differential is the diagonal of its weight pairings. -/
theorem tangentMatrixLieHom_derivationComp_corootCocharacter (i : Fin 6) :
    tangentMatrixLieHom
        (derivationComp (B := B) (corootCocharacter i)
          (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B))) =
      Matrix.diagonal fun a ↦ (matrixWeight a i : B) := by
  have hπ : weightTorusIntegralCoordinateMap.hom.comp
      (Bialgebra.Quotient.mkBialgHom definingIdeal.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := ℤ) matrixWeight := by
    rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
      mkQuotient_comp_weightTorusIntegralCoordinateMap,
      GeneralLinear.hom_weightTorusCoordinateMap]
  rw [tangentMatrixLieHom_apply, HopfIdeal.quotientLieHom_apply, corootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  congr 1
  ext a
  simp

/-- The opposite-root bracket is the unit tangent vector of the actual simple-coroot
cocharacter. No invertibility of the Cartan determinant or characteristic hypothesis is needed. -/
theorem cartanVector_eq_derivationComp_corootCocharacter (i : Fin 6) :
    cartanVector (B := B) i =
      derivationComp (corootCocharacter i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B)) := by
  apply tangentMatrixLieHom_injective
  rw [tangentMatrixLieHom_cartanVector, tangentMatrixLieHom_derivationComp_corootCocharacter]

/-- The weight-torus differential sends its coordinate basis to the normalized Cartan vectors. -/
theorem derivationCompLieHom_weightTorus_tangentBasis (i : Fin 6) :
    derivationCompLieHom (B := B) weightTorusIntegralCoordinateMap.hom
        (SplitTorus.tangentBasis (R := ℤ) (B := B) i) = cartanVector (B := B) i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis,
    cartanVector_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply]

/-- The tangent image of the integral weight torus is the span of the Cartan vectors. -/
theorem range_derivationCompLieHom_weightTorus_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := B) weightTorusIntegralCoordinateMap.hom).toLinearMap =
      Submodule.span B (Set.range (cartanVector (B := B))) := by
  rw [SplitTorus.range_derivationCompLieHom]
  congr 1
  apply congrArg Set.range
  funext i
  rw [cartanVector_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply]

/-- The integral weight-torus differential is injective, including over nonreduced value rings. -/
theorem derivationCompLieHom_weightTorus_injective :
    Function.Injective
      (derivationCompLieHom (B := B) weightTorusIntegralCoordinateMap.hom) := by
  apply derivationCompLieHom_injective_of_surjective
  have h := GeneralLinear.weightTorusCoordinateMap_surjective (R := ℤ) matrixWeight
    span_range_matrixWeight_eq_top
  rw [← mkQuotient_comp_weightTorusIntegralCoordinateMap,
    CommHopfAlgCat.hom_comp, BialgHom.coe_comp] at h
  exact Function.Surjective.of_comp h

/-- The six normalized Cartan vectors are independent over every commutative value ring. -/
theorem linearIndependent_cartanVector : LinearIndependent B (cartanVector (B := B)) := by
  change LinearIndependent B (fun i : Fin 6 ↦ cartanVector (B := B) i)
  simpa only [cartanVector_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply] using
    SplitTorus.linearIndependent_derivationComp_cocharacter (B := B)
      weightTorusIntegralCoordinateMap.hom derivationCompLieHom_weightTorus_injective

/-- The normalized Cartan vectors form a basis of their span, the toral tangent image. -/
def cartanBasis :
    Module.Basis (Fin 6) B (Submodule.span B (Set.range (cartanVector (B := B)))) :=
  Module.Basis.span linearIndependent_cartanVector

/-- Including a basis vector of the toral tangent image recovers the normalized Cartan vector. -/
@[simp↓]
theorem coe_cartanBasis (i : Fin 6) :
    (cartanBasis (B := B) i : Derivation ℤ H (Bialgebra.CounitAlgebra ℤ H B)) =
      cartanVector i :=
  Module.Basis.coe_span_apply linearIndependent_cartanVector i

end

end TauCeti.E6DoubledMinuscule
