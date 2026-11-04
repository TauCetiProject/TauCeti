/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.D4.Tripled.Root.Differential
import TauCeti.Algebra.Lie.Presentation.Serre.IntegralCast
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# Simple-coroot differentials of the integral tripled D₄ carrier

The simple coroots define cocharacters through the weight torus of the integral tripled
carrier. Their differentials at the unit tangent vector are the brackets of the normalized
opposite simple-root vectors. These four vectors form a basis of the toral tangent image over
every commutative coefficient ring, including rings of characteristic two.

This identifies the coroot normalization of the root parametrizations. It asserts neither
that the root lines exhaust the adjoint weight spaces nor that the carrier is identified
with an independently pinned simply connected group scheme. Constructions on this carrier
transfer to that pinned group only along such an identification, once proved.

## Main declarations

* `corootCocharacter`: the cocharacter from a fundamental-weight coordinate.
* `corootCocharacter_eq_cocharacter_coroot_simpleIndex`: identification with the named coroot.
* `cartanVector_eq_derivationComp_corootCocharacter`: the opposite-root bracket identity.
* `range_derivationCompLieHom_weightTorusIntegralCoordinateMap_eq_span`: the toral tangent image.
* `cartanBasis`: the basis of this image given by the normalized Cartan vectors.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.

The construction adapts `TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot`, using the
integral tripled root differentials and the tripled minuscule Serre matrices.
-/

public section

namespace TauCeti.D4Tripled

open CategoryTheory DynkinType

noncomputable section

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The simple cocharacter obtained by evaluating the `i`-th fundamental-weight coordinate
and then including the weight torus in the integral carrier. -/
def corootCocharacter (i : Fin 4) :
    (GeneralLinear.coordinateHopfAlgebra ℤ 24 ⧸ definingIdeal.toIdeal) →ₐc[ℤ]
      LaurentPolynomial ℤ :=
  weightTorusIntegralCoordinateMap.hom.cocharacter (Finsupp.applyAddHom i).toMultiplicative

/-- The simple cocharacter is induced by the corresponding fundamental-weight coordinate. -/
theorem corootCocharacter_def (i : Fin 4) :
    corootCocharacter i =
      weightTorusIntegralCoordinateMap.hom.cocharacter
        (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The coordinate cocharacter is the named simple coroot of the simply connected D₄ datum,
with the existing Bourbaki numbering. -/
theorem corootCocharacter_eq_cocharacter_coroot_simpleIndex
    (ht : (D 4).Valid) (i : Fin 4) :
    corootCocharacter i =
      weightTorusIntegralCoordinateMap.hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          (((D 4).simplyConnectedRootDatum ht).coroot ((D 4).simpleIndex ht i))) := by
  rw [corootCocharacter_def]
  congr 1
  apply SplitTorus.cocharEquiv.eq_symm_apply.mpr
  exact (SplitTorus.cocharEquiv_applyAddHom i).trans ((D 4).coroot_simpleIndex ht i).symm

variable {B : Type*} [CommRing B]

/-- The normalized Cartan vector is the bracket of opposite normalized simple-root vectors. -/
def cartanVector (i : Fin 4) :
    Derivation ℤ (GeneralLinear.coordinateHopfAlgebra ℤ 24 ⧸ definingIdeal.toIdeal)
      (Bialgebra.CounitAlgebra ℤ
        (GeneralLinear.coordinateHopfAlgebra ℤ 24 ⧸ definingIdeal.toIdeal) B) :=
  ⁅rootVector (B := B) (.inl i), rootVector (B := B) (.inr i)⁆

/-- The Cartan vector is the bracket of the normalized opposite simple-root vectors. -/
theorem cartanVector_def (i : Fin 4) :
    cartanVector (B := B) i =
      ⁅rootVector (B := B) (.inl i), rootVector (B := B) (.inr i)⁆ :=
  (rfl)

/-- Coefficient change preserves the normalized integral Cartan vector. -/
-- Match before simplification changes the counit-indexed integer module structure.
@[simp↓]
theorem mapValue_cartanVector {C : Type*} [CommRing C] (φ : B →ₐ[ℤ] C) (i : Fin 4) :
    Derivation.mapValue φ (cartanVector (B := B) i) = cartanVector (B := C) i := by
  simp only [cartanVector_def, Derivation.mapValue_lie, mapValue_rootVector]

/-- The matrix of a Cartan vector is the integral diagonal simple-coroot matrix. -/
@[simp]
theorem tangentMatrix_cartanVector (i : Fin 4) :
    GeneralLinear.tangentMatrix 24
        (HopfIdeal.quotientLieHom (B := B) definingIdeal (cartanVector (B := B) i)) =
      (cartanGeneratorMatrix i).map (Int.cast : ℤ → B) := by
  simpa only [LieHom.comp_apply, LieEquiv.coe_toLieHom,
    GeneralLinear.tangentLieEquivMatrix_apply, cartanVector_def] using
    isSerreSystem.map_lie_eq_intCast
      (e := fun i ↦ rootVector (B := B) (.inl i))
      (f := fun i ↦ rootVector (B := B) (.inr i))
      ((GeneralLinear.tangentLieEquivMatrix (R := ℤ) (B := B) 24).toLieHom.comp
        (HopfIdeal.quotientLieHom (B := B) definingIdeal))
      (fun i ↦ by simpa only [LieHom.comp_apply, LieEquiv.coe_toLieHom,
        GeneralLinear.tangentLieEquivMatrix_apply, rootMatrix_inl] using
          tangentMatrix_rootVector (B := B) (.inl i))
      (fun i ↦ by simpa only [LieHom.comp_apply, LieEquiv.coe_toLieHom,
        GeneralLinear.tangentLieEquivMatrix_apply, rootMatrix_inr] using
          tangentMatrix_rootVector (B := B) (.inr i)) i

/-- The differential of the actual simple-coroot cocharacter has the diagonal weight-pairing
matrix. The multiplicative tangent parameter is normalized to one. -/
theorem tangentMatrix_derivationComp_corootCocharacter (i : Fin 4) :
    GeneralLinear.tangentMatrix 24
        (HopfIdeal.quotientLieHom (B := B) definingIdeal
          (derivationComp (corootCocharacter i)
            ((MultiplicativeGroup.tangentLinearEquiv (B := B)).symm 1))) =
      (cartanGeneratorMatrix i).map (Int.cast : ℤ → B) := by
  rw [HopfIdeal.quotientLieHom_apply, corootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _
      weightTorusIntegralCoordinateMap_comp_quotient]
  ext a b
  by_cases hab : a = b
  · subst b
    simp
  · simp [hab]

/-- The bracket of opposite normalized root vectors is the differential of the corresponding
actual coroot, over every commutative coefficient ring. -/
theorem cartanVector_eq_derivationComp_corootCocharacter (i : Fin 4) :
    cartanVector (B := B) i =
      derivationComp (corootCocharacter i)
        ((MultiplicativeGroup.tangentLinearEquiv (B := B)).symm 1) := by
  apply HopfIdeal.quotientLieHom_injective definingIdeal
  apply (GeneralLinear.tangentLieEquivMatrix (R := ℤ) (B := B) 24).injective
  simp only [LieEquiv.coe_toLieHom, GeneralLinear.tangentLieEquivMatrix_apply,
    tangentMatrix_cartanVector,
    tangentMatrix_derivationComp_corootCocharacter]

/-- The weight-torus differential sends a coordinate tangent vector to its Cartan vector. -/
theorem derivationCompLieHom_weightTorusIntegralCoordinateMap_tangentBasis (i : Fin 4) :
    derivationCompLieHom (B := B) weightTorusIntegralCoordinateMap.hom
        (SplitTorus.tangentBasis (R := ℤ) (B := B) i) = cartanVector (B := B) i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis,
    cartanVector_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply]

/-- The toral tangent image is the span of the normalized Cartan vectors. -/
theorem range_derivationCompLieHom_weightTorusIntegralCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := B) weightTorusIntegralCoordinateMap.hom).toLinearMap =
      Submodule.span B (Set.range (cartanVector (B := B))) := by
  rw [SplitTorus.range_derivationCompLieHom]
  congr 1
  apply congrArg Set.range
  funext i
  rw [← SplitTorus.derivationCompLieHom_tangentBasis,
    derivationCompLieHom_weightTorusIntegralCoordinateMap_tangentBasis]

/-- The integral weight-torus differential is injective over every coefficient ring. -/
theorem derivationCompLieHom_weightTorusIntegralCoordinateMap_injective :
    Function.Injective (derivationCompLieHom (B := B) weightTorusIntegralCoordinateMap.hom) := by
  apply derivationCompLieHom_injective_of_surjective
  have h := GeneralLinear.weightTorusCoordinateMap_surjective (R := ℤ) d4TripledWeight
    span_range_d4TripledWeight_eq_top
  rw [← mkQuotient_comp_weightTorusIntegralCoordinateMap] at h
  exact Function.Surjective.of_comp
    (by simpa only [CommHopfAlgCat.hom_comp, BialgHom.coe_comp] using h)

/-- The four numbered Cartan vectors are independent, including in characteristic two. -/
theorem linearIndependent_cartanVector : LinearIndependent B (cartanVector (B := B)) := by
  convert SplitTorus.linearIndependent_derivationCompLieHom_cocharacter
    (B := B) weightTorusIntegralCoordinateMap.hom
    derivationCompLieHom_weightTorusIntegralCoordinateMap_injective using 1
  funext i
  rw [← SplitTorus.derivationCompLieHom_tangentBasis,
    derivationCompLieHom_weightTorusIntegralCoordinateMap_tangentBasis]

/-- The normalized Cartan vectors form a basis of their span, the toral tangent image. -/
def cartanBasis : Module.Basis (Fin 4) B (Submodule.span B (Set.range (cartanVector (B := B)))) :=
  Module.Basis.span linearIndependent_cartanVector

/-- Including a Cartan basis vector in the tangent algebra gives its normalized Cartan vector. -/
@[simp]
theorem coe_cartanBasis (i : Fin 4) :
    (cartanBasis (B := B) i :
      Derivation ℤ (GeneralLinear.coordinateHopfAlgebra ℤ 24 ⧸ definingIdeal.toIdeal)
        (Bialgebra.CounitAlgebra ℤ
          (GeneralLinear.coordinateHopfAlgebra ℤ 24 ⧸ definingIdeal.toIdeal) B)) =
      cartanVector (B := B) i :=
  Module.Basis.coe_span_apply linearIndependent_cartanVector i

end

end TauCeti.D4Tripled
