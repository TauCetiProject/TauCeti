/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.E6.Minuscule.Root.Differential
public import TauCeti.Algebra.Lie.E6.Minuscule.WeightTorus
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly
import TauCeti.Algebra.Lie.Matrix.IntegralCast

/-!
# Simple-coroot differentials of the integral E₆ minuscule carrier

Evaluation at a fundamental-weight coordinate defines a cocharacter of the integral
27-dimensional minuscule carrier through its closed weight torus. These are the simple
coroots of the named simply connected root datum. Their differentials are the brackets of
the normalized opposite simple-root vectors, over every commutative value ring, including
rings with nilpotents and rings of characteristic three.

The differentials form a basis of the toral tangent image. This identifies the torus and
root-vector normalizations needed for a pinning. It does not assert maximality of the torus,
full root-space recognition, or identification with an independently constructed pinned group.
The integral carrier here is not the separately ground-ring-generated subgroup.

## Main declarations

* `TauCeti.E6Minuscule.corootCocharacter`: the integral simple-coroot cocharacters.
* `TauCeti.E6Minuscule.corootCocharacter_eq_cocharacter_coroot_simpleIndex`:
  agreement with the numbered simply connected root datum.
* `TauCeti.E6Minuscule.cartanVector_eq_derivationComp_corootCocharacter`:
  the opposite-root bracket is the actual coroot differential.
* `TauCeti.E6Minuscule.cartanBasis`: a basis of the toral tangent image.

The argument follows the character–cocharacter calculation in
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot`, using the integral E₆ root differentials
and minuscule matrix relations rather than a comparison between the two group models.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
-/

public section

open CategoryTheory

namespace TauCeti.E6Minuscule

noncomputable section

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

local notation "H" => CommHopfAlgCat.quotient
  (GeneralLinear.coordinateHopfAlgebra ℤ 27) definingIdeal

/-- The integral cocharacter obtained by evaluating the `i`th fundamental-weight coordinate
and including the weight torus into the minuscule carrier. -/
def corootCocharacter (i : Fin 6) : H →ₐc[ℤ] LaurentPolynomial ℤ :=
  weightTorusIntegralCoordinateMap.hom.cocharacter (Finsupp.applyAddHom i).toMultiplicative

/-- The integral cocharacter is induced by evaluation at its fundamental-weight coordinate. -/
theorem corootCocharacter_def (i : Fin 6) :
    corootCocharacter i =
      weightTorusIntegralCoordinateMap.hom.cocharacter (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The coordinate cocharacter agrees with the named simple coroot in Bourbaki numbering. -/
theorem corootCocharacter_eq_cocharacter_coroot_simpleIndex
    (ht : DynkinType.E6.Valid) (i : Fin 6) :
    corootCocharacter i =
      weightTorusIntegralCoordinateMap.hom.cocharacter
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
  exact heval.trans (DynkinType.coroot_simpleIndex _ ht i).symm

variable {B : Type*} [CommRing B]

/-- The differential of a simple coroot has the diagonal matrix of weight–coroot pairings,
scaled by its multiplicative tangent parameter. -/
theorem tangentMatrix_derivationComp_corootCocharacter (ht : DynkinType.E6.Valid)
    (i : Fin 6) (d : Derivation ℤ (LaurentPolynomial ℤ)
      (Bialgebra.CounitAlgebra ℤ (LaurentPolynomial ℤ) B)) :
    GeneralLinear.tangentMatrix 27
        (HopfIdeal.quotientLieHom (B := B) definingIdeal
          (derivationComp (corootCocharacter i) d)) =
      Matrix.diagonal fun a ↦
        (DynkinType.E6.simplyConnectedRootDatum ht).coroot'
          (DynkinType.E6.simpleIndex ht i) (DynkinType.e6MinusculeWeight a) •
            MultiplicativeGroup.tangentLinearEquiv d := by
  have hπ : weightTorusIntegralCoordinateMap.hom.comp
      (Bialgebra.Quotient.mkBialgHom definingIdeal.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := ℤ) DynkinType.e6MinusculeWeight := by
    rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
      mkQuotient_comp_weightTorusIntegralCoordinateMap,
      GeneralLinear.hom_weightTorusCoordinateMap, weightTable_weight]
  rw [HopfIdeal.quotientLieHom_apply, corootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  congr 1
  ext a
  rw [DynkinType.coroot'_simpleIndex_apply DynkinType.E6 ht i
    (DynkinType.e6MinusculeWeight a)]
  simp

/-- The Cartan vector defined by the bracket of the normalized opposite simple-root vectors. -/
def cartanVector (i : Fin 6) :
    Derivation ℤ H (Bialgebra.CounitAlgebra ℤ H B) :=
  ⁅rootVector (B := B) (.inl i), rootVector (B := B) (.inr i)⁆

/-- The Cartan vector is the bracket of the normalized opposite root vectors. -/
theorem cartanVector_def (i : Fin 6) :
    cartanVector (B := B) i = ⁅rootVector (B := B) (.inl i), rootVector (B := B) (.inr i)⁆ :=
  (rfl)

/-- The Cartan bracket has the integral diagonal Cartan generator matrix. -/
@[simp]
theorem tangentMatrix_cartanVector (i : Fin 6) :
    GeneralLinear.tangentMatrix 27
        (HopfIdeal.quotientLieHom (B := B) definingIdeal (cartanVector (B := B) i)) =
      (cartanGeneratorMatrix i).map (Int.cast : ℤ → B) := by
  let f := (GeneralLinear.tangentLieEquivMatrix (R := ℤ) (B := B) 27).toLieHom.comp
    (HopfIdeal.quotientLieHom (B := B) definingIdeal)
  have hf (x) : f x = GeneralLinear.tangentMatrix 27
      (HopfIdeal.quotientLieHom (B := B) definingIdeal x) := by
    simp only [f, LieHom.comp_apply, LieEquiv.coe_toLieHom,
      GeneralLinear.tangentLieEquivMatrix_apply]
  rw [cartanVector_def, ← hf, LieHom.map_lie, hf, hf,
    tangentMatrix_rootVector, tangentMatrix_rootVector, Sum.elim_inl, Sum.elim_inr]
  simpa only [Function.comp_apply, matrixIntCastLieHom_eq_map] using
    (isSerreSystem.map (matrixIntCastLieHom B)).lie_E_F_self i

/-- The normalized opposite-root bracket is the differential of the actual simple coroot,
with no restriction on the characteristic or reducedness of the value ring. -/
theorem cartanVector_eq_derivationComp_corootCocharacter (i : Fin 6) :
    cartanVector (B := B) i =
      derivationComp (corootCocharacter i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B)) := by
  apply HopfIdeal.quotientLieHom_injective definingIdeal
  apply (GeneralLinear.tangentLieEquivMatrix (R := ℤ) (B := B) 27).injective
  simp only [LieEquiv.coe_toLieHom, GeneralLinear.tangentLieEquivMatrix_apply]
  rw [tangentMatrix_cartanVector,
    tangentMatrix_derivationComp_corootCocharacter DynkinType.valid_E6]
  ext a b
  rw [Matrix.map_apply, cartanGeneratorMatrix_apply, Matrix.diagonal_apply,
    DynkinType.coroot'_simpleIndex_apply DynkinType.E6 DynkinType.valid_E6 i
      (DynkinType.e6MinusculeWeight a)]
  split_ifs with hab
  · subst b
    simp
  · simp

/-- Coefficient change preserves the normalized Cartan brackets. -/
@[simp↓]
theorem mapValue_cartanVector {C : Type*} [CommRing C] (φ : B →ₐ[ℤ] C) (i : Fin 6) :
    Derivation.mapValue φ (cartanVector (B := B) i) = cartanVector (B := C) i := by
  rw [cartanVector_def, Derivation.mapValue_lie, mapValue_rootVector,
    mapValue_rootVector, cartanVector_def]

/-- The torus differential sends its coordinate tangent basis to the Cartan brackets. -/
theorem derivationCompLieHom_weightTorusIntegralCoordinateMap_tangentBasis (i : Fin 6) :
    derivationCompLieHom (B := B) weightTorusIntegralCoordinateMap.hom
        (SplitTorus.tangentBasis (R := ℤ) (B := B) i) = cartanVector (B := B) i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis,
    cartanVector_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply]

/-- The toral tangent image is exactly the span of the opposite-root Cartan brackets. -/
theorem range_derivationCompLieHom_weightTorusIntegralCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := B) weightTorusIntegralCoordinateMap.hom).toLinearMap =
      Submodule.span B (Set.range (cartanVector (B := B))) := by
  rw [SplitTorus.range_derivationCompLieHom]
  congr 1
  apply congrArg Set.range
  funext i
  rw [cartanVector_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply]

/-- The Cartan brackets are independent over every commutative value ring, including in
characteristic three, because the weight torus is a closed subgroup of the integral carrier. -/
theorem linearIndependent_cartanVector :
    LinearIndependent B (cartanVector (B := B)) := by
  have h := (SplitTorus.tangentBasis (R := ℤ) (B := B) (I := Fin 6)).linearIndependent.map_injOn
    (derivationCompLieHom (B := B) weightTorusIntegralCoordinateMap.hom).toLinearMap
    (derivationCompLieHom_injective_of_surjective _
      weightTorusIntegralCoordinateMap_surjective).injOn
  have heq :
      ⇑(derivationCompLieHom (B := B) weightTorusIntegralCoordinateMap.hom).toLinearMap ∘
          SplitTorus.tangentBasis (R := ℤ) (B := B) (I := Fin 6) = cartanVector (B := B) := by
    funext i
    exact derivationCompLieHom_weightTorusIntegralCoordinateMap_tangentBasis i
  rwa [heq] at h

/-- A basis of the toral tangent image, realized as the span of the Cartan brackets. -/
def cartanBasis : Module.Basis (Fin 6) B (Submodule.span B (Set.range (cartanVector (B := B)))) :=
  Module.Basis.span linearIndependent_cartanVector

/-- A toral basis vector includes into the tangent algebra as its numbered Cartan bracket. -/
@[simp↓]
theorem coe_cartanBasis (i : Fin 6) :
    (cartanBasis (B := B) i : Derivation ℤ H (Bialgebra.CounitAlgebra ℤ H B)) =
      cartanVector (B := B) i :=
  Module.Basis.coe_span_apply linearIndependent_cartanVector i

end

end TauCeti.E6Minuscule
