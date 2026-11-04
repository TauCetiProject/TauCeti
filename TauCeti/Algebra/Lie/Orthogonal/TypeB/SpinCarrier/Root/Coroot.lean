/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Root.Differential
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.WeightTorus

/-!
# Simple-coroot differentials of the integral type-B spin carrier

The coordinate cocharacters of the full spin weight torus are the numbered simple coroots.
Their differentials are the brackets of the normalized opposite root vectors, over every
commutative value ring, including nonreduced rings and characteristic two. These Cartan
vectors form a basis of the toral tangent image: independence follows from the closed weight
torus, not from invertibility of the Cartan matrix.

This supplies the compatibility of the root vectors and coroots required of a numbered pinning.
It does not assert maximality of the torus, exhaustion of the root spaces, or an identification
of the carrier with an independently pinned simply connected group scheme.

The character–cocharacter calculation follows
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot`, applied here to the integral spin carrier.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §10.a and §21.1.
-/

public section

namespace TauCeti.TypeBSpinCarrier

noncomputable section

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ) {B : Type*} [CommRing B]

/-- The coordinate cocharacter of the integral spin weight torus, included in the carrier. -/
def corootCocharacter (i : Fin (n + 1)) :
    (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) ⧸ (definingIdeal n).toIdeal) →ₐc[ℤ]
      LaurentPolynomial ℤ :=
  (weightTorusIntegralCoordinateMap n).hom.cocharacter (Finsupp.applyAddHom i).toMultiplicative

/-- The simple cocharacter is evaluation at the corresponding fundamental-weight coordinate. -/
theorem corootCocharacter_def (i : Fin (n + 1)) :
    corootCocharacter n i =
      (weightTorusIntegralCoordinateMap n).hom.cocharacter
        (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The coordinate cocharacter is the named simple coroot in Bourbaki numbering. Only this
comparison needs validity of the named type; the differential formulas also cover rank one. -/
theorem corootCocharacter_eq_cocharacter_coroot_simpleIndex
    (ht : (DynkinType.B (n + 1)).Valid) (i : Fin (n + 1)) :
    corootCocharacter n i =
      (weightTorusIntegralCoordinateMap n).hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          (((DynkinType.B (n + 1)).simplyConnectedRootDatum ht).coroot
            ((DynkinType.B (n + 1)).simpleIndex ht i))) := by
  rw [corootCocharacter_def]
  congr 1
  apply SplitTorus.cocharEquiv.eq_symm_apply.mpr
  have heval : SplitTorus.cocharEquiv (Finsupp.applyAddHom i).toMultiplicative =
      (Pi.single i 1 : Fin (n + 1) → ℤ) := by
    ext j
    simp [SplitTorus.cocharEquiv_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  exact heval.trans ((DynkinType.B (n + 1)).coroot_simpleIndex ht i).symm

/-- The coroot differential has diagonal entries equal to the spin weights paired with that
simple coroot, multiplied by the multiplicative tangent parameter. -/
@[simp↓]
theorem tangentMatrix_derivationComp_corootCocharacter (i : Fin (n + 1))
    (d : Derivation ℤ (LaurentPolynomial ℤ)
      (Bialgebra.CounitAlgebra ℤ (LaurentPolynomial ℤ) B)) :
    GeneralLinear.tangentMatrix (dimension n)
        (HopfIdeal.quotientLieHom (B := B) (definingIdeal n)
          (derivationComp (B := B) (corootCocharacter n i) d)) =
      Matrix.diagonal (fun a ↦ basisWeight n a i • MultiplicativeGroup.tangentLinearEquiv d) := by
  have hπ : (weightTorusIntegralCoordinateMap n).hom.comp
      (Bialgebra.Quotient.mkBialgHom (definingIdeal n).toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := ℤ) (basisWeight n) := by
    rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
      mkQuotient_comp_weightTorusIntegralCoordinateMap,
      GeneralLinear.hom_weightTorusCoordinateMap]
  rw [HopfIdeal.quotientLieHom_apply, corootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  simp

/-- The Cartan vector is the bracket of the normalized opposite root vectors at a common node. -/
def cartanVector (i : Fin (n + 1)) :
    Derivation ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) ⧸ (definingIdeal n).toIdeal)
      (Bialgebra.CounitAlgebra ℤ
        (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) ⧸ (definingIdeal n).toIdeal) B) :=
  ⁅rootVector n (B := B) (.inl i), rootVector n (B := B) (.inr i)⁆

/-- The defining opposite-root bracket of the Cartan vector. -/
theorem cartanVector_def (i : Fin (n + 1)) :
    cartanVector n (B := B) i =
      ⁅rootVector n (B := B) (.inl i), rootVector n (B := B) (.inr i)⁆ :=
  (rfl)

/-- The Cartan vector is diagonal, with the integral spin weight's simple-coroot coordinates. -/
@[simp↓]
theorem tangentMatrix_cartanVector (i : Fin (n + 1)) :
    GeneralLinear.tangentMatrix (dimension n)
        (HopfIdeal.quotientLieHom (B := B) (definingIdeal n) (cartanVector n (B := B) i)) =
      Matrix.diagonal (fun a ↦ (basisWeight n a i : B)) := by
  have hm := congrArg (fun M ↦ M.map (Int.castRingHom B)) (lie_rootIntMatrix_inl_inr n i)
  simp only [Ring.lie_def, Matrix.map_sub _ (map_sub (Int.castRingHom B)),
    Matrix.map_mul, Matrix.diagonal_map (map_zero (Int.castRingHom B))] at hm
  rw [cartanVector_def, LieHom.map_lie,
    ← GeneralLinear.tangentLieEquivMatrix_apply, LieEquiv.map_lie]
  simpa only [GeneralLinear.tangentLieEquivMatrix_apply, tangentMatrix_rootVector,
    Ring.lie_def, Int.coe_castRingHom] using hm

/-- The opposite-root bracket is the differential of the actual simple-coroot cocharacter. -/
theorem cartanVector_eq_derivationComp_corootCocharacter (i : Fin (n + 1)) :
    cartanVector n (B := B) i =
      derivationComp (B := B) (corootCocharacter n i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B)) := by
  apply (HopfIdeal.quotientLieHom_injective (B := B) (definingIdeal n))
  apply (GeneralLinear.tangentLieEquivMatrix (R := ℤ) (B := B) (dimension n)).injective
  simp only [LieEquiv.coe_toLieHom, GeneralLinear.tangentLieEquivMatrix_apply,
    tangentMatrix_cartanVector,
    tangentMatrix_derivationComp_corootCocharacter, LinearEquiv.apply_symm_apply,
    zsmul_eq_mul, mul_one]

/-- Coefficient change preserves the normalized Cartan vectors. -/
@[simp↓]
theorem mapValue_cartanVector {C : Type*} [CommRing C] (φ : B →ₐ[ℤ] C)
    (i : Fin (n + 1)) :
    Derivation.mapValue φ (cartanVector n (B := B) i) = cartanVector n (B := C) i := by
  simp only [cartanVector_def, Derivation.mapValue_lie, mapValue_rootVector]

/-- The weight-torus differential sends its coordinate tangent basis to the Cartan vectors. -/
theorem derivationCompLieHom_weightTorusIntegralCoordinateMap_tangentBasis (i : Fin (n + 1)) :
    derivationCompLieHom (B := B) (weightTorusIntegralCoordinateMap n).hom
        (SplitTorus.tangentBasis (R := ℤ) (B := B) i) = cartanVector n (B := B) i := by
  simpa only [cartanVector_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply] using
    (SplitTorus.derivationCompLieHom_tangentBasis
      (B := B) (weightTorusIntegralCoordinateMap n).hom i)

/-- The toral tangent image is exactly the span of the normalized Cartan vectors. -/
theorem range_derivationCompLieHom_weightTorusIntegralCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := B) (weightTorusIntegralCoordinateMap n).hom).toLinearMap =
      Submodule.span B (Set.range (cartanVector n (B := B))) := by
  simpa only [funext (cartanVector_eq_derivationComp_corootCocharacter n (B := B)),
    corootCocharacter_def, derivationCompLieHom_apply] using
    (SplitTorus.range_derivationCompLieHom (B := B) (weightTorusIntegralCoordinateMap n).hom)

/-- The weight-torus differential is injective over every commutative value ring. -/
theorem derivationCompLieHom_weightTorusIntegralCoordinateMap_injective :
    Function.Injective
      (derivationCompLieHom (B := B) (weightTorusIntegralCoordinateMap n).hom) :=
  derivationCompLieHom_injective_of_surjective _ (weightTorusIntegralCoordinateMap_surjective n)

/-- The simple-coroot differentials are independent, including in characteristic two. -/
theorem linearIndependent_cartanVector : LinearIndependent B (cartanVector n (B := B)) := by
  simpa only [funext (cartanVector_eq_derivationComp_corootCocharacter n (B := B)),
    corootCocharacter_def, derivationCompLieHom_apply] using
    (SplitTorus.linearIndependent_derivationComp_cocharacter
      (B := B) (weightTorusIntegralCoordinateMap n).hom
      (derivationCompLieHom_weightTorusIntegralCoordinateMap_injective n (B := B)))

/-- The numbered Cartan vectors form a basis of their span, the toral tangent image. -/
def cartanBasis :
    Module.Basis (Fin (n + 1)) B (Submodule.span B (Set.range (cartanVector n (B := B)))) :=
  Module.Basis.span (linearIndependent_cartanVector n)

/-- Including a Cartan basis vector into the tangent algebra gives its numbered Cartan vector. -/
@[simp↓]
theorem coe_cartanBasis (i : Fin (n + 1)) :
    (cartanBasis n (B := B) i :
      Derivation ℤ
        (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) ⧸ (definingIdeal n).toIdeal)
        (Bialgebra.CounitAlgebra ℤ
          (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) ⧸ (definingIdeal n).toIdeal) B)) =
      cartanVector n (B := B) i :=
  Module.Basis.coe_span_apply (linearIndependent_cartanVector n) i

end

end TauCeti.TypeBSpinCarrier
