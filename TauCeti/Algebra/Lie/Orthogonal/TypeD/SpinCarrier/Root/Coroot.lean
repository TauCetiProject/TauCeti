/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Root.Differential
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.WeightTorus
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Naturality

/-!
# Simple-coroot differentials of the integral type-D spin carrier

The numbered simple coroots in fundamental-weight coordinates give actual cocharacters of the
full-weight spin carrier. Their differentials are the brackets of its normalized opposite root
vectors over every commutative value ring, including characteristic two and nonreduced rings.
These Cartan vectors form a basis of the tangent image of the closed weight torus.

This identifies the coroot normalization required to compare the root parametrizations with a
pinning. It asserts neither maximality of the weight torus nor exhaustion of adjoint root spaces.
The carrier is not identified with an independently pinned simply connected group scheme of type
`Dₙ`; constructions transfer to that group only along such an identification.

## Main declarations

* `corootCocharacter`: the cocharacter obtained by evaluating a fundamental-weight coordinate.
* `tangentMatrix_derivationComp_corootCocharacter`: its diagonal weight-pairing formula.
* `cartanVector_eq_derivationComp_corootCocharacter`: the opposite-root bracket normalization.
* `range_derivationCompLieHom_weightTorusIntegralCoordinateMap_eq_span`: the toral tangent image.
* `cartanBasis`: a basis of that image, expressed as the span of the Cartan vectors.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §10.a and §21.1.

The cocharacter and tangent-basis interface follows
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot`. The matrix calculation uses the general
represented weight-torus differential and the integral spin root matrices.
-/

public section

namespace TauCeti.TypeDSpinCarrier

noncomputable section

universe v

-- Use the algebra-induced integer module consistently for counit coefficient synonyms.
attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ) (hn : 4 ≤ n) {B : Type v} [CommRing B]

/-- The simple coroot cocharacter evaluates the `i`-th fundamental-weight coordinate and
includes the weight torus into the integral spin carrier. -/
def corootCocharacter (i : Fin n) :
    (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) ⧸ (definingIdeal n hn).toIdeal)
      →ₐc[ℤ] LaurentPolynomial ℤ :=
  (weightTorusIntegralCoordinateMap n hn).hom.cocharacter
    (Finsupp.applyAddHom i).toMultiplicative

/-- The coroot cocharacter is induced by the coordinate evaluation character of the lattice. -/
theorem corootCocharacter_def (i : Fin n) :
    corootCocharacter n hn i =
      (weightTorusIntegralCoordinateMap n hn).hom.cocharacter
        (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- These cocharacters are the Bourbaki-numbered simple coroots of the named simply connected
type-D root datum, rather than the coroots of an adjoint or half-spin form. -/
theorem corootCocharacter_eq_cocharacter_coroot_simpleIndex (i : Fin n) :
    corootCocharacter n hn i =
      (weightTorusIntegralCoordinateMap n hn).hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          (((DynkinType.D n).simplyConnectedRootDatum (DynkinType.valid_D.mpr hn)).coroot
            ((DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i))) := by
  rw [corootCocharacter_def]
  congr 1
  apply SplitTorus.cocharEquiv.eq_symm_apply.mpr
  have heval : SplitTorus.cocharEquiv (Finsupp.applyAddHom i).toMultiplicative =
      (Pi.single i 1 : Fin n → ℤ) := by
    ext j
    simp [SplitTorus.cocharEquiv_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  exact heval.trans ((DynkinType.D n).coroot_simpleIndex (DynkinType.valid_D.mpr hn) i).symm

/-- A coroot differential is the diagonal matrix of simple-coroot weights times the
multiplicative tangent parameter, over any commutative value ring. -/
-- Match before simplification changes the counit-indexed integer module structure.
@[simp↓]
theorem tangentMatrix_derivationComp_corootCocharacter (i : Fin n)
    (d : Derivation ℤ (LaurentPolynomial ℤ)
      (Bialgebra.CounitAlgebra ℤ (LaurentPolynomial ℤ) B)) :
    GeneralLinear.tangentMatrix (dimension n)
        (HopfIdeal.quotientLieHom (B := B) (definingIdeal n hn)
          (derivationComp (corootCocharacter n hn i) d)) =
      Matrix.diagonal (fun a ↦ basisWeight n a i • MultiplicativeGroup.tangentLinearEquiv d) := by
  have hπ : (weightTorusIntegralCoordinateMap n hn).hom.comp
      (Bialgebra.Quotient.mkBialgHom (definingIdeal n hn).toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := ℤ) (basisWeight n) := by
    rw [← CommHopfAlgCat.hom_mkQuotient, ← CommHopfAlgCat.hom_comp,
      mkQuotient_comp_weightTorusIntegralCoordinateMap, GeneralLinear.hom_weightTorusCoordinateMap]
  rw [HopfIdeal.quotientLieHom_apply, corootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  simp

/-- The Cartan vector is the bracket of the normalized positive and negative root vectors at
the same numbered simple root. -/
def cartanVector (i : Fin n) :=
  ⁅rootVector n hn (B := B) (.inl i), rootVector n hn (B := B) (.inr i)⁆

/-- The Cartan vector is normalized by the opposite-root bracket. -/
theorem cartanVector_def (i : Fin n) :
    cartanVector n hn (B := B) i =
      ⁅rootVector n hn (B := B) (.inl i), rootVector n hn (B := B) (.inr i)⁆ :=
  (rfl)

/-- A Cartan vector has diagonal matrix given by the integral simple-coroot weights. -/
@[simp]
theorem tangentMatrix_cartanVector (i : Fin n) :
    GeneralLinear.tangentMatrix (dimension n)
        (HopfIdeal.quotientLieHom (B := B) (definingIdeal n hn)
          (cartanVector n hn (B := B) i)) =
      Matrix.diagonal (fun a ↦ (basisWeight n a i : B)) := by
  rw [cartanVector_def, LieHom.map_lie, GeneralLinear.tangentMatrix_lie,
    tangentMatrix_rootVector, tangentMatrix_rootVector]
  have h := congrArg (((Int.castRingHom B).mapMatrix (m := Fin (dimension n))))
    (lie_rootIntMatrix_inl_inr n hn i)
  simpa only [Ring.lie_def, map_sub, map_mul, RingHom.mapMatrix_apply,
    Int.coe_castRingHom, Matrix.diagonal_map (Int.cast_zero (R := B))] using h

/-- The normalized opposite-root bracket is the differential of the actual coroot cocharacter
at the multiplicative unit tangent vector, without any characteristic restriction. -/
theorem cartanVector_eq_derivationComp_corootCocharacter (i : Fin n) :
    cartanVector n hn (B := B) i =
      derivationComp (corootCocharacter n hn i)
        ((MultiplicativeGroup.tangentLinearEquiv (R := ℤ) (B := B)).symm 1) := by
  apply HopfIdeal.quotientLieHom_injective (definingIdeal n hn)
  apply (GeneralLinear.tangentLieEquivMatrix (R := ℤ) (B := B) (dimension n)).injective
  simp only [LieEquiv.coe_toLieHom, GeneralLinear.tangentLieEquivMatrix_apply,
    tangentMatrix_cartanVector, tangentMatrix_derivationComp_corootCocharacter,
    LinearEquiv.apply_symm_apply, zsmul_eq_mul, mul_one]

/-- Coefficient change preserves the normalized Cartan vectors. -/
@[simp↓]
theorem mapValue_cartanVector {C : Type*} [CommRing C] (φ : B →ₐ[ℤ] C) (i : Fin n) :
    Derivation.mapValue φ (cartanVector n hn (B := B) i) = cartanVector n hn (B := C) i := by
  rw [cartanVector_def, Derivation.mapValue_lie, mapValue_rootVector, mapValue_rootVector,
    cartanVector_def]

/-- The weight-torus differential sends its coordinate tangent basis to the Cartan vectors. -/
theorem derivationCompLieHom_weightTorusIntegralCoordinateMap_tangentBasis (i : Fin n) :
    derivationCompLieHom (B := B) (weightTorusIntegralCoordinateMap n hn).hom
        (SplitTorus.tangentBasis (R := ℤ) (B := B) i) = cartanVector n hn (B := B) i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis,
    cartanVector_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply]

/-- The toral tangent image is exactly the span of the normalized Cartan vectors. -/
theorem range_derivationCompLieHom_weightTorusIntegralCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := B) (weightTorusIntegralCoordinateMap n hn).hom).toLinearMap =
      Submodule.span B (Set.range (cartanVector n hn (B := B))) := by
  rw [SplitTorus.range_derivationCompLieHom]
  congr 1
  apply congrArg Set.range
  funext i
  rw [cartanVector_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply]

/-- The Cartan vectors are independent over every commutative value ring, since the weight
torus is closed and its differential is injective. -/
theorem linearIndependent_cartanVector :
    LinearIndependent B (cartanVector n hn (B := B)) := by
  have h := (SplitTorus.tangentBasis (R := ℤ) (B := B) (I := Fin n)).linearIndependent.map_injOn
    (derivationCompLieHom (B := B) (weightTorusIntegralCoordinateMap n hn).hom).toLinearMap
    (derivationCompLieHom_injective_of_surjective _
      (weightTorusIntegralCoordinateMap_surjective n hn)).injOn
  have heq :
      ⇑(derivationCompLieHom (B := B) (weightTorusIntegralCoordinateMap n hn).hom).toLinearMap ∘
          SplitTorus.tangentBasis (R := ℤ) (B := B) (I := Fin n) =
        cartanVector n hn (B := B) := by
    funext i
    exact derivationCompLieHom_weightTorusIntegralCoordinateMap_tangentBasis n hn i
  rwa [heq] at h

/-- The simple-coroot differentials form a basis of their span, the toral tangent image. -/
def cartanBasis :
    Module.Basis (Fin n) B (Submodule.span B (Set.range (cartanVector n hn (B := B)))) :=
  Module.Basis.span (linearIndependent_cartanVector n hn)

/-- Including a Cartan basis vector into the tangent algebra recovers the numbered Cartan vector. -/
@[simp]
theorem coe_cartanBasis (i : Fin n) :
    (cartanBasis n hn (B := B) i :
      Derivation ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) ⧸
        (definingIdeal n hn).toIdeal)
        (Bialgebra.CounitAlgebra ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) ⧸
          (definingIdeal n hn).toIdeal) B)) = cartanVector n hn (B := B) i :=
  Module.Basis.coe_span_apply (linearIndependent_cartanVector n hn) i

end

end TauCeti.TypeDSpinCarrier
