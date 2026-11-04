/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.D4.Tripled.Generated.RootWeight
public import TauCeti.Algebra.Lie.D4.Tripled.Generated.WeightTorus
import TauCeti.Algebra.Lie.Matrix.IntegralCast
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# Simple-coroot differentials of the generated tripled D₄ group

The fundamental-weight coordinates give simple-coroot cocharacters through the weight torus
of the subgroup generated over the base ring. Their unit tangent vectors are the brackets of
the normalized opposite simple-root vectors. The four resulting Cartan vectors form a basis
of the toral tangent image, over every commutative base ring and every commutative value algebra.
In particular their independence survives characteristic two and nonreduced coefficients.

These identities fix the infinitesimal coroot normalization of the numbered root subgroups.
The generated subgroup is not identified with the specialization of the integral toral closure,
nor with the independently pinned simply connected group scheme. Transport to that pinned group
requires such an identification. No exhaustion of root spaces or Borel recognition is asserted.

The construction follows `TauCeti.Algebra.Lie.D4.Tripled.Coroot` and
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot`, using the generated tripled root vectors
and its surjective weight-torus restriction.

## Main declarations

* `generatedCorootCocharacter`: the actual numbered cocharacter through the generated torus.
* `generatedCartanVector_eq_derivationComp_generatedCorootCocharacter`: the opposite-root bracket.
* `range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span`: the toral tangent image.
* `generatedCartanBasis`: its basis of normalized Cartan vectors.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
-/

public section

namespace TauCeti.D4Tripled

open CategoryTheory DynkinType

noncomputable section

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

/-- The numbered simple cocharacter evaluates a fundamental-weight coordinate and then
includes the weight torus in the group generated over `R`. -/
def generatedCorootCocharacter (i : Fin 4) :
    generatedCoordinateHopfAlgebra R →ₐc[R] LaurentPolynomial R :=
  (generatedWeightTorusCoordinateMap R).hom.cocharacter
    (Finsupp.applyAddHom i).toMultiplicative

/-- The simple cocharacter is induced by its fundamental-weight coordinate. -/
theorem generatedCorootCocharacter_def (i : Fin 4) :
    generatedCorootCocharacter R i =
      (generatedWeightTorusCoordinateMap R).hom.cocharacter
        (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The coordinate cocharacter is the named simple coroot of the simply connected D₄ datum,
with its existing Bourbaki numbering. -/
theorem generatedCorootCocharacter_eq_cocharacter_coroot_simpleIndex
    (ht : (D 4).Valid) (i : Fin 4) :
    generatedCorootCocharacter R i =
      (generatedWeightTorusCoordinateMap R).hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          (((D 4).simplyConnectedRootDatum ht).coroot ((D 4).simpleIndex ht i))) := by
  rw [generatedCorootCocharacter_def]
  congr 1
  apply SplitTorus.cocharEquiv.eq_symm_apply.mpr
  exact (SplitTorus.cocharEquiv_applyAddHom i).trans ((D 4).coroot_simpleIndex ht i).symm

variable {B : Type*} [CommRing B] [Algebra R B]

/-- The normalized generated Cartan vector is the bracket of opposite simple-root vectors. -/
def generatedCartanVector (i : Fin 4) :
    Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) B) :=
  ⁅generatedRootVector (B := B) R (.inl i), generatedRootVector (B := B) R (.inr i)⁆

/-- The Cartan vector is the bracket of the normalized opposite simple-root vectors. -/
theorem generatedCartanVector_def (i : Fin 4) :
    generatedCartanVector (B := B) R i =
      ⁅generatedRootVector (B := B) R (.inl i), generatedRootVector (B := B) R (.inr i)⁆ :=
  (rfl)

/-- Change of value algebra preserves the normalized Cartan vector. -/
@[simp↓]
theorem mapValue_generatedCartanVector {C : Type*} [CommRing C] [Algebra R C]
    (φ : B →ₐ[R] C) (i : Fin 4) :
    Derivation.mapValue φ (generatedCartanVector (B := B) R i) =
      generatedCartanVector (B := C) R i := by
  simp only [generatedCartanVector_def, Derivation.mapValue_lie, mapValue_generatedRootVector]

/-- The matrix of a normalized generated Cartan vector is the integral diagonal coroot matrix. -/
@[simp]
theorem tangentMatrix_generatedCartanVector (i : Fin 4) :
    GeneralLinear.tangentMatrix 24
        (derivationComp (B := B) (generatedCoordinateMap R).hom
          (generatedCartanVector (B := B) R i)) =
      (cartanGeneratorMatrix i).map (Int.cast : ℤ → B) := by
  have h := ((GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) 24).toLieHom.comp
    (derivationCompLieHom (B := B) (generatedCoordinateMap R).hom)).map_lie
      (generatedRootVector (B := B) R (.inl i)) (generatedRootVector (B := B) R (.inr i))
  simp only [LieHom.comp_apply, LieEquiv.coe_toLieHom, derivationCompLieHom_apply,
    GeneralLinear.tangentLieEquivMatrix_apply, tangentMatrix_generatedRootVector,
    rootMatrix_inl, rootMatrix_inr] at h
  rw [generatedCartanVector_def, h]
  simpa only [Function.comp_apply, matrixIntCastLieHom_eq_map] using
    (isSerreSystem.map (matrixIntCastLieHom B)).lie_E_F_self i

/-- The simple-coroot differential has the diagonal weight-pairing matrix, with multiplicative
unit tangent parameter one. -/
theorem tangentMatrix_derivationComp_generatedCorootCocharacter (i : Fin 4) :
    GeneralLinear.tangentMatrix 24
        (derivationComp (B := B) (generatedCoordinateMap R).hom
          (derivationComp (generatedCorootCocharacter R i)
            ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm 1))) =
      (cartanGeneratorMatrix i).map (Int.cast : ℤ → B) := by
  have hπ : (generatedWeightTorusCoordinateMap R).hom.comp (generatedCoordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) d4TripledWeight := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  rw [generatedCorootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  -- Both matrices are diagonal, with entry the i-th coordinate of the tripled weight.
  ext a b
  by_cases hab : a = b <;> simp [hab]

/-- The opposite-root bracket equals the differential of the actual numbered coroot,
over every commutative value algebra. -/
theorem generatedCartanVector_eq_derivationComp_generatedCorootCocharacter (i : Fin 4) :
    generatedCartanVector (B := B) R i =
      derivationComp (generatedCorootCocharacter R i)
        ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm 1) := by
  apply derivationComp_injective_of_surjective _ (generatedCoordinateMap_surjective R)
  apply (GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) 24).injective
  simp only [LieEquiv.coe_toLieHom, GeneralLinear.tangentLieEquivMatrix_apply,
    tangentMatrix_generatedCartanVector, tangentMatrix_derivationComp_generatedCorootCocharacter]

/-- The weight-torus differential sends each coordinate tangent vector to its Cartan vector. -/
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_tangentBasis (i : Fin 4) :
    derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap R).hom
        (SplitTorus.tangentBasis (R := R) (B := B) i) =
      generatedCartanVector (B := B) R i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis,
    generatedCartanVector_eq_derivationComp_generatedCorootCocharacter,
    generatedCorootCocharacter_def, derivationCompLieHom_apply]

/-- The tangent image of the generated weight torus is the span of its normalized Cartan
vectors. -/
theorem range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap R).hom).toLinearMap =
      Submodule.span B (Set.range (generatedCartanVector (B := B) R)) := by
  rw [SplitTorus.range_derivationCompLieHom]
  congr 1
  apply congrArg Set.range
  funext i
  rw [← SplitTorus.derivationCompLieHom_tangentBasis,
    derivationCompLieHom_generatedWeightTorusCoordinateMap_tangentBasis]

/-- The generated weight-torus differential is injective over every commutative value algebra. -/
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_injective :
    Function.Injective
      (derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap R).hom) :=
  derivationCompLieHom_injective_of_surjective _ (generatedWeightTorusCoordinateMap_surjective R)

/-- The four normalized Cartan vectors are independent, including in characteristic two. -/
theorem linearIndependent_generatedCartanVector :
    LinearIndependent B (generatedCartanVector (B := B) R) := by
  convert SplitTorus.linearIndependent_derivationComp_cocharacter
    (B := B) (generatedWeightTorusCoordinateMap R).hom
    (derivationCompLieHom_generatedWeightTorusCoordinateMap_injective (B := B) R) using 1
  funext i
  rw [← SplitTorus.derivationCompLieHom_tangentBasis,
    derivationCompLieHom_generatedWeightTorusCoordinateMap_tangentBasis]

/-- The simple-coroot differentials form a basis of their span, the toral tangent image. -/
def generatedCartanBasis :
    Module.Basis (Fin 4) B (Submodule.span B (Set.range (generatedCartanVector (B := B) R))) :=
  Module.Basis.span (linearIndependent_generatedCartanVector (B := B) R)

/-- Including a Cartan basis vector in the tangent algebra gives its numbered Cartan vector. -/
@[simp]
theorem coe_generatedCartanBasis (i : Fin 4) :
    (generatedCartanBasis (B := B) R i :
      Derivation R (generatedCoordinateHopfAlgebra R)
        (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) B)) =
      generatedCartanVector (B := B) R i :=
  Module.Basis.coe_span_apply (linearIndependent_generatedCartanVector (B := B) R) i

end

end TauCeti.D4Tripled
