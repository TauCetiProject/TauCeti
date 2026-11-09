/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.E7.Minuscule.Root.Coroot
public import TauCeti.Algebra.Lie.E7.Minuscule.Root.Differential

/-!
# Simple-coroot differentials of the integral E₇ carrier

The simple coroots of the 56-dimensional minuscule carrier are the coordinate cocharacters
of its weight torus. Their differentials are the brackets of the normalized opposite
simple-root vectors, over every commutative ring. These seven brackets form a basis of
the toral tangent image, including in characteristic two.

`corootCocharacter_eq_cocharacter_coroot_simpleIndex` identifies the cocharacters with the
numbered simply connected root datum, and `cartanVector_eq_derivationComp_corootCocharacter`
provides the bracket normalization. `cartanBasis` gives the resulting basis of the toral
image. No maximality, full root-space decomposition, or identification of the specialized
integral carrier with an independently pinned group is asserted.

The calculation uses the carrier-independent lemmas in `Root.Coroot`, shared with
`Generated.Coroot`, and the integral carrier's own closed immersion and root parametrizations.
It does not identify that carrier with the separately generated subgroup.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 21.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
-/

public section

open CategoryTheory

namespace TauCeti.E7Minuscule

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable (R : Type*) [CommRing R]

/-- The differential of the integral carrier's closed immersion into `GL₅₆`, in matrix form. -/
def tangentMatrixLieHom :
    Derivation R (coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R) R) →ₗ⁅R⁆
        Matrix (Fin 56) (Fin 56) R :=
  GeneralLinear.tangentMatrixLieHom (coordinateMap R).hom

/-- The matrix realization evaluates the precomposed tangent vector on the generic matrix. -/
theorem tangentMatrixLieHom_apply
    (d : Derivation R (coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R) R)) :
    tangentMatrixLieHom R d = GeneralLinear.tangentMatrix 56
      (derivationComp (B := R) (coordinateMap R).hom d) := by
  exact GeneralLinear.tangentMatrixLieHom_apply _ d

/-- The tangent matrix realization is injective over every commutative base ring. -/
theorem tangentMatrixLieHom_injective : Function.Injective (tangentMatrixLieHom R) :=
  GeneralLinear.tangentMatrixLieHom_injective_of_surjective _ (coordinateMap_surjective R)

/-- Each normalized root vector has its prescribed integral root matrix. -/
@[simp↓]
theorem tangentMatrixLieHom_rootVector (k : Fin 7 ⊕ Fin 7) :
    tangentMatrixLieHom R (rootVector R k) =
      (Sum.elim raisingMatrix loweringMatrix k).map (Int.cast : ℤ → R) := by
  rw [tangentMatrixLieHom_apply, tangentMatrix_rootVector]

/-- The Cartan vector obtained by bracketing the normalized opposite simple-root vectors. -/
def cartanVector (i : Fin 7) :
    Derivation R (coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R) R) :=
  ⁅rootVector R (.inl i), rootVector R (.inr i)⁆

/-- The Cartan vector is the normalized opposite-root bracket. -/
theorem cartanVector_def (i : Fin 7) :
    cartanVector R i = ⁅rootVector R (.inl i), rootVector R (.inr i)⁆ :=
  (rfl)

/-- The opposite-root bracket has the integral diagonal Cartan matrix. -/
@[simp↓]
theorem tangentMatrixLieHom_cartanVector (i : Fin 7) :
    tangentMatrixLieHom R (cartanVector R i) =
      (cartanMatrix i).map (Int.cast : ℤ → R) := by
  exact map_lie_eq_cartanMatrix (tangentMatrixLieHom R) _ _ i
    (tangentMatrixLieHom_rootVector R (.inl i))
    (tangentMatrixLieHom_rootVector R (.inr i))

/-- The cocharacter defined by the `i`-th fundamental-weight coordinate of the weight torus. -/
def corootCocharacter (i : Fin 7) : coordinateHopfAlgebra R →ₐc[R] LaurentPolynomial R :=
  (weightTorusToBaseChangeCoordinateMap R).hom.cocharacter
    (Finsupp.applyAddHom i).toMultiplicative

/-- The coroot cocharacter factors through the existing weight-torus map. -/
theorem corootCocharacter_def (i : Fin 7) :
    corootCocharacter R i = (weightTorusToBaseChangeCoordinateMap R).hom.cocharacter
      (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The coordinate cocharacter is the named Bourbaki simple coroot of the E₇ root datum. -/
theorem corootCocharacter_eq_cocharacter_coroot_simpleIndex
    (ht : DynkinType.E7.Valid) (i : Fin 7) :
    corootCocharacter R i = (weightTorusToBaseChangeCoordinateMap R).hom.cocharacter
      (SplitTorus.cocharEquiv.symm
        ((DynkinType.E7.simplyConnectedRootDatum ht).coroot
          (DynkinType.E7.simpleIndex ht i))) := by
  rw [corootCocharacter_def]
  congr 1
  exact (cocharEquiv_symm_coroot_simpleIndex ht i).symm

/-- The coroot differential has diagonal entries given by the weight–coroot pairings.
The multiplicative tangent vector is normalized to one. -/
theorem tangentMatrixLieHom_derivationComp_corootCocharacter
    (ht : DynkinType.E7.Valid) (i : Fin 7) :
    tangentMatrixLieHom R
        (derivationComp (corootCocharacter R i)
          (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R))) =
      Matrix.diagonal fun a ↦
        ((DynkinType.E7.simplyConnectedRootDatum ht).coroot'
          (DynkinType.E7.simpleIndex ht i) (DynkinType.e7MinusculeWeight a) : R) := by
  have hπ : (weightTorusToBaseChangeCoordinateMap R).hom.comp (coordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) DynkinType.e7MinusculeWeight := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  exact generalLinearTangentMatrixLieHom_derivationComp_cocharacter_applyAddHom _ _ hπ ht i

/-- The bracket of normalized opposite simple-root vectors is the actual coroot differential,
without any restriction on characteristic. -/
theorem cartanVector_eq_derivationComp_corootCocharacter (i : Fin 7) :
    cartanVector R i = derivationComp (corootCocharacter R i)
      (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R)) := by
  apply tangentMatrixLieHom_injective R
  rw [tangentMatrixLieHom_cartanVector,
    tangentMatrixLieHom_derivationComp_corootCocharacter R DynkinType.valid_E7,
    cartanMatrix_map_intCast_eq_diagonal_coroot' DynkinType.valid_E7]

/-- The weight-torus differential sends each coordinate tangent vector to its Cartan bracket. -/
theorem derivationCompLieHom_weightTorusToBaseChangeCoordinateMap_tangentBasis (i : Fin 7) :
    derivationCompLieHom (B := R) (weightTorusToBaseChangeCoordinateMap R).hom
        (SplitTorus.tangentBasis (R := R) (B := R) i) = cartanVector R i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis,
    cartanVector_eq_derivationComp_corootCocharacter, corootCocharacter_def,
    derivationCompLieHom_apply]

/-- The toral tangent image is exactly the span of the normalized Cartan brackets. -/
theorem range_derivationCompLieHom_weightTorusToBaseChangeCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := R) (weightTorusToBaseChangeCoordinateMap R).hom).toLinearMap =
      Submodule.span R (Set.range (cartanVector R)) := by
  simpa only [derivationCompLieHom_apply, ← corootCocharacter_def R,
    ← cartanVector_eq_derivationComp_corootCocharacter R] using
    SplitTorus.range_derivationCompLieHom (B := R) (weightTorusToBaseChangeCoordinateMap R).hom

/-- The seven Cartan brackets are independent, even in characteristic two. -/
theorem linearIndependent_cartanVector : LinearIndependent R (cartanVector R) := by
  simpa only [derivationCompLieHom_apply, ← corootCocharacter_def R,
    ← cartanVector_eq_derivationComp_corootCocharacter R] using
    SplitTorus.linearIndependent_derivationCompLieHom_cocharacter
      (B := R) (weightTorusToBaseChangeCoordinateMap R).hom
      (derivationCompLieHom_injective_of_surjective _
        (weightTorusToBaseChangeCoordinateMap_surjective R))

/-- The simple-coroot differentials form a basis of the toral tangent image, expressed as a span. -/
def cartanBasis : Module.Basis (Fin 7) R (Submodule.span R (Set.range (cartanVector R))) :=
  Module.Basis.span (linearIndependent_cartanVector R)

/-- The Cartan basis vectors include as the normalized opposite-root brackets. -/
@[simp↓]
theorem coe_cartanBasis (i : Fin 7) :
    (cartanBasis R i : Derivation R (coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R) R)) = cartanVector R i :=
  Module.Basis.coe_span_apply (linearIndependent_cartanVector R) i

end

end TauCeti.E7Minuscule
