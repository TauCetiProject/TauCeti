/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Generated.RootWeight
public import TauCeti.Algebra.Lie.Presentation.Serre.IntegralCast

/-!
# Serre generators in the Lie algebra of the generated E₆ group

The normalized positive and negative root vectors of the generated subgroup of `GL₂₇`
satisfy the E₆ Serre relations over every commutative ring. Their Cartan vectors are their
opposite-root brackets. The differential of the closed immersion into `GL₂₇` is injective,
so the existing integral minuscule matrix relations give the relations in the actual tangent
Lie algebra, including in characteristics two and three.

`generatedSerreLift` is the resulting comparison from the Serre presentation, characterized
by its generator values. Its composite with `generatedTangentMatrixLieHom` recovers the
minuscule representation. No assertion that the comparison is surjective, or that the carrier
is the pinned simply connected group scheme, is made here. The matrix convention retains the
transpose of `CartanMatrix.E 6`, as in the integral minuscule representation.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1–2.
* The construction follows `TauCeti.Algebra.Lie.E7.Minuscule.Generated.Serre`, using the
  integral E₆ representation `TauCeti.E6Minuscule.isSerreSystem`.
-/

public section

open scoped Matrix

namespace TauCeti.E6Minuscule

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable (R : Type*) [CommRing R]

/-- The differential of the generated group's closed immersion into `GL₂₇`, in matrix form. -/
def generatedTangentMatrixLieHom :
    Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R) →ₗ⁅R⁆
        Matrix (Fin 27) (Fin 27) R :=
  (GeneralLinear.tangentLieEquivMatrix (R := R) (B := R) 27).toLieHom.comp
    (derivationCompLieHom (B := R) (generatedCoordinateMap R).hom)

/-- The tangent inclusion evaluates the precomposed derivation on the generic matrix. -/
theorem generatedTangentMatrixLieHom_apply
    (d : Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R)) :
    generatedTangentMatrixLieHom R d = GeneralLinear.tangentMatrix 27
      (derivationComp (B := R) (generatedCoordinateMap R).hom d) := by
  simp only [generatedTangentMatrixLieHom, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    GeneralLinear.tangentLieEquivMatrix_apply, derivationCompLieHom_apply]

/-- The tangent inclusion is injective over every commutative ring. -/
theorem generatedTangentMatrixLieHom_injective :
    Function.Injective (generatedTangentMatrixLieHom R) :=
  (GeneralLinear.tangentLieEquivMatrix (R := R) (B := R) 27).injective.comp
    (derivationCompLieHom_injective_of_surjective _ (generatedCoordinateMap_surjective R))

/-- A normalized root vector maps to its integral raising or lowering matrix. -/
@[simp]
theorem generatedTangentMatrixLieHom_generatedRootVector (k : Fin 6 ⊕ Fin 6) :
    generatedTangentMatrixLieHom R (generatedRootVector R k) =
      (Sum.elim raisingMatrix loweringMatrix k).map (Int.cast : ℤ → R) := by
  rw [generatedTangentMatrixLieHom_apply, tangentMatrix_generatedRootVector]

/-- The Cartan vector is the bracket of the normalized opposite simple-root vectors. -/
def generatedCartanVector (i : Fin 6) :
    Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R) :=
  ⁅generatedRootVector R (.inl i), generatedRootVector R (.inr i)⁆

/-- The defining opposite-root bracket of the Cartan vector. -/
theorem generatedCartanVector_def (i : Fin 6) :
    generatedCartanVector R i =
      ⁅generatedRootVector R (.inl i), generatedRootVector R (.inr i)⁆ :=
  (rfl)

/-- A Cartan vector maps to the diagonal matrix of its minuscule weight coordinates. -/
@[simp]
theorem generatedTangentMatrixLieHom_generatedCartanVector (i : Fin 6) :
    generatedTangentMatrixLieHom R (generatedCartanVector R i) =
      (cartanGeneratorMatrix i).map (Int.cast : ℤ → R) := by
  rw [generatedCartanVector_def]
  exact isSerreSystem.map_lie_eq_intCast (generatedTangentMatrixLieHom R)
    (fun i ↦ generatedTangentMatrixLieHom_generatedRootVector R (.inl i))
    (fun i ↦ generatedTangentMatrixLieHom_generatedRootVector R (.inr i)) i

/-- The normalized root vectors and their Cartan brackets satisfy all E₆ Serre relations. -/
theorem isSerreSystem_generatedRootVector :
    IsSerreSystem R (CartanMatrix.E 6)ᵀ (generatedCartanVector R)
      (fun i ↦ generatedRootVector R (.inl i)) (fun i ↦ generatedRootVector R (.inr i)) := by
  exact isSerreSystem.of_injective_intCast (generatedTangentMatrixLieHom R)
    (generatedTangentMatrixLieHom_injective R)
    (fun i ↦ generatedTangentMatrixLieHom_generatedRootVector R (.inl i))
    (fun i ↦ generatedTangentMatrixLieHom_generatedRootVector R (.inr i))

/-- The comparison from the E₆ Serre presentation to the generated group's tangent Lie algebra. -/
def generatedSerreLift :
    Matrix.ToLieAlgebra R (CartanMatrix.E 6)ᵀ →ₗ⁅R⁆
      Derivation R (generatedCoordinateHopfAlgebra R)
        (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R) :=
  serreLift (isSerreSystem_generatedRootVector R)

/-- The comparison sends a Cartan generator to its opposite-root bracket. -/
@[simp]
theorem generatedSerreLift_serreH (i : Fin 6) :
    generatedSerreLift R (serreH R (CartanMatrix.E 6)ᵀ i) = generatedCartanVector R i :=
  serreLift_serreH _ i

/-- The comparison sends a positive generator to its normalized root vector. -/
@[simp]
theorem generatedSerreLift_serreE (i : Fin 6) :
    generatedSerreLift R (serreE R (CartanMatrix.E 6)ᵀ i) = generatedRootVector R (.inl i) :=
  serreLift_serreE _ i

/-- The comparison sends a negative generator to its normalized root vector. -/
@[simp]
theorem generatedSerreLift_serreF (i : Fin 6) :
    generatedSerreLift R (serreF R (CartanMatrix.E 6)ᵀ i) = generatedRootVector R (.inr i) :=
  serreLift_serreF _ i

/-- The tangent composite is the cast integral minuscule matrix representation. -/
theorem generatedTangentMatrixLieHom_comp_generatedSerreLift :
    (generatedTangentMatrixLieHom R).comp (generatedSerreLift R) =
      serreLift ((isSerreSystem.map (matrixIntCastLieHom R)).changeScalars (S := R)) := by
  apply serre_hom_ext <;> intro i <;>
    simp only [LieHom.comp_apply, generatedSerreLift_serreH, generatedSerreLift_serreE,
      generatedSerreLift_serreF, generatedTangentMatrixLieHom_generatedCartanVector,
      generatedTangentMatrixLieHom_generatedRootVector, serreLift_serreH, serreLift_serreE,
      serreLift_serreF, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
      matrixIntCastLieHom_eq_map]

/-- Over the integers, the tangent composite recovers the existing minuscule representation. -/
theorem generatedTangentMatrixLieHom_comp_generatedSerreLift_int :
    (generatedTangentMatrixLieHom ℤ).comp (generatedSerreLift ℤ) = serreRepresentation := by
  rw [generatedTangentMatrixLieHom_comp_generatedSerreLift, serreLift_intCast isSerreSystem]
  exact (eq_serreLift serreRepresentation_serreH serreRepresentation_serreE
    serreRepresentation_serreF).symm

end

end TauCeti.E6Minuscule
