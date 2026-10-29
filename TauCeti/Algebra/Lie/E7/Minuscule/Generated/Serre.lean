/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.RootWeight
public import TauCeti.Algebra.Lie.Matrix.IntegralCast
public import TauCeti.Algebra.Lie.Presentation.Serre

/-!
# Serre generators in the Lie algebra of the generated E₇ group

The normalized positive and negative root vectors of the generated subgroup of `GL₅₆`
satisfy the E₇ Serre relations over every commutative ring. Their Cartan vectors are their
pairwise brackets. The differential of the closed immersion into `GL₅₆` is injective, so
these relations follow from the existing integral minuscule matrix relations.

This constructs a comparison from the Serre presentation to the Lie algebra of the generated
group and recovers the matrix representation after its tangent inclusion. The companion
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot` module identifies the Cartan vectors with
actual simple-coroot differentials.
The comparison does not assert that these vectors generate the whole Lie algebra.

## Main declarations

* `generatedTangentMatrixLieHom`: the injective matrix realization of the tangent Lie algebra.
* `generatedCartanVector`: the brackets of the normalized opposite simple-root vectors.
* `isSerreSystem_generatedRootVector`: the Serre relations in the generated group's Lie algebra.
* `generatedSerreLift`: the universal comparison with specified generator values.
* `generatedTangentMatrixLieHom_comp_generatedSerreLift`: the matrix factorization.
-/

public section

namespace TauCeti.E7Minuscule

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable (R : Type*) [CommRing R]

/-- The differential of the generated group's closed immersion into `GL₅₆`, in matrix form. -/
def generatedTangentMatrixLieHom :
    Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R) →ₗ⁅R⁆
        Matrix (Fin 56) (Fin 56) R :=
  (GeneralLinear.tangentLieEquivMatrix (R := R) (B := R) 56).toLieHom.comp
    (derivationCompLieHom (B := R) (generatedCoordinateMap R).hom)

/-- The tangent inclusion evaluates a derivation, precomposed with the coordinate map,
on the generic matrix. -/
theorem generatedTangentMatrixLieHom_apply
    (d : Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R)) :
    generatedTangentMatrixLieHom R d = GeneralLinear.tangentMatrix 56
      (derivationComp (B := R) (generatedCoordinateMap R).hom d) := by
  simp only [generatedTangentMatrixLieHom, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    GeneralLinear.tangentLieEquivMatrix_apply, derivationCompLieHom_apply]

/-- The tangent inclusion is injective because the generated coordinate map is surjective. -/
theorem generatedTangentMatrixLieHom_injective :
    Function.Injective (generatedTangentMatrixLieHom R) :=
  (GeneralLinear.tangentLieEquivMatrix (R := R) (B := R) 56).injective.comp
    (derivationCompLieHom_injective_of_surjective _ (generatedCoordinateMap_surjective R))

/-- A normalized root vector maps to its integral raising or lowering matrix. -/
@[simp]
theorem generatedTangentMatrixLieHom_generatedRootVector (k : Fin 7 ⊕ Fin 7) :
    generatedTangentMatrixLieHom R (generatedRootVector R k) =
      (Sum.elim raisingMatrix loweringMatrix k).map (Int.cast : ℤ → R) := by
  rw [generatedTangentMatrixLieHom_apply, tangentMatrix_generatedRootVector]

/-- The Cartan vector defined by the bracket of the normalized opposite root vectors.
The companion `Generated.Coroot` module identifies it with the simple-coroot differential. -/
def generatedCartanVector (i : Fin 7) :
    Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R) :=
  ⁅generatedRootVector R (.inl i), generatedRootVector R (.inr i)⁆

/-- The Cartan vector is the bracket of the normalized opposite simple-root vectors. -/
theorem generatedCartanVector_def (i : Fin 7) :
    generatedCartanVector R i =
      ⁅generatedRootVector R (.inl i), generatedRootVector R (.inr i)⁆ :=
  (rfl)

/-- The Cartan vector maps to the integral Cartan generator matrix `H_i`, the diagonal
matrix of the `i`-th coordinates of the minuscule weights. -/
@[simp]
theorem generatedTangentMatrixLieHom_generatedCartanVector (i : Fin 7) :
    generatedTangentMatrixLieHom R (generatedCartanVector R i) =
      (cartanMatrix i).map (Int.cast : ℤ → R) := by
  rw [generatedCartanVector_def, LieHom.map_lie,
    generatedTangentMatrixLieHom_generatedRootVector,
    generatedTangentMatrixLieHom_generatedRootVector, Sum.elim_inl, Sum.elim_inr]
  simpa only [Function.comp_apply, matrixIntCastLieHom_eq_map] using
    (isSerreSystem.map (matrixIntCastLieHom R)).lie_E_F_self i

/-- The normalized simple-root vectors and their Cartan brackets satisfy all E₇ Serre
relations over any commutative ring, including rings of characteristic two or three. -/
theorem isSerreSystem_generatedRootVector :
    IsSerreSystem R (CartanMatrix.E 7) (generatedCartanVector R)
      (fun i ↦ generatedRootVector R (.inl i)) (fun i ↦ generatedRootVector R (.inr i)) := by
  apply IsSerreSystem.of_injective (generatedTangentMatrixLieHom R)
    (generatedTangentMatrixLieHom_injective R)
  simpa only [Function.comp_def, generatedTangentMatrixLieHom_generatedCartanVector,
    generatedTangentMatrixLieHom_generatedRootVector, Sum.elim_inl, Sum.elim_inr,
    matrixIntCastLieHom_eq_map] using
    (isSerreSystem.map (matrixIntCastLieHom R)).changeScalars (S := R)

/-- The comparison from the E₇ Serre presentation to the Lie algebra of the generated group. -/
def generatedSerreLift :
    Matrix.ToLieAlgebra R (CartanMatrix.E 7) →ₗ⁅R⁆
      Derivation R (generatedCoordinateHopfAlgebra R)
        (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R) :=
  serreLift (isSerreSystem_generatedRootVector R)

/-- The comparison sends a Cartan generator to the bracket-defined Cartan vector. -/
@[simp]
theorem generatedSerreLift_serreH (i : Fin 7) :
    generatedSerreLift R (serreH R (CartanMatrix.E 7) i) = generatedCartanVector R i :=
  serreLift_serreH _ i

/-- The comparison sends a positive generator to its normalized root vector. -/
@[simp]
theorem generatedSerreLift_serreE (i : Fin 7) :
    generatedSerreLift R (serreE R (CartanMatrix.E 7) i) = generatedRootVector R (.inl i) :=
  serreLift_serreE _ i

/-- The comparison sends a negative generator to its normalized root vector. -/
@[simp]
theorem generatedSerreLift_serreF (i : Fin 7) :
    generatedSerreLift R (serreF R (CartanMatrix.E 7) i) = generatedRootVector R (.inr i) :=
  serreLift_serreF _ i

/-- The normalized generator values characterize the comparison uniquely. -/
theorem eq_generatedSerreLift
    {g : Matrix.ToLieAlgebra R (CartanMatrix.E 7) →ₗ⁅R⁆
      Derivation R (generatedCoordinateHopfAlgebra R)
        (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R)}
    (hH : ∀ i, g (serreH R (CartanMatrix.E 7) i) = generatedCartanVector R i)
    (hE : ∀ i, g (serreE R (CartanMatrix.E 7) i) = generatedRootVector R (.inl i))
    (hF : ∀ i, g (serreF R (CartanMatrix.E 7) i) = generatedRootVector R (.inr i)) :
    g = generatedSerreLift R :=
  eq_serreLift hH hE hF

/-- After the tangent inclusion, the comparison is the cast minuscule matrix representation. -/
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
  apply serre_hom_ext
  · intro i
    rw [LieHom.comp_apply, generatedSerreLift_serreH,
      generatedTangentMatrixLieHom_generatedCartanVector]
    calc
      _ = cartanMatrix i := Matrix.ext fun _ _ ↦ Int.cast_id
      _ = _ := (serreRepresentation_serreH i).symm
  · intro i
    rw [LieHom.comp_apply, generatedSerreLift_serreE,
      generatedTangentMatrixLieHom_generatedRootVector, Sum.elim_inl]
    calc
      _ = raisingMatrix i := Matrix.ext fun _ _ ↦ Int.cast_id
      _ = _ := (serreRepresentation_serreE i).symm
  · intro i
    rw [LieHom.comp_apply, generatedSerreLift_serreF,
      generatedTangentMatrixLieHom_generatedRootVector, Sum.elim_inr]
    calc
      _ = loweringMatrix i := Matrix.ext fun _ _ ↦ Int.cast_id
      _ = _ := (serreRepresentation_serreF i).symm

end

end TauCeti.E7Minuscule
