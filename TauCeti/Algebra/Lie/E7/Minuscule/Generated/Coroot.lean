/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.E7.Minuscule.Generated.Serre

/-!
# Simple-coroot differentials in the generated E₇ group

The simple coroots in fundamental-weight coordinates define actual cocharacters through the
weight torus of the generated group. Their differentials at the unit tangent vector are the
brackets of the normalized opposite root vectors, over every commutative ring.

The calculation uses character–cocharacter pairings in the 56-dimensional minuscule
representation and the injective tangent inclusion. Consequently the Serre comparison sends
its Cartan generators to these coroot differentials. They form a basis of the tangent image
of the weight torus, which is contained in the image of the Serre comparison. This also proves
linear independence of the presented Serre Cartan generators over every commutative ring.
No assertion of torus maximality or of surjectivity of the Serre comparison is needed.

## Main declarations

* `generatedCorootCocharacter`: the cocharacter defined by a fundamental-weight coordinate.
* `generatedCorootCocharacter_eq_cocharacter_coroot_simpleIndex`:
  its identification with the named simple coroot.
* `generatedTangentMatrixLieHom_derivationComp_generatedCorootCocharacter`:
  its matrix of weight–coroot pairings.
* `generatedCartanVector_eq_derivationComp_generatedCorootCocharacter`:
  the normalized opposite-root bracket.
* `generatedSerreLift_serreH_eq_derivationComp_generatedCorootCocharacter`:
  the Cartan-generator value of the comparison.
* `range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span`: the toral tangent image.
* `range_derivationCompLieHom_generatedWeightTorusCoordinateMap_le_range_generatedSerreLift`:
  containment of that image in the Serre image.
* `linearIndependent_generatedCartanVector`: independence of the numbered Cartan vectors.
* `generatedCartanBasis`: their basis of the toral tangent image.
* `linearIndependent_serreH`: independence of the presented E₇ Cartan generators.
-/

public section

open CategoryTheory

namespace TauCeti.E7Minuscule

noncomputable section

variable (R : Type*) [CommRing R]

/-- The simple cocharacter obtained by evaluating a fundamental-weight coordinate at `i`
and then including the weight torus in the generated group. -/
def generatedCorootCocharacter (i : Fin 7) :
    generatedCoordinateHopfAlgebra R →ₐc[R] LaurentPolynomial R :=
  (generatedWeightTorusCoordinateMap R).hom.cocharacter
    (Finsupp.applyAddHom i).toMultiplicative

/-- The simple cocharacter is induced by evaluation at its fundamental-weight coordinate. -/
theorem generatedCorootCocharacter_def (i : Fin 7) :
    generatedCorootCocharacter R i =
      (generatedWeightTorusCoordinateMap R).hom.cocharacter
        (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The cocharacter is the named simple coroot of the simply connected E₇ root datum,
with the existing simple-root numbering. -/
theorem generatedCorootCocharacter_eq_cocharacter_coroot_simpleIndex
    (ht : DynkinType.E7.Valid) (i : Fin 7) :
    generatedCorootCocharacter R i =
      (generatedWeightTorusCoordinateMap R).hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          ((DynkinType.E7.simplyConnectedRootDatum ht).coroot
            (DynkinType.E7.simpleIndex ht i))) := by
  rw [generatedCorootCocharacter_def]
  congr 1
  exact (cocharEquiv_symm_coroot_simpleIndex ht i).symm

/-- The differential of the `i`-th coroot has diagonal entries given by pairing the
minuscule weights with the named simple coroot. The tangent vector of `𝔾ₘ` is normalized to one. -/
theorem generatedTangentMatrixLieHom_derivationComp_generatedCorootCocharacter
    (ht : DynkinType.E7.Valid) (i : Fin 7) :
    generatedTangentMatrixLieHom R
        (derivationComp (generatedCorootCocharacter R i)
          (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R))) =
      Matrix.diagonal fun a ↦
        ((DynkinType.E7.simplyConnectedRootDatum ht).coroot'
          (DynkinType.E7.simpleIndex ht i) (DynkinType.e7MinusculeWeight a) : R) := by
  have hπ : (generatedWeightTorusCoordinateMap R).hom.comp (generatedCoordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) DynkinType.e7MinusculeWeight := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  rw [generatedTangentMatrixLieHom_apply, generatedCorootCocharacter_def,
    ← GeneralLinear.tangentMatrixLieHom_apply]
  exact generalLinearTangentMatrixLieHom_derivationComp_cocharacter_applyAddHom _ _ hπ ht i

/-- The bracket of the opposite normalized root vectors is the differential of the
corresponding actual coroot cocharacter, with no characteristic assumption. -/
theorem generatedCartanVector_eq_derivationComp_generatedCorootCocharacter (i : Fin 7) :
    generatedCartanVector R i =
      derivationComp (generatedCorootCocharacter R i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R)) := by
  apply generatedTangentMatrixLieHom_injective R
  rw [generatedTangentMatrixLieHom_generatedCartanVector,
    generatedTangentMatrixLieHom_derivationComp_generatedCorootCocharacter R DynkinType.valid_E7,
    cartanMatrix_map_intCast_eq_diagonal_coroot' DynkinType.valid_E7]

/-- The Serre comparison sends each Cartan generator to the actual simple-coroot differential. -/
theorem generatedSerreLift_serreH_eq_derivationComp_generatedCorootCocharacter (i : Fin 7) :
    generatedSerreLift R (serreH R (CartanMatrix.E 7) i) =
      derivationComp (generatedCorootCocharacter R i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R)) := by
  rw [generatedSerreLift_serreH,
    generatedCartanVector_eq_derivationComp_generatedCorootCocharacter]

/-- The differential of a coordinate cocharacter of the generated weight torus is its
numbered Cartan vector. -/
-- Rewrite before `derivationCompLieHom_apply` unfolds the differential.
@[simp↓]
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_cocharacter (i : Fin 7) :
    derivationCompLieHom
        ((generatedWeightTorusCoordinateMap R).hom.cocharacter
          (Finsupp.applyAddHom i).toMultiplicative)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R)) = generatedCartanVector R i := by
  rw [generatedCartanVector_eq_derivationComp_generatedCorootCocharacter,
    generatedCorootCocharacter_def, derivationCompLieHom_apply]

/-- The weight-torus differential sends a coordinate tangent vector to its Cartan vector. -/
-- Rewrite before `derivationCompLieHom_apply` unfolds the differential.
@[simp↓]
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_tangentBasis (i : Fin 7) :
    derivationCompLieHom (B := R) (generatedWeightTorusCoordinateMap R).hom
        (SplitTorus.tangentBasis (R := R) (B := R) i) = generatedCartanVector R i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis,
    derivationCompLieHom_generatedWeightTorusCoordinateMap_cocharacter]

/-- The tangent image of the generated weight torus is the span of the normalized
Cartan vectors. No injectivity of the torus differential is assumed. -/
theorem range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := R) (generatedWeightTorusCoordinateMap R).hom).toLinearMap =
      Submodule.span R (Set.range (generatedCartanVector R)) := by
  simpa only [derivationCompLieHom_apply, ← generatedCorootCocharacter_def R,
    ← generatedCartanVector_eq_derivationComp_generatedCorootCocharacter R] using
    SplitTorus.range_derivationCompLieHom (B := R) (generatedWeightTorusCoordinateMap R).hom

/-- Every tangent vector in the weight-torus image is in the image of the Serre comparison. -/
theorem range_derivationCompLieHom_generatedWeightTorusCoordinateMap_le_range_generatedSerreLift :
    LinearMap.range
        (derivationCompLieHom (B := R) (generatedWeightTorusCoordinateMap R).hom).toLinearMap ≤
      LinearMap.range (generatedSerreLift R).toLinearMap := by
  rw [range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨serreH R (CartanMatrix.E 7) i, generatedSerreLift_serreH R i⟩

/-- The weight-torus differential is injective over every coefficient algebra. -/
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_injective
    (B : Type*) [CommRing B] [Algebra R B] :
    Function.Injective
      (derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap R).hom) := by
  apply derivationCompLieHom_injective_of_surjective
  have h : Function.Surjective
      (coordinateMap R ≫ weightTorusToBaseChangeCoordinateMap R).hom := by
    simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] using
      (weightTorusToBaseChangeCoordinateMap_surjective R).comp (coordinateMap_surjective R)
  rw [coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
    ← generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap] at h
  exact Function.Surjective.of_comp
    (by simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] using h)

/-- The numbered Cartan vectors are independent, including in characteristic two. -/
theorem linearIndependent_generatedCartanVector :
    LinearIndependent R (generatedCartanVector R) := by
  simpa only [derivationCompLieHom_apply, ← generatedCorootCocharacter_def R,
    ← generatedCartanVector_eq_derivationComp_generatedCorootCocharacter R] using
    SplitTorus.linearIndependent_derivationCompLieHom_cocharacter
      (B := R) (generatedWeightTorusCoordinateMap R).hom
      (derivationCompLieHom_generatedWeightTorusCoordinateMap_injective R R)

/-- The simple-coroot differentials form a basis of their span, the toral tangent image. -/
def generatedCartanBasis :
    Module.Basis (Fin 7) R (Submodule.span R (Set.range (generatedCartanVector R))) :=
  Module.Basis.span (linearIndependent_generatedCartanVector R)

/-- Including a Cartan basis vector into the tangent algebra gives the numbered Cartan vector. -/
@[simp]
theorem coe_generatedCartanBasis (i : Fin 7) :
    (generatedCartanBasis R i :
      Derivation R (generatedCoordinateHopfAlgebra R)
        (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R)) =
      generatedCartanVector R i :=
  Module.Basis.coe_span_apply (linearIndependent_generatedCartanVector R) i

/-- The presented E₇ Cartan generators are independent over every commutative ring. -/
theorem linearIndependent_serreH :
    LinearIndependent R (serreH R (CartanMatrix.E 7)) :=
  TauCeti.linearIndependent_serreH (isSerreSystem_generatedRootVector R)
    (linearIndependent_generatedCartanVector R)

end

end TauCeti.E7Minuscule
