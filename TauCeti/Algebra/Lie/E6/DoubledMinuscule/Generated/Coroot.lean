/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent.Map
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.WeightTorus
public import TauCeti.Algebra.Lie.E6.Minuscule.Root.Coordinates

/-!
# Simple-coroot differentials of the generated doubled E₆ group

The fundamental-weight coordinates define actual simple-coroot cocharacters through the
closed weight torus of the ground-ring-generated doubled minuscule group. Their differentials
have the diagonal matrices of weight–coroot pairings and form a basis of the toral tangent
image over every commutative coefficient algebra. In particular, independence survives
characteristic three and nonreduced coefficient algebras; no Cartan determinant is inverted.

These are toral normalization data for a pinning, not an identification with opposite-root
brackets or a maximality assertion. The generated subgroup is not identified with the
specialization of the integral toral closure or with an independently pinned simply connected
group scheme of type E₆.

## Main declarations

* `generatedCorootCocharacter_eq_cocharacter_coroot_simpleIndex`: identification with the
  numbered simply connected root datum.
* `tangentMatrixLieHom_derivationComp_generatedCorootCocharacter`: the represented differential.
* `linearIndependent_generatedCorootVector`: independence of the simple-coroot differentials.
* `generatedCorootBasis`: their basis of the toral tangent image, expressed as their span.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 21.

The cocharacter and tangent-image construction follows
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot`, using the existing generated doubled E₆
weight torus and the general represented-weight differential formula.
-/

public section

open CategoryTheory

namespace TauCeti.E6DoubledMinuscule

noncomputable section

variable (R : Type*) [CommRing R]

/-- The simple-coroot cocharacter obtained by evaluating a fundamental-weight coordinate
and including the weight torus in the generated doubled minuscule group. -/
def generatedCorootCocharacter (i : Fin 6) :
    generatedCoordinateHopfAlgebra R →ₐc[R] LaurentPolynomial R :=
  (generatedWeightTorusCoordinateMap R).hom.cocharacter
    (Finsupp.applyAddHom i).toMultiplicative

/-- The simple-coroot cocharacter uses the corresponding coordinate evaluation. -/
theorem generatedCorootCocharacter_def (i : Fin 6) :
    generatedCorootCocharacter R i =
      (generatedWeightTorusCoordinateMap R).hom.cocharacter
        (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The coordinate cocharacter is induced by the named Bourbaki simple coroot. -/
theorem generatedCorootCocharacter_eq_cocharacter_coroot_simpleIndex
    (ht : DynkinType.E6.Valid) (i : Fin 6) :
    generatedCorootCocharacter R i =
      (generatedWeightTorusCoordinateMap R).hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          ((DynkinType.E6.simplyConnectedRootDatum ht).coroot
            (DynkinType.E6.simpleIndex ht i))) := by
  rw [generatedCorootCocharacter_def]
  exact congrArg _ (E6Minuscule.cocharEquiv_symm_coroot_simpleIndex ht i).symm

variable {B : Type*} [CommRing B] [Algebra R B]

/-- The differential of a simple coroot is diagonal in the doubled weight basis, with
entries the coordinate weight pairings times the multiplicative tangent parameter. -/
@[simp]
theorem tangentMatrixLieHom_derivationComp_generatedCorootCocharacter (i : Fin 6)
    (d : Derivation R (LaurentPolynomial R)
      (Bialgebra.CounitAlgebra R (LaurentPolynomial R) B)) :
    GeneralLinear.tangentMatrixLieHom (generatedCoordinateMap R).hom
        (derivationComp (generatedCorootCocharacter R i) d) =
      Matrix.diagonal (fun a ↦ matrixWeight a i •
        MultiplicativeGroup.tangentLinearEquiv d) := by
  have hπ : (generatedWeightTorusCoordinateMap R).hom.comp (generatedCoordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) matrixWeight := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  rw [GeneralLinear.tangentMatrixLieHom_apply, generatedCorootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  have heval (a : Fin 54) :
      ((Finsupp.applyAddHom i).toMultiplicative
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (matrixWeight a)))).toAdd =
      matrixWeight a i := by
    simp
  simp only [heval]

/-- The simple-coroot tangent vector, normalized by the unit tangent parameter of `𝔾ₘ`.
The coefficient algebra can be nonreduced and can have any characteristic. -/
def generatedCorootVector (i : Fin 6) :
    Derivation R (generatedCoordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) B) :=
  derivationComp (generatedCorootCocharacter R i)
    (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B))

/-- The coroot vector is the differential at the unit multiplicative tangent parameter. -/
theorem generatedCorootVector_def (i : Fin 6) :
    generatedCorootVector R (B := B) i =
      derivationComp (generatedCorootCocharacter R i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : B)) :=
  (rfl)

/-- The represented coroot vector has the named simple-coroot pairings on its diagonal. -/
@[simp]
theorem tangentMatrixLieHom_generatedCorootVector (ht : DynkinType.E6.Valid) (i : Fin 6) :
    GeneralLinear.tangentMatrixLieHom (generatedCoordinateMap R).hom
        (generatedCorootVector R (B := B) i) =
      Matrix.diagonal (fun a ↦
        ((DynkinType.E6.simplyConnectedRootDatum ht).coroot'
          (DynkinType.E6.simpleIndex ht i) (matrixWeight a) : B)) := by
  rw [generatedCorootVector_def, tangentMatrixLieHom_derivationComp_generatedCorootCocharacter,
    LinearEquiv.apply_symm_apply]
  congr 1
  funext a
  rw [E6Minuscule.coroot'_simpleIndex_apply ht i (matrixWeight a)]
  exact zsmul_one _

/-- The torus differential sends a coordinate tangent vector to the corresponding coroot vector.
-/
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_tangentBasis (i : Fin 6) :
    derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap R).hom
        (SplitTorus.tangentBasis (R := R) (B := B) i) =
      generatedCorootVector R i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis, generatedCorootVector_def,
    generatedCorootCocharacter_def, derivationCompLieHom_apply]

/-- The coroot differentials span exactly the tangent image of the generated weight torus. -/
theorem range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap R).hom).toLinearMap =
      Submodule.span B (Set.range (generatedCorootVector R (B := B))) := by
  simpa only [derivationCompLieHom_apply, ← generatedCorootCocharacter_def R,
    ← generatedCorootVector_def R] using
    SplitTorus.range_derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap R).hom

/-- The closed weight-torus immersion has injective differential over every coefficient algebra.
-/
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_injective :
    Function.Injective
      (derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap R).hom) :=
  derivationCompLieHom_injective_of_surjective _ (generatedWeightTorusCoordinateMap_surjective R)

/-- The numbered simple-coroot differentials are independent over every coefficient algebra. -/
theorem linearIndependent_generatedCorootVector :
    LinearIndependent B (generatedCorootVector R (B := B)) := by
  simpa only [derivationCompLieHom_apply, ← generatedCorootCocharacter_def R,
    ← generatedCorootVector_def R] using
    SplitTorus.linearIndependent_derivationComp_cocharacter
      (B := B) (generatedWeightTorusCoordinateMap R).hom
      (derivationCompLieHom_generatedWeightTorusCoordinateMap_injective R)

/-- The simple-coroot differentials form a basis of their span, the toral tangent image. -/
def generatedCorootBasis :
    Module.Basis (Fin 6) B (Submodule.span B (Set.range (generatedCorootVector R (B := B)))) :=
  Module.Basis.span (linearIndependent_generatedCorootVector R)

/-- Including a coroot basis vector into the tangent algebra gives its named coroot vector. -/
@[simp]
theorem coe_generatedCorootBasis (i : Fin 6) :
    (generatedCorootBasis R (B := B) i :
      Derivation R (generatedCoordinateHopfAlgebra R)
        (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) B)) =
      generatedCorootVector R i :=
  Module.Basis.coe_span_apply (linearIndependent_generatedCorootVector R) i

end

end TauCeti.E6DoubledMinuscule
