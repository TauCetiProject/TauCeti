/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Tangent
public import TauCeti.Algebra.Lie.E6.Minuscule.Generated.Serre
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly
import TauCeti.Algebra.Lie.E6.Minuscule.Generated.WeightTorus

/-!
# Simple-coroot differentials in the generated E₆ group

The simple coroots, expressed as fundamental-weight coordinate evaluations, define
cocharacters through the weight torus of the generated subgroup of `GL₂₇`. Their differentials
are precisely the opposite-root brackets `generatedCartanVector`, over every commutative ring.
Thus the Serre comparison sends its Cartan generators to the actual coroot differentials,
not merely to matrices with the expected eigenvalues.

`generatedCartanBasis` gives a basis of the toral tangent image. The torus differential and
these six vectors are injective and independent, respectively, even in characteristic three,
where the E₆ Cartan matrix itself becomes singular. This uses the full weight lattice of the
minuscule representation, not invertibility of the Cartan matrix. Neither maximality of the
torus nor surjectivity of the Serre comparison is asserted.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
* The coroot comparison follows `TauCeti.Algebra.Lie.E7.Minuscule.Generated.Coroot`, using
  the generic `DynkinType.coroot_simpleIndex` and split-torus tangent interfaces directly.
-/

public section

open CategoryTheory
open scoped Matrix

namespace TauCeti.E6Minuscule

noncomputable section

variable (R : Type*) [CommRing R]

/-- Evaluate a fundamental-weight coordinate, then include the resulting cocharacter
through the weight torus of the generated group. -/
def generatedCorootCocharacter (i : Fin 6) :
    generatedCoordinateHopfAlgebra R →ₐc[R] LaurentPolynomial R :=
  (generatedWeightTorusCoordinateMap R).hom.cocharacter
    (Finsupp.applyAddHom i).toMultiplicative

/-- The defining coordinate evaluation of the coroot cocharacter. -/
theorem generatedCorootCocharacter_def (i : Fin 6) :
    generatedCorootCocharacter R i =
      (generatedWeightTorusCoordinateMap R).hom.cocharacter
        (Finsupp.applyAddHom i).toMultiplicative :=
  (rfl)

/-- The cocharacter is the numbered simple coroot of the simply connected E₆ root datum. -/
theorem generatedCorootCocharacter_eq_cocharacter_coroot_simpleIndex (i : Fin 6) :
    generatedCorootCocharacter R i =
      (generatedWeightTorusCoordinateMap R).hom.cocharacter
        (SplitTorus.cocharEquiv.symm
          ((DynkinType.E6.simplyConnectedRootDatum DynkinType.valid_E6).coroot
            (DynkinType.E6.simpleIndex DynkinType.valid_E6 i))) := by
  rw [generatedCorootCocharacter_def]
  congr 1
  apply SplitTorus.cocharEquiv.eq_symm_apply.mpr
  have heval : SplitTorus.cocharEquiv (Finsupp.applyAddHom i).toMultiplicative =
      (Pi.single i 1 : Fin 6 → ℤ) := by
    ext j
    simp [SplitTorus.cocharEquiv_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  -- The generic formula uses `Fin E6.rank`, which is definitionally `Fin 6`.
  exact heval.trans (DynkinType.E6.coroot_simpleIndex DynkinType.valid_E6 i).symm

/-- The coroot differential has diagonal entries given by pairing each minuscule weight
with the corresponding simple coroot. The tangent vector of `𝔾ₘ` is normalized to one. -/
theorem generatedTangentMatrixLieHom_derivationComp_generatedCorootCocharacter (i : Fin 6) :
    generatedTangentMatrixLieHom R
        (derivationComp (generatedCorootCocharacter R i)
          (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R))) =
      Matrix.diagonal fun a ↦
        ((DynkinType.E6.simplyConnectedRootDatum DynkinType.valid_E6).coroot'
          (DynkinType.E6.simpleIndex DynkinType.valid_E6 i)
          (DynkinType.e6MinusculeWeight a) : R) := by
  have hπ : (generatedWeightTorusCoordinateMap R).hom.comp (generatedCoordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) DynkinType.e6MinusculeWeight := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap, weightTable_weight]
  rw [generatedTangentMatrixLieHom_apply, generatedCorootCocharacter_def,
    GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus _ _ _ hπ]
  congr 1
  ext a
  -- Supply the rank-indexed arguments explicitly: `Fin E6.rank` is definitionally `Fin 6`.
  rw [DynkinType.E6.coroot'_simpleIndex_apply DynkinType.valid_E6 i
    (DynkinType.e6MinusculeWeight a)]
  simp

/-- The opposite-root bracket is the differential of the actual simple-coroot cocharacter. -/
theorem generatedCartanVector_eq_derivationComp_generatedCorootCocharacter (i : Fin 6) :
    generatedCartanVector R i =
      derivationComp (generatedCorootCocharacter R i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R)) := by
  apply generatedTangentMatrixLieHom_injective R
  rw [generatedTangentMatrixLieHom_generatedCartanVector,
    generatedTangentMatrixLieHom_derivationComp_generatedCorootCocharacter]
  ext a b
  simp only [Matrix.map_apply, cartanGeneratorMatrix_apply, Matrix.diagonal_apply]
  split_ifs with hab
  · subst b
    -- As above, supply the arguments to specialize from `Fin E6.rank` to `Fin 6`.
    rw [DynkinType.E6.coroot'_simpleIndex_apply DynkinType.valid_E6 i
      (DynkinType.e6MinusculeWeight a)]
  · simp

/-- The Serre comparison sends its Cartan generators to the simple-coroot differentials. -/
theorem generatedSerreLift_serreH_eq_derivationComp_generatedCorootCocharacter (i : Fin 6) :
    generatedSerreLift R (serreH R (CartanMatrix.E 6)ᵀ i) =
      derivationComp (generatedCorootCocharacter R i)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R)) := by
  rw [generatedSerreLift_serreH,
    generatedCartanVector_eq_derivationComp_generatedCorootCocharacter]

/-- The differential of a coordinate cocharacter of the generated weight torus is its
numbered Cartan vector. -/
-- Rewrite before `derivationCompLieHom_apply` unfolds the differential.
@[simp↓]
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_cocharacter (i : Fin 6) :
    derivationCompLieHom
        ((generatedWeightTorusCoordinateMap R).hom.cocharacter
          (Finsupp.applyAddHom i).toMultiplicative)
        (MultiplicativeGroup.tangentLinearEquiv.symm (1 : R)) = generatedCartanVector R i := by
  rw [generatedCartanVector_eq_derivationComp_generatedCorootCocharacter,
    generatedCorootCocharacter_def, derivationCompLieHom_apply]

/-- A coordinate tangent basis vector of the weight torus maps to its Cartan vector. -/
-- Rewrite before `derivationCompLieHom_apply` unfolds the differential.
@[simp↓]
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_tangentBasis (i : Fin 6) :
    derivationCompLieHom (B := R) (generatedWeightTorusCoordinateMap R).hom
        (SplitTorus.tangentBasis (R := R) (B := R) i) = generatedCartanVector R i := by
  rw [SplitTorus.derivationCompLieHom_tangentBasis,
    derivationCompLieHom_generatedWeightTorusCoordinateMap_cocharacter]

/-- The tangent image of the weight torus is the span of the opposite-root brackets. -/
theorem range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span :
    LinearMap.range
        (derivationCompLieHom (B := R) (generatedWeightTorusCoordinateMap R).hom).toLinearMap =
      Submodule.span R (Set.range (generatedCartanVector R)) := by
  rw [SplitTorus.range_derivationCompLieHom]
  congr 1
  apply congrArg Set.range
  funext i
  exact derivationCompLieHom_generatedWeightTorusCoordinateMap_cocharacter R i

/-- The entire toral tangent image lies in the image of the Serre comparison. -/
theorem range_derivationCompLieHom_generatedWeightTorusCoordinateMap_le_range_generatedSerreLift :
    LinearMap.range
        (derivationCompLieHom (B := R) (generatedWeightTorusCoordinateMap R).hom).toLinearMap ≤
      LinearMap.range (generatedSerreLift R).toLinearMap := by
  rw [range_derivationCompLieHom_generatedWeightTorusCoordinateMap_eq_span, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨serreH R (CartanMatrix.E 6)ᵀ i, generatedSerreLift_serreH R i⟩

/-- The weight-torus differential is injective with values in every commutative algebra. -/
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_injective
    (B : Type*) [CommRing B] [Algebra R B] :
    Function.Injective
      (derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap R).hom) := by
  apply derivationCompLieHom_injective_of_surjective
  simpa only [generatedWeightTorusCoordinateMap_def] using
    Generated.generatedCoordinateLift_torus_surjective R

/-- The six Cartan vectors are independent over every commutative ring. -/
theorem linearIndependent_generatedCartanVector :
    LinearIndependent R (generatedCartanVector R) := by
  have h := SplitTorus.linearIndependent_derivationCompLieHom_cocharacter
    (generatedWeightTorusCoordinateMap R).hom
    (derivationCompLieHom_generatedWeightTorusCoordinateMap_injective R R)
  convert h using 1
  funext i
  exact (derivationCompLieHom_generatedWeightTorusCoordinateMap_cocharacter R i).symm

/-- The simple-coroot differentials give a basis of their span, the toral tangent image. -/
def generatedCartanBasis :
    Module.Basis (Fin 6) R (Submodule.span R (Set.range (generatedCartanVector R))) :=
  Module.Basis.span (linearIndependent_generatedCartanVector R)

/-- The included Cartan basis vector is the numbered opposite-root bracket. -/
@[simp]
theorem coe_generatedCartanBasis (i : Fin 6) :
    (generatedCartanBasis R i :
      Derivation R (generatedCoordinateHopfAlgebra R)
        (Bialgebra.CounitAlgebra R (generatedCoordinateHopfAlgebra R) R)) =
      generatedCartanVector R i :=
  Module.Basis.coe_span_apply (linearIndependent_generatedCartanVector R) i

/-- The Cartan generators of the E₆ Serre presentation are independent over every ring. -/
theorem linearIndependent_serreH :
    LinearIndependent R (serreH R (CartanMatrix.E 6)ᵀ) :=
  TauCeti.linearIndependent_serreH (isSerreSystem_generatedRootVector R)
    (linearIndependent_generatedCartanVector R)

end

end TauCeti.E6Minuscule
