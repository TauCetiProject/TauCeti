/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Differential
import TauCeti.LinearAlgebra.Matrix.Polynomial

/-!
# Differentials at every root of the short-root F₄ carrier

Differentiate the closed additive subgroup at each of the forty-eight roots of the carrier
generated over 𝔽₂. Its tangent line is exactly the image of the root-subgroup differential,
and its normalized vector is nonzero over every nontrivial coefficient algebra. Its matrix
is also the linear coefficient of the polynomial root curve, and is the Weyl conjugate of the
numbered simple-root matrix. The formulas hold over arbitrary
commutative 𝔽₂-algebras, including nonreduced ones, and commute with coefficient change.

The normalization uses the same selected Weyl word as the root subgroup. At positive simple
roots it recovers the numbered root vector. No independence of Weyl presentations, exhaustion
of an adjoint weight space, or identification with an independently pinned group is asserted.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* J. S. Milne, *Algebraic Groups* (2017), §10.a.

The universal-point calculation follows `PrimeField.Root.Differential`; the subgroup maps
and their Weyl presentations come from `PrimeField.Root.Subgroup`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

noncomputable section

local notation "R" => ZMod 2
local notation "S" => AdditiveGroup.coordinateHopfAlgebra R
local notation "H₂₆" => GeneralLinear.coordinateHopfAlgebra R 26
local notation "J" => CommHopfAlgCat.commonKernelHopfIdeal generator
local notation "Q" => CommHopfAlgCat.quotient H₂₆ J

private theorem map_genericMatrix_weylRootSubgroupCoordinateMap
    (l : List (Fin 4)) (i : Fin 4) :
    (GeneralLinear.genericMatrix R 26).map
        ((weylRootSubgroupCoordinateMap l i).hom.comp
          (Bialgebra.Quotient.mkBialgHom (J).toIdeal)).toAlgHom =
      ((weylRootSubgroupPoints l i S
        (Multiplicative.ofAdd (SymmetricAlgebra.ι R R 1)) :
          Matrix.GeneralLinearGroup (Fin 26) S) : Matrix (Fin 26) (Fin 26) S) := by
  let A := CommAlgCat.of R S
  let q : HopfAlgebra.points («R» := ZMod 2) (H := AdditiveGroup.coordinateHopfAlgebra R) A :=
    toConv (AlgHom.id R S)
  have hp := coordinatePointsEquiv_weylRootSubgroupCoordinateMap l i S q
  rw [AdditiveGroup.gaPointsMulEquiv_toConv_id] at hp
  rw [← hp]
  -- `erw` erases the `CommAlgCat.of` wrapper of the universal point's value algebra.
  erw [coe_coordinatePointsEquiv,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
    GeneralLinear.pointsMulEquiv_apply]
  rw [GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]
  -- Composing with the universal identity point leaves the underlying algebra map unchanged.
  rfl

/-- The differential of a Weyl-transported root subgroup is the conjugate of the numbered
simple-root matrix, multiplied by the additive tangent parameter. -/
theorem tangentMatrix_derivationComp_weylRootSubgroupCoordinateMap
    {B : Type*} [CommRing B] [Algebra R B] (l : List (Fin 4)) (i : Fin 4)
    (d : Derivation R S (Bialgebra.CounitAlgebra R S B)) :
    GeneralLinear.tangentMatrix 26
        (derivationComp (B := B)
          ((weylRootSubgroupCoordinateMap l i).hom.comp
            (Bialgebra.Quotient.mkBialgHom (J).toIdeal)) d) =
      AdditiveGroup.gaTangentLinearEquiv d •
        ((weylWordPoint l B : Matrix.GeneralLinearGroup (Fin 26) B) *
          (rootMatrix (.inl i)).map (Int.cast : ℤ → B) *
          ((weylWordPoint l B : Matrix.GeneralLinearGroup (Fin 26) B)⁻¹ :
            Matrix.GeneralLinearGroup (Fin 26) B)) := by
  have hn := coe_pointsMap (Algebra.ofId R S) (weylWordPoint l R)
  have hnB := coe_pointsMap (Algebra.ofId R B) (weylWordPoint l R)
  rw [pointsMap_weylWordPoint] at hn hnB
  have hentry := map_genericMatrix_weylRootSubgroupCoordinateMap l i
  simp only [weylRootSubgroupPoints_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    Units.val_mul] at hentry
  rw [hn, ← map_inv] at hentry
  simp only [Matrix.GeneralLinearGroup.val_map_apply, Algebra.toRingHom_ofId] at hentry
  rw [← map_genericMatrix_generator_inl (.inl i)] at hentry
  rw [GeneralLinear.tangentMatrix_derivationComp_eq_mul_mul_of_map_genericMatrix
    ((weylRootSubgroupCoordinateMap l i).hom.comp
      (Bialgebra.Quotient.mkBialgHom (J).toIdeal))
    (generator (.inl (.inl i))).hom _ _ hentry d,
    tangentMatrix_derivationComp_generator_inl]
  rw [hnB, ← map_inv]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.GeneralLinearGroup.val_map_apply, Algebra.toRingHom_ofId]

/-- The unit tangent vector of the selected root subgroup, with values in a coefficient
algebra. Its normalization is fixed by the selected root parametrization. -/
def rootDerivationAt (B : Type*) [CommRing B] [Algebra R B] (k : Fin F4.numRoots) :
    Derivation R Q (Bialgebra.CounitAlgebra R Q B) :=
  derivationComp (B := B) (rootSubgroupCoordinateMapAt k).hom
    ((AdditiveGroup.gaTangentLinearEquiv («R» := ZMod 2) (B := B)).symm 1)

/-- The defining normalization is the image of additive tangent parameter one. -/
theorem rootDerivationAt_def (B : Type*) [CommRing B] [Algebra R B]
    (k : Fin F4.numRoots) :
    rootDerivationAt B k = derivationComp (B := B) (rootSubgroupCoordinateMapAt k).hom
      ((AdditiveGroup.gaTangentLinearEquiv («R» := ZMod 2) (B := B)).symm 1) :=
  (rfl)

/-- Every selected root has a nonzero differential over a nontrivial coefficient algebra. -/
@[simp↓]
theorem rootDerivationAt_ne_zero (B : Type*) [CommRing B] [Algebra R B] [Nontrivial B]
    (k : Fin F4.numRoots) : rootDerivationAt B k ≠ 0 := by
  exact AdditiveGroup.derivationComp_gaTangentLinearEquiv_symm_one_ne_zero _
    (derivationComp_injective_of_surjective (B := B) _
      (rootSubgroupCoordinateMapAt_surjective k))

/-- Coefficient change preserves the selected root normalization. -/
@[simp↓]
theorem mapValue_rootDerivationAt {B C : Type*} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (f : B →ₐ[R] C) (k : Fin F4.numRoots) :
    Derivation.mapValue f (rootDerivationAt B k) = rootDerivationAt C k :=
  AdditiveGroup.mapValue_derivationComp_gaTangentLinearEquiv_symm_one f _

/-- The image of the root-subgroup differential is exactly the line of its normalized
root derivation, over arbitrary coefficient algebras. -/
theorem range_derivationCompLieHom_rootSubgroupCoordinateMapAt (B : Type*)
    [CommRing B] [Algebra R B] (k : Fin F4.numRoots) :
    (derivationCompLieHom (B := B) (rootSubgroupCoordinateMapAt k).hom).range.toSubmodule =
      B ∙ rootDerivationAt B k :=
  AdditiveGroup.range_derivationCompLieHom_eq_span B _

/-- At a positive simple root the new family recovers the original numbered root vector
under cotangent duality. -/
@[simp]
theorem rootDerivationAt_simpleIndex (i : Fin 4) :
    rootDerivationAt R (Fin.castAdd 44 i) =
      Derivation.cotangentLinearEquiv (B := R) (rootVector (.inl i)) := by
  simp only [rootDerivationAt, rootSubgroupCoordinateMapAt_simpleIndex]
  exact (cotangentLinearEquiv_rootVector (.inl i)).symm

/-- The matrix of every selected root differential is the Weyl conjugate of its simple
root matrix. The word and node are those of the root subgroup itself. -/
theorem tangentMatrix_rootDerivationAt (B : Type*) [CommRing B] [Algebra R B]
    (k : Fin F4.numRoots) :
    GeneralLinear.tangentMatrix 26 (HopfIdeal.quotientLieHom J (rootDerivationAt B k)) =
      (weylWordPoint (F4ShortRoot.rootSubgroupPresentation k).1 B :
        Matrix.GeneralLinearGroup (Fin 26) B) *
      (rootMatrix (.inl (F4ShortRoot.rootSubgroupPresentation k).2)).map (Int.cast : ℤ → B) *
      ((weylWordPoint (F4ShortRoot.rootSubgroupPresentation k).1 B :
        Matrix.GeneralLinearGroup (Fin 26) B)⁻¹ : Matrix.GeneralLinearGroup (Fin 26) B) := by
  rw [rootDerivationAt_def, HopfIdeal.quotientLieHom_apply,
    ← LinearMap.comp_apply, ← derivationComp_comp, rootSubgroupCoordinateMapAt_def,
    tangentMatrix_derivationComp_weylRootSubgroupCoordinateMap,
    LinearEquiv.apply_symm_apply, one_smul]

/-- The coefficient of the linear parameter in a selected root curve is its normalized
root differential. The scalar parameter is retained over every coefficient algebra. -/
theorem map_coeff_one_rootSubgroupPointsAt (B : Type*) [CommRing B] [Algebra R B]
    (k : Fin F4.numRoots) (c : B) :
    (((rootSubgroupPointsAt k (Polynomial B)
        (Multiplicative.ofAdd (Polynomial.C c * Polynomial.X)) :
        Matrix.GeneralLinearGroup (Fin 26) (Polynomial B)) :
        Matrix (Fin 26) (Fin 26) (Polynomial B)).map (fun p ↦ p.coeff 1)) =
      c • GeneralLinear.tangentMatrix 26
        (HopfIdeal.quotientLieHom J (rootDerivationAt B k)) := by
  let l := (F4ShortRoot.rootSubgroupPresentation k).1
  let i := (F4ShortRoot.rootSubgroupPresentation k).2
  have hW := coe_pointsMap (Polynomial.CAlgHom («R» := ZMod 2) (A := B)) (weylWordPoint l B)
  rw [pointsMap_weylWordPoint] at hW
  rw [rootSubgroupPointsAt_def, weylRootSubgroupPoints_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  rw [hW, ← map_inv]
  simp only [Matrix.GeneralLinearGroup.val_map_apply]
  have hC : ((Polynomial.CAlgHom : B →ₐ[ZMod 2] Polynomial B) : B →+* Polynomial B) =
      Polynomial.C := rfl
  rw [hC]
  rw [Matrix.map_coeff_mul_map_C, Matrix.map_coeff_map_C_mul]
  have hroot : (((rootSubgroupPoints (.inl i) (Polynomial B)
      (Multiplicative.ofAdd (Polynomial.C c * Polynomial.X)) :
        Matrix.GeneralLinearGroup (Fin 26) (Polynomial B)) :
        Matrix (Fin 26) (Fin 26) (Polynomial B)).map (fun p ↦ p.coeff 1)) =
      c • (rootMatrix (.inl i)).map (Int.cast : ℤ → B) := by
    rw [coe_rootSubgroupPoints, F4ShortRoot.coe_rootSubgroupPoints_eq]
    ext a b
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      toAdd_ofAdd, smul_eq_mul]
    have h12 : (1 : ℕ) ≠ 2 := by decide
    by_cases hab : a = b <;>
      simp only [Matrix.one_apply, hab, ↓reduceIte, mul_pow, ← Polynomial.C_pow,
        ← Polynomial.C_eq_intCast, Polynomial.coeff_add, Polynomial.coeff_mul_C,
        Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
        Polynomial.coeff_one, one_ne_zero, h12, ↓reduceIte,
        mul_one, mul_zero, zero_mul, zero_add, add_zero]
  rw [hroot, Matrix.mul_smul, Matrix.smul_mul, tangentMatrix_rootDerivationAt]

end

end TauCeti.F4ShortRoot.PrimeField
