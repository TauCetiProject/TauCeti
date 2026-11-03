/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Subgroup
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Differential

/-!
# Differentials at every root of the short-root F₄ carrier

Differentiate the closed additive subgroup at each of the forty-eight roots of the carrier
generated over 𝔽₂. Its tangent line is exactly the image of the root-subgroup differential,
and its normalized vector is nonzero over every nontrivial coefficient algebra. Its matrix
is the Weyl conjugate of the numbered simple-root matrix. The formulas hold over arbitrary
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
  have hu : AdditiveGroup.gaPointsMulEquiv («R» := ZMod 2) q =
      Multiplicative.ofAdd (SymmetricAlgebra.ι R R 1) := by
    rw [← ofAdd_toAdd (AdditiveGroup.gaPointsMulEquiv («R» := ZMod 2) q),
      AdditiveGroup.toAdd_gaPointsMulEquiv]
    simp [q]
  have hp := coordinatePointsEquiv_weylRootSubgroupCoordinateMap l i S q
  rw [hu] at hp
  rw [← hp]
  erw [coe_coordinatePointsEquiv,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
    GeneralLinear.pointsMulEquiv_apply]
  rw [GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]
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
  ext a b
  rw [GeneralLinear.tangentMatrix_apply, algEquivSelf_derivationComp_apply,
    ← GeneralLinear.genericMatrix_apply]
  have he := congrFun (congrFun hentry a) b
  rw [Matrix.map_apply] at he
  rw [he]
  -- Only the middle root matrix varies with the additive coordinate.
  have hd (c e : Fin 26) :
      Bialgebra.CounitAlgebra.algEquivSelf R S B
        (d ((rootSubgroupPoints (.inl i) S
          (Multiplicative.ofAdd (SymmetricAlgebra.ι R R 1)) :
            Matrix.GeneralLinearGroup (Fin 26) S) c e)) =
        AdditiveGroup.gaTangentLinearEquiv d * (rootMatrix (.inl i) c e : B) := by
    have h := congrFun (congrFun (tangentMatrix_derivationComp_generator_inl (.inl i) d) c) e
    rw [GeneralLinear.tangentMatrix_apply, algEquivSelf_derivationComp_apply,
      ← GeneralLinear.genericMatrix_apply] at h
    have hg := congrFun (congrFun (map_genericMatrix_generator_inl (.inl i)) c) e
    rw [Matrix.map_apply] at hg
    rw [hg] at h
    exact h
  rw [hnB, ← map_inv]
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.GeneralLinearGroup.map_apply, AlgHom.coe_toRingHom, Algebra.ofId_apply, map_sum,
    Bialgebra.CounitAlgebra.algEquivSelf_apply_mul,
    Derivation.map_algebraMap, map_zero, mul_zero, add_zero, zero_add,
    Bialgebra.counit_algebraMap, hd]
  have hcollect (x y z t : B) : z * (x * (t * y)) = t * (x * y * z) := by ring
  simp only [smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  exact hcollect _ _ _ _

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
  -- The explicit index has type Fin 48, the computed number of F₄ roots.
  erw [rootDerivationAt_def, rootSubgroupCoordinateMapAt_simpleIndex,
    cotangentLinearEquiv_rootVector]

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

end

end TauCeti.F4ShortRoot.PrimeField
