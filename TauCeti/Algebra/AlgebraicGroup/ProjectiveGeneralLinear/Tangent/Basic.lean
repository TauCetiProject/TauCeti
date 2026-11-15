/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Antipode
public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Tangent
public import TauCeti.LinearAlgebra.Matrix.Derivation

/-!
# The Lie algebra of the projective general linear group

The tangent Lie algebra of `PGLₙ`, represented as the automorphism group of the matrix
algebra, acts on that algebra by associative derivations. Every such derivation is inner.
Thus its image in the endomorphism algebra is exactly the space of commutators with matrices,
without a restriction on the characteristic or on the rank. Coefficients may lie in any
commutative algebra over the base ring.

The construction uses the closed-subgroup tangent equivalence and the tangent-matrix
identification for `GL`. The linearized multiplication relations characterize its image.
`tangentLieEquivInnerDerivations` identifies it with the range of the adjoint action on
the matrix algebra, bundled as a Lie subalgebra of its endomorphisms.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10, tangent spaces of automorphism groups.
* N. Jacobson, *Basic Algebra II*, inner derivations of matrix algebras.
-/

public section

open Matrix

namespace TauCeti.ProjectiveGeneralLinear

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable (n : ℕ) {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]

/-- The tangent action of the projective general linear group on its matrix algebra.
It is the differential of its defining inclusion into `GL_{n²}`, expressed in the
matrix-unit basis. -/
def tangentEnd :
    Derivation R (coordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra n R) B) →ₗ⁅B⁆
        Module.End B (Matrix (Fin n) (Fin n) B) :=
  ((Matrix.toLinAlgEquiv (matrixUnitBasis n B)).toLieEquiv.toLieHom).comp
    ((GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) (n * n)).toLieHom.comp
      (HopfIdeal.quotientLieHom (B := B) (definingHopfIdeal n R)))

/-- The tangent action is the endomorphism represented by the ambient tangent matrix. -/
@[simp]
theorem tangentEnd_apply
    (d : Derivation R (coordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra n R) B)) :
    tangentEnd n d = Matrix.toLinAlgEquiv (matrixUnitBasis n B)
      (GeneralLinear.tangentMatrix (n * n)
        (HopfIdeal.quotientLieHom (definingHopfIdeal n R) d)) := by
  simp [tangentEnd, GeneralLinear.tangentLieEquivMatrix_apply]

/-- An inner representative gives the ambient tangent matrix by the two Kronecker
multiplication matrices. This formula does not require a choice of normalization. -/
theorem tangentMatrix_eq_of_tangentEnd_eq
    (d : Derivation R (coordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra n R) B))
    (X : Matrix (Fin n) (Fin n) B)
    (hd : tangentEnd (R := R) n d = LinearMap.mulLeft B X - LinearMap.mulRight B X) :
    GeneralLinear.tangentMatrix (n * n)
        (HopfIdeal.quotientLieHom (definingHopfIdeal n R) d) =
      conjugationMatrix X 1 - conjugationMatrix 1 X := by
  apply (Matrix.toLinAlgEquiv (matrixUnitBasis n B)).injective
  rw [← tangentEnd_apply, hd, map_sub]
  simp

private theorem tangentMatrix_conjugationMap_eq_map
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B)) :
    GeneralLinear.tangentMatrix (n * n)
        (HopfIdeal.quotientLieHom (definingHopfIdeal n R)
          (derivationComp (B := B) (conjugationMap n R).hom d)) =
      (conjugationMatrix (GeneralLinear.genericMatrix R n)
        (GeneralLinear.genericMatrix R n)⁻¹).map
          (fun x ↦ Bialgebra.CounitAlgebra.algEquivSelf R
            (GeneralLinear.coordinateHopfAlgebra R n) B (d x)) := by
  -- Differentiate the coordinate matrix identity before evaluating individual entries.
  rw [← map_genericMatrix_conjugationMap, Matrix.map_map]
  ext a b
  -- Use the bialgebra-hom coercion on both sides of the transported identity.
  simp only [HopfIdeal.quotientLieHom_apply, ← LinearMap.comp_apply, ← derivationComp_comp,
    GeneralLinear.tangentMatrix_apply, algEquivSelf_derivationComp_apply,
    Matrix.map_apply, Function.comp_apply, GeneralLinear.genericMatrix_apply,
    CommHopfAlgCat.hom_comp, CommHopfAlgCat.hom_mkQuotient, BialgHom.coe_comp,
    BialgHom.coe_toAlgHom]

private theorem map_derivation_conjugationMatrix_genericMatrix
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B)) :
    (conjugationMatrix (GeneralLinear.genericMatrix R n)
      (GeneralLinear.genericMatrix R n)⁻¹).map
        (fun x ↦ Bialgebra.CounitAlgebra.algEquivSelf R
          (GeneralLinear.coordinateHopfAlgebra R n) B (d x)) =
      conjugationMatrix (GeneralLinear.tangentMatrix n d) 1 -
        conjugationMatrix 1 (GeneralLinear.tangentMatrix n d) := by
  classical
  ext a b
  -- Leibniz differentiates the two factors; inversion contributes the negative sign.
  rw [Matrix.map_apply, ← GeneralLinear.map_antipode_genericMatrix, conjugationMatrix_apply,
    Matrix.map_apply, HopfAlgebra.antipodeAlgHom_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_apply_mul, d.apply_antipode]
  simp only [HopfAlgebra.counit_antipode, map_neg,
    ← GeneralLinear.tangentMatrix_apply, conjugationMatrix_apply, Matrix.sub_apply,
    GeneralLinear.genericMatrix_apply, GeneralLinear.coordinateHopfAlgebra_counit_X,
    Matrix.one_apply]
  split_ifs <;>
    simp only [map_one, map_zero, one_mul, zero_mul, mul_one, mul_zero,
      sub_eq_add_neg, neg_zero, zero_add, add_zero, add_comm]

/-- The differential of conjugation, in the matrix-unit basis, is the matrix of the
commutator with the general-linear tangent matrix. -/
@[simp]
theorem tangentMatrix_quotientLieHom_derivationComp_conjugationMap
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B)) :
    GeneralLinear.tangentMatrix (n * n)
        (HopfIdeal.quotientLieHom (definingHopfIdeal n R)
          (derivationComp (B := B) (conjugationMap n R).hom d)) =
      conjugationMatrix (GeneralLinear.tangentMatrix n d) 1 -
        conjugationMatrix 1 (GeneralLinear.tangentMatrix n d) := by
  rw [tangentMatrix_conjugationMap_eq_map, map_derivation_conjugationMatrix_genericMatrix]

/-- The differential of `GLₙ → PGLₙ` sends a tangent matrix `X` to the inner
derivation `Y ↦ X Y - Y X` of the matrix algebra. -/
@[simp]
theorem tangentEnd_derivationComp_conjugationMap
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B)) :
    tangentEnd n (derivationComp (B := B) (conjugationMap n R).hom d) =
      LinearMap.mulLeft B (GeneralLinear.tangentMatrix n d) -
        LinearMap.mulRight B (GeneralLinear.tangentMatrix n d) := by
  rw [tangentEnd_apply, tangentMatrix_quotientLieHom_derivationComp_conjugationMap]
  simp only [map_sub, toLinAlgEquiv_conjugationMatrix,
    LinearMap.mulLeft_one, LinearMap.mulRight_one, LinearMap.comp_id, LinearMap.id_comp]

/-- The action of the tangent Lie algebra on the matrix algebra is faithful. -/
theorem tangentEnd_injective : Function.Injective (tangentEnd (R := R) (B := B) n) :=
  (Matrix.toLinAlgEquiv (matrixUnitBasis n B)).injective.comp
    ((GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) (n * n)).injective.comp
      (HopfIdeal.quotientLieHom_injective (B := B) (definingHopfIdeal n R)))

/-- A linear endomorphism of the matrix algebra comes from a tangent vector of `PGLₙ`
exactly when it satisfies the associative Leibniz rule. -/
theorem mem_range_tangentEnd_iff_leibniz
    (f : Module.End B (Matrix (Fin n) (Fin n) B)) :
    f ∈ Set.range (tangentEnd (R := R) n) ↔
      ∀ x y, f (x * y) = f x * y + x * f y := by
  let e := GeneralLinear.tangentLieEquivMatrix (R := R) (B := B) (n * n)
  let X := LinearMap.toMatrix (matrixUnitBasis n B) (matrixUnitBasis n B) f
  have hX : e (e.symm X) = X := e.apply_symm_apply X
  have hf : Matrix.toLinAlgEquiv (matrixUnitBasis n B) X = f := by
    exact (Matrix.toLinAlgEquiv (matrixUnitBasis n B)).apply_symm_apply f
  have hmem : e.symm X ∈ (definingHopfIdeal n R).lieSubalgebra (B := B) ↔
      ∀ x y, f (x * y) = f x * y + x * f y := by
    rw [ConstantMultiplication.mem_lieSubalgebra_definingHopfIdeal_iff]
    rw [← GeneralLinear.tangentLieEquivMatrix_apply, hX]
    exact ConstantMultiplication.toMatrix_leibniz_iff (R := R)
      (structureMatrix n R) (matrixUnitBasis n B)
      (toMatrix_mulLeft_matrixUnitBasis n B R) f
  rw [← hmem]
  constructor
  · rintro ⟨d, hd⟩
    have hmatrix : e (HopfIdeal.quotientLieHom (definingHopfIdeal n R) d) = X := by
      apply (Matrix.toLinAlgEquiv (matrixUnitBasis n B)).injective
      rw [hf]
      exact hd
    rw [← hmatrix, e.symm_apply_apply]
    rw [← HopfIdeal.quotientLieEquiv_apply_coe]
    exact ((definingHopfIdeal n R).quotientLieEquiv d).property
  · intro hd
    let q := (definingHopfIdeal n R).quotientLieEquiv (B := B)
    let d := q.symm ⟨e.symm X, hd⟩
    have hqd := congrArg Subtype.val (q.apply_symm_apply ⟨e.symm X, hd⟩)
    rw [HopfIdeal.quotientLieEquiv_apply_coe] at hqd
    refine ⟨d, ?_⟩
    rw [tangentEnd_apply, ← GeneralLinear.tangentLieEquivMatrix_apply, hqd, hX, hf]

/-- The tangent Lie algebra of `PGLₙ` consists exactly of inner associative derivations
of the matrix algebra. This includes ranks zero and one and every characteristic. -/
theorem mem_range_tangentEnd_iff
    (f : Module.End B (Matrix (Fin n) (Fin n) B)) :
    f ∈ Set.range (tangentEnd (R := R) n) ↔
      ∃ X : Matrix (Fin n) (Fin n) B,
        f = LinearMap.mulLeft B X - LinearMap.mulRight B X := by
  rw [mem_range_tangentEnd_iff_leibniz,
    LinearMap.leibniz_iff_exists_matrix_eq_mulLeft_sub_mulRight]

/-- The tangent Lie algebra of `PGLₙ` is the Lie subalgebra of inner derivations of its
matrix algebra, bundled as the range of `LieAlgebra.ad`. This holds over every commutative
coefficient algebra, in all ranks and characteristics. -/
def tangentLieEquivInnerDerivations :
    Derivation R (coordinateHopfAlgebra n R)
        (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra n R) B) ≃ₗ⁅B⁆
      (LieAlgebra.ad B (Matrix (Fin n) (Fin n) B)).range :=
  (LieEquiv.ofInjective (tangentEnd (R := R) (B := B) n) (tangentEnd_injective n)).trans
    (LieEquiv.ofEq _ _ (by
      ext f
      rw [LieHom.coe_range, LieHom.coe_range, mem_range_tangentEnd_iff]
      simp only [Set.mem_range,
        LieAlgebra.ad_eq_lmul_left_sub_lmul_right, Pi.sub_apply]
      exact exists_congr fun X => eq_comm))

/-- The Lie equivalence acts by the tangent endomorphism of the matrix algebra. -/
@[simp]
theorem tangentLieEquivInnerDerivations_apply
    (d : Derivation R (coordinateHopfAlgebra n R)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra n R) B)) :
    (tangentLieEquivInnerDerivations n d : Module.End B (Matrix (Fin n) (Fin n) B)) =
      tangentEnd n d := by
  simp [tangentLieEquivInnerDerivations]

end

end TauCeti.ProjectiveGeneralLinear
