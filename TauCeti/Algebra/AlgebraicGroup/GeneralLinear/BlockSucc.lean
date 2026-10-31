/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.MultiplicativeMatrix
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
public import TauCeti.Algebra.Lie.GeneralLinear.Embedding
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.BlockSucc

/-!
# The block inclusion `GLₙ → GLₙ₊₁` in coordinates

Placing an invertible matrix in the upper-left block of a matrix of the next size, and filling
the last row and column with those of the identity matrix, is the block inclusion
`TauCeti.glBlockSucc : GL (Fin n) A →* GL (Fin (n + 1)) A`. It is natural in the value algebra
`A`, so it is a homomorphism of affine group schemes `GLₙ → GLₙ₊₁`, and it is induced by a
morphism of coordinate Hopf algebras

`TauCeti.GeneralLinear.blockSuccCoordinateMap R n : O(GLₙ₊₁) →ₐc[R] O(GLₙ)`.

This file constructs that morphism as the coordinate morphism of the multiplicative matrix
`Matrix.blockSucc` of the generic matrix of `GLₙ`, identifies its action on points with the block
inclusion, and computes its differential: a tangent vector of `GLₙ` with matrix `X` goes to the
tangent vector of `GLₙ₊₁` with matrix `X` in the upper-left block and zeros elsewhere, the corner
embedding `TauCeti.glEmbedding R Fin.castSuccEmb X`. The constant last diagonal entry `1`
contributes nothing to the derivative.

This is what lets the differential of a representation of `GLₙ₊₁` be compared with the
differential of its restriction to `GLₙ`.

## Main definitions

* `TauCeti.GeneralLinear.blockSuccCoordinateMap`: the coordinate morphism of the block
  inclusion.

## Main results

* `TauCeti.GeneralLinear.blockSuccCoordinateMap_apply_X`: it sends a generic matrix entry of
  `GLₙ₊₁` to the corresponding entry of `Matrix.blockSucc` of the generic matrix of `GLₙ`.
* `TauCeti.GeneralLinear.pointsMulEquiv_mapDomain_blockSuccCoordinateMap`: on points it is the
  block inclusion `TauCeti.glBlockSucc`.
* `TauCeti.GeneralLinear.tangentMatrix_derivationComp_blockSuccCoordinateMap`: its differential
  is the corner embedding of matrices.
-/

public section

open WithConv

namespace TauCeti.GeneralLinear

universe u v

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The extension of the generic matrix of `GLₙ` to size `n + 1` is multiplicative for the
comultiplication, as the generic matrix is. -/
private theorem map_comul_blockSucc_genericMatrix :
    (Matrix.blockSucc (genericMatrix R n)).map (Bialgebra.comulAlgHom R _) =
      (Matrix.blockSucc (genericMatrix R n)).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (Matrix.blockSucc (genericMatrix R n)).map
          (Algebra.TensorProduct.includeRight (R := R)) := by
  rw [Matrix.map_blockSucc, Matrix.map_blockSucc, Matrix.map_blockSucc, map_comul_genericMatrix,
    Matrix.blockSucc_mul]

/-- The extension of the generic matrix of `GLₙ` to size `n + 1` is unital for the counit. -/
private theorem map_counit_blockSucc_genericMatrix :
    (Matrix.blockSucc (genericMatrix R n)).map (Bialgebra.counitAlgHom R _) = 1 := by
  rw [Matrix.map_blockSucc, map_counit_genericMatrix, Matrix.blockSucc_one]

/-- **The coordinate morphism of the block inclusion** `GLₙ → GLₙ₊₁`: the morphism of coordinate
Hopf algebras sending the generic matrix of `GLₙ₊₁` to the generic matrix of `GLₙ` placed in the
upper-left block, with the last row and column of the identity matrix. On points it is
`TauCeti.glBlockSucc` (`TauCeti.GeneralLinear.pointsMulEquiv_mapDomain_blockSuccCoordinateMap`). -/
noncomputable def blockSuccCoordinateMap :
    coordinateHopfAlgebra R (n + 1) →ₐc[R] coordinateHopfAlgebra R n :=
  coordinateBialgHomOfMultiplicative R (n + 1) (Matrix.blockSucc (genericMatrix R n))
    (map_comul_blockSucc_genericMatrix R n) (map_counit_blockSucc_genericMatrix R n)

/-- The coordinate morphism of the block inclusion sends a generic matrix entry of `GLₙ₊₁` to the
corresponding entry of the extended generic matrix of `GLₙ`. -/
@[simp]
theorem blockSuccCoordinateMap_apply_X (i j : Fin (n + 1)) :
    blockSuccCoordinateMap R n
        (coordinateHopfAlgebraAlgEquiv R (n + 1)
          (coordinateRingMap R (n + 1) (MvPolynomial.X (i, j)))) =
      Matrix.blockSucc (genericMatrix R n) i j :=
  coordinateBialgHomOfMultiplicative_X ..

/-- **On points the coordinate morphism is the block inclusion**: precomposing an `A`-valued
point of `GLₙ` with `TauCeti.GeneralLinear.blockSuccCoordinateMap` gives the point of `GLₙ₊₁`
whose matrix is the block extension of the original one. -/
theorem pointsMulEquiv_mapDomain_blockSuccCoordinateMap {A : Type v} [CommRing A] [Algebra R A]
    (f : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)) :
    pointsMulEquiv (n + 1) (BialgHom.mapDomain (blockSuccCoordinateMap R n) f) =
      glBlockSucc A n (pointsMulEquiv n f) := by
  refine Matrix.GeneralLinearGroup.ext fun i j ↦ ?_
  rw [pointsMulEquiv_apply, pointToGeneralLinear_apply, BialgHom.mapDomain_apply, ofConv_toConv,
    AlgHom.comp_apply, BialgHom.coe_toAlgHom, blockSuccCoordinateMap_apply_X, coe_glBlockSucc,
    ← Matrix.map_apply (f := f.ofConv), Matrix.map_blockSucc, pointsMulEquiv_apply]
  congr 2
  ext a b
  rw [Matrix.map_apply, pointToGeneralLinear_apply, genericMatrix_apply]

/-- **The differential of the block inclusion** `GLₙ → GLₙ₊₁` places the matrix of a tangent
vector in the upper-left block: it is the corner embedding of `n × n` matrices in
`(n + 1) × (n + 1)` matrices along `Fin.castSucc`. This holds over every commutative base ring and
coefficient algebra. -/
@[simp]
theorem tangentMatrix_derivationComp_blockSuccCoordinateMap {B : Type v} [CommRing B]
    [Algebra R B]
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    tangentMatrix (n + 1) (derivationComp (B := B) (blockSuccCoordinateMap R n) d) =
      glEmbedding B Fin.castSuccEmb (tangentMatrix n d) := by
  ext i j
  rw [tangentMatrix_apply, algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom,
    blockSuccCoordinateMap_apply_X]
  -- Off the upper-left block the corner embedding has no matrix unit, while the extended
  -- generic matrix has the constant entries `0` and `1` there, which every derivation kills.
  have hzero (i j : Fin (n + 1)) (h : i = Fin.last n ∨ j = Fin.last n) :
      glEmbedding B Fin.castSuccEmb (tangentMatrix n d) i j = 0 := by
    rw [glEmbedding_eq_sum_single, Matrix.sum_apply]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    rw [Matrix.sum_apply]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rcases h with rfl | rfl
    · exact Matrix.single_apply_of_row_ne (Fin.castSucc_ne_last a) _ _ _
    · exact Matrix.single_apply_of_col_ne _ _ (Fin.castSucc_ne_last b) _
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      rw [hzero _ _ (.inl rfl), Matrix.blockSucc_last_last, Derivation.map_one_eq_zero, map_zero]
    | cast j => rw [hzero _ _ (.inl rfl), Matrix.blockSucc_last_castSucc, map_zero, map_zero]
  | cast i =>
    induction j using Fin.lastCases with
    | last => rw [hzero _ _ (.inr rfl), Matrix.blockSucc_castSucc_last, map_zero, map_zero]
    | cast j =>
      rw [Matrix.blockSucc_castSucc_castSucc, genericMatrix_apply, ← tangentMatrix_apply,
        ← Fin.coe_castSuccEmb, glEmbedding_apply_apply]

end TauCeti.GeneralLinear
