/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.MultiplicativeMatrix
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.Lie.GeneralLinear.Embedding
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.BlockSucc

/-!
# The block inclusion `GLₙ → GLₙ₊₁` as a morphism of group schemes

The block inclusion `TauCeti.glBlockSucc` sends an invertible matrix `g` to `diag(g, 1)`. Its
coordinate morphism `O(GLₙ₊₁) → O(GLₙ)` sends the generic matrix of `GLₙ₊₁` to
`diag(X, 1)` for the generic matrix `X` of `GLₙ`; that matrix is multiplicative, because the
generic matrix is and `Matrix.blockSucc` is multiplicative, so the morphism is the one attached to
it by `TauCeti.GeneralLinear.coordinateBialgHomOfMultiplicative`.

On points it is the block inclusion, and on tangent vectors it is the corner embedding
`X ↦ diag(X, 0)` of the matrix Lie algebras, `TauCeti.glEmbedding` along `Fin.castSuccEmb`. This
is what identifies the differential of a representation restricted along the block inclusion
with the restriction of its differential.

## Main definitions

* `TauCeti.GeneralLinear.blockSuccCoordinateMap`: the coordinate morphism of the block inclusion.

## Main results

* `TauCeti.GeneralLinear.map_genericMatrix_blockSuccCoordinateMap`: it sends the generic matrix
  of `GLₙ₊₁` to `diag(X, 1)`.
* `TauCeti.GeneralLinear.mapDomain_blockSuccCoordinateMap_generalLinearToPoint`: on points it is
  the block inclusion.
* `TauCeti.GeneralLinear.tangentMatrix_derivationComp_blockSuccCoordinateMap`: on tangent vectors
  it is the corner embedding of matrices.
-/

public section

open Matrix WithConv

namespace TauCeti.GeneralLinear

universe u w

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The matrix `diag(X, 1)` built from the generic matrix of `GLₙ` is multiplicative. -/
private theorem map_comul_blockSucc_genericMatrix :
    (blockSucc (genericMatrix R n)).map
        (Bialgebra.comulAlgHom R (coordinateHopfAlgebra R n)) =
      (blockSucc (genericMatrix R n)).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (blockSucc (genericMatrix R n)).map (Algebra.TensorProduct.includeRight (R := R)) := by
  rw [map_blockSucc, map_blockSucc, map_blockSucc, map_comul_genericMatrix, blockSucc_mul]

/-- The matrix `diag(X, 1)` built from the generic matrix of `GLₙ` is unital. -/
private theorem map_counit_blockSucc_genericMatrix :
    (blockSucc (genericMatrix R n)).map
      (Bialgebra.counitAlgHom R (coordinateHopfAlgebra R n)) = 1 := by
  rw [map_blockSucc, map_counit_genericMatrix, blockSucc_one]

/-- **The coordinate morphism of the block inclusion** `GLₙ → GLₙ₊₁`, `g ↦ diag(g, 1)`: the
morphism of coordinate Hopf algebras `O(GLₙ₊₁) → O(GLₙ)` sending the generic matrix of `GLₙ₊₁` to
`diag(X, 1)` for the generic matrix `X` of `GLₙ`. -/
noncomputable def blockSuccCoordinateMap :
    coordinateHopfAlgebra R (n + 1) →ₐc[R] coordinateHopfAlgebra R n :=
  coordinateBialgHomOfMultiplicative R (n + 1) (blockSucc (genericMatrix R n))
    (map_comul_blockSucc_genericMatrix R n) (map_counit_blockSucc_genericMatrix R n)

/-- The coordinate morphism of the block inclusion sends the generic matrix of `GLₙ₊₁` to
`diag(X, 1)`. -/
@[simp]
theorem map_genericMatrix_blockSuccCoordinateMap :
    (genericMatrix R (n + 1)).map (blockSuccCoordinateMap R n) =
      blockSucc (genericMatrix R n) :=
  map_genericMatrix_coordinateBialgHomOfMultiplicative _ _ _ _ _

/-- The coordinate morphism of the block inclusion on a generic matrix entry. -/
@[simp]
theorem blockSuccCoordinateMap_X (i j : Fin (n + 1)) :
    blockSuccCoordinateMap R n
        (coordinateHopfAlgebraAlgEquiv R (n + 1)
          (coordinateRingMap R (n + 1) (MvPolynomial.X (i, j)))) =
      blockSucc (genericMatrix R n) i j :=
  coordinateBialgHomOfMultiplicative_X _ _ _ _ _ i j

variable {R n}

/-- **On points, the coordinate morphism of the block inclusion is the block inclusion**: it
carries the point of `GLₙ` attached to an invertible matrix `g` to the point of `GLₙ₊₁` attached
to `diag(g, 1)`. -/
theorem mapDomain_blockSuccCoordinateMap_generalLinearToPoint {A : Type w} [CommRing A]
    [Algebra R A] (g : GL (Fin n) A) :
    BialgHom.mapDomain (blockSuccCoordinateMap R n) (generalLinearToPoint (R := R) n g) =
      generalLinearToPoint (R := R) (n + 1) (glBlockSucc A n g) := by
  apply WithConv.ext
  apply coordinateHopfAlgebra_algHom_ext R (n + 1)
  intro i j
  rw [BialgHom.mapDomain_apply, ofConv_toConv, generalLinearToPoint_apply, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, blockSuccCoordinateMap_X, coe_glBlockSucc]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp [genericMatrix_apply]

/-- **On tangent vectors, the coordinate morphism of the block inclusion is the corner
embedding**: the matrix of the image in the Lie algebra of `GLₙ₊₁` of a tangent vector `d` to `GLₙ`
is `diag(tangentMatrix d, 0)`, the image of the matrix of `d` under `TauCeti.glEmbedding` along
`Fin.castSuccEmb`. -/
theorem tangentMatrix_derivationComp_blockSuccCoordinateMap {B : Type w} [CommRing B]
    [Algebra R B]
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    tangentMatrix (n + 1) (derivationComp (B := B) (blockSuccCoordinateMap R n) d) =
      glEmbedding B Fin.castSuccEmb (tangentMatrix n d) := by
  ext a b
  rw [tangentMatrix_apply, algEquivSelf_derivationComp_apply, BialgHom.coe_toAlgHom,
    blockSuccCoordinateMap_X]
  induction a using Fin.lastCases with
  | last =>
    have ha : Fin.last n ∉ Set.range Fin.castSuccEmb := by simp
    induction b using Fin.lastCases with
    | last =>
      rw [glEmbedding_apply_apply_of_notMem_range_left _ _ ha, blockSucc_last_last,
        Derivation.map_one_eq_zero, map_zero]
    | cast b =>
      rw [glEmbedding_apply_apply_of_notMem_range_left _ _ ha, blockSucc_last_castSucc,
        map_zero, map_zero]
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      have hb : Fin.last n ∉ Set.range Fin.castSuccEmb := by simp
      rw [glEmbedding_apply_apply_of_notMem_range_right _ _ _ hb, blockSucc_castSucc_last,
        map_zero, map_zero]
    | cast b =>
      rw [blockSucc_castSucc_castSucc, genericMatrix_apply, ← tangentMatrix_apply,
        ← Fin.coe_castSuccEmb, glEmbedding_apply_apply]

end TauCeti.GeneralLinear
