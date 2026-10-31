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
# The block inclusion `GLₙ → GLₙ₊₁` on coordinate algebras

The block inclusion `TauCeti.glBlockSucc`, which places an invertible matrix in the upper-left
block and fixes the last basis vector, is a homomorphism of algebraic groups `GLₙ → GLₙ₊₁`. This
file builds its comorphism

`O(GLₙ₊₁) →ₐc[R] O(GLₙ)`,

`TauCeti.GeneralLinear.blockSuccCoordinateMap`, the morphism of coordinate Hopf algebras sending
the generic matrix of `GLₙ₊₁` to the generic matrix of `GLₙ` placed in the upper-left block
(`Matrix.blockSucc`). That matrix is multiplicative, being the image of a multiplicative matrix
under a unital multiplicative map, so the comorphism is an instance of
`TauCeti.GeneralLinear.coordinateBialgHomOfMultiplicative`.

On points it is the block inclusion itself, and on tangent vectors it is the corner embedding
`TauCeti.glEmbedding` of `𝔤𝔩ₙ` in `𝔤𝔩ₙ₊₁`: the last row and column of `Matrix.blockSucc` are
constant, so every derivation kills them. Restricting representations of `GLₙ₊₁` along this
comorphism is how their differentials are compared with those of the restricted representations
of `GLₙ`.

## Main definitions

* `TauCeti.GeneralLinear.blockSuccCoordinateMap`: the comorphism `O(GLₙ₊₁) →ₐc[R] O(GLₙ)` of the
  block inclusion.

## Main results

* `TauCeti.GeneralLinear.map_genericMatrix_blockSuccCoordinateMap`: it sends the generic matrix of
  `GLₙ₊₁` to the block extension of the generic matrix of `GLₙ`.
* `TauCeti.GeneralLinear.mapDomain_blockSuccCoordinateMap_generalLinearToPoint`: on points it is
  the block inclusion `TauCeti.glBlockSucc`.
* `TauCeti.GeneralLinear.tangentMatrix_derivationComp_blockSuccCoordinateMap`: on tangent vectors
  it is the corner embedding along `Fin.castSuccEmb`.
-/

public section

open WithConv

namespace TauCeti.GeneralLinear

universe u v w

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **The comorphism of the block inclusion** `GLₙ → GLₙ₊₁`: the morphism of coordinate Hopf
algebras `O(GLₙ₊₁) → O(GLₙ)` sending the generic matrix of `GLₙ₊₁` to the generic matrix of `GLₙ`
placed in the upper-left block, with the last row and column of the identity matrix. -/
noncomputable def blockSuccCoordinateMap :
    coordinateHopfAlgebra R (n + 1) →ₐc[R] coordinateHopfAlgebra R n :=
  coordinateBialgHomOfMultiplicative R (n + 1) (Matrix.blockSucc (genericMatrix R n))
    (by
      rw [Matrix.blockSucc_map _ _ (map_zero _) (map_one _),
        Matrix.blockSucc_map _ _ (map_zero _) (map_one _),
        Matrix.blockSucc_map _ _ (map_zero _) (map_one _), map_comul_genericMatrix,
        Matrix.blockSucc_mul])
    (by
      rw [Matrix.blockSucc_map _ _ (map_zero _) (map_one _), map_counit_genericMatrix,
        Matrix.blockSucc_one])

/-- The comorphism of the block inclusion sends the generic matrix of `GLₙ₊₁` to the block
extension of the generic matrix of `GLₙ`. -/
@[simp]
theorem map_genericMatrix_blockSuccCoordinateMap :
    (genericMatrix R (n + 1)).map (blockSuccCoordinateMap R n) =
      Matrix.blockSucc (genericMatrix R n) :=
  map_genericMatrix_coordinateBialgHomOfMultiplicative ..

/-- The comorphism of the block inclusion on a generic coordinate of `GLₙ₊₁`. -/
theorem blockSuccCoordinateMap_genericMatrix_apply (a b : Fin (n + 1)) :
    blockSuccCoordinateMap R n (genericMatrix R (n + 1) a b) =
      Matrix.blockSucc (genericMatrix R n) a b := by
  rw [← map_genericMatrix_blockSuccCoordinateMap, Matrix.map_apply]

variable {R n}

/-- **On points, the comorphism is the block inclusion**: precomposing the point of `GLₙ` attached
to an invertible matrix `g` with `TauCeti.GeneralLinear.blockSuccCoordinateMap` gives the point of
`GLₙ₊₁` attached to `TauCeti.glBlockSucc g`. -/
theorem mapDomain_blockSuccCoordinateMap_generalLinearToPoint {A : Type w} [CommRing A]
    [Algebra R A] (g : Matrix.GeneralLinearGroup (Fin n) A) :
    BialgHom.mapDomain (blockSuccCoordinateMap R n) (generalLinearToPoint (R := R) n g) =
      generalLinearToPoint (R := R) (n + 1) (glBlockSucc A n g) := by
  apply WithConv.ext
  apply coordinateHopfAlgebra_algHom_ext R (n + 1)
  intro a b
  have hg : (genericMatrix R n).map (generalLinearToPoint (R := R) n g).ofConv =
      (g : Matrix (Fin n) (Fin n) A) := by
    rw [map_genericMatrix_eq_coe_pointToGeneralLinear, toConv_ofConv,
      pointToGeneralLinear_generalLinearToPoint]
  rw [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply, generalLinearToPoint_apply,
    coe_glBlockSucc, ← genericMatrix_apply, BialgHom.coe_toAlgHom,
    blockSuccCoordinateMap_genericMatrix_apply, ← hg,
    ← Matrix.blockSucc_map _ _ (map_zero _) (map_one _), Matrix.map_apply]

variable {B : Type v} [CommRing B] [Algebra R B]

/-- **On tangent vectors, the comorphism is the corner embedding** `𝔤𝔩ₙ → 𝔤𝔩ₙ₊₁` along
`Fin.castSuccEmb`: the matrix of the pushed-forward tangent vector has the matrix of the original
one in its upper-left block and zeros elsewhere. -/
theorem tangentMatrix_derivationComp_blockSuccCoordinateMap
    (d : Derivation R (coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) B)) :
    tangentMatrix (n + 1) (derivationComp (B := B) (blockSuccCoordinateMap R n) d) =
      glEmbedding B Fin.castSuccEmb (tangentMatrix n d) := by
  ext a b
  rw [tangentMatrix_apply, algEquivSelf_derivationComp_apply, ← genericMatrix_apply,
    BialgHom.coe_toAlgHom, blockSuccCoordinateMap_genericMatrix_apply]
  induction a using Fin.lastCases with
  | last =>
    rw [glEmbedding_apply_apply_eq_zero _ _ (Or.inl (by simp))]
    induction b using Fin.lastCases with
    | last => rw [Matrix.blockSucc_last_last, Derivation.map_one_eq_zero, map_zero]
    | cast b => rw [Matrix.blockSucc_last_castSucc, map_zero, map_zero]
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [glEmbedding_apply_apply_eq_zero _ _ (Or.inr (by simp)),
        Matrix.blockSucc_castSucc_last, map_zero, map_zero]
    | cast b =>
      have h := glEmbedding_apply_apply (R := B) Fin.castSuccEmb (tangentMatrix n d) a b
      rw [Fin.castSuccEmb_apply, Fin.castSuccEmb_apply] at h
      rw [h, Matrix.blockSucc_castSucc_castSucc, tangentMatrix_apply, genericMatrix_apply]

end TauCeti.GeneralLinear
