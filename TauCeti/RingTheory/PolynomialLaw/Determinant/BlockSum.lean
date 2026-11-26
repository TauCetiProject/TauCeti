/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant.Mul
public import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant of a block sum of matrix representations

For matrix representations `ρ₁ : R →ₐ[A] Matrix n₁ n₁ A` and `ρ₂ : R →ₐ[A] Matrix n₂ n₂ A`, the
block-diagonal representation `x ↦ diag(ρ₁ x, ρ₂ x)` (`TauCeti.fromBlocksAlgHom`) has determinant
law the product of the determinant laws of `ρ₁` and `ρ₂`, after every scalar extension
(`TauCeti.Determinant.toLaw_algHomDet_fromBlocksAlgHom`): the direct sum of determinants
`TauCeti.Determinant.mul` is the determinant of the direct sum of representations. The dimensions
`card (n₁ ⊕ n₂)` and `card n₁ + card n₂` are equal but not definitionally, so the statement is about
the underlying laws.

## Main declarations

* `TauCeti.fromBlocksAlgHom ρ₁ ρ₂`: the block-diagonal representation `x ↦ diag(ρ₁ x, ρ₂ x)`.
* `TauCeti.Determinant.toLaw_algHomDet_fromBlocksAlgHom`: its determinant law is the product of
  the determinant laws of `ρ₁` and `ρ₂`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, proof of Lemma 2.2](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u

open TensorProduct

namespace TauCeti

section FromBlocks

variable {A : Type*} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R]
  {n₁ n₂ : Type*} [Fintype n₁] [Fintype n₂] [DecidableEq n₁] [DecidableEq n₂]

/-- The **block-diagonal representation** `x ↦ diag(ρ₁ x, ρ₂ x)` of two matrix representations,
the direct sum of `ρ₁` and `ρ₂`. -/
def fromBlocksAlgHom (ρ₁ : R →ₐ[A] Matrix n₁ n₁ A) (ρ₂ : R →ₐ[A] Matrix n₂ n₂ A) :
    R →ₐ[A] Matrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) A where
  toFun x := Matrix.fromBlocks (ρ₁ x) 0 0 (ρ₂ x)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.fromBlocks_multiply]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.fromBlocks_add]
  commutes' a := by
    simp [Algebra.algebraMap_eq_smul_one, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]

@[simp]
theorem fromBlocksAlgHom_apply (ρ₁ : R →ₐ[A] Matrix n₁ n₁ A) (ρ₂ : R →ₐ[A] Matrix n₂ n₂ A)
    (x : R) : fromBlocksAlgHom ρ₁ ρ₂ x = Matrix.fromBlocks (ρ₁ x) 0 0 (ρ₂ x) :=
  (rfl)

end FromBlocks

namespace Determinant

variable {A : Type u} [CommRing A] {R : Type*} [Semiring R] [Algebra A R]
  {n₁ n₂ : Type*} [Fintype n₁] [Fintype n₂] [DecidableEq n₁] [DecidableEq n₂]

/-- After scalar extension to `S`, the block-diagonal representation is block diagonal. -/
private theorem matrixBaseChangeAlgEquiv_map_fromBlocksAlgHom (ρ₁ : R →ₐ[A] Matrix n₁ n₁ A)
    (ρ₂ : R →ₐ[A] Matrix n₂ n₂ A) (S : Type*) [CommSemiring S] [Algebra A S] (x : S ⊗[A] R) :
    Algebra.matrixBaseChangeAlgEquiv A S (n₁ ⊕ n₂)
        (Algebra.TensorProduct.map (AlgHom.id A S) (fromBlocksAlgHom ρ₁ ρ₂) x) =
      Matrix.fromBlocks
        (Algebra.matrixBaseChangeAlgEquiv A S n₁
          (Algebra.TensorProduct.map (AlgHom.id A S) ρ₁ x))
        0 0
        (Algebra.matrixBaseChangeAlgEquiv A S n₂
          (Algebra.TensorProduct.map (AlgHom.id A S) ρ₂ x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul s r => simp [Matrix.fromBlocks_map, Matrix.fromBlocks_smul]
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.fromBlocks_add, add_zero]

/-- **The determinant of a block sum is the product of the determinants**, as polynomial laws: the
determinant law of `x ↦ diag(ρ₁ x, ρ₂ x)` is the product of the determinant laws of `ρ₁` and
`ρ₂`, which is the law of `(algHomDet ρ₁).mul (algHomDet ρ₂)`. -/
theorem toLaw_algHomDet_fromBlocksAlgHom (ρ₁ : R →ₐ[A] Matrix n₁ n₁ A)
    (ρ₂ : R →ₐ[A] Matrix n₂ n₂ A) :
    (algHomDet (fromBlocksAlgHom ρ₁ ρ₂)).toLaw = ((algHomDet ρ₁).mul (algHomDet ρ₂)).toLaw := by
  ext S _ _ x
  -- reduce to a polynomial ring over `A`, which is a commutative ring
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift x
  rw [PolynomialLaw.toFun'_eq_toFun, PolynomialLaw.toFun'_eq_toFun,
    ← PolynomialLaw.isCompat_apply, ← PolynomialLaw.isCompat_apply, toLaw_mul,
    PolynomialLaw.mul_toFun, algHomDet_toFun, algHomDet_toFun, algHomDet_toFun,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, matrixBaseChangeAlgEquiv_map_fromBlocksAlgHom,
    Matrix.det_fromBlocks_zero₂₁]

/-- The value of the determinant of a block sum: `det diag(ρ₁ x, ρ₂ x) = det ρ₁(x) · det ρ₂(x)`. -/
theorem algHomDet_fromBlocksAlgHom_apply (ρ₁ : R →ₐ[A] Matrix n₁ n₁ A)
    (ρ₂ : R →ₐ[A] Matrix n₂ n₂ A) (x : R) :
    algHomDet (fromBlocksAlgHom ρ₁ ρ₂) x = algHomDet ρ₁ x * algHomDet ρ₂ x := by
  rw [← mul_apply, ← ground_toLaw, ← ground_toLaw, toLaw_algHomDet_fromBlocksAlgHom]

end Determinant

end TauCeti
