/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant.Mul
public import TauCeti.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant of a block sum of matrix representations

For matrix representations `ρ₁ : R →ₐ[A] Matrix n₁ n₁ A` and `ρ₂ : R →ₐ[A] Matrix n₂ n₂ A`, the
block-diagonal representation `x ↦ diag(ρ₁ x, ρ₂ x)` (`AlgHom.fromBlocks`) has determinant
law the product of the determinant laws of `ρ₁` and `ρ₂`, after every scalar extension
(`TauCeti.Determinant.toLaw_algHomDet_fromBlocks`): the direct sum of determinants
`TauCeti.Determinant.mul` is the determinant of the direct sum of representations. The dimensions
`card (n₁ ⊕ n₂)` and `card n₁ + card n₂` are equal but not definitionally, so the statement is about
the underlying laws.

## Main declarations

* `TauCeti.Determinant.toLaw_algHomDet_fromBlocks`: the determinant law of
  `x ↦ diag(ρ₁ x, ρ₂ x)` is the product of the determinant laws of `ρ₁` and `ρ₂`.
* `TauCeti.Determinant.algHomDet_fromBlocks_apply`: its value,
  `det diag(ρ₁ x, ρ₂ x) = det ρ₁(x) · det ρ₂(x)`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, proof of Lemma 2.2](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u

open TensorProduct

namespace TauCeti

namespace Determinant

variable {A : Type u} [CommRing A] {R : Type*} [Semiring R] [Algebra A R]
  {n₁ n₂ : Type*} [Fintype n₁] [Fintype n₂] [DecidableEq n₁] [DecidableEq n₂]

/-- **The determinant of a block sum is the product of the determinants**, as polynomial laws: the
determinant law of `x ↦ diag(ρ₁ x, ρ₂ x)` is the product of the determinant laws of `ρ₁` and
`ρ₂`, which is the law of `(algHomDet ρ₁).mul (algHomDet ρ₂)`. -/
theorem toLaw_algHomDet_fromBlocks (ρ₁ : R →ₐ[A] Matrix n₁ n₁ A)
    (ρ₂ : R →ₐ[A] Matrix n₂ n₂ A) :
    (algHomDet (ρ₁.fromBlocks ρ₂)).toLaw = ((algHomDet ρ₁).mul (algHomDet ρ₂)).toLaw := by
  ext S _ _ x
  -- reduce to a polynomial ring over `A`, which is a commutative ring
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift x
  rw [PolynomialLaw.toFun'_eq_toFun, PolynomialLaw.toFun'_eq_toFun,
    ← PolynomialLaw.isCompat_apply, ← PolynomialLaw.isCompat_apply]
  simp [toLaw_mul, PolynomialLaw.mul_toFun, algHomDet_toFun, Matrix.det_fromBlocks_zero₂₁]

/-- The value of the determinant of a block sum: `det diag(ρ₁ x, ρ₂ x) = det ρ₁(x) · det ρ₂(x)`. -/
theorem algHomDet_fromBlocks_apply (ρ₁ : R →ₐ[A] Matrix n₁ n₁ A)
    (ρ₂ : R →ₐ[A] Matrix n₂ n₂ A) (x : R) :
    algHomDet (ρ₁.fromBlocks ρ₂) x = algHomDet ρ₁ x * algHomDet ρ₂ x := by
  rw [← mul_apply, ← ground_toLaw, ← ground_toLaw, toLaw_algHomDet_fromBlocks]

end Determinant

end TauCeti
