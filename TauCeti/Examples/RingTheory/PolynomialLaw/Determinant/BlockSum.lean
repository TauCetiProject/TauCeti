/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.PolynomialLaw.Determinant.BlockSum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Examples: the determinant of a block sum

* The determinant law of `diag(ρ₁, ρ₂)` is the product law of `det ∘ ρ₁` and `det ∘ ρ₂`, after
  every scalar extension, not only on values.
* Characteristic polynomials multiply and traces add, as for `TauCeti.Determinant.mul`.
* For the identity representation of `M₂(ℤ)` twice, `diag(M, M)` at `M = !![1, 2; 3, 4]` has
  determinant `(-2)² = 4`.
-/

open TauCeti Determinant

variable {A R : Type*} [CommRing A] [Ring R] [Algebra A R] {n₁ n₂ : Type*} [Fintype n₁]
  [Fintype n₂] [DecidableEq n₁] [DecidableEq n₂]

-- The determinant law of a block sum is the product law.
example (ρ₁ : R →ₐ[A] Matrix n₁ n₁ A) (ρ₂ : R →ₐ[A] Matrix n₂ n₂ A) :
    (algHomDet (ρ₁.fromBlocks ρ₂)).toLaw = (algHomDet ρ₁).toLaw * (algHomDet ρ₂).toLaw :=
  (toLaw_algHomDet_fromBlocks ρ₁ ρ₂).trans (toLaw_mul _ _)

-- Characteristic polynomials multiply, as for the product determinant.
example (ρ₁ : R →ₐ[A] Matrix n₁ n₁ A) (ρ₂ : R →ₐ[A] Matrix n₂ n₂ A) (x : R) :
    (algHomDet (ρ₁.fromBlocks ρ₂)).charpoly x =
      ((algHomDet ρ₁).mul (algHomDet ρ₂)).charpoly x := by
  simp [Matrix.charpoly_fromBlocks_zero₂₁]

-- Traces add, as for the product determinant.
example (ρ₁ : R →ₐ[A] Matrix n₁ n₁ A) (ρ₂ : R →ₐ[A] Matrix n₂ n₂ A) (x : R) :
    (algHomDet (ρ₁.fromBlocks ρ₂)).trace x = ((algHomDet ρ₁).mul (algHomDet ρ₂)).trace x := by
  simp [Matrix.trace_fromBlocks]

-- `det diag(M, M) = (det M)² = 4` for `M = !![1, 2; 3, 4]`.
example : algHomDet (AlgHom.fromBlocks (AlgHom.id ℤ (Matrix (Fin 2) (Fin 2) ℤ))
    (AlgHom.id ℤ (Matrix (Fin 2) (Fin 2) ℤ))) !![1, 2; 3, 4] = 4 := by
  rw [algHomDet_fromBlocks_apply, algHomDet_apply]
  simp [Matrix.det_fin_two]
