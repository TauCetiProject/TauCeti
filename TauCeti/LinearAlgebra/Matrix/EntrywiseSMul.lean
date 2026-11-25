/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Data.Matrix.Basic

/-!
# Entrywise scaling of matrices by weights

For a commutative semiring `R` and an `R`-module `E`, scaling the entry `(i, j)` of a matrix `Y`
with entries in `E` by `r i j : R` is an `R`-linear endomorphism of `Matrix m n E`, multiplicative
and additive in the weights `r`. It is `Algebra.lsmul` for the pointwise action of the weights.

## Main definitions

* `Matrix.entrywiseSMulAlgHom`: entrywise scaling by a matrix of weights, as an algebra
  homomorphism into the `R`-linear endomorphisms of `Matrix m n E`.
-/

public section

namespace Matrix

variable {m n R : Type*} [CommSemiring R]

/-- Entrywise scaling by a matrix of weights in `R`, as an `R`-algebra homomorphism from the
weights to the `R`-linear endomorphisms of `Matrix m n E`. This is `Algebra.lsmul` for the
pointwise action of `m → n → R` on `m → n → E`, the underlying type of `Matrix m n E`. -/
def entrywiseSMulAlgHom (E : Type*) [AddCommMonoid E] [Module R E] :
    (m → n → R) →ₐ[R] Module.End R (Matrix m n E) :=
  Algebra.lsmul R R (m → n → E)

/-- `entrywiseSMulAlgHom E r Y` is the matrix with entries `r i j • Y i j`. -/
theorem entrywiseSMulAlgHom_apply {E : Type*} [AddCommMonoid E] [Module R E]
    (r : m → n → R) (Y : Matrix m n E) :
    entrywiseSMulAlgHom E r Y = of fun i j ↦ r i j • Y i j :=
  (rfl)

/-- The entry `(i, j)` of `entrywiseSMulAlgHom E r Y` is `r i j • Y i j`. -/
@[simp]
theorem entrywiseSMulAlgHom_apply_apply {E : Type*} [AddCommMonoid E] [Module R E]
    (r : m → n → R) (Y : Matrix m n E) (i : m) (j : n) :
    entrywiseSMulAlgHom E r Y i j = r i j • Y i j :=
  (rfl)

end Matrix
