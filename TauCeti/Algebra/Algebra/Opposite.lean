/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite

/-!
# Algebra homomorphisms from commutative algebras into opposites

Package `AlgHom.toOpposite` when commutativity of the domain supplies its commutation hypothesis.
-/

public section

/-- The opposite-valued algebra homomorphism induced by a map from commutative `L`. -/
def AlgHom.toOppositeOfComm {K L A : Type*} [CommSemiring K] [CommSemiring L]
    [Semiring A] [Algebra K L] [Algebra K A] (f : L →ₐ[K] A) : L →ₐ[K] Aᵐᵒᵖ :=
  f.toOpposite fun x y ↦ by simp [commute_iff_eq, ← map_mul, mul_comm]

/-- The induced homomorphism sends `x` to the opposite of `f x`. -/
@[simp]
theorem AlgHom.toOppositeOfComm_apply {K L A : Type*} [CommSemiring K] [CommSemiring L]
    [Semiring A] [Algebra K L] [Algebra K A] (f : L →ₐ[K] A) (x : L) :
    f.toOppositeOfComm x = MulOpposite.op (f x) := by
  rfl
