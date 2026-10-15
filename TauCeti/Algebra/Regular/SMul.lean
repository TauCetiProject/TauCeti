/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Regular.SMul

/-!
# Nonzerodivisors under multiplicative isomorphisms

A multiplicative isomorphism `e : R ≃* S`, for instance a ring isomorphism, preserves and reflects
the elements whose left multiplication is injective: `a` is `IsSMulRegular` in `R` if and only if
`e a` is in `S` (`TauCeti.isSMulRegular_map_iff`). This specializes Mathlib's
`Equiv.isSMulRegular_congr` to an element acting on its own ring, where the compatibility
hypothesis is `map_mul`.
-/

public section

namespace TauCeti

variable {R S F : Type*} [Mul R] [Mul S] [EquivLike F R S] [MulEquivClass F R S]

/-- A multiplicative isomorphism preserves and reflects nonzerodivisors: `e a` is a nonzerodivisor
of `S` if and only if `a` is one of `R`. -/
@[simp]
theorem isSMulRegular_map_iff (e : F) (a : R) : IsSMulRegular S (e a) ↔ IsSMulRegular R a :=
  (Equiv.isSMulRegular_congr (e := EquivLike.toEquiv e) fun b ↦ map_mul e a b).symm

end TauCeti
