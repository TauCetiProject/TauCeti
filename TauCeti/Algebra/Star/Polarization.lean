/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module

/-!
# Polarization for the products `star u * x * c`

In a complex star algebra, the "sesquilinear" product `(u, c) ↦ star u * x * c` is recovered from
its values on the diagonal: `4 • (star u * x * c)` is the sum over `k` of
`Iᵏ • (star (c + Iᵏ • u) * x * (c + Iᵏ • u))`. This lets a statement about all products
`star b * x * b` be upgraded to one about all products `b * x * c`. On the diagonal, a complex
scalar comes out of `star (c • x) * (c • x)` as `‖c‖ ^ 2`, and in any star ring the products
`star x * x` satisfy the parallelogram identity.

## Main results

* `TauCeti.star_mul_mul_polarization`: the polarization identity for `star u * x * c`.
* `TauCeti.star_smul_mul_smul`: `star (c • x) * (c • x) = ‖c‖ ^ 2 • (star x * x)`.
* `TauCeti.star_add_mul_add_add_star_sub_mul_sub`: the parallelogram identity
  `star (x + y) * (x + y) + star (x - y) * (x - y) = 2 • (star x * x + star y * y)`.
-/

public section

namespace TauCeti

/-- The parallelogram identity for the products `star x * x` in a star ring. -/
theorem star_add_mul_add_add_star_sub_mul_sub {R : Type*} [NonUnitalNonAssocRing R] [StarRing R]
    (x y : R) :
    star (x + y) * (x + y) + star (x - y) * (x - y) = 2 • (star x * x + star y * y) := by
  simp only [star_add, star_sub, add_mul, sub_mul, mul_add, mul_sub]
  abel

variable {A : Type*} [NonUnitalNonAssocRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

/-- Polarization: `4 • (star u * x * c)` is the sum over `k` of
`Iᵏ • (star (c + Iᵏ • u) * x * (c + Iᵏ • u))`. -/
theorem star_mul_mul_polarization (u x c : A) :
    (4 : ℂ) • (star u * x * c) =
      star (c + u) * x * (c + u) + Complex.I • (star (c + Complex.I • u) * x *
        (c + Complex.I • u)) - star (c - u) * x * (c - u) -
        Complex.I • (star (c - Complex.I • u) * x * (c - Complex.I • u)) := by
  simp only [star_add, star_sub, star_smul, Complex.star_def, Complex.conj_I, add_mul, sub_mul,
    mul_add, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, neg_smul,
    neg_mul, smul_neg, Complex.I_mul_I]
  module

/-- A complex scalar comes out of `star (c • x) * (c • x)` as `‖c‖ ^ 2`. -/
theorem star_smul_mul_smul (c : ℂ) (x : A) :
    star (c • x) * (c • x) = (‖c‖ ^ 2 : ℝ) • (star x * x) := by
  simp [star_smul, smul_mul_smul_comm, Complex.conj_mul', ← Complex.coe_smul]

end TauCeti
