/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

import Mathlib.Algebra.Polynomial.Inductions

/-!
# Polynomial adjointness for sesquilinear forms

For a `σ`-sesquilinear pairing `B : V →ₛₗ[σ] V →ₗ[R] M₂` over a commutative semiring `R` with
`σ : R →+* R` and endomorphisms `U, U' : Module.End R V`:

* `LinearMap.apply_aeval_apply_eq_apply_aeval_map`: if `U'` is left-adjoint to `U`, then
  `B (aeval U' G a) y = B a (aeval U (G.map σ) y)` for every polynomial `G`.
-/

public section

open Module Polynomial

namespace LinearMap

variable {R V M₂ : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
  [AddCommMonoid M₂] [Module R M₂]

/-- If `U'` is left-adjoint to `U` for a `σ`-sesquilinear pairing `B`, then
`B (aeval U' G a) y = B a (aeval U (G.map σ) y)` for every polynomial `G`. -/
theorem apply_aeval_apply_eq_apply_aeval_map {σ : R →+* R} (B : V →ₛₗ[σ] V →ₗ[R] M₂)
    {U U' : End R V} (adj : ∀ a y : V, B (U' a) y = B a (U y)) (G : R[X]) (a y : V) :
    B (aeval U' G a) y = B a (aeval U (G.map σ) y) := by
  induction G using recOnHorner generalizing a y with
  | M0 => simp
  | MC G c _ _ ih => simp [ih]
  | MX G _ ih =>
    simpa [mul_comm (G.map σ) X, adj] using ih (U' a) y

end LinearMap
