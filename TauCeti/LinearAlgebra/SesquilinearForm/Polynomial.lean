/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Star.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

import Mathlib.Algebra.Polynomial.Inductions

/-!
# Polynomial adjointness for sesquilinear forms

For a sesquilinear form `B : V →ₛₗ[starRingEnd R] V →ₗ[R] R` over a commutative star semiring `R`
and endomorphisms `U, U' : Module.End R V`:

* `LinearMap.apply_aeval_map_starRingEnd_apply`: if `U'` is left-adjoint to `U`, then
  `B (aeval U' (G.map (starRingEnd R)) a) y = B a (aeval U G y)` for every polynomial `G`.
-/

public section

open Module Polynomial

namespace LinearMap

variable {R V : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid V] [Module R V]

/-- If `U'` is left-adjoint to `U` for a sesquilinear form `B`, then
`B (aeval U' (G.map (starRingEnd R)) a) y = B a (aeval U G y)` for every polynomial `G`. -/
theorem apply_aeval_map_starRingEnd_apply (B : V →ₛₗ[starRingEnd R] V →ₗ[R] R) {U U' : End R V}
    (adj : ∀ a y : V, B (U' a) y = B a (U y)) (G : R[X]) (a y : V) :
    B (aeval U' (G.map (starRingEnd R)) a) y = B a (aeval U G y) := by
  induction G using recOnHorner generalizing a y with
  | M0 => simp
  | MC G c _ _ ih => simp [ih]
  | MX G _ ih =>
    simpa [mul_comm (G.map _) X, adj] using ih a (U y)

end LinearMap
