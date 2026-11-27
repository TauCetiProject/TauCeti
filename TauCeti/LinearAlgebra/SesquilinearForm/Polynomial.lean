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

* `LinearMap.aeval_map_starRingEnd`: if `U'` is left-adjoint to `U` on a `U`-invariant set `S`,
  then `aeval U' (G.map (starRingEnd R))` is left-adjoint to `aeval U G` on `S`.
* `LinearMap.aeval_eq_zero_of_eigen`: if `U` is left-adjoint to `U'` and `z` is an eigenvector of
  `U'` orthogonal to `x`, then `z` is orthogonal to `aeval U G x` for every polynomial `G`.
-/

public section

open Module Polynomial

namespace LinearMap

variable {R V : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid V] [Module R V]

/-- If `U'` is left-adjoint to `U` on a `U`-invariant set `S` for a sesquilinear form `B`, then
`aeval U' (G.map (starRingEnd R))` is left-adjoint to `aeval U G` on `S`. -/
theorem aeval_map_starRingEnd (B : V →ₛₗ[starRingEnd R] V →ₗ[R] R) {U U' : End R V}
    (S : Set V) (adj : ∀ y ∈ S, U y ∈ S ∧ ∀ a : V, B (U' a) y = B a (U y)) (G : R[X]) (a : V) :
    ∀ y ∈ S, B (aeval U' (G.map (starRingEnd R)) a) y = B a (aeval U G y) := by
  induction G using recOnHorner generalizing a with
  | M0 => simp
  | MC G c _ _ ih => simp_all
  | MX G _ ih =>
    intro y hy
    rw [Polynomial.map_mul, Polynomial.map_X, mul_comm _ X, map_mul, aeval_X,
      mul_apply_eq_comp, (adj y hy).2, map_mul, aeval_X, mul_apply_eq_comp,
      ih a (U y) (adj y hy).1]

/-- If `U` is left-adjoint to `U'` for a sesquilinear form `B` and `z` is an eigenvector of `U'`
with `B x z = 0`, then `B (aeval U G x) z = 0` for every polynomial `G`. -/
theorem aeval_eq_zero_of_eigen (B : V →ₛₗ[starRingEnd R] V →ₗ[R] R) {U U' : End R V}
    {x z : V} {μ : R} (adj : ∀ a y : V, B (U a) y = B a (U' y))
    (eigen_z : U' z = μ • z) (orth_x : B x z = 0) (G : R[X]) :
    B (aeval U G x) z = 0 := by
  induction G using recOnHorner with
  | M0 => simp
  | MC G a _ _ ih => simp [ih, orth_x]
  | MX G _ ih => simp [← X_mul, adj, eigen_z, ih]

end LinearMap
