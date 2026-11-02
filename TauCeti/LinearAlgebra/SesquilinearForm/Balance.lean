/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Balancing a sesquilinear form against a conjugate-semilinear map

A sesquilinear form `H` on a module and a `star`-semilinear map `K` of that module are unrelated
data.  This file makes them compatible: the **balanced** form

`balance H K x y = H x y + star (H (K x) (K y))`

is again sesquilinear -- each argument of the second summand picks up a conjugation from `K`, and
the outer conjugation restores the shape -- and it satisfies

`balance H K (K x) (K y) = star (balance H K x y)`

as soon as `K ∘ K` is a scalar of modulus one, which an arbitrary `H` need not.  That is the
only property balancing adds: being Hermitian and being nonnegative pass from `H` to
`balance H K` unchanged, and for nonnegative `H` so does being definite off the origin, since
`balance H K x x` is nonzero wherever `H x x` is.

The construction and its compatibility are plain star-ring algebra, so they are stated over a
commutative star semiring.  Nonnegativity and definiteness off the origin need an order on the
scalars compatible with the star, and are stated over a commutative star-ordered semiring, such as
`ℂ` with its partial order `ComplexOrder`.

## Main definitions

* `LinearMap.balance`: the balanced form `x, y ↦ H x y + star (H (K x) (K y))`.

## Main results

* `LinearMap.balance_apply`: the defining formula of the balanced form.
* `LinearMap.balance_map_map`: the balanced form is compatible with the map it was balanced
  against, once that map squares to a scalar of modulus one.
* `LinearMap.isSymm_balance` and `LinearMap.isNonneg_balance`: balancing preserves Hermitian
  symmetry and nonnegativity.
* `LinearMap.balance_apply_self_ne_zero`: for nonnegative `H`, the balanced form is nonzero on the
  diagonal wherever `H` is, so balancing preserves definiteness off the origin.
-/

public section

namespace LinearMap

section CommSemiring

variable {R V : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid V] [Module R V]

/-- The **balanced** form of a sesquilinear form `H` against a `star`-semilinear map `K`:
`x, y ↦ H x y + star (H (K x) (K y))`.  Each argument of the second summand picks up a conjugation
from `K`, and the outer conjugation restores the shape of a sesquilinear form, conjugate-linear in
the first argument and linear in the second.  Adding it to `H` is what forces the compatibility
`balance H K (K x) (K y) = star (balance H K x y)` whenever `K ∘ K` is a scalar of modulus
one. -/
def balance (H : V →ₗ⋆[R] V →ₗ[R] R) (K : V →ₛₗ[starRingEnd R] V) :
    V →ₗ⋆[R] V →ₗ[R] R where
  toFun x :=
    { toFun y := H x y + starRingEnd R (H (K x) (K y))
      map_add' y z := by simp only [map_add]; ring
      map_smul' c y := by simp; ring }
  map_add' x y := by ext; simp; ring
  map_smul' c x := by ext; simp; ring

/-- The defining formula of the balanced form. -/
@[simp]
theorem balance_apply (H : V →ₗ⋆[R] V →ₗ[R] R) (K : V →ₛₗ[starRingEnd R] V) (x y : V) :
    balance H K x y = H x y + starRingEnd R (H (K x) (K y)) := (rfl)

/-- **The balanced form is compatible with the map it was balanced against**: replacing both
arguments by their `K`-images conjugates the value, as soon as `K ∘ K` is a scalar `ε` of modulus
one.  The conjugation of the first argument of `H` turns the two `ε`-factors into `star ε * ε`, so
no more than `star ε * ε = 1` is used; the real signs `ε = 1` and `ε = -1` (an involution, or a
quaternionic structure) are the main examples.  This is the only property of `balance` that `H`
alone does not already have, and the whole point of the construction. -/
theorem balance_map_map {H : V →ₗ⋆[R] V →ₗ[R] R} {K : V →ₛₗ[starRingEnd R] V} {ε : R}
    (hε : star ε * ε = 1) (hK : ∀ x : V, K (K x) = ε • x) (x y : V) :
    balance H K (K x) (K y) = starRingEnd R (balance H K x y) := by
  -- The first argument of `H` contributes a factor `star ε` and the second a factor `ε`.
  have hH : H (ε • x) (ε • y) = H x y := by
    simp [starRingEnd_apply, ← mul_assoc, mul_comm ε (star ε), hε]
  rw [balance_apply, balance_apply, hK x, hK y, hH, map_add, starRingEnd_self_apply, add_comm]

/-- The balanced form is Hermitian if `H` is. -/
theorem isSymm_balance {H : V →ₗ⋆[R] V →ₗ[R] R} (hH : H.IsSymm)
    (K : V →ₛₗ[starRingEnd R] V) : (balance H K).IsSymm where
  eq x y := by
    rw [balance_apply, balance_apply, map_add, starRingEnd_self_apply, hH.eq x y,
      hH.eq (K y) (K x)]

section StarOrderedRing

variable [PartialOrder R] [StarOrderedRing R]

/-- The balanced form is nonnegative if `H` is: both summands are, the second because conjugation
fixes a nonnegative scalar. -/
theorem isNonneg_balance {H : V →ₗ⋆[R] V →ₗ[R] R} (hH : H.IsNonneg)
    (K : V →ₛₗ[starRingEnd R] V) : (balance H K).IsNonneg where
  nonneg x := by
    rw [balance_apply, starRingEnd_apply, (hH.nonneg (K x)).star_eq]
    exact add_nonneg (hH.nonneg x) (hH.nonneg (K x))

/-- For nonnegative `H`, the balanced form is nonzero on the diagonal wherever `H` is: both
summands are nonnegative and the first is nonzero.  In particular, balancing a nonnegative form
that is definite off the origin gives a form that is again definite off the origin. -/
theorem balance_apply_self_ne_zero {H : V →ₗ⋆[R] V →ₗ[R] R} (hH : H.IsNonneg)
    (K : V →ₛₗ[starRingEnd R] V) {x : V} (hx : H x x ≠ 0) :
    balance H K x x ≠ 0 := by
  rw [balance_apply, starRingEnd_apply, (hH.nonneg (K x)).star_eq]
  exact fun h ↦ hx ((add_eq_zero_iff_of_nonneg (hH.nonneg x) (hH.nonneg (K x))).1 h).1

end StarOrderedRing

end CommSemiring

end LinearMap
