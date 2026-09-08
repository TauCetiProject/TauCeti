/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Balancing a sesquilinear form against a conjugate-semilinear map, and separation

A sesquilinear form `H` on a module and a `star`-semilinear map `K` of that module are unrelated
data.  This file makes them compatible: the **balanced** form

`balance H K x y = H x y + star (H (K x) (K y))`

is again sesquilinear -- each argument of the second summand picks up a conjugation from `K`, and
the outer conjugation restores the shape -- and it satisfies

`balance H K (K x) (K y) = star (balance H K x y)`

as soon as `K ∘ K` is a scalar of modulus one, which an arbitrary `H` need not.  That is the
only property balancing adds: being Hermitian, nonnegative, and definite off the origin all pass
from `H` to `balance H K` unchanged.

The construction and its compatibility are plain star-ring algebra, so they are stated over a
commutative star semiring.  Nonnegativity and definiteness off the origin need an order on the
scalars and are stated over `ℂ`, which is why the file sits here: the complex half is what the
representation theory of `TauCeti/RepresentationTheory/InvariantForm/StructureMap.lean` consumes.

Definiteness off the origin is also what makes a form **separate** vectors: two vectors pairing
identically against every vector are equal, because their difference pairs to zero with itself.
That principle is what the representation theory downstream uses to identify two vectors, and it
is recorded here beside the construction; it needs subtraction, hence a commutative star *ring*.

## Main definitions

* `LinearMap.balance`: the balanced form `x, y ↦ H x y + star (H (K x) (K y))`.

## Main results

* `LinearMap.balance_apply`: the defining formula of the balanced form.
* `LinearMap.balance_map_map`: the balanced form is compatible with the map it was balanced
  against, once that map squares to a scalar of modulus one.
* `LinearMap.isSymm_balance`, `LinearMap.isNonneg_balance` and
  `LinearMap.balance_apply_self_ne_zero`: balancing preserves Hermitian symmetry, nonnegativity,
  and definiteness off the origin.
* `LinearMap.eq_of_forall_sesq_eq`: a form definite off the origin separates vectors.
-/

public section

open scoped ComplexOrder

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
    { toFun := fun y => H x y + (starRingEnd R) (H (K x) (K y))
      map_add' := fun y z => by simp only [map_add]; ring
      map_smul' := fun c y => by
        simp only [map_smulₛₗ, RingHom.id_apply, smul_eq_mul, map_mul, starRingEnd_self_apply]
        ring }
  map_add' x y := by
    ext z
    simp only [map_add, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  map_smul' c x := by
    ext z
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, starRingEnd_self_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    ring

/-- The defining formula of the balanced form. -/
@[simp]
theorem balance_apply (H : V →ₗ⋆[R] V →ₗ[R] R) (K : V →ₛₗ[starRingEnd R] V) (x y : V) :
    balance H K x y = H x y + (starRingEnd R) (H (K x) (K y)) := (rfl)

/-- **The balanced form is compatible with the map it was balanced against**: replacing both
arguments by their `K`-images conjugates the value, as soon as `K ∘ K` is a scalar `ε` of modulus
one.  The conjugation of the first argument of `H` turns the two `ε`-factors into `star ε * ε`, so
no more than `star ε * ε = 1` is used; the real signs `ε = 1` and `ε = -1` -- an involution, or a
quaternionic structure -- are the cases the representation theory needs.  This is the only property
of `balance` that `H` alone does not already have, and the whole point of the construction. -/
theorem balance_map_map {H : V →ₗ⋆[R] V →ₗ[R] R} {K : V →ₛₗ[starRingEnd R] V} {ε : R}
    (hε : star ε * ε = 1) (hK : ∀ x : V, K (K x) = ε • x) (x y : V) :
    balance H K (K x) (K y) = (starRingEnd R) (balance H K x y) := by
  -- The first argument of `H` contributes a factor `star ε` and the second a factor `ε`.
  have hεmul : ε * star ε = 1 := by rw [mul_comm]; exact hε
  have hH : H (ε • x) (ε • y) = H x y := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
    rw [← mul_assoc, hεmul, one_mul]
  rw [balance_apply, balance_apply, hK x, hK y, hH, map_add, starRingEnd_self_apply, add_comm]

/-- The balanced form is Hermitian if `H` is. -/
theorem isSymm_balance {H : V →ₗ⋆[R] V →ₗ[R] R} (hH : H.IsSymm)
    (K : V →ₛₗ[starRingEnd R] V) : (balance H K).IsSymm where
  eq x y := by
    rw [balance_apply, balance_apply, map_add, starRingEnd_self_apply, hH.eq x y,
      hH.eq (K y) (K x)]

end CommSemiring

section CommRing

variable {R V : Type*} [CommRing R] [StarRing R] [AddCommGroup V] [Module R V]

/-- **A form definite off the origin separates vectors**: two vectors pairing identically against
every vector are equal, because their difference pairs to zero with itself.  Mathlib's
`LinearMap.SeparatingLeft` is the same separation stated as a property of the form; definiteness
off the origin is what supplies it here, and is the shape the callers carry it in. -/
theorem eq_of_forall_sesq_eq {H : V →ₗ⋆[R] V →ₗ[R] R} (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) {u v : V}
    (h : ∀ y : V, H u y = H v y) : u = v := by
  rw [← sub_eq_zero]
  by_contra hne
  refine hdef _ hne ?_
  -- The difference pairs to zero against every vector, so in particular against itself.
  have hzero : H (u - v) = 0 := by
    ext y
    rw [map_sub, LinearMap.sub_apply, h y, sub_self, LinearMap.zero_apply]
  rw [hzero, LinearMap.zero_apply]

end CommRing

section Complex

variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

/-- The balanced form is nonnegative if `H` is: both summands are, the second because conjugation
fixes a nonnegative complex number. -/
theorem isNonneg_balance {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hH : H.IsNonneg)
    (K : V →ₛₗ[starRingEnd ℂ] V) : (balance H K).IsNonneg where
  nonneg x := by
    rw [balance_apply, starRingEnd_apply, (hH.nonneg (K x)).star_eq]
    exact add_nonneg (hH.nonneg x) (hH.nonneg (K x))

/-- The balanced form is definite off the origin if `H` is: the first summand is already nonzero
and the second is nonnegative. -/
theorem balance_apply_self_ne_zero {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hH : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) (K : V →ₛₗ[starRingEnd ℂ] V) {x : V} (hx : x ≠ 0) :
    balance H K x x ≠ 0 := by
  rw [balance_apply, starRingEnd_apply, (hH.nonneg (K x)).star_eq]
  exact (add_pos_of_pos_of_nonneg
    (lt_of_le_of_ne (hH.nonneg x) (Ne.symm (hdef x hx))) (hH.nonneg (K x))).ne'

end Complex

end LinearMap
