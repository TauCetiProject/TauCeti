/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Symmetry and alternating properties of sesquilinear maps

Mathlib's `LinearMap.IsAlt.neg` says that an alternating sesquilinear map `ω` is skew-symmetric:
`-ω x y = ω y x`. Conversely, skew symmetry at `y = x` gives `ω x x + ω x x = 0`, so a
skew-symmetric map is alternating as soon as doubling is injective on its values. Nothing else is
asked of the scalars or of the values, so this holds over commutative semirings and for values in
any module that is an additive group. It is a module-valued, semiring form of the reverse
direction of `LinearMap.isAlt_iff_eq_neg_flip`, which is stated for scalar-valued forms over a
`CharZero` integral domain.

For a star-sesquilinear form `a : V →ₗ⋆[R] V →ₗ[R] R` over a commutative star semiring, Mathlib's
`LinearMap.IsSymm` (`∀ u v, starRingEnd R (a u v) = a v u`) is equivalent to the Hermitian
identity `∀ u v, a u v = star (a v u)` (`LinearMap.isSymm_iff_eq_star`).

## Main results

* `LinearMap.isSymm_iff_eq_star`: `a.IsSymm` holds if and only if `∀ u v, a u v = star (a v u)`.
* `LinearMap.IsAlt.of_neg_eq_flip`: a skew-symmetric sesquilinear map is alternating when doubling
  is injective on its values.
-/

public section

namespace LinearMap

/-- A sesquilinear form `a : V →ₗ⋆[R] V →ₗ[R] R` is symmetric in Mathlib's `LinearMap.IsSymm`
sense precisely when `a u v = star (a v u)` for all `u` and `v`. -/
theorem isSymm_iff_eq_star {R V : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid V]
    [Module R V] {a : V →ₗ⋆[R] V →ₗ[R] R} :
    a.IsSymm ↔ ∀ u v, a u v = star (a v u) := by
  rw [isSymm_def]
  refine forall₂_congr fun u v ↦ ?_
  rw [starRingEnd_apply, star_eq_iff_star_eq, eq_comm]

namespace IsAlt

/-- A skew-symmetric sesquilinear map is alternating when doubling is injective on its values.
This is the converse of `LinearMap.IsAlt.neg`, and a module-valued, semiring form of the reverse
direction of `LinearMap.isAlt_iff_eq_neg_flip`. -/
theorem of_neg_eq_flip {R R₁ M N : Type*} [CommSemiring R] [CommSemiring R₁] [AddCommMonoid M]
    [Module R₁ M] [AddCommGroup N] [Module R N] {I₁ I₂ : R₁ →+* R}
    {ω : M →ₛₗ[I₁] M →ₛₗ[I₂] N} (h2 : IsSMulRegular N (2 : ℕ))
    (h : ∀ x y, -ω x y = ω y x) : ω.IsAlt := fun x ↦ by
  apply h2
  simpa only [two_nsmul, smul_zero, h x x] using neg_add_cancel (ω x x)

end IsAlt

end LinearMap
