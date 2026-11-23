/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Skew-symmetric sesquilinear maps are alternating

Mathlib's `LinearMap.IsAlt.neg` says that an alternating sesquilinear map `ω` is skew-symmetric:
`-ω x y = ω y x`. Conversely, skew symmetry at `y = x` gives `ω x x + ω x x = 0`, so a
skew-symmetric map is alternating as soon as doubling is injective on its values. Nothing else is
asked of the scalars or of the values, so this holds over commutative semirings and for values in
any module that is an additive group. It is a module-valued, semiring form of the reverse
direction of `LinearMap.isAlt_iff_eq_neg_flip`, which is stated for scalar-valued forms over a
`CharZero` integral domain.

## Main results

* `LinearMap.IsAlt.of_neg_eq_flip`: a skew-symmetric sesquilinear map is alternating when doubling
  is injective on its values.
-/

public section

namespace LinearMap.IsAlt

/-- A skew-symmetric sesquilinear map is alternating when doubling is injective on its values.
This is the converse of `LinearMap.IsAlt.neg`, and a module-valued, semiring form of the reverse
direction of `LinearMap.isAlt_iff_eq_neg_flip`. -/
theorem of_neg_eq_flip {R R₁ M N : Type*} [CommSemiring R] [CommSemiring R₁] [AddCommMonoid M]
    [Module R₁ M] [AddCommGroup N] [Module R N] {I₁ I₂ : R₁ →+* R}
    {ω : M →ₛₗ[I₁] M →ₛₗ[I₂] N} (h2 : IsSMulRegular N (2 : ℕ))
    (h : ∀ x y, -ω x y = ω y x) : ω.IsAlt := fun x ↦ by
  apply h2
  simpa only [two_nsmul, smul_zero, h x x] using neg_add_cancel (ω x x)

end LinearMap.IsAlt
