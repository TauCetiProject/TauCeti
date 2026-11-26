/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Skew-symmetric sesquilinear maps are alternating, and forms vanishing on the diagonal

Mathlib's `LinearMap.IsAlt.neg` says that an alternating sesquilinear map `ω` is skew-symmetric:
`-ω x y = ω y x`. Conversely, skew symmetry at `y = x` gives `ω x x + ω x x = 0`, so a
skew-symmetric map is alternating as soon as doubling is injective on its values. Nothing else is
asked of the scalars or of the values, so this holds over commutative semirings and for values in
any module that is an additive group. It is a module-valued, semiring form of the reverse
direction of `LinearMap.isAlt_iff_eq_neg_flip`, which is stated for scalar-valued forms over a
`CharZero` integral domain.

A sesquilinear form `B` with `B x x = 0` for every `x` is skew-symmetric. If moreover the
involution `σ` moves some `z` with `z - σ z` cancellable, then `B` is zero: the skew symmetry for
`x` and `z • y` gives `(z - σ z) B x y = 0`. This needs no hypothesis on `2`, so in characteristic
two it replaces polarization.

## Main results

* `LinearMap.IsAlt.of_neg_eq_flip`: a skew-symmetric sesquilinear map is alternating when doubling
  is injective on its values.
* `LinearMap.eq_zero_of_forall_apply_self_eq_zero`: over a commutative ring with an involution
  moving some `z` with `z - σ z` cancellable, a sesquilinear form vanishing on the diagonal is
  zero.
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

namespace LinearMap

/-- **A sesquilinear form vanishing on the diagonal is zero** when the involution moves some `z`
with `z - σ z` cancellable. Indeed `B y x = -B x y` by `LinearMap.IsAlt.neg`, and the
same identity for `z • y` gives `(z - σ z) B x y = 0`. This needs no hypothesis on `2`. -/
theorem eq_zero_of_forall_apply_self_eq_zero {K V : Type*} [CommRing K] [AddCommGroup V]
    [Module K V] {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {z : K}
    (hz : z - σ z ∈ nonZeroDivisors K) (hB : ∀ x, B x x = 0) : B = 0 := by
  -- `B.IsAlt` is by definition `∀ x, B x x = 0`, so `hB` is that hypothesis.
  have hswap (x y : V) : B y x = -B x y := ((show B.IsAlt from hB).neg x y).symm
  ext x y
  have h := hswap x (z • y)
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hswap x y, RingHom.id_apply] at h
  have h' : (z - σ z) * B x y = 0 := by linear_combination h
  simpa using (mul_right_mem_nonZeroDivisors_eq_zero_iff hz).1 (by rwa [mul_comm] at h')

end LinearMap
