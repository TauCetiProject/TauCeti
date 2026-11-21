/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Algebra.MonoidAlgebra.Opposite
import Mathlib.Algebra.Ring.GeomSum

/-!
# Eigenvectors of right multiplication by a monoid element

Let `g` be an element of a monoid `G` and `c` a scalar of a ring `R`. A nonzero element `x` of the
monoid algebra `R[G]` with `x (g - c) = 0` is an eigenvector of right multiplication by `g` with
eigenvalue `c`, the scalar `c` also acting on the right. When `g` has finite order, right
multiplication by `g ^ orderOf g = 1` is the identity, so when `R` has no zero divisors the
eigenvalue is a root of unity of order dividing `orderOf g`. The equality `c ^ orderOf g = 1` also
holds when `g` has infinite order, but is then vacuous because `orderOf g = 0`. In characteristic
zero the only natural number that is such a root of unity is `1`. At the other extreme, when `G` is
a cancellative monoid, an element of infinite order has no nonzero eigenvector of eigenvalue `1`:
the support of such an eigenvector would be stable under right translation by `g`, hence infinite.
Over a ring, it follows that for such `G` and `g` the element `g - 1` is not a zero divisor of
`R[G]`.

## Main statements

* `TauCeti.pow_orderOf_eq_one_of_mul_single_sub_eq_zero`: the eigenvalue `c`
  satisfies `c ^ orderOf g = 1`.
* `TauCeti.nat_eq_one_of_mul_single_sub_eq_zero`: in characteristic zero, a
  natural-number eigenvalue of an element of finite order is `1`.
* `TauCeti.eq_zero_of_mul_single_eq_self_of_not_isOfFinOrder`: in a cancellative monoid, if `g`
  has infinite order, then `x * g = x` forces `x = 0`; its additive form is
  `TauCeti.eq_zero_of_mul_single_eq_self_of_not_isOfFinAddOrder`.
* `TauCeti.isRegular_single_sub_one_of_not_isOfFinOrder`: over a ring, if `g` is an element of
  infinite order of a cancellative monoid, then `g - 1` is regular; for `G = ℤ` this says that
  `t - 1` is not a zero divisor in `R[t, t⁻¹]`.
-/

public section

namespace TauCeti

open _root_.MonoidAlgebra

variable {R : Type*} [Ring R] [NoZeroDivisors R] {G : Type*} [Monoid G]

/-- If a nonzero element `x` of `R[G]` satisfies `x (g - c) = 0`, then `c ^ orderOf g = 1`. -/
theorem pow_orderOf_eq_one_of_mul_single_sub_eq_zero {x : MonoidAlgebra R G} (hx : x ≠ 0)
    {g : G} {c : R} (h : x * (single g (1 : R) - single 1 c) = 0) : c ^ orderOf g = 1 := by
  -- `g` commutes with the scalar `c`, so `g - c` divides `g ^ n - c ^ n`. For `n = orderOf g`
  -- this says that right multiplication by the scalar `c ^ orderOf g` fixes `x`.
  have hcomm : Commute (single g (1 : R)) (single 1 c) :=
    single_commute_single (.one_right g) (.one_left c)
  have hfix : x * (single g (1 : R) ^ orderOf g - single 1 c ^ orderOf g) = 0 := by
    rw [← hcomm.mul_geom_sum₂, ← mul_assoc, h, zero_mul]
  simp only [single_pow, one_pow, pow_orderOf_eq_one, ← one_def, mul_one_sub, sub_eq_zero] at hfix
  obtain ⟨i, hi⟩ : ∃ i, x.coeff i ≠ 0 := by
    simpa [Finsupp.ext_iff] using coeff_eq_zero.not.mpr hx
  have hi' : x.coeff i * 1 = x.coeff i * c ^ orderOf g := by
    rw [mul_one, ← coeff_mul_single_one, ← hfix]
  exact (mul_left_cancel₀ hi hi').symm

/-- In characteristic zero, if a nonzero element `x` of `R[G]` satisfies `x (g - a) = 0` for an
element `g` of finite order and a natural number `a`, then `a = 1`. -/
theorem nat_eq_one_of_mul_single_sub_eq_zero [CharZero R] {x : MonoidAlgebra R G} (hx : x ≠ 0)
    {g : G} (hg : IsOfFinOrder g) {a : ℕ} (h : x * (single g (1 : R) - single 1 (a : R)) = 0) :
    a = 1 := by
  have ha : a ^ orderOf g = 1 := by
    exact_mod_cast pow_orderOf_eq_one_of_mul_single_sub_eq_zero hx h
  exact (Nat.pow_eq_one.mp ha).resolve_right hg.orderOf_pos.ne'

section CancelMonoid

variable {R : Type*} [Semiring R] {G : Type*} [CancelMonoid G]

/-- An element `g` of infinite order has no nonzero eigenvector of eigenvalue `1` under right
multiplication: `x * g = x` forces `x = 0`. -/
@[to_additive (dont_translate := R) eq_zero_of_mul_single_eq_self_of_not_isOfFinAddOrder
  /-- An element `a` of infinite order has no nonzero eigenvector of eigenvalue `1` under
  multiplication by `e^a`: `x * e^a = x` forces `x = 0`. -/]
theorem eq_zero_of_mul_single_eq_self_of_not_isOfFinOrder {x : MonoidAlgebra R G} {g : G}
    (hg : ¬IsOfFinOrder g) (h : x * single g (1 : R) = x) : x = 0 := by
  by_contra hx
  obtain ⟨y, hy⟩ : ∃ y, x.coeff y ≠ 0 := by
    simpa [Finsupp.ext_iff] using coeff_eq_zero.not.mpr hx
  -- The coefficient at `y` recurs at every `y * g ^ n`, and these are pairwise distinct.
  have hpow (n : ℕ) : x.coeff (y * g ^ n) = x.coeff y := by
    induction n with
    | zero => rw [pow_zero, mul_one]
    | succ n ih => rw [pow_succ, ← mul_assoc, ← ih, ← mul_one (x.coeff (y * g ^ n)),
        ← coeff_mul_single_mul, h]
  have hinj : Function.Injective fun n : ℕ ↦ y * g ^ n :=
    (mul_right_injective y).comp (injective_pow_iff_not_isOfFinOrder.mpr hg)
  refine (Set.infinite_range_of_injective hinj).not_finite (x.coeff.support.finite_toSet.subset ?_)
  rintro - ⟨n, rfl⟩
  simpa [hpow n] using hy

end CancelMonoid

section Ring

variable {R : Type*} [Ring R] {G : Type*} [CancelMonoid G]

/-- Over a ring, right multiplication by `g - 1` is injective when `g` is an element of infinite
order of a cancellative monoid. -/
@[to_additive (dont_translate := R) isRightRegular_single_sub_one_of_not_isOfFinAddOrder
  /-- Over a ring, multiplication by `e^a - 1` on the right is injective when `a` is an element of
  infinite order of a cancellative additive monoid. -/]
theorem isRightRegular_single_sub_one_of_not_isOfFinOrder {g : G} (hg : ¬IsOfFinOrder g) :
    IsRightRegular (single g (1 : R) - 1) := fun x y hxy ↦ sub_eq_zero.mp <|
  eq_zero_of_mul_single_eq_self_of_not_isOfFinOrder hg <| by
    rw [← sub_eq_zero, ← mul_sub_one, sub_mul]
    exact sub_eq_zero.mpr hxy

/-- Over a ring, `g - 1` is regular when `g` is an element of infinite order of a cancellative
monoid. -/
@[to_additive (dont_translate := R) isRegular_single_sub_one_of_not_isOfFinAddOrder
  /-- Over a ring, `e^a - 1` is regular when `a` is an element of infinite order of a
  cancellative additive monoid. -/]
theorem isRegular_single_sub_one_of_not_isOfFinOrder {g : G} (hg : ¬IsOfFinOrder g) :
    IsRegular (single g (1 : R) - 1) := by
  -- Left regularity is right regularity in the opposite monoid algebra `Rᵐᵒᵖ[Gᵐᵒᵖ]`.
  refine ⟨fun x y hxy ↦ ?_, isRightRegular_single_sub_one_of_not_isOfFinOrder hg⟩
  have hg' : ¬IsOfFinOrder (MulOpposite.op g) := by
    simpa [isOfFinOrder_iff_pow_eq_one, ← MulOpposite.op_pow] using hg
  have h := congrArg (fun z ↦ MonoidAlgebra.opRingEquiv (MulOpposite.op z)) hxy
  simp only [MulOpposite.op_mul, map_mul, MulOpposite.op_sub, map_sub, opRingEquiv_single,
    MulOpposite.op_one, map_one] at h
  simpa using isRightRegular_single_sub_one_of_not_isOfFinOrder hg' h

end Ring

end TauCeti
