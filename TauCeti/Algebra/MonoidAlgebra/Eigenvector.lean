/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Algebra.MonoidAlgebra.Opposite
import Mathlib.Algebra.MonoidAlgebra.Support
import TauCeti.Algebra.MonoidAlgebra.Basic

/-!
# Eigenvectors of right multiplication by a monoid element

Let `g` be an element of a monoid `G` and `c` a scalar of a semiring `R`. A nonzero element `x` of
the monoid algebra `R[G]` with `x g = x c` is an eigenvector of right multiplication by `g` with
eigenvalue `c`, the scalar `c` also acting on the right. Over any semiring, right multiplication
by `g ^ n` then acts on `x` as right multiplication by the scalar `c ^ n`. When `g` has finite
order, `g ^ orderOf g = 1`, so the scalar `c ^ orderOf g` fixes `x`, and when nonzero elements of
`R` are left cancellable the eigenvalue is a root of unity of order dividing `orderOf g`. The
equality `c ^ orderOf g = 1` also holds when `g` has infinite order, but is then vacuous because
`orderOf g = 0`. A natural-number eigenvalue `a` of an element of finite order is `1` as soon as
the additive monoid of `R` is cancellative and torsion-free: `x` is then fixed by multiplication by
`a ^ orderOf g`, and no cancellation hypothesis on the multiplication of `R` is needed. At the
other extreme, when `G` is a left-cancellative monoid, an element of infinite order has no nonzero
eigenvector of eigenvalue `1`: each element of the support of such an eigenvector would be a right
translate by every power of `g` of a distinct element of the support, so the support would be
infinite. Over a ring, it follows that for such `G` and `g` right multiplication by `g - 1` is
injective, and that `g - 1` is not a zero divisor of `R[G]` when `G` is cancellative.

## Main statements

* `TauCeti.mul_single_pow_eq_mul_single_one_pow`: over any semiring, if `x g = x c` then
  `x g ^ n = x c ^ n` for every `n`.
* `TauCeti.pow_orderOf_eq_one_of_mul_single_eq_mul_single`: if nonzero elements of `R` are left
  cancellable, the eigenvalue `c` satisfies `c ^ orderOf g = 1`.
* `TauCeti.nat_eq_one_of_mul_single_eq_mul_single`: over a semiring whose additive monoid is
  cancellative and torsion-free, a natural-number eigenvalue of an element of finite order is `1`.
* `TauCeti.eq_zero_of_mul_single_eq_self_of_not_isOfFinOrder`: in a left-cancellative monoid, if
  `g` has infinite order, then `x * g = x` forces `x = 0`; its additive form is
  `TauCeti.eq_zero_of_mul_single_eq_self_of_not_isOfFinAddOrder`.
* `TauCeti.isRegular_single_sub_one_of_not_isOfFinOrder`: over a ring, if `g` is an element of
  infinite order of a cancellative monoid, then `g - 1` is regular; for `G = ℤ` this says that
  `t - 1` is not a zero divisor in `R[t, t⁻¹]`.
-/

public section

namespace TauCeti

open _root_.MonoidAlgebra

variable {R : Type*} [Semiring R] {G : Type*} [Monoid G]

/-- If an element `x` of `R[G]` satisfies `x g = x c`, then `x g ^ n = x c ^ n` for every `n`,
the scalar `c` acting on the right. -/
theorem mul_single_pow_eq_mul_single_one_pow {x : MonoidAlgebra R G} {g : G} {c : R}
    (h : x * single g (1 : R) = x * single 1 c) (n : ℕ) :
    x * single (g ^ n) (1 : R) = x * single 1 (c ^ n) := by
  -- `g` commutes with the scalar `c`, so `c ^ n` can be moved past `g`.
  have hcomm : Commute (single g (1 : R)) (single 1 c) :=
    single_commute_single (.one_right g) (.one_left c)
  have key : x * single g (1 : R) ^ n = x * single 1 c ^ n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, ← (hcomm.pow_right n).eq, ← mul_assoc, h,
        mul_assoc, ← pow_succ']
  simpa only [single_pow, one_pow] using key

/-- If nonzero elements of `R` are left cancellable and a nonzero element `x` of `R[G]` satisfies
`x g = x c`, then `c ^ orderOf g = 1`. -/
theorem pow_orderOf_eq_one_of_mul_single_eq_mul_single [IsLeftCancelMulZero R]
    {x : MonoidAlgebra R G} (hx : x ≠ 0) {g : G} {c : R}
    (h : x * single g (1 : R) = x * single 1 c) : c ^ orderOf g = 1 := by
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr (coeff_eq_zero.not.mpr hx)
  have hfix := congrArg (fun z ↦ z.coeff i) (mul_single_pow_eq_mul_single_one_pow h (orderOf g))
  simp only [pow_orderOf_eq_one, ← one_def, mul_one, coeff_mul_single_one] at hfix
  exact mul_left_cancel₀ (Finsupp.mem_support_iff.mp hi) (hfix.symm.trans (mul_one _).symm)

/-- If the additive monoid of `R` is cancellative and torsion-free and a nonzero element `x` of
`R[G]` satisfies `x g = x a` for an element `g` of finite order and a natural number `a`, then
`a = 1`. -/
theorem nat_eq_one_of_mul_single_eq_mul_single [IsCancelAdd R] [IsAddTorsionFree R]
    {x : MonoidAlgebra R G} (hx : x ≠ 0) {g : G} (hg : IsOfFinOrder g) {a : ℕ}
    (h : x * single g (1 : R) = x * single 1 (a : R)) : a = 1 := by
  have ha : a ^ orderOf g • x = x := by
    rw [nsmul_eq_mul', natCast_def, Nat.cast_pow, ← mul_single_pow_eq_mul_single_one_pow h,
      pow_orderOf_eq_one, ← one_def, mul_one]
  -- In a cancellative torsion-free additive monoid, `m • x = x` with `x ≠ 0` forces `m = 1`.
  have key : ∀ m : ℕ, m • x = x → m = 1 := by
    rintro (_ | _ | m) hm
    · exact absurd (by simpa using hm.symm) hx
    · rfl
    · refine absurd (eq_of_nsmul_eq_nsmul_of_addCommute m.succ_ne_zero (.zero_right x) ?_) hx
      rw [nsmul_zero]
      exact add_right_cancel (b := x) (by rw [← succ_nsmul, hm, zero_add])
  exact (Nat.pow_eq_one.mp (key _ ha)).resolve_right hg.orderOf_pos.ne'

section LeftCancelMonoid

variable {R : Type*} [Semiring R] {G : Type*} [LeftCancelMonoid G]

/-- An element `g` of infinite order has no nonzero eigenvector of eigenvalue `1` under right
multiplication: `x * g = x` forces `x = 0`. -/
@[to_additive (dont_translate := R) eq_zero_of_mul_single_eq_self_of_not_isOfFinAddOrder
  /-- An element `a` of infinite order has no nonzero eigenvector of eigenvalue `1` under
  multiplication by `e^a`: `x * e^a = x` forces `x = 0`. -/]
theorem eq_zero_of_mul_single_eq_self_of_not_isOfFinOrder {x : MonoidAlgebra R G} {g : G}
    (hg : ¬IsOfFinOrder g) (h : x * single g (1 : R) = x) : x = 0 := by
  classical
  by_contra hx
  obtain ⟨y, hy⟩ := Finsupp.support_nonempty_iff.mpr (coeff_eq_zero.not.mpr hx)
  have hpow (n : ℕ) : x * single (g ^ n) (1 : R) = x := by
    have := (Function.IsFixedPt.iterate (f := (· * single g (1 : R))) h n).eq
    rwa [mul_right_iterate_apply, single_pow, one_pow] at this
  -- For each `n`, the coefficient at `y` comes from some `z n` in the support with
  -- `z n * g ^ n = y`; by left cancellation, these are pairwise distinct.
  have hz (n : ℕ) : ∃ z ∈ x.coeff.support, z * g ^ n = y := by
    simpa using support_coeff_mul_single_subset x 1 (g ^ n) (by rwa [hpow n])
  choose z hzs hzy using hz
  refine (Set.infinite_of_injective_forall_mem (fun m n hmn ↦ ?_) hzs).not_finite
    x.coeff.support.finite_toSet
  exact injective_pow_iff_not_isOfFinOrder.mpr hg <| mul_left_cancel (a := z m) <| by
    rw [hzy m, hmn, hzy n]

end LeftCancelMonoid

section Ring

variable {R : Type*} [Ring R] {G : Type*}

/-- Over a ring, right multiplication by `g - 1` is injective when `g` is an element of infinite
order of a left-cancellative monoid. -/
@[to_additive (dont_translate := R) isRightRegular_single_sub_one_of_not_isOfFinAddOrder
  /-- Over a ring, multiplication by `e^a - 1` on the right is injective when `a` is an element of
  infinite order of a left-cancellative additive monoid. -/]
theorem isRightRegular_single_sub_one_of_not_isOfFinOrder [LeftCancelMonoid G] {g : G}
    (hg : ¬IsOfFinOrder g) : IsRightRegular (single g (1 : R) - 1) := fun x y hxy ↦
  sub_eq_zero.mp <| eq_zero_of_mul_single_eq_self_of_not_isOfFinOrder hg <| by
    rw [← sub_eq_zero, ← mul_sub_one, sub_mul]
    exact sub_eq_zero.mpr hxy

/-- Over a ring, `g - 1` is regular when `g` is an element of infinite order of a cancellative
monoid. -/
@[to_additive (dont_translate := R) isRegular_single_sub_one_of_not_isOfFinAddOrder
  /-- Over a ring, `e^a - 1` is regular when `a` is an element of infinite order of a
  cancellative additive monoid. -/]
theorem isRegular_single_sub_one_of_not_isOfFinOrder [CancelMonoid G] {g : G}
    (hg : ¬IsOfFinOrder g) : IsRegular (single g (1 : R) - 1) := by
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
