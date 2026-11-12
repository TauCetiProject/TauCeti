/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Eigenvectors of right multiplication by a monoid element

Let `g` be an element of a monoid `G` and `c` a scalar of a commutative ring `R`. A nonzero
element `x` of the monoid algebra `R[G]` with `x (g - c) = 0` is an eigenvector of right
multiplication by `g` with eigenvalue `c`. When `g` has finite order, right multiplication by
`g ^ orderOf g = 1` is the identity, so when `R` has no zero divisors the eigenvalue is a root of
unity of order dividing `orderOf g`. The equality `c ^ orderOf g = 1` also holds when `g` has
infinite order, but is then vacuous because `orderOf g = 0`. In characteristic zero the only
natural number that is such a root of unity is `1`. At the other extreme, an element of infinite
order has no nonzero eigenvector of eigenvalue `1`: the support of such an eigenvector would be
stable under right translation by `g`, hence infinite.

## Main statements

* `TauCeti.pow_orderOf_eq_one_of_mul_single_sub_eq_zero`: the eigenvalue `c`
  satisfies `c ^ orderOf g = 1`.
* `TauCeti.nat_eq_one_of_mul_single_sub_eq_zero`: in characteristic zero, a
  natural-number eigenvalue of an element of finite order is `1`.
* `TauCeti.eq_zero_of_mul_single_eq_self_of_not_isOfFinOrder`: if `g` has infinite order, then
  `x * g = x` forces `x = 0`; its additive form is
  `TauCeti.eq_zero_of_mul_single_eq_self_of_not_isOfFinAddOrder`.
-/

public section

namespace TauCeti

open _root_.MonoidAlgebra

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {G : Type*} [Monoid G]

/-- If a nonzero element `x` of `R[G]` satisfies `x (g - c) = 0`, then `c ^ orderOf g = 1`. -/
theorem pow_orderOf_eq_one_of_mul_single_sub_eq_zero {x : MonoidAlgebra R G} (hx : x ≠ 0)
    {g : G} {c : R} (h : x * (single g (1 : R) - single 1 c) = 0) : c ^ orderOf g = 1 := by
  have hmul : x * single g (1 : R) = c • x := by
    rw [mul_sub, sub_eq_zero] at h
    rw [← single_one_comm] at h
    refine h.trans ?_
    ext i
    rw [coeff_single_one_mul, coeff_smul_apply]
    rfl
  have hpow (n : ℕ) : x * single (g ^ n) (1 : R) = c ^ n • x := by
    induction n with
    | zero => rw [pow_zero, pow_zero, one_smul, ← one_def, mul_one]
    | succ n ih =>
      calc
        x * single (g ^ (n + 1)) (1 : R) = x * (single (g ^ n) 1 * single g 1) := by
              rw [pow_succ, single_mul_single, one_mul]
        _ = (x * single (g ^ n) 1) * single g 1 := by rw [mul_assoc]
        _ = (c ^ n • x) * single g 1 := by rw [ih]
        _ = c ^ n • (x * single g 1) := by rw [smul_mul_assoc]
        _ = c ^ n • (c • x) := by rw [hmul]
        _ = c ^ (n + 1) • x := by rw [smul_smul, pow_succ]
  have hfix := hpow (orderOf g)
  rw [pow_orderOf_eq_one, ← one_def, mul_one] at hfix
  obtain ⟨i, hi⟩ : ∃ i, x.coeff i ≠ 0 := by
    by_contra hall
    apply hx
    ext i
    simpa using not_exists.mp hall i
  have hi' := congrArg (fun y : MonoidAlgebra R G ↦ y.coeff i) hfix
  rw [coeff_smul_apply, smul_eq_mul] at hi'
  exact mul_right_cancel₀ hi (by simpa only [one_mul] using hi'.symm)

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
    by_contra! hall
    exact hx (coeff_injective (Finsupp.ext hall))
  -- The coefficient at `y` recurs at every `y * g ^ n`, and these are pairwise distinct.
  have hpow (n : ℕ) : x.coeff (y * g ^ n) = x.coeff y := by
    induction n with
    | zero => rw [pow_zero, mul_one]
    | succ n ih => rw [pow_succ, ← mul_assoc, ← ih, ← mul_one (x.coeff (y * g ^ n)),
        ← coeff_mul_single_mul, h]
  have hinj : Function.Injective fun n : ℕ ↦ y * g ^ n :=
    fun _ _ hmn ↦ injective_pow_iff_not_isOfFinOrder.mpr hg (by simpa using mul_left_cancel hmn)
  refine (Set.infinite_range_of_injective hinj).not_finite (x.coeff.support.finite_toSet.subset ?_)
  rintro - ⟨n, rfl⟩
  simpa [hpow n] using hy

end CancelMonoid

end TauCeti
