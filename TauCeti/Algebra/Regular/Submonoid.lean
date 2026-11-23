/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# The submonoid of regular elements

An element of a monoid is regular when multiplication by it, on either side, is injective. The
regular elements form the submonoid `TauCeti.regulars M`. Localizing a commutative semiring at
it gives its total quotient semiring.

Every regular element of a monoid with zero is a non-zero-divisor, and in a ring the two
notions agree (`TauCeti.regulars_eq_nonZeroDivisors`). In a semiring they can differ, which is
why localizations of semirings use regular elements. In a nontrivial monoid with zero whose
multiplication cancels nonzero elements, such as a semiring domain, the regular elements are
exactly the nonzero ones.

The name follows the terminology proposed in Mathlib issue 22997, on non-zero-divisors, regular
elements and localization.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

/-- The submonoid of regular elements of a monoid: those `a` for which both `(a * ·)` and
`(· * a)` are injective. -/
def regulars (M : Type*) [Monoid M] : Submonoid M where
  carrier := {a | IsRegular a}
  one_mem' := isRegular_one
  mul_mem' ha hb := ha.mul hb

@[simp]
theorem mem_regulars {M : Type*} [Monoid M] {a : M} : a ∈ regulars M ↔ IsRegular a :=
  Iff.rfl

/-- In a ring the regular elements are exactly the non-zero-divisors. -/
theorem regulars_eq_nonZeroDivisors (R : Type*) [Ring R] : regulars R = R⁰ :=
  Submonoid.ext fun _ ↦ isRegular_iff_mem_nonZeroDivisors

/-- In a nontrivial monoid with zero whose multiplication cancels nonzero elements, the regular
elements are exactly the nonzero ones. -/
theorem mem_regulars_iff_ne_zero {M : Type*} [MonoidWithZero M] [IsCancelMulZero M] [Nontrivial M]
    {a : M} : a ∈ regulars M ↔ a ≠ 0 :=
  isRegular_iff_ne_zero

end TauCeti
