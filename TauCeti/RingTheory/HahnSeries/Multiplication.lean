/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Orders and leading coefficients of powers of Hahn series

Over a domain, taking a power multiplies the order and raises the leading coefficient to that
power. These formulas detect whether a leading pole term can be cancelled by a power.

The formulas are `TauCeti.HahnSeries.leadingCoeff_pow f n` and
`TauCeti.HahnSeries.orderTop_pow f n`; both are also simplification lemmas.
-/

public section

namespace TauCeti
namespace HahnSeries

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [Semiring R] [NoZeroDivisors R]

/-- The leading coefficient of a power is the power of the leading coefficient. -/
@[simp]
theorem leadingCoeff_pow (f : HahnSeries Γ R) (n : ℕ) :
    (f ^ n).leadingCoeff = f.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- The order of a power is the corresponding multiple of the order, including at zero. -/
@[simp]
theorem orderTop_pow [Nontrivial R] (f : HahnSeries Γ R) (n : ℕ) :
    (f ^ n).orderTop = n • f.orderTop := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih, add_nsmul]

end HahnSeries
end TauCeti
