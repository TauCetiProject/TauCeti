/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Leading coefficients of powers of Hahn series

Over a domain, taking a power raises the leading coefficient to that power. This formula
detects whether a leading pole term can be cancelled by a power.
-/

public section

namespace TauCeti

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [Semiring R] [NoZeroDivisors R]

/-- The leading coefficient of a power is the power of the leading coefficient. -/
@[simp]
theorem _root_.HahnSeries.leadingCoeff_pow (f : HahnSeries Γ R) (n : ℕ) :
    (f ^ n).leadingCoeff = f.leadingCoeff ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

end TauCeti
