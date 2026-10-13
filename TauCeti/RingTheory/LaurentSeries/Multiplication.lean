/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Multiplication

/-!
# Orders of powers of Laurent series

Over a nontrivial semiring without zero divisors, the order of a power of a nonzero Laurent
series is the exponent times its integer order. In particular, a power greater than one
strictly lowers a negative order.
These formulas compare poles of a Laurent series and its powers.
-/

public section

open scoped LaurentSeries

namespace TauCeti

open _root_.HahnSeries

variable {k : Type*} [Semiring k] [NoZeroDivisors k] [Nontrivial k] {n : ℕ}

/-- The order of a power of a nonzero Laurent series is the corresponding multiple of its
integer order. -/
theorem laurentSeries_orderTop_pow_of_ne_zero (n : ℕ) {w : k⸨X⸩} (hw : w ≠ 0) :
    (w ^ n).orderTop = ((n : ℤ) * w.order : ℤ) := by
  rw [hahnSeries_orderTop_pow, ← order_eq_orderTop_of_ne_zero hw,
    ← WithTop.coe_nsmul, nsmul_eq_mul]

/-- Raising a Laurent series of negative order to a power greater than one strictly lowers
its order. -/
theorem laurentSeries_orderTop_pow_lt_orderTop_of_order_neg
    (hn : 1 < n) {w : k⸨X⸩} (hw : w.order < 0) :
    (w ^ n).orderTop < w.orderTop := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hnZ : (1 : ℤ) < n := by exact_mod_cast hn
  rw [laurentSeries_orderTop_pow_of_ne_zero n hw0, ← order_eq_orderTop_of_ne_zero hw0]
  exact_mod_cast (by nlinarith : (n : ℤ) * w.order < w.order)

end TauCeti
