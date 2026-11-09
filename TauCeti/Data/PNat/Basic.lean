/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PNat.Basic

/-!
# Exact division of positive integers

For positive integers `k ∣ m`, `PNat.divExact m k` is the quotient `m / k` as a positive integer.
This file identifies it with the natural-number quotient.

## Main results

* `PNat.coe_divExact`: for `k ∣ m`, `(PNat.divExact m k : ℕ) = m / k`.
-/

public section

namespace PNat

/-- For `k ∣ m`, the exact quotient `PNat.divExact m k` is the natural-number quotient `m / k`. -/
theorem coe_divExact {m k : ℕ+} (h : k ∣ m) : (divExact m k : ℕ) = m / k :=
  (Nat.div_eq_of_eq_mul_right k.pos (by rw [← mul_coe, mul_div_exact h])).symm

end PNat
