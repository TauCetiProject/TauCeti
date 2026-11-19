/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.ZMod.Basic

/-!
# Divisibility of `c (c² - 1)` for odd integers `c`

For an odd integer `c`, `24 ∣ c (c² - 1)`: the factor `c² - 1` is divisible by `8`
(`Int.eight_dvd_sq_sub_one_of_odd`), and the product `(c - 1) c (c + 1)` of three consecutive
integers is divisible by `3`. The proof checks every residue class modulo `24`.

## Main results

* `Int.twentyFour_dvd_mul_sq_sub_one_of_odd`: for odd `c`, `24 ∣ c (c² - 1)`.
-/

public section

namespace Int

/-- For odd `c`, `24 ∣ c (c² - 1)`. -/
theorem twentyFour_dvd_mul_sq_sub_one_of_odd {c : ℤ} (hc : Odd c) : 24 ∣ c * (c ^ 2 - 1) := by
  obtain ⟨u, rfl⟩ := hc
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 24).mp
  push_cast
  generalize (u : ZMod 24) = U
  revert U
  decide

end Int
