/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Integer powers of `i` equal to `±i`

Since `i` has multiplicative order four, `i ^ m` depends only on `m % 4`
(`Complex.I_zpow_eq_zpow_mod`). This file records when an integer power of `i` is `i` or `-i`.

## Main results

* `TauCeti.Complex.I_zpow_eq_I_iff`: `i ^ m = i` exactly when `m % 4 = 1`.
* `TauCeti.Complex.I_zpow_eq_neg_I_iff`: `i ^ m = -i` exactly when `m % 4 = 3`.
-/

public section

namespace TauCeti.Complex

open _root_.Complex

/-- An integer power `i ^ m` equals `i` exactly when `m ≡ 1 (mod 4)`. -/
theorem I_zpow_eq_I_iff (m : ℤ) : I ^ m = I ↔ m % 4 = 1 := by
  rw [I_zpow_eq_zpow_mod]
  have h0 : 0 ≤ m % 4 := Int.emod_nonneg m (by norm_num)
  have h4 : m % 4 < 4 := Int.emod_lt_of_pos m (by norm_num)
  generalize m % 4 = k at h0 h4 ⊢
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  all_goals norm_num [Complex.ext_iff]

/-- An integer power `i ^ m` equals `-i` exactly when `m ≡ 3 (mod 4)`. -/
theorem I_zpow_eq_neg_I_iff (m : ℤ) : I ^ m = -I ↔ m % 4 = 3 := by
  rw [I_zpow_eq_zpow_mod]
  have h0 : 0 ≤ m % 4 := Int.emod_nonneg m (by norm_num)
  have h4 : m % 4 < 4 := Int.emod_lt_of_pos m (by norm_num)
  generalize m % 4 = k at h0 h4 ⊢
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  all_goals norm_num [Complex.ext_iff]

end TauCeti.Complex
