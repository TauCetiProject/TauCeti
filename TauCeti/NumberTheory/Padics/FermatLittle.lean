/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Fermat's little theorem in `ℤ_p`

Every `p`-adic integer `x` satisfies `x ^ p ≡ x` modulo `p`, because its reduction lies in the
residue field `𝔽_p`, where Fermat's little theorem `ZMod.pow_card` holds. Equivalently,
`‖x ^ p - x‖ ≤ p⁻¹` for every `x` in the closed unit disc of `ℚ_p`.

The case `p = 2` is `PadicInt.two_dvd_sq_sub_self`, proved without the finite-field import closure.

## Main results

* `PadicInt.dvd_pow_sub_self`: `p` divides `x ^ p - x` in `ℤ_p`.
* `PadicInt.norm_pow_sub_self_le`: so `‖x ^ p - x‖ ≤ p⁻¹` in `ℤ_p`.
* `Padic.norm_pow_sub_self_le`: the same bound for `x ∈ ℚ_p` with `‖x‖ ≤ 1`.
-/

public section

variable {p : ℕ} [Fact p.Prime]

namespace PadicInt

/-- **Fermat's little theorem in `ℤ_p`**: `p` divides `x ^ p - x`, since the reduction of `x`
modulo `p` lies in `𝔽_p`. -/
theorem dvd_pow_sub_self (x : ℤ_[p]) : (p : ℤ_[p]) ∣ x ^ p - x := by
  rw [← toZMod_eq_zero_iff_dvd, map_sub, map_pow, ZMod.pow_card, sub_self]

/-- Every `p`-adic integer `x` satisfies `‖x ^ p - x‖ ≤ p⁻¹`. -/
theorem norm_pow_sub_self_le (x : ℤ_[p]) : ‖x ^ p - x‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨y, hy⟩ := dvd_pow_sub_self x
  rw [hy, norm_mul, norm_p]
  exact mul_le_of_le_one_right (by positivity) (norm_le_one y)

end PadicInt

namespace Padic

/-- Every `x` in the closed unit disc of `ℚ_p` satisfies `‖x ^ p - x‖ ≤ p⁻¹`. -/
theorem norm_pow_sub_self_le {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) : ‖x ^ p - x‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨y, rfl⟩ : ∃ y : ℤ_[p], (y : ℚ_[p]) = x := ⟨lift x hx, PadicInt.coe_lift hx⟩
  rw [← PadicInt.coe_pow, ← PadicInt.coe_sub, ← PadicInt.norm_def]
  exact PadicInt.norm_pow_sub_self_le y

end Padic
