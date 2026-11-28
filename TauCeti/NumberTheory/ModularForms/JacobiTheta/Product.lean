/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.SpecialFunctions.JacobiTripleProduct

/-!
# Infinite-product formula and nonvanishing for `jacobiTheta`

Using the triple-product specialization `TauCeti.tsum_pow_sq`, this file expresses Mathlib's
`jacobiTheta` on the upper half-plane as a convergent nonvanishing infinite product and deduces
that `jacobiTheta` never vanishes on the upper half-plane.

## Main results

* `TauCeti.jacobiTheta_eq_tprod`: on `0 < τ.im`,
  `jacobiTheta τ = (∏' n, (1 + e^{π i (2n+1) τ})) ^ 2 * ∏' n, (1 - e^{2π i (n+1) τ})`.
* `TauCeti.jacobiTheta_ne_zero`, `TauCeti.jacobiTheta_natCast_mul_ne_zero`: `jacobiTheta τ ≠ 0`
  whenever `0 < τ.im`, and `jacobiTheta (m * (z : ℂ)) ≠ 0` for `m ≠ 0` and `z : ℍ`.
-/

public section

open Complex
open scoped Real UpperHalfPlane

namespace TauCeti

/-- **Infinite-product formula for `jacobiTheta`**: for `0 < τ.im`,
`jacobiTheta τ = (∏_{n ≥ 0} (1 + e^{π i (2n+1) τ}))² ∏_{n ≥ 1} (1 - e^{2π i n τ})`. -/
theorem jacobiTheta_eq_tprod {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ = (∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1))) ^ 2 *
      ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1)) := by
  have hs := UpperHalfPlane.norm_exp_pi_I_lt_one hτ
  have hθ : jacobiTheta τ = ∑' k : ℤ, cexp (π * I * τ) ^ (k ^ 2) := by
    rw [jacobiTheta]
    refine tsum_congr fun k ↦ ?_
    rw [← Complex.exp_intCast_mul]
    congr 1
    push_cast
    ring
  rw [hθ, tsum_pow_sq hs, ← UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq]

/-- **`jacobiTheta` never vanishes on the upper half-plane**. -/
theorem jacobiTheta_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiTheta τ ≠ 0 := by
  rw [jacobiTheta_eq_tprod hτ]
  have h1 : ∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1)) ≠ 0 := by
    have h := tprod_one_sub_pow_odd_ne_zero (q := -cexp (π * I * τ))
      (by simpa [norm_neg] using UpperHalfPlane.norm_exp_pi_I_lt_one hτ)
    rwa [tprod_congr (one_sub_neg_pow_odd (cexp (π * I * τ)))] at h
  have h2 : ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1)) ≠ 0 :=
    tprod_one_sub_pow_ne_zero (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩)
  exact mul_ne_zero (pow_ne_zero 2 h1) h2

/-- `jacobiTheta (m * (z : ℂ))` never vanishes on the upper half-plane for `m ≠ 0`. -/
theorem jacobiTheta_natCast_mul_ne_zero (m : ℕ) [NeZero m] (z : ℍ) :
    jacobiTheta (m * (z : ℂ)) ≠ 0 :=
  jacobiTheta_ne_zero (by simpa using mul_pos (Nat.cast_pos.mpr (NeZero.pos m)) z.im_pos)

end TauCeti
