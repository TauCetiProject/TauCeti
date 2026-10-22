/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Ostrowski
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Inverses of natural numbers in a normed field of characteristic zero

In a normed field `K` of characteristic zero the norm restricts to an absolute value on `ℚ`. By
Ostrowski's theorem it is trivial, a power of the real absolute value, or a power `|·|_p ^ s` of a
`p`-adic absolute value. In each case the inverse of a positive integer has at most polynomial
size: `‖n⁻¹‖ ≤ n ^ c` for a constant `c ≥ 0`. In the `p`-adic case `c = s` (`|n|_p ≥ 1 / n`), in
the other two cases `c = 0`.

Consequently `‖n⁻¹‖ qⁿ → 0` for every `0 ≤ q < 1`. This is the estimate that makes termwise
integration of power series lose only an arbitrarily small amount of convergence radius in
characteristic zero.

## Main results

* `NormedField.exists_norm_inv_natCast_le_rpow`: `‖(n : K)⁻¹‖ ≤ n ^ c` for some `c ≥ 0`.
* `NormedField.tendsto_norm_inv_natCast_mul_pow`: `‖(n : K)⁻¹‖ * q ^ n → 0` for `0 ≤ q < 1`.
-/

public section

namespace NormedField

open Filter Topology

variable (K : Type*) [NormedField K] [CharZero K]

/-- **Inverses of natural numbers have polynomial size.** In a normed field of characteristic
zero there is `c ≥ 0` with `‖(n : K)⁻¹‖ ≤ n ^ c` for every natural number `n`. -/
theorem exists_norm_inv_natCast_le_rpow :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, ‖(n : K)⁻¹‖ ≤ (n : ℝ) ^ c := by
  -- The norm of `K`, restricted to `ℚ`.
  let v : AbsoluteValue ℚ ℝ := (NormedField.toAbsoluteValue K).comp (Rat.castHom K).injective
  have hv (n : ℕ) : v n = ‖(n : K)‖ := by simp [v]
  -- It suffices to bound `‖(n : K)‖` from below by `n ^ (-c)` for positive `n`.
  suffices h : ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, 0 < n → (n : ℝ) ^ (-c) ≤ v n by
    obtain ⟨c, hc, h⟩ := h
    refine ⟨c, hc, fun n ↦ ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using Real.rpow_nonneg le_rfl c
    · have hn' := h n hn
      rw [hv, Real.rpow_neg (Nat.cast_nonneg n)] at hn'
      rw [norm_inv]
      exact inv_le_of_inv_le₀ (by positivity) hn'
  by_cases hnt : v.IsNontrivial
  · rcases Rat.AbsoluteValue.equiv_real_or_padic v hnt with hreal | ⟨p, ⟨hp, hpad⟩, -⟩
    · -- A power of the real absolute value: positive integers have norm at least `1`.
      obtain ⟨t, ht, heq⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 hreal
      refine ⟨0, le_rfl, fun n hn ↦ ?_⟩
      have h1 : v n ^ t = n := by
        simpa using congrFun heq n
      rw [neg_zero, Real.rpow_zero]
      by_contra! hlt
      have := Real.rpow_lt_one (v.nonneg _) hlt ht
      rw [h1] at this
      exact absurd this (not_lt.2 (by exact_mod_cast hn))
    · -- `v ^ t` is a `p`-adic absolute value, so `v = |·|_p ^ (1 / t)`: use `|n|_p ≥ 1 / n`.
      obtain ⟨t, ht, heq⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 hpad
      refine ⟨t⁻¹, inv_nonneg.2 ht.le, fun n hn ↦ ?_⟩
      have h1 : v n ^ t = padicNorm p n := by
        simpa using congrFun heq n
      have h2 : (n : ℝ)⁻¹ ≤ padicNorm p n := by
        have : NeZero n := ⟨hn.ne'⟩
        have hnorm : ‖(n : ℚ_[p])‖ = padicNorm p n := by simpa using Padic.eq_padicNorm (p := p) n
        exact hnorm ▸ Padic.inv_natCast_le_norm_natCast n
      calc (n : ℝ) ^ (-t⁻¹) = ((n : ℝ)⁻¹) ^ t⁻¹ := by
            rw [Real.rpow_neg (Nat.cast_nonneg n), Real.inv_rpow (Nat.cast_nonneg n)]
        _ ≤ (v n ^ t) ^ t⁻¹ := by
            rw [h1]
            exact Real.rpow_le_rpow (by positivity) h2
              (inv_nonneg.2 ht.le)
        _ = v n := Real.rpow_rpow_inv (v.nonneg _) ht.ne'
  · -- The trivial absolute value: nonzero integers have norm `1`.
    refine ⟨0, le_rfl, fun n hn ↦ ?_⟩
    rw [AbsoluteValue.not_isNontrivial_iff] at hnt
    rw [hnt n (by exact_mod_cast hn.ne'), neg_zero, Real.rpow_zero]

/-- In a normed field of characteristic zero, `‖(n : K)⁻¹‖ * q ^ n → 0` for every `0 ≤ q < 1`:
the inverses of the natural numbers grow more slowly than any exponential. -/
theorem tendsto_norm_inv_natCast_mul_pow {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Tendsto (fun n : ℕ ↦ ‖(n : K)⁻¹‖ * q ^ n) atTop (𝓝 0) := by
  obtain ⟨c, -, hc⟩ := exists_norm_inv_natCast_le_rpow K
  -- Bound `n ^ c` by the natural power `n ^ ⌈c⌉₊`, which `qⁿ` beats.
  have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ⌈c⌉₊ * q ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one _ (by rwa [abs_of_nonneg hq₀])
  refine squeeze_zero' (.of_forall fun n ↦ by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  gcongr
  calc ‖(n : K)⁻¹‖ ≤ (n : ℝ) ^ c := hc n
    _ ≤ (n : ℝ) ^ (⌈c⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
          (Nat.le_ceil c)
    _ = (n : ℝ) ^ ⌈c⌉₊ := Real.rpow_natCast _ _

end NormedField
