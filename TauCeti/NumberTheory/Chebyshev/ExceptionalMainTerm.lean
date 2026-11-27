/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Integrals.InvLog

/-!
# Lower bounds for prime-counting main terms with an exceptional zero

An exceptional zero at `β` can reduce the main term for primes in an arithmetic progression.
These estimates quantify how much of the main term remains, even when `β` is very close to `1`.
The retained factor is proportional to `min 1 ((1 - β) * log x)`, both for the Chebyshev main term
and for the logarithmic-integral main term. There is no dependence on the modulus before division
by its totient.

For the role of this depletion factor in relative prime-counting errors, see P. X. Gallagher,
*A large sieve density estimate near σ = 1*, Invent. Math. 11 (1970), 329–339, after (29).
-/

public section

namespace TauCeti

open _root_.Real Set

/-- Attenuating `x` by `exp (-((1 - β) * log x))` gives the real power `x ^ β`. -/
private theorem mul_exp_neg_sub_mul_log_eq_rpow {x : ℝ} (hx : 0 < x) (β : ℝ) :
    x * exp (-((1 - β) * log x)) = x ^ β := by
  rw [rpow_def_of_pos hx]
  nth_rw 1 [← exp_log hx]
  rw [← exp_add]
  ring_nf

/-- The Chebyshev main term with exceptional coefficient `a ≤ 1` is bounded below by
`x / 4` times `min 1 ((1 - β) * log x)`, provided `x ≥ exp (2 / β)`. In particular,
`log x ≥ 4` suffices for `β ≥ 1/2`. -/
theorem mul_min_one_le_sub_mul_rpow_div {x β a : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (hx : exp (2 / β) ≤ x) (ha : a ≤ 1) :
    x * (min 1 ((1 - β) * log x) / 4) ≤ x - a * (x ^ β / β) := by
  have hx₀ := (exp_pos _).trans_le hx
  have hlog := (le_log_iff_exp_le hx₀).mpr hx
  have hscale := (div_le_iff₀ hβ₀).mp hlog
  let u := (1 - β) * log x
  have hu : 0 ≤ u := mul_nonneg (sub_nonneg.mpr hβ₁) ((by positivity : 0 ≤ 2 / β).trans hlog)
  -- The denominator `β` costs at most half the exponential decay at this cutoff.
  have hlogβ : -log β ≤ u / 2 := by
    have h := log_le_sub_one_of_pos (inv_pos.mpr hβ₀)
    rw [log_inv, inv_eq_one_div, div_sub_one hβ₀.ne'] at h
    exact h.trans ((div_le_iff₀ hβ₀).mpr (by
      dsimp [u]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hβ₁) (sub_nonneg.mpr hscale)]))
  have hrpow : x ^ β / β = x * exp (-u - log β) := by
    dsimp only [u]
    rw [exp_sub, exp_log hβ₀, ← mul_div_assoc, mul_exp_neg_sub_mul_log_eq_rpow hx₀]
  have hdecay : a * (x ^ β / β) ≤ x * exp (-(u / 2)) := by
    calc
      _ ≤ x ^ β / β := mul_le_of_le_one_left (by positivity) ha
      _ = x * exp (-u - log β) := hrpow
      _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hx₀.le
  have hmin : min 1 u / 2 ≤ min 1 (u / 2) := by
    rw [le_min_iff]
    exact ⟨by linarith [min_le_left (1 : ℝ) u], by linarith [min_le_right (1 : ℝ) u]⟩
  have hgap : min 1 u / 4 ≤ 1 - exp (-(u / 2)) := by
    calc
      _ ≤ min 1 (u / 2) / 2 := by linarith
      _ ≤ _ := min_one_div_two_le_one_sub_exp_neg (by positivity)
  calc
    _ ≤ x * (1 - exp (-(u / 2))) := mul_le_mul_of_nonneg_left hgap hx₀.le
    _ ≤ _ := by linarith only [hdecay, mul_sub x 1 (exp (-(u / 2))), mul_one x]

namespace Real

/-- The logarithmic-integral main term with exceptional coefficient `a ≤ 1` is bounded below by
`x / (2 log x)` times `min 1 ((1 - β) * log x)` as soon as `x^β ≥ 2` and `x > 1`. -/
theorem mul_min_one_le_logIntegral_sub_mul_logIntegral_rpow {x β a : ℝ} (hx : 1 < x)
    (hβ : β ≤ 1) (h₂ : 2 ≤ x ^ β) (ha : a ≤ 1) :
    x * (min 1 ((1 - β) * log x) / 2) / log x ≤ logIntegral x - a * logIntegral (x ^ β) := by
  have hx₀ := zero_lt_one.trans hx
  have hle : x ^ β ≤ x := by simpa using rpow_le_rpow_of_exponent_le hx.le hβ
  have hβx : 1 < x ^ β := one_lt_two.trans_le h₂
  have hsplit : (∫ t in x ^ β..x, (log t)⁻¹) = logIntegral x - logIntegral (x ^ β) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · exact fun t ht ↦ hasDerivAt_logIntegral ((ordConnected_Ioi.uIcc_subset hβx hx) ht)
    · simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 hβx hx
  have hlog := log_pos hx
  have hgap := min_one_div_two_le_one_sub_exp_neg
    (mul_nonneg (sub_nonneg.mpr hβ) hlog.le)
  calc
    _ ≤ x * (1 - exp (-((1 - β) * log x))) / log x := by gcongr
    _ = (x - x ^ β) / log x := by rw [mul_sub, mul_one, mul_exp_neg_sub_mul_log_eq_rpow hx₀]
    _ ≤ logIntegral x - logIntegral (x ^ β) := by
      rw [← hsplit]
      simpa only [pow_one] using le_integral_inv_log_pow 1 hβx hle
    _ ≤ _ := sub_le_sub_left (mul_le_of_le_one_left (logIntegral_nonneg h₂) ha) _

end Real
end TauCeti
