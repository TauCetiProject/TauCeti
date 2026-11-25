/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# The size of the Gauss hypergeometric coefficients

The coefficients `cₛ = (a)ₛ (b)ₛ / ((c)ₛ s!)` of the Gauss series `₂F₁(a, b; c; ·)` grow like a
power of `s`. By Euler's limit formula for the Gamma function in Pochhammer form, the normalized
coefficients `cₛ / s^(a + b − c − 1)` tend to `Γ(c) / (Γ(a) Γ(b))` for all complex parameters, with
Mathlib's junk values `Γ(−k) = 0` and `x / 0 = 0` covering the terminating and undefined cases.
When none of `a`, `b`, `c` is a nonpositive integer this limit is nonzero, and the coefficients are
asymptotically equivalent to `Γ(c) / (Γ(a) Γ(b)) s^(a + b − c − 1)`.

## Main results

* `Complex.tendsto_ordinaryHypergeometricCoefficient_div_natCast_cpow`: the normalized coefficient
  limit `cₛ / s^(a + b − c − 1) → Γ(c) / (Γ(a) Γ(b))`, for all complex parameters.
* `Complex.isBigO_ordinaryHypergeometricCoefficient`,
  `Complex.isTheta_ordinaryHypergeometricCoefficient`: `cₛ = O(s^(Re(a + b − c) − 1))` for all
  parameters, with equality of orders when no parameter is a nonpositive integer.
* `Complex.isBigO_ordinaryHypergeometricCoefficient_add_one_sub`:
  `cₛ₊₁ − cₛ = O(s^(Re(a + b − c) − 2))`, for all parameters.

## References

* NIST Digital Library of Mathematical Functions, §15.2(i), <https://dlmf.nist.gov/15.2.i>.
* G. E. Andrews, R. Askey and R. Roy, *Special Functions*, Theorem 2.1.2.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Hypergeometric/Basic/GaussSeries.lean`.
-/

public section

open Asymptotics Filter Polynomial
open scoped Nat Topology

namespace Complex

/-- **The coefficient asymptotic of the Gauss series.** For all complex `a`, `b`, `c`, the
coefficients `cₛ = (a)ₛ (b)ₛ / ((c)ₛ s!)` of `₂F₁(a, b; c; ·)` satisfy
`cₛ / s^(a + b − c − 1) → Γ(c) / (Γ(a) Γ(b))`. When a parameter is a nonpositive integer both
sides are eventually `0`. -/
theorem tendsto_ordinaryHypergeometricCoefficient_div_natCast_cpow (a b c : ℂ) :
    Tendsto (fun n : ℕ => ordinaryHypergeometricCoefficient a b c n / (n : ℂ) ^ (a + b - c - 1))
      atTop (𝓝 (Gamma c / (Gamma a * Gamma b))) := by
  have h := ((tendsto_ascPochhammer_eval_div_natCast_cpow_mul_factorial a).mul
    (tendsto_ascPochhammer_eval_div_natCast_cpow_mul_factorial b)).mul
    (tendsto_natCast_cpow_mul_factorial_div_ascPochhammer_eval c)
  -- Regroup the product of the three limits as the quotient `Γ(c) / (Γ(a) Γ(b))`.
  have hΓ : (Gamma a)⁻¹ * (Gamma b)⁻¹ * Gamma c = Gamma c / (Gamma a * Gamma b) := by
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [hΓ] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hexp : a + b - c - 1 = (a - 1) + (b - 1) - (c - 1) := by ring
  conv_rhs => rw [TauCeti.ordinaryHypergeometricCoefficient_eq_div, hexp, cpow_sub _ _ hn',
    cpow_add _ _ hn']
  have ha := cpow_ne_zero_iff.mpr (Or.inl hn' : (n : ℂ) ≠ 0 ∨ a - 1 = 0)
  have hb := cpow_ne_zero_iff.mpr (Or.inl hn' : (n : ℂ) ≠ 0 ∨ b - 1 = 0)
  have hc := cpow_ne_zero_iff.mpr (Or.inl hn' : (n : ℂ) ≠ 0 ∨ c - 1 = 0)
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  field_simp

/-- The coefficients of the Gauss series are `O(s^(Re(a + b − c) − 1))`, for all complex
parameters. -/
theorem isBigO_ordinaryHypergeometricCoefficient (a b c : ℂ) :
    ordinaryHypergeometricCoefficient a b c =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (a + b - c - 1).re := by
  have h := isBigO_of_div_tendsto_nhds ?_ _
    (tendsto_ordinaryHypergeometricCoefficient_div_natCast_cpow a b c)
  · simpa [Function.comp_def] using h.norm_right.trans_eventuallyEq
      ((norm_ofReal_cpow_eventually_eq_atTop _).comp_tendsto tendsto_natCast_atTop_atTop)
  · filter_upwards [eventually_ne_atTop 0] with n hn h0
    exact absurd h0 (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn)))

/-- When none of `a`, `b`, `c` is a nonpositive integer, the coefficients of the Gauss series are
of exact order `s^(Re(a + b − c) − 1)`. -/
theorem isTheta_ordinaryHypergeometricCoefficient {a b c : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k) :
    ordinaryHypergeometricCoefficient a b c =Θ[atTop]
      fun n : ℕ => (n : ℝ) ^ (a + b - c - 1).re := by
  have hL : Gamma c / (Gamma a * Gamma b) ≠ 0 :=
    div_ne_zero (Gamma_ne_zero hc) (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero hb))
  refine (isTheta_norm_right.mpr (isTheta_of_div_tendsto_nhds_ne_zero
    (tendsto_ordinaryHypergeometricCoefficient_div_natCast_cpow a b c) hL).symm).trans_eventuallyEq
      ?_
  have h := (norm_ofReal_cpow_eventually_eq_atTop (a + b - c - 1)).comp_tendsto
    tendsto_natCast_atTop_atTop
  simp only [Function.comp_def, ofReal_natCast] at h
  exact h

/-- The recurrence multiplier `r(s) = (a + s)(b + s) / ((s + 1)(c + s))` of the Gauss coefficients,
`cₛ₊₁ = r(s) cₛ` (`TauCeti.ordinaryHypergeometricCoefficient_add_one`), satisfies
`r(s) − 1 = O(1 / s)`, for all complex parameters. It is the ratio `cₛ₊₁ / cₛ` only where
`cₛ ≠ 0`; for a terminating series the coefficients vanish from some index on. -/
private theorem isBigO_coefficientRatio_sub_one (a b c : ℂ) :
    (fun n : ℕ => (a + n) * (b + n) / ((n + 1) * (c + n)) - 1) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (-1 : ℝ) := by
  -- `n (r(n) − 1) = (α + β / n) / ((1 + 1 / n) (1 + c / n))` tends to `α = a + b − c − 1`.
  have h0 (s : ℂ) : Tendsto (fun n : ℕ => s / (n : ℂ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat s
  have hlim : Tendsto (fun n : ℕ => (a + b - c - 1 + (a * b - c) / n) /
      ((1 + 1 / n) * (1 + c / n))) atTop (𝓝 (a + b - c - 1)) := by
    have h := ((tendsto_const_nhds (x := a + b - c - 1)).add (h0 (a * b - c))).div
      (((tendsto_const_nhds (x := (1 : ℂ))).add (h0 1)).mul
        ((tendsto_const_nhds (x := (1 : ℂ))).add (h0 c))) (by norm_num)
    rwa [add_zero, add_zero, mul_one, div_one] at h
  have hinv : (fun n : ℕ => ((n : ℂ))⁻¹) =O[atTop] fun n : ℕ => (n : ℝ) ^ (-1 : ℝ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [norm_inv, norm_natCast, Real.rpow_neg_one, Real.norm_of_nonneg (by positivity), one_mul]
  refine ((hlim.isBigO_one ℝ).mul hinv).congr' ?_ (Eventually.of_forall fun n => one_mul _)
  · filter_upwards [eventually_ne_atTop 0,
      tendsto_natCast_atTop_cobounded.eventually_ne_cobounded (-c)] with n hn hcn
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have hcn' : (n : ℂ) + c ≠ 0 := fun h => hcn (by linear_combination h)
    have hcn'' : c + n ≠ 0 := by rwa [add_comm]
    -- Clear the inner denominators `n` of `1 + 1 / n` and `1 + c / n`.
    have h1 : (1 : ℂ) + 1 / n = (n + 1) / n := by rw [add_div, div_self hn']
    have h2 : (1 : ℂ) + c / n = (n + c) / n := by rw [add_div, div_self hn']
    rw [h1, h2]
    field_simp
    ring

/-- The differences of consecutive coefficients of the Gauss series are
`O(s^(Re(a + b − c) − 2))`, for all complex parameters. -/
theorem isBigO_ordinaryHypergeometricCoefficient_add_one_sub (a b c : ℂ) :
    (fun n : ℕ => ordinaryHypergeometricCoefficient a b c (n + 1) -
      ordinaryHypergeometricCoefficient a b c n) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ ((a + b - c - 1).re - 1) := by
  refine ((isBigO_coefficientRatio_sub_one a b c).mul
    (isBigO_ordinaryHypergeometricCoefficient a b c)).congr' (Eventually.of_forall fun n => ?_) ?_
  · dsimp only
    rw [TauCeti.ordinaryHypergeometricCoefficient_add_one]
    ring
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← Real.rpow_add (Nat.cast_pos.mpr hn), neg_add_eq_sub]

end Complex
