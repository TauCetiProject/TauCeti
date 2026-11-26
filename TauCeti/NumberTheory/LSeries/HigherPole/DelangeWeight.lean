/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic

/-!
# Delange's polynomial weight

For `k : ℕ` and real `t`, Delange's regularising weight is

`w_k(t) = t * ∫ u in 0..1, exp (-u * t) * u ^ k / k!`.

In Delange's Tauberian theorem for a pole of order `k + 1`, a nondecreasing function `α` with
`α(t) ~ C exp (a t) t ^ k` is studied through `w_k(t) exp (-a t) α(t)`, which then tends to `C`.
The weight is chosen so that this works: after the substitution `x = u t`,

`w_k(t) * t ^ k = ∫ x in 0..t, x ^ k * exp (-x) / k!`,

which is the regularised lower incomplete Gamma function `P(k + 1, t)` for `t ≥ 0`. Hence
`w_k(t) * t ^ k` increases from `0` to `1`, so `w_k(t) ~ t ^ (-k)` as `t → ∞`, while `w_k` stays
smooth at the origin, where `t ^ (-k)` blows up when `k > 0`. On the Laplace side,
multiplying a function with transform `F(s)` by the weight replaces `F(s)` by
`-∫ u in 0..1, F'(s + u) * u ^ k / k!`, which turns a pole of order `k + 1` on the boundary line
into a locally integrable singularity.

## Main definitions

* `TauCeti.HigherPoleTauberian.delangeWeight k t`: the weight `w_k(t)`, total in `t`.

## Main results

* `delangeWeight_mul_pow`: `w_k(t) t ^ k = 1 - exp (-t) * ∑ j < k + 1, t ^ j / j!` for every
  real `t`; `delangeWeight_zero_left` is the case `w_0(t) = 1 - exp (-t)`.
* `delangeWeight_mul_pow_eq_regularizedGamma`: `w_k(t) t ^ k = P(k + 1, t)` for `t ≥ 0`.
* `delangeWeight_pos_iff`, `delangeWeight_nonneg`, `delangeWeight_mul_pow_lt_one`: the weight has
  the sign of `t`, and `w_k(t) t ^ k < 1` for `t ≥ 0`.
* `tendsto_delangeWeight_mul_pow_atTop`: the normalisation `w_k(t) t ^ k → 1` as `t → ∞`.
* `tendstoUniformlyOn_delangeWeight_add_div`: `w_k(t + h) / w_k(t) → 1` as `t → ∞`, uniformly
  for `h` in a bounded interval; `tendsto_delangeWeight_add_div_atTop` is the pointwise form.
* `hasDerivAt_delangeWeight`, `hasDerivAt_delangeWeight_of_ne_zero`,
  `deriv_delangeWeight_zero`, `contDiff_delangeWeight`: `w_k` is smooth on `ℝ`, with
  `w_k'(t) = exp (-t) / k! - k w_k(t) / t` for `t ≠ 0` and `w_k'(0) = 1 / (k! (k + 1))`.
* `tendsto_deriv_delangeWeight_div_atTop`: the logarithmic derivative `w_k' / w_k` tends to `0`.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) 71 (1954),
  213–242: §3.1–3.2 (the function `v`, its positivity and `v(t + h)/v(t) → 1`), and §5.2.1, p. 237
  (the choice `γ(u) = u ^ (ω - 1)` for an exponent `ω ≥ 1`). For `ω = k + 1` and the cutoff `1`,
  `t v(t)` is `w_k(t)`.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Nat Topology

namespace TauCeti.HigherPoleTauberian

/-- Delange's regularising weight `w_k(t) = t * ∫ u in 0..1, exp (-u * t) * u ^ k / k!`.

It vanishes at `0`, has the sign of `t`, and `w_k(t) * t ^ k` is the regularised lower incomplete
Gamma function `P(k + 1, t)` for `t ≥ 0`, so that `w_k(t) ~ t ^ (-k)` as `t → ∞`. The definition
is total in `t`. -/
def delangeWeight (k : ℕ) (t : ℝ) : ℝ :=
  t * ∫ u in (0 : ℝ)..1, Real.exp (-u * t) * u ^ k / (k ! : ℝ)

variable {k : ℕ} {t : ℝ}

/-- Unfolding lemma for `delangeWeight`. -/
theorem delangeWeight_def (k : ℕ) (t : ℝ) :
    delangeWeight k t = t * ∫ u in (0 : ℝ)..1, Real.exp (-u * t) * u ^ k / (k ! : ℝ) := (rfl)

/-- The weight vanishes at the origin: `w_k(0) = 0`. -/
@[simp]
theorem delangeWeight_zero_right (k : ℕ) : delangeWeight k 0 = 0 := by
  simp [delangeWeight_def]

/-- The integral factor `∫ u in 0..1, exp (-u * t) * u ^ k / k!` of the weight is smooth in
`t`. -/
private theorem contDiff_integral_delangeWeight (k : ℕ) :
    ContDiff ℝ ∞ fun t : ℝ ↦ ∫ u in (0 : ℝ)..1, Real.exp (-u * t) * u ^ k / (k ! : ℝ) :=
  ContDiff.parametric_intervalIntegral
    (f := fun p : ℝ × ℝ ↦ Real.exp (-p.2 * p.1) * p.2 ^ k / (k ! : ℝ)) (by fun_prop)

/-- The integral factor of the weight is positive at every real `t`. -/
private theorem integral_delangeWeight_pos (k : ℕ) (t : ℝ) :
    0 < ∫ u in (0 : ℝ)..1, Real.exp (-u * t) * u ^ k / (k ! : ℝ) :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun u : ℝ ↦ Real.exp (-u * t) * u ^ k / (k ! : ℝ)).intervalIntegrable
      _ _)
    (fun u hu ↦ by have := hu.1; positivity) zero_lt_one

/-- The integral factor of the weight at `t = 0` is `∫ u in 0..1, u ^ k / k! = 1 / (k! (k + 1))`. -/
private theorem integral_delangeWeight_zero (k : ℕ) :
    ∫ u in (0 : ℝ)..1, Real.exp (-u * 0) * u ^ k / (k ! : ℝ) = 1 / ((k ! : ℝ) * (k + 1)) := by
  simp [integral_pow]
  field_simp

/-- After the substitution `x = u t`, the normalised weight `w_k(t) t ^ k` is the truncated Euler
integral `∫ x in 0..t, x ^ k * exp (-x) / k!`, for every real `t`. -/
theorem delangeWeight_mul_pow_eq_integral (k : ℕ) (t : ℝ) :
    delangeWeight k t * t ^ k = ∫ x in (0 : ℝ)..t, x ^ k * Real.exp (-x) / (k ! : ℝ) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hint : ∀ u : ℝ, Real.exp (-u * t) * u ^ k / (k ! : ℝ) =
      (t ^ k)⁻¹ * ((u * t) ^ k * Real.exp (-(u * t)) / (k ! : ℝ)) := fun u ↦ by
    rw [mul_pow, neg_mul]
    field_simp
  simp_rw [delangeWeight_def, hint, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_right
      (fun x : ℝ ↦ x ^ k * Real.exp (-x) / (k ! : ℝ)) ht, zero_mul, one_mul, smul_eq_mul]
  field_simp

/-- **The closed form of the weight.** For every real `t`,
`w_k(t) t ^ k = 1 - exp (-t) * ∑ j < k + 1, t ^ j / j!`. -/
theorem delangeWeight_mul_pow (k : ℕ) (t : ℝ) :
    delangeWeight k t * t ^ k =
      1 - Real.exp (-t) * ∑ j ∈ Finset.range (k + 1), t ^ j / (j ! : ℝ) := by
  rw [delangeWeight_mul_pow_eq_integral, intervalIntegral.integral_div, integral_pow_mul_exp_neg]
  field_simp

/-- The weight of order `0` is `w_0(t) = 1 - exp (-t)`, for every real `t`. -/
@[simp]
theorem delangeWeight_zero_left (t : ℝ) : delangeWeight 0 t = 1 - Real.exp (-t) := by
  simpa using delangeWeight_mul_pow 0 t

/-- For `t ≥ 0`, the normalised weight `w_k(t) t ^ k` is the regularised lower incomplete Gamma
function `P(k + 1, t)`. -/
theorem delangeWeight_mul_pow_eq_regularizedGamma (k : ℕ) (ht : 0 ≤ t) :
    delangeWeight k t * t ^ k = regularizedGamma (k + 1) t := by
  rw [delangeWeight_mul_pow, ← Nat.cast_succ, regularizedGamma_natCast k.succ_ne_zero ht]

/-- For `t ≥ 0`, `w_k(t) = P(k + 1, t) / t ^ k`. -/
theorem delangeWeight_eq_regularizedGamma_div (k : ℕ) (ht : 0 ≤ t) :
    delangeWeight k t = regularizedGamma (k + 1) t / t ^ k := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rw [← delangeWeight_mul_pow_eq_regularizedGamma k ht.le, mul_div_cancel_right₀ _ (by positivity)]

/-- The weight is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_delangeWeight (k : ℕ) : Continuous (delangeWeight k) := by
  simp_rw [funext (delangeWeight_def k)]
  exact continuous_id.mul (contDiff_integral_delangeWeight k).continuous

/-! ### Sign and size -/

/-- The weight has the sign of its argument: `0 < w_k(t)` exactly when `0 < t`. -/
theorem delangeWeight_pos_iff : 0 < delangeWeight k t ↔ 0 < t := by
  rw [delangeWeight_def, mul_pos_iff_of_pos_right (integral_delangeWeight_pos k t)]

/-- The weight is positive at positive time. -/
theorem delangeWeight_pos (ht : 0 < t) : 0 < delangeWeight k t :=
  delangeWeight_pos_iff.2 ht

/-- The weight is nonnegative at nonnegative time. -/
theorem delangeWeight_nonneg (ht : 0 ≤ t) : 0 ≤ delangeWeight k t := by
  rw [delangeWeight_def]
  exact mul_nonneg ht (integral_delangeWeight_pos k t).le

/-- The normalised weight is bounded: `w_k(t) t ^ k < 1` for `t ≥ 0`. -/
theorem delangeWeight_mul_pow_lt_one (ht : 0 ≤ t) : delangeWeight k t * t ^ k < 1 := by
  rw [delangeWeight_mul_pow_eq_regularizedGamma k ht]
  exact regularizedGamma_lt_one _ _

/-! ### Behaviour at infinity -/

/-- **Normalisation of the weight.** `w_k(t) t ^ k → 1` as `t → ∞`, so `w_k(t) ~ t ^ (-k)`. -/
theorem tendsto_delangeWeight_mul_pow_atTop (k : ℕ) :
    Tendsto (fun t : ℝ ↦ delangeWeight k t * t ^ k) atTop (𝓝 1) := by
  refine (tendsto_regularizedGamma_atTop (s := (k : ℝ) + 1) (by positivity)).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [delangeWeight_mul_pow_eq_regularizedGamma k ht]

/-- For positive `s` and `t`, `w_k(s) / w_k(t) = P(k + 1, s) / P(k + 1, t) * (t / s) ^ k`. -/
private theorem delangeWeight_div_delangeWeight {s : ℝ} (hs : 0 < s) (ht : 0 < t) :
    delangeWeight k s / delangeWeight k t =
      regularizedGamma (k + 1) s / regularizedGamma (k + 1) t * (t / s) ^ k := by
  have hPt : 0 < regularizedGamma (k + 1) t := regularizedGamma_pos (by positivity) ht
  rw [delangeWeight_eq_regularizedGamma_div k hs.le, delangeWeight_eq_regularizedGamma_div k ht.le,
    div_pow]
  field_simp

/-- The squeeze behind the uniform slow variation: for `H < t` and `h ∈ [-H, H]`, with
`P = P(k + 1, ·)`, the ratio `w_k(t + h) / w_k(t)` lies between `P(t - H) (1 - H / t) ^ k` and
`(1 + H / (t - H)) ^ k / P(t - H)`. -/
private theorem delangeWeight_add_div_mem_Icc {H h : ℝ} (htH : H < t) (hh : h ∈ Icc (-H) H) :
    delangeWeight k (t + h) / delangeWeight k t ∈
      Icc (regularizedGamma (k + 1) (t - H) * (1 - H / t) ^ k)
        ((1 + H / (t - H)) ^ k / regularizedGamma (k + 1) (t - H)) := by
  obtain ⟨hh₁, hh₂⟩ := hh
  have hk : (0 : ℝ) < k + 1 := by positivity
  have ht : 0 < t := by linarith
  have htH' : 0 < t - H := by linarith
  have hth : 0 < t + h := by linarith
  have hPt : 0 < regularizedGamma (k + 1) t := regularizedGamma_pos hk ht
  have hPH : 0 < regularizedGamma (k + 1) (t - H) := regularizedGamma_pos hk htH'
  have hPmono : regularizedGamma (k + 1) (t - H) ≤ regularizedGamma (k + 1) t :=
    regularizedGamma_monotone _ (by linarith)
  have hPh : regularizedGamma (k + 1) (t - H) ≤ regularizedGamma (k + 1) (t + h) :=
    regularizedGamma_monotone _ (by linarith)
  have hfrac_nonneg : 0 ≤ 1 - H / t := by
    rw [sub_nonneg, div_le_one ht]
    exact htH.le
  have hfrac_low : 1 - H / t ≤ t / (t + h) := by
    rw [one_sub_div ht.ne', div_le_div_iff₀ ht hth]
    nlinarith
  have hfrac_up : t / (t + h) ≤ 1 + H / (t - H) := by
    rw [one_add_div htH'.ne', sub_add_cancel]
    exact div_le_div_of_nonneg_left ht.le htH' (by linarith)
  rw [delangeWeight_div_delangeWeight hth ht]
  refine ⟨mul_le_mul (hPh.trans (le_div_self (hPH.le.trans hPh) hPt
    (regularizedGamma_le_one _ _))) (pow_le_pow_left₀ hfrac_nonneg hfrac_low k)
    (pow_nonneg hfrac_nonneg k) (div_nonneg (regularizedGamma_nonneg _ _) hPt.le), ?_⟩
  calc regularizedGamma (k + 1) (t + h) / regularizedGamma (k + 1) t * (t / (t + h)) ^ k
      ≤ 1 / regularizedGamma (k + 1) (t - H) * (1 + H / (t - H)) ^ k :=
        mul_le_mul (div_le_div₀ zero_le_one (regularizedGamma_le_one _ _) hPH hPmono)
          (pow_le_pow_left₀ (div_nonneg ht.le hth.le) hfrac_up k)
          (pow_nonneg (div_nonneg ht.le hth.le) k) (one_div_nonneg.2 hPH.le)
    _ = (1 + H / (t - H)) ^ k / regularizedGamma (k + 1) (t - H) := by ring

/-- **Uniform slow variation of the weight.** For every `H`, `w_k(t + h) / w_k(t) → 1` as
`t → ∞`, uniformly in `h ∈ [-H, H]`. -/
theorem tendstoUniformlyOn_delangeWeight_add_div (k : ℕ) (H : ℝ) :
    TendstoUniformlyOn (fun t h ↦ delangeWeight k (t + h) / delangeWeight k t) (fun _ ↦ 1) atTop
      (Icc (-H) H) := by
  have hsub : Tendsto (fun t : ℝ ↦ t - H) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hP : Tendsto (fun t ↦ regularizedGamma (k + 1) (t - H)) atTop (𝓝 1) :=
    (tendsto_regularizedGamma_atTop (by positivity)).comp hsub
  -- Both bounds of `delangeWeight_add_div_mem_Icc` tend to `1`.
  have hlow : Tendsto (fun t ↦ regularizedGamma (k + 1) (t - H) * (1 - H / t) ^ k) atTop
      (𝓝 1) := by
    have h := hP.mul (((tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := H)).div_atTop tendsto_id)).pow k)
    rw [sub_zero, one_pow, one_mul] at h
    exact h
  have hup : Tendsto (fun t ↦ (1 + H / (t - H)) ^ k / regularizedGamma (k + 1) (t - H)) atTop
      (𝓝 1) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := H)).div_atTop hsub)).pow k).div hP one_ne_zero
    rw [add_zero, one_pow, div_one] at h
    exact h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hlow.eventually (lt_mem_nhds (sub_lt_self 1 hε)),
    hup.eventually (gt_mem_nhds (lt_add_of_pos_right 1 hε)), eventually_gt_atTop H]
    with t hlt hut htH h hh
  have hmem := delangeWeight_add_div_mem_Icc (k := k) htH hh
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hmem.1, hmem.2]

/-- **Slow variation of the weight.** For each fixed real `h`, `w_k(t + h) / w_k(t) → 1` as
`t → ∞`. -/
theorem tendsto_delangeWeight_add_div_atTop (k : ℕ) (h : ℝ) :
    Tendsto (fun t ↦ delangeWeight k (t + h) / delangeWeight k t) atTop (𝓝 1) :=
  (tendstoUniformlyOn_delangeWeight_add_div k |h|).tendsto_at
    ⟨neg_abs_le h, le_abs_self h⟩

/-! ### Differentiability -/

/-- Away from the origin, `w_k(t) = t ^ (-k) ∫ x in 0..t, x ^ k * exp (-x) / k!` has derivative
`exp (-t) / k! - k w_k(t) / t`. -/
theorem hasDerivAt_delangeWeight_of_ne_zero (k : ℕ) (ht : t ≠ 0) :
    HasDerivAt (delangeWeight k) (Real.exp (-t) / (k ! : ℝ) - k * delangeWeight k t / t) t := by
  have hg : Continuous fun x : ℝ ↦ x ^ k * Real.exp (-x) / (k ! : ℝ) := by fun_prop
  have hN := (hg.integral_hasStrictDerivAt 0 t).hasDerivAt.mul
    (hasDerivAt_zpow (-(k : ℤ)) t (Or.inl ht))
  have heq : ∀ x : ℝ, x ≠ 0 → delangeWeight k x =
      (∫ y in (0 : ℝ)..x, y ^ k * Real.exp (-y) / (k ! : ℝ)) * x ^ (-(k : ℤ)) := fun x hx ↦ by
    rw [← delangeWeight_mul_pow_eq_integral, zpow_neg, zpow_natCast,
      mul_inv_cancel_right₀ (pow_ne_zero k hx)]
  refine (hN.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [eventually_ne_nhds ht] with x hx using heq x hx
  · rw [heq t ht, zpow_sub_one₀ ht, zpow_neg, zpow_natCast]
    push_cast
    field_simp
    ring

/-- The weight is differentiable on all of `ℝ`, with derivative
`exp (-t) / k! - k ∫ u in 0..1, exp (-u * t) * u ^ k / k!`. For `t ≠ 0` the integral is
`w_k(t) / t`, as in `hasDerivAt_delangeWeight_of_ne_zero`. -/
theorem hasDerivAt_delangeWeight (k : ℕ) (t : ℝ) :
    HasDerivAt (delangeWeight k) (Real.exp (-t) / (k ! : ℝ) -
      k * ∫ u in (0 : ℝ)..1, Real.exp (-u * t) * u ^ k / (k ! : ℝ)) t := by
  rcases eq_or_ne t 0 with rfl | ht
  · -- At the origin, the slope `w_k(s) / s` is the continuous integral factor.
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hlim := (contDiff_integral_delangeWeight k).continuous.continuousAt (x := 0) |>.tendsto
      |>.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    convert hlim.congr' ?_ using 2
    · rw [integral_delangeWeight_zero, neg_zero, Real.exp_zero]
      field_simp
      ring
    · filter_upwards [self_mem_nhdsWithin] with s hs
      rw [zero_add, delangeWeight_zero_right, sub_zero, delangeWeight_def, smul_eq_mul,
        inv_mul_cancel_left₀ hs]
  · convert hasDerivAt_delangeWeight_of_ne_zero k ht using 3
    rw [delangeWeight_def, mul_div_assoc, mul_div_cancel_left₀ _ ht]

/-- The derivative of the weight at the origin is `w_k'(0) = 1 / (k! (k + 1))`. -/
theorem deriv_delangeWeight_zero (k : ℕ) :
    deriv (delangeWeight k) 0 = 1 / ((k ! : ℝ) * (k + 1)) := by
  rw [(hasDerivAt_delangeWeight k 0).deriv, integral_delangeWeight_zero, neg_zero,
    Real.exp_zero]
  field_simp
  ring

/-- The weight is smooth on `ℝ`. -/
theorem contDiff_delangeWeight (k : ℕ) : ContDiff ℝ ∞ (delangeWeight k) := by
  rw [funext (delangeWeight_def k)]
  exact contDiff_id.mul (contDiff_integral_delangeWeight k)

/-- The logarithmic derivative of the weight tends to `0`: `w_k'(t) / w_k(t) → 0` as `t → ∞`. -/
theorem tendsto_deriv_delangeWeight_div_atTop (k : ℕ) :
    Tendsto (fun t ↦ deriv (delangeWeight k) t / delangeWeight k t) atTop (𝓝 0) := by
  -- For `t > 0` the ratio is `t ^ k exp (-t) / (k! P(k + 1, t)) - k / t`.
  have h₁ : Tendsto (fun t : ℝ ↦ t ^ k * Real.exp (-t) / (k ! : ℝ) /
      regularizedGamma (k + 1) t) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).div_const (k ! : ℝ)).div
      (tendsto_regularizedGamma_atTop (s := k + 1) (by positivity)) one_ne_zero
    rw [zero_div, zero_div] at h
    exact h
  have h₂ : Tendsto (fun t : ℝ ↦ (k : ℝ) / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := h₁.sub h₂
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hP : 0 < regularizedGamma (k + 1) t := regularizedGamma_pos (by positivity) ht
  rw [(hasDerivAt_delangeWeight_of_ne_zero k ht.ne').deriv,
    delangeWeight_eq_regularizedGamma_div k ht.le]
  field_simp

end TauCeti.HigherPoleTauberian
