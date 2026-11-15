/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic

/-!
# Delange's polynomial weight

For `k : ℕ` and real `t` this file defines Delange's weight

`w_k(t) = delangeWeight k t = t * ∫ u in 0..1, exp (-u * t) * u ^ k / k!`.

After the substitution `x = u * t`, `w_k(t) * t ^ k = (1 / k!) ∫ x in 0..t, x ^ k * exp (-x)` is
the regularized lower incomplete gamma function `P(k + 1, t)`, which increases from `0` to `1` on
`[0, ∞)`. So `w_k(t)` is asymptotic to `t ^ (-k)` as `t → ∞`, while `w_k(0) = 0`: unlike `t ^ (-k)`,
the weight has no singularity at the origin.

In Delange's Tauberian theorem for a pole of order `k + 1`, the counting function `α` is studied
through `w_k(t) * exp (-a t) * α(t)`. Multiplying by `w_k` corresponds, on the Laplace side, to
integrating the derivative of the transform against `u ^ k / k!` over `[0, 1]`, which lowers a pole
of order `k + 1` to a locally integrable singularity. The properties proved here are the ones the
unsmoothing argument consumes: positivity, the normalization `w_k(t) * t ^ k → 1`, and the slow
variation `w_k(t + h) / w_k(t) → 1`, uniformly for `h` in a compact interval.

## Main definitions

* `TauCeti.HigherPoleTauberian.delangeWeight`: the weight `w_k(t)`, total in `t`.

## Main results

* `delangeWeight_mul_pow_eq_integral`: `w_k(t) * t ^ k = (∫ x in 0..t, x ^ k * exp (-x)) / k!`
  for every real `t`.
* `delangeWeight_mul_pow_eq_regularizedGamma`: `w_k(t) * t ^ k = P(k + 1, t)` for `0 ≤ t`.
* `delangeWeight_mul_pow_eq_one_sub`: the closed form
  `w_k(t) * t ^ k = 1 - exp (-t) * ∑ j ≤ k, t ^ j / j!` for every real `t`.
* `delangeWeight_nonneg`, `delangeWeight_pos`, `delangeWeight_mul_pow_le_one`: the range on
  `[0, ∞)`; positivity fails for negative `t` (`delangeWeight_zero_left`).
* `delangeWeight_normalization`: `w_k(t) * t ^ k → 1` as `t → ∞`.
* `tendstoUniformlyOn_delangeWeight_shift`, `delangeWeight_shift`: `w_k(t + h) / w_k(t) → 1` as
  `t → ∞`, uniformly for `h ∈ [-H, H]`.
* `contDiff_delangeWeight`: `w_k` is smooth on `ℝ`.
* `hasDerivAt_delangeWeight_zero`, `hasDerivAt_delangeWeight`: `w_k′(0) = 1 / (k! (k + 1))` and
  `w_k′(t) = exp (-t) / k! - k w_k(t) / t` for `t ≠ 0`.
* `tendsto_deriv_delangeWeight_div_atTop`: `w_k′(t) / w_k(t) → 0` as `t → ∞`.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242: §3.1–3.2, pp. 220–221 (the function `v`, its positivity and
  `v(t + h) / v(t) → 1`), Lemma 3, §5.1.1, pp. 231–232, and §5.2.1, p. 237 (the choice
  `γ(u) = u ^ (ω - 1)` for an exponent `ω ≥ 1`). For `ω = k + 1`, `γ(u) = u ^ k / k!` and the
  cutoff `1`, Delange's `t v(t)` is `w_k(t)`.
-/

public section

noncomputable section

open Filter Set
open scoped Topology Nat ContDiff

namespace TauCeti.HigherPoleTauberian

/-- **Delange's polynomial weight** `w_k(t) = t * ∫ u in 0..1, exp (-u * t) * u ^ k / k!`.

The definition is total in `t`. For `t ≥ 0`, `0 ≤ w_k(t)` and `w_k(t) * t ^ k ≤ 1`; the weight
is positive for `t > 0`, and `w_k(t) * t ^ k → 1` as `t → ∞`. See
`delangeWeight_mul_pow_eq_regularizedGamma` for its expression through the regularized incomplete
gamma function. -/
def delangeWeight (k : ℕ) (t : ℝ) : ℝ :=
  t * ∫ u in (0 : ℝ)..1, Real.exp (-u * t) * u ^ k / (k ! : ℝ)

variable {k : ℕ} {t : ℝ}

/-- The defining formula of `delangeWeight`. -/
theorem delangeWeight_def (k : ℕ) (t : ℝ) :
    delangeWeight k t = t * ∫ u in (0 : ℝ)..1, Real.exp (-u * t) * u ^ k / (k ! : ℝ) := (rfl)

/-- The weight vanishes at the origin. -/
@[simp]
theorem delangeWeight_zero_right (k : ℕ) : delangeWeight k 0 = 0 := by
  simp [delangeWeight_def]

/-! ### Regularity -/

/-- The parametric integral `t ↦ ∫ u in 0..1, exp (-u * t) * u ^ k / k!` is smooth. -/
private theorem contDiff_integral_exp_mul_pow (k : ℕ) :
    ContDiff ℝ ∞ fun t : ℝ => ∫ u in (0 : ℝ)..1, Real.exp (-u * t) * u ^ k / (k ! : ℝ) :=
  ContDiff.parametric_intervalIntegral
    (f := fun p : ℝ × ℝ => Real.exp (-p.2 * p.1) * p.2 ^ k / (k ! : ℝ)) (by fun_prop)

/-- Delange's weight is smooth on all of `ℝ`. -/
theorem contDiff_delangeWeight (k : ℕ) : ContDiff ℝ ∞ (delangeWeight k) := by
  rw [funext (delangeWeight_def k)]
  exact contDiff_id.mul (contDiff_integral_exp_mul_pow k)

/-- Delange's weight is continuous on all of `ℝ`. -/
@[fun_prop]
theorem continuous_delangeWeight (k : ℕ) : Continuous (delangeWeight k) :=
  (contDiff_delangeWeight k).continuous

/-! ### The incomplete gamma function -/

/-- After the substitution `x = u * t`, `w_k(t) * t ^ k` is the truncated Euler integral
`(1 / k!) ∫ x in 0..t, x ^ k * exp (-x)`, for every real `t`. -/
theorem delangeWeight_mul_pow_eq_integral (k : ℕ) (t : ℝ) :
    delangeWeight k t * t ^ k = (∫ x in (0 : ℝ)..t, x ^ k * Real.exp (-x)) / (k ! : ℝ) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hsub : ∀ u : ℝ, Real.exp (-u * t) * u ^ k / (k ! : ℝ) =
      (t ^ k * (k ! : ℝ))⁻¹ * ((t * u) ^ k * Real.exp (-(t * u))) := by
    intro u
    field_simp
    ring_nf
  simp_rw [delangeWeight_def, hsub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => x ^ k * Real.exp (-x)) ht, mul_zero,
    mul_one, smul_eq_mul]
  field_simp

/-- On `[0, ∞)`, `w_k(t) * t ^ k` is the regularized lower incomplete gamma function
`P(k + 1, t)`. -/
theorem delangeWeight_mul_pow_eq_regularizedGamma (k : ℕ) (ht : 0 ≤ t) :
    delangeWeight k t * t ^ k = regularizedGamma (k + 1) t := by
  rw [delangeWeight_mul_pow_eq_integral, regularizedGamma_eq_div,
    lowerIncompleteGamma_eq_integral ht, Real.Gamma_nat_eq_factorial]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp [← Real.rpow_natCast]

/-- The closed form `w_k(t) * t ^ k = 1 - exp (-t) * ∑ j ≤ k, t ^ j / j!`, for every real `t`.
On `[0, ∞)` this is the Erlang form `TauCeti.regularizedGamma_natCast` of `P(k + 1, t)`. -/
theorem delangeWeight_mul_pow_eq_one_sub (k : ℕ) (t : ℝ) :
    delangeWeight k t * t ^ k =
      1 - Real.exp (-t) * ∑ j ∈ Finset.range (k + 1), t ^ j / (j ! : ℝ) := by
  -- `x ↦ exp (-x) * ∑ j ≤ n, x ^ j / j!` has derivative `-(x ^ n * exp (-x) / n!)`.
  have hderiv : ∀ (n : ℕ) (x : ℝ), HasDerivAt
      (fun x => Real.exp (-x) * ∑ j ∈ Finset.range (n + 1), x ^ j / (j ! : ℝ))
      (-(x ^ n * Real.exp (-x) / (n ! : ℝ))) x := by
    intro n x
    induction n with
    | zero => simpa using (hasDerivAt_neg x).exp
    | succ n ih =>
      convert ih.add ((hasDerivAt_neg x).exp.mul
        ((hasDerivAt_pow (n + 1) x).div_const ((n + 1)! : ℝ))) using 1
      · funext y
        simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_range_succ]
        ring
      · rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
  have h₀ : ∑ j ∈ Finset.range (k + 1), (0 : ℝ) ^ j / (j ! : ℝ) = 1 := by
    rw [Finset.sum_range_succ']
    simp
  have hint : ∫ x in (0 : ℝ)..t, x ^ k * Real.exp (-x) =
      (k ! : ℝ) * (1 - Real.exp (-t) * ∑ j ∈ Finset.range (k + 1), t ^ j / (j ! : ℝ)) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => -(k ! : ℝ) * (Real.exp (-x) * ∑ j ∈ Finset.range (k + 1), x ^ j / (j ! : ℝ)))
      (fun x _ => by
        convert (hderiv k x).const_mul (-(k ! : ℝ)) using 1
        field_simp)
      ((by fun_prop : Continuous fun x : ℝ => x ^ k * Real.exp (-x)).intervalIntegrable 0 t)]
    simp only [neg_zero, Real.exp_zero, one_mul, h₀]
    ring
  rw [delangeWeight_mul_pow_eq_integral, hint]
  field_simp

/-- At `k = 0` the weight is `w_0(t) = 1 - exp (-t)`, for every real `t`. In particular
`w_0(-1) = 1 - e < 0`: the positivity of the weight is a statement about `t > 0` only. -/
@[simp]
theorem delangeWeight_zero_left (t : ℝ) : delangeWeight 0 t = 1 - Real.exp (-t) := by
  simpa using delangeWeight_mul_pow_eq_one_sub 0 t

/-! ### Range on `[0, ∞)` -/

private theorem delangeWeight_eq_regularizedGamma_div (k : ℕ) (ht : 0 < t) :
    delangeWeight k t = regularizedGamma (k + 1) t / t ^ k :=
  eq_div_of_mul_eq (pow_ne_zero k ht.ne') (delangeWeight_mul_pow_eq_regularizedGamma k ht.le)

/-- The weight is nonnegative on `[0, ∞)`. -/
theorem delangeWeight_nonneg (k : ℕ) (ht : 0 ≤ t) : 0 ≤ delangeWeight k t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  rw [delangeWeight_eq_regularizedGamma_div k ht]
  exact div_nonneg (regularizedGamma_nonneg _ _) (pow_nonneg ht.le k)

/-- The weight is positive on `(0, ∞)`. -/
theorem delangeWeight_pos (k : ℕ) (ht : 0 < t) : 0 < delangeWeight k t := by
  rw [delangeWeight_eq_regularizedGamma_div k ht]
  exact div_pos (regularizedGamma_pos (by positivity) ht) (pow_pos ht k)

/-- The normalized bound `w_k(t) * t ^ k ≤ 1` on `[0, ∞)`. -/
theorem delangeWeight_mul_pow_le_one (k : ℕ) (ht : 0 ≤ t) : delangeWeight k t * t ^ k ≤ 1 := by
  rw [delangeWeight_mul_pow_eq_regularizedGamma k ht]
  exact regularizedGamma_le_one _ _

/-! ### Behaviour at infinity -/

/-- **Normalization of Delange's weight**: `w_k(t) * t ^ k → 1` as `t → ∞`. -/
theorem delangeWeight_normalization (k : ℕ) :
    Tendsto (fun t : ℝ => delangeWeight k t * t ^ k) atTop (𝓝 1) :=
  (tendsto_regularizedGamma_atTop (by positivity : (0 : ℝ) < k + 1)).congr' <| by
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (delangeWeight_mul_pow_eq_regularizedGamma k ht).symm

/-- The shift ratio `w_k(t + h) / w_k(t)` tends to `1` jointly as `t → ∞` and `h` stays in
`[-H, H]`. -/
private theorem tendsto_delangeWeight_add_div_prod (k : ℕ) (H : ℝ) :
    Tendsto (fun p : ℝ × ℝ => delangeWeight k (p.1 + p.2) / delangeWeight k p.1)
      (atTop ×ˢ 𝓟 (Icc (-H) H)) (𝓝 1) := by
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) (atTop ×ˢ 𝓟 (Icc (-H) H)) atTop := tendsto_fst
  have hmem : ∀ᶠ p : ℝ × ℝ in atTop ×ˢ 𝓟 (Icc (-H) H), p.2 ∈ Icc (-H) H :=
    tendsto_principal.1 tendsto_snd
  have hsum : Tendsto (fun p : ℝ × ℝ => p.1 + p.2) (atTop ×ˢ 𝓟 (Icc (-H) H)) atTop :=
    tendsto_atTop_add_right_of_le' _ (-H) hfst (hmem.mono fun p hp => hp.1)
  -- `t / (t + h) → 1`, because `h / t → 0` for bounded `h`.
  have hdiv : Tendsto (fun p : ℝ × ℝ => p.2 / p.1) (atTop ×ˢ 𝓟 (Icc (-H) H)) (𝓝 0) := by
    have hH : Tendsto (fun p : ℝ × ℝ => H / p.1) (atTop ×ˢ 𝓟 (Icc (-H) H)) (𝓝 0) :=
      tendsto_const_nhds.div_atTop hfst
    refine squeeze_zero_norm' ?_ hH
    filter_upwards [hmem, hfst.eventually_gt_atTop 0] with p hp hpos
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (abs_le.2 hp) hpos.le
  have hratio : Tendsto (fun p : ℝ × ℝ => (p.1 / (p.1 + p.2)) ^ k)
      (atTop ×ˢ 𝓟 (Icc (-H) H)) (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hdiv).inv₀ (by norm_num) |>.pow k
    rw [add_zero, inv_one, one_pow] at h
    refine h.congr' ?_
    filter_upwards [hfst.eventually_gt_atTop 0] with p hp
    rw [one_add_div hp.ne', inv_div]
  have hA : Tendsto (fun p : ℝ × ℝ => delangeWeight k (p.1 + p.2) * (p.1 + p.2) ^ k)
      (atTop ×ˢ 𝓟 (Icc (-H) H)) (𝓝 1) := (delangeWeight_normalization k).comp hsum
  have hB : Tendsto (fun p : ℝ × ℝ => delangeWeight k p.1 * p.1 ^ k)
      (atTop ×ˢ 𝓟 (Icc (-H) H)) (𝓝 1) := (delangeWeight_normalization k).comp hfst
  have hN := hA.div hB one_ne_zero
  rw [div_one] at hN
  have h := hN.mul hratio
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [hfst.eventually_gt_atTop 0, hsum.eventually_gt_atTop 0] with p hp hq
  have h₁ := delangeWeight_pos k hp
  have h₂ := delangeWeight_pos k hq
  rw [Pi.div_apply, div_pow]
  field_simp

/-- **Uniform slow variation of Delange's weight**: `w_k(t + h) / w_k(t) → 1` as `t → ∞`,
uniformly for `h ∈ [-H, H]`. Through `Metric.tendstoUniformlyOn_iff`, for every `ε > 0` there is
`T` such that `|w_k(t + h) / w_k(t) - 1| < ε` for all `t ≥ T` and `|h| ≤ H`. -/
theorem tendstoUniformlyOn_delangeWeight_shift (k : ℕ) (H : ℝ) :
    TendstoUniformlyOn (fun t h => delangeWeight k (t + h) / delangeWeight k t) (fun _ => 1)
      atTop (Icc (-H) H) := by
  rw [tendstoUniformlyOn_iff_tendsto]
  exact Uniform.tendsto_nhds_right.1 (tendsto_delangeWeight_add_div_prod k H)

/-- **Slow variation of Delange's weight**: `w_k(t + h) / w_k(t) → 1` as `t → ∞`, for each fixed
real `h`. -/
theorem delangeWeight_shift (k : ℕ) (h : ℝ) :
    Tendsto (fun t : ℝ => delangeWeight k (t + h) / delangeWeight k t) atTop (𝓝 1) :=
  (tendstoUniformlyOn_delangeWeight_shift k |h|).tendsto_at (abs_le.1 le_rfl)

/-! ### Derivatives -/

/-- The derivative of Delange's weight at the origin is `1 / (k! (k + 1))`. -/
theorem hasDerivAt_delangeWeight_zero (k : ℕ) :
    HasDerivAt (delangeWeight k) (1 / ((k ! : ℝ) * (k + 1))) 0 := by
  have hI := (contDiff_integral_exp_mul_pow k).differentiable (by simp) 0
  convert (hasDerivAt_id (0 : ℝ)).mul hI.hasDerivAt using 1
  · exact funext (delangeWeight_def k)
  · simp [intervalIntegral.integral_div, integral_pow]
    field_simp

/-- Away from the origin, the derivative of Delange's weight is
`exp (-t) / k! - k * w_k(t) / t`. The hypothesis `t ≠ 0` is needed: at `t = 0` the derivative is
`1 / (k! (k + 1))` (`hasDerivAt_delangeWeight_zero`), whereas the right-hand side, read with
`0 / 0 = 0`, is `1 / k!`. -/
theorem hasDerivAt_delangeWeight (k : ℕ) (ht : t ≠ 0) :
    HasDerivAt (delangeWeight k)
      (Real.exp (-t) / (k ! : ℝ) - k * delangeWeight k t / t) t := by
  set P := fun x : ℝ => ∫ y in (0 : ℝ)..x, y ^ k * Real.exp (-y)
  have heq : ∀ x : ℝ, x ≠ 0 → delangeWeight k x = P x / (k ! : ℝ) / x ^ k := fun x hx =>
    eq_div_of_mul_eq (pow_ne_zero k hx) (delangeWeight_mul_pow_eq_integral k x)
  have hP : HasDerivAt P (t ^ k * Real.exp (-t)) t :=
    ((by fun_prop : Continuous fun y : ℝ => y ^ k * Real.exp (-y)).integral_hasStrictDerivAt
      0 t).hasDerivAt
  have hq := (hP.div_const (k ! : ℝ)).div (hasDerivAt_pow k t) (pow_ne_zero k ht)
  refine (hq.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [eventually_ne_nhds ht] with x hx using heq x hx
  · rw [heq t ht]
    rcases k with _ | k
    · simp
    · simp only [add_tsub_cancel_right]
      field_simp
      ring

/-- The derivative of Delange's weight at the origin. -/
theorem deriv_delangeWeight_zero (k : ℕ) :
    deriv (delangeWeight k) 0 = 1 / ((k ! : ℝ) * (k + 1)) :=
  (hasDerivAt_delangeWeight_zero k).deriv

/-- The derivative of Delange's weight away from the origin. -/
theorem deriv_delangeWeight (k : ℕ) (ht : t ≠ 0) :
    deriv (delangeWeight k) t = Real.exp (-t) / (k ! : ℝ) - k * delangeWeight k t / t :=
  (hasDerivAt_delangeWeight k ht).deriv

/-- The logarithmic derivative of Delange's weight tends to zero: `w_k′(t) / w_k(t) → 0` as
`t → ∞`. -/
theorem tendsto_deriv_delangeWeight_div_atTop (k : ℕ) :
    Tendsto (fun t : ℝ => deriv (delangeWeight k) t / delangeWeight k t) atTop (𝓝 0) := by
  have h₁ := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).div
    ((delangeWeight_normalization k).const_mul (k ! : ℝ)) (by positivity)
  have h₂ : Tendsto (fun t : ℝ => (k : ℝ) / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := h₁.sub h₂
  rw [zero_div, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hw := delangeWeight_pos k ht
  rw [deriv_delangeWeight k ht.ne', Pi.div_apply]
  field_simp

end TauCeti.HigherPoleTauberian
