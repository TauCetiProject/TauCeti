/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Hermite.Laplace.Series

/-!
# Entire continuation of the normalized Laplace–Hermite series

The rotational Gaussian–Laplace identity in `Hermite.Laplace.Series` initially holds for positive
real part of the order. This file shows that its reciprocal-Gamma normalization commutes with
entire continuation of the order. The coefficients become rising factorials, and shifted integral
tails provide absolute convergence and holomorphy even at nonpositive integer orders.

The result is stated for entire functions agreeing with the normalized integral on the right
half-plane, so it can be applied to a special function without choosing its construction here.
This gives the continuation in the order for the rotational addition formula DLMF 12.13.5.
In the Gaussian–Laplace representation DLMF 12.5.1 the order here is `s = a + 1 / 2` and the
ratio is `r = -tan t`. The radial limit at `|r| = 1` follows by continuity of the rotated value.

## Main results

* `TauCeti.summable_norm_ascPochhammer_mul_hermite_of_eqOn_integral`: absolute convergence at
  every order in the interior and in the admissible boundary regions.
* `TauCeti.hasSum_ascPochhammer_mul_hermite_of_eqOn_integral`: the rotational identity at every
  complex order for entire continuations of the two normalized Gaussian–Laplace integrals.
* `TauCeti.tendsto_tsum_ascPochhammer_mul_hermite_nhdsLT_one`: the radial limit on `|r| ≤ 1`.
* `TauCeti.hasSum_ascPochhammer_mul_hermite_of_abs_le_one`: evaluation on the closed interval
  throughout the interior and in the convergent boundary regimes, including terminating orders.

## References

* [DLMF, Chapter 12, Parabolic Cylinder Functions](https://dlmf.nist.gov/12), equations
  [12.5.1](https://dlmf.nist.gov/12.5.E1) and [12.13.5](https://dlmf.nist.gov/12.13.E5).
-/

public section

open Complex Filter MeasureTheory Polynomial Set
open scoped Nat Topology

namespace TauCeti

private theorem ascPochhammer_mul_eq_inv_Gamma_mul_integral
    {F : ℂ → ℂ} {x s : ℂ}
    (hF : ∀ z : ℂ, 0 < z.re → F z = (Gamma z)⁻¹ *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
    (m : ℕ) (hs : 0 < s.re + (m : ℝ)) :
    (ascPochhammer ℂ m).eval s * F (s + m) = (Gamma s)⁻¹ *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) := by
  rw [hF (s + m) (by simpa using hs), ← mul_assoc,
    ← Complex.inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add]

/-- Absolute convergence of the rising-factorial Laplace–Hermite series for any function agreeing
with the reciprocal-Gamma normalized integral on the right half-plane. The values of the function
outside the half-plane affect only finitely many terms for each order. -/
theorem summable_norm_ascPochhammer_mul_hermite_of_eqOn_integral
    {s x r : ℂ} (y : ℝ) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.re → F z = (Gamma z)⁻¹ *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
    (hconv : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ s.re < 0)))) :
    Summable fun m : ℕ =>
      ‖r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        (ascPochhammer ℂ m).eval s * F (s + m)‖ := by
  obtain ⟨M, hM⟩ := exists_nat_gt (-s.re)
  have hsM : 0 < s.re + (M : ℝ) := by linarith
  rw [← summable_nat_add_iff M, summable_norm_iff]
  refine ((summable_pow_div_factorial_mul_hermite_mul_integral_add M x r y hsM hconv).mul_left
    (Gamma s)⁻¹).congr fun k => ?_
  rw [mul_assoc (_ * _), ascPochhammer_mul_eq_inv_Gamma_mul_integral hF (k + M)
    (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])]
  ring

private theorem tsum_ascPochhammer_mul_hermite_eq_head_add_tail
    {s x r : ℂ} (y : ℝ) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.re → F z = (Gamma z)⁻¹ *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
    (M : ℕ) (hsM : 0 < s.re + (M : ℝ))
    (hconv : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ (0 < x.re ∨ (0 ≤ x.re ∧ s.re < 0)))) :
    (∑' m : ℕ, r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
      (ascPochhammer ℂ m).eval s * F (s + m)) =
    (∑ m ∈ Finset.range M, r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
      (ascPochhammer ℂ m).eval s * F (s + m)) + (Gamma s)⁻¹ *
      ∑' k : ℕ, r ^ (k + M) / ((k + M)! : ℂ) * aeval (y : ℂ) (hermite (k + M)) *
        ∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (s + ((k + M : ℕ) : ℂ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u) := by
  have hsum := (summable_norm_iff.mp
    (summable_norm_ascPochhammer_mul_hermite_of_eqOn_integral y hF hconv))
  rw [← hsum.sum_add_tsum_nat_add M]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [mul_assoc (_ * _), ascPochhammer_mul_eq_inv_Gamma_mul_integral hF (k + M)
    (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])]
  ring

private theorem differentiable_tsum_ascPochhammer_mul_hermite_of_eqOn_integral
    {x r : ℂ} (y : ℝ) {F : ℂ → ℂ} (hFd : Differentiable ℂ F)
    (hF : ∀ z : ℂ, 0 < z.re → F z = (Gamma z)⁻¹ *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
    (hconv : ‖r‖ < 1 ∨ (‖r‖ ≤ 1 ∧ 0 < x.re)) :
    Differentiable ℂ fun s : ℂ => ∑' m : ℕ,
      r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        (ascPochhammer ℂ m).eval s * F (s + m) := by
  intro s
  obtain ⟨M, hM⟩ := exists_nat_gt (-s.re)
  have hsM : 0 < s.re + (M : ℝ) := by linarith
  have hopen : IsOpen {z : ℂ | 0 < z.re + (M : ℝ)} :=
    isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)
  have hhead : Differentiable ℂ fun z : ℂ => ∑ m ∈ Finset.range M,
      r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        (ascPochhammer ℂ m).eval z * F (z + m) := by
    have hterm : ∀ m ∈ Finset.range M, Differentiable ℂ fun z : ℂ =>
        r ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
          (ascPochhammer ℂ m).eval z * F (z + m) := fun m _ =>
      ((ascPochhammer ℂ m).differentiable.const_mul _).mul
        (hFd.comp (differentiable_id.add_const _))
    exact Differentiable.fun_sum hterm
  have htail := differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral_add M x y hconv
  refine (hhead s |>.add ((Complex.differentiable_one_div_Gamma s).mul
    (htail.differentiableAt (hopen.mem_nhds hsM)))).congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds hsM] with z hz
  exact tsum_ascPochhammer_mul_hermite_eq_head_add_tail y hF M hz
    (hconv.imp_right fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩)

private theorem hasSum_ascPochhammer_mul_hermite_of_re_pos
    {s : ℂ} (hs : 0 < s.re) (x : ℂ) (y : ℝ) {r : ℝ} {F G : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.re → F z = (Gamma z)⁻¹ *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
    (hG : ∀ z : ℂ, 0 < z.re → G z = (Gamma z)⁻¹ *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z - 1) *
        cexp (-(u : ℂ) ^ 2 / 2 - ((x - r * y) / Real.sqrt (1 + r ^ 2)) * u))
    (hr : |r| < 1 ∨ (|r| ≤ 1 ∧ 0 < x.re)) :
    HasSum (fun m : ℕ => (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
      (ascPochhammer ℂ m).eval s * F (s + m))
      ((Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) * G s) := by
  have hsum := (hasSum_pow_div_factorial_mul_hermite_mul_integral hs x y hr).mul_left
    (Gamma s)⁻¹
  have hterms : ∀ m : ℕ,
      (Gamma s)⁻¹ * ((r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u)) =
      (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        (ascPochhammer ℂ m).eval s * F (s + m) := by
    intro m
    rw [mul_assoc (_ * _), ascPochhammer_mul_eq_inv_Gamma_mul_integral hF m
      (by linarith [Nat.cast_nonneg (α := ℝ) m])]
    ring
  have hvalue : (Gamma s)⁻¹ * ((Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) *
        cexp (-(u : ℂ) ^ 2 / 2 - ((x - r * y) / Real.sqrt (1 + r ^ 2)) * u)) =
      (Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) * G s := by
    rw [hG s hs]
    ring
  exact hvalue ▸ hsum.congr_fun (fun m => (hterms m).symm)

/-- Entire continuation in the order of the normalized rotational Laplace–Hermite identity.
The two entire functions are required only to agree with the normalized Gaussian–Laplace
integrals on the right half-plane. The conclusion holds at every complex order, including the
nonpositive integers. -/
theorem hasSum_ascPochhammer_mul_hermite_of_eqOn_integral
    (s x : ℂ) (y : ℝ) {r : ℝ} {F G : ℂ → ℂ}
    (hFd : Differentiable ℂ F) (hGd : Differentiable ℂ G)
    (hF : ∀ z : ℂ, 0 < z.re → F z = (Gamma z)⁻¹ *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z - 1) * cexp (-(u : ℂ) ^ 2 / 2 - x * u))
    (hG : ∀ z : ℂ, 0 < z.re → G z = (Gamma z)⁻¹ *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z - 1) *
        cexp (-(u : ℂ) ^ 2 / 2 - ((x - r * y) / Real.sqrt (1 + r ^ 2)) * u))
    (hr : |r| < 1 ∨ (|r| ≤ 1 ∧ 0 < x.re)) :
    HasSum (fun m : ℕ => (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
      (ascPochhammer ℂ m).eval s * F (s + m))
      ((Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) * G s) := by
  have hr' : ‖(r : ℂ)‖ < 1 ∨ (‖(r : ℂ)‖ ≤ 1 ∧ 0 < x.re) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hr
  have hS := differentiable_tsum_ascPochhammer_mul_hermite_of_eqOn_integral y hFd hF hr'
  have hc : (Real.sqrt (1 + r ^ 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hR : Differentiable ℂ fun z : ℂ =>
      (Real.sqrt (1 + r ^ 2) : ℂ) ^ (-z) * G z :=
    (differentiable_id.neg.const_cpow (Or.inl hc)).mul hGd
  have hpos : (0 : ℝ) < (1 : ℂ).re := by norm_num
  have heq := AnalyticOnNhd.eq_of_eventuallyEq
    (fun z _ => hS.analyticAt z) (fun z _ => hR.analyticAt z) (z₀ := (1 : ℂ))
    (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos] with z hz
      exact (hasSum_ascPochhammer_mul_hermite_of_re_pos hz x y hF hG hr).tsum_eq)
  rw [← congrFun heq s]
  exact (summable_norm_iff.mp (summable_norm_ascPochhammer_mul_hermite_of_eqOn_integral y hF
    (hr'.imp_right fun ⟨h1, h2⟩ => ⟨h1, Or.inl h2⟩))).hasSum

/-- The damped Hermite series of an entire continuation of the normalized Gaussian–Laplace
integral has a radial limit for every real ratio in `[-1, 1]`. This includes boundary points
where the undamped series may diverge. -/
theorem tendsto_tsum_ascPochhammer_mul_hermite_nhdsLT_one
    (s x : ℂ) (y : ℝ) {r : ℝ} {F : ℂ → ℂ → ℂ}
    (hF : ∀ z, Differentiable ℂ (fun w ↦ F w z))
    (hcont : ContinuousAt (F s) ((x - r * y) / Real.sqrt (1 + r ^ 2)))
    (hLaplace : ∀ w, 0 < w.re → ∀ z, F w z = (Gamma w)⁻¹ * ∫ u in Ioi (0 : ℝ),
      (u : ℂ) ^ (w - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
    (hr : |r| ≤ 1) :
    Tendsto
      (fun t : ℝ ↦ ∑' m : ℕ, (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        (ascPochhammer ℂ m).eval s * F (s + m) x * (t : ℂ) ^ m)
      (𝓝[<] 1)
      (𝓝 ((Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) *
        F s ((x - r * y) / Real.sqrt (1 + r ^ 2)))) := by
  let c : ℝ → ℝ := fun t ↦ Real.sqrt (1 + (r * t) ^ 2)
  have hc (t : ℝ) : 0 < c t := Real.sqrt_pos.mpr (by positivity)
  have hc_cont : Continuous fun t ↦ (c t : ℂ) :=
    Complex.continuous_ofReal.comp (by dsimp [c]; fun_prop)
  have hp : Continuous fun t ↦ (c t : ℂ) ^ (-s) :=
    hc_cont.cpow continuous_const fun t ↦ Complex.ofReal_mem_slitPlane.mpr (hc t)
  let z : ℝ → ℂ := fun t ↦ (x - ((r * t : ℝ) : ℂ) * y) / c t
  have harg : Continuous z :=
    Continuous.div (by fun_prop) hc_cont fun t ↦ Complex.ofReal_ne_zero.mpr (hc t).ne'
  have hFcont : ContinuousAt (F s) (z 1) := by simpa only [z, c, mul_one] using hcont
  let g : ℝ → ℂ := fun t ↦ (c t : ℂ) ^ (-s) * F s (z t)
  have hg : ContinuousAt g 1 := hp.continuousAt.mul (hFcont.comp harg.continuousAt)
  have hlim : Tendsto g (𝓝[<] 1) (𝓝 (g 1)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  simp only [g, z, c, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one : (0 : ℝ) < 1)] with t ⟨ht0, ht1⟩
  have hrt : |r * t| < 1 := by
    rw [abs_mul, abs_of_pos ht0]
    exact lt_of_le_of_lt (mul_le_of_le_one_left ht0.le hr) ht1
  have hsum := hasSum_ascPochhammer_mul_hermite_of_eqOn_integral s x y (r := r * t)
    (hF x) (hF _) (fun w hw ↦ hLaplace w hw x) (fun w hw ↦ hLaplace w hw _) (Or.inl hrt)
  rw [← hsum.tsum_eq]
  refine tsum_congr fun m ↦ ?_
  rw [Complex.ofReal_mul, mul_pow]
  ring

/-- The normalized rotational Laplace–Hermite identity on the closed ratio interval.
The series converges throughout the interior without restrictions on the order or Laplace parameter.
Endpoint convergence holds for `0 < x.re`, for `0 ≤ x.re` with `s.re < 0`, and at every
nonpositive integer order, where the rising factorial makes the series terminate. -/
theorem hasSum_ascPochhammer_mul_hermite_of_abs_le_one
    (s x : ℂ) (y : ℝ) {r : ℝ} {F : ℂ → ℂ → ℂ}
    (hF : ∀ z, Differentiable ℂ (fun w ↦ F w z))
    (hcont : ContinuousAt (F s) ((x - r * y) / Real.sqrt (1 + r ^ 2)))
    (hLaplace : ∀ w, 0 < w.re → ∀ z, F w z = (Gamma w)⁻¹ * ∫ u in Ioi (0 : ℝ),
      (u : ℂ) ^ (w - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
    (hr : |r| ≤ 1)
    (hconv : |r| < 1 ∨ (0 < x.re ∨ (0 ≤ x.re ∧ s.re < 0)) ∨ ∃ n : ℕ, s = -(n : ℂ)) :
    HasSum
      (fun m : ℕ ↦ (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        (ascPochhammer ℂ m).eval s * F (s + m) x)
      ((Real.sqrt (1 + r ^ 2) : ℂ) ^ (-s) * F s ((x - r * y) / Real.sqrt (1 + r ^ 2))) := by
  rcases hconv with hrlt | hconv
  · exact hasSum_ascPochhammer_mul_hermite_of_eqOn_integral s x y
      (hF x) (hF _) (fun w hw ↦ hLaplace w hw x) (fun w hw ↦ hLaplace w hw _) (Or.inl hrlt)
  have hsum : Summable (fun m : ℕ ↦ (r : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
      (ascPochhammer ℂ m).eval s * F (s + m) x) := by
    rcases hconv with hx | ⟨n, rfl⟩
    · have hr' : ‖(r : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hr
      exact (summable_norm_ascPochhammer_mul_hermite_of_eqOn_integral y
        (fun w hw ↦ hLaplace w hw x) (Or.inr ⟨hr', hx⟩)).of_norm
    · refine summable_of_ne_finset_zero (s := Finset.range (n + 1)) fun m hm ↦ ?_
      have hnm : n < m := by simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hm
      simp [ascPochhammer_eval_neg_natCast_of_lt hnm]
  have habel := tendsto_map'_iff.mp
    (Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hsum.hasSum.tendsto_sum_nat)
  have heq := tendsto_nhds_unique habel
    (tendsto_tsum_ascPochhammer_mul_hermite_nhdsLT_one s x y hF hcont hLaplace hr)
  exact heq ▸ hsum.hasSum

end TauCeti
