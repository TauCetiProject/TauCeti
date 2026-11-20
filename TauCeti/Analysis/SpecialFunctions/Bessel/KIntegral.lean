/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Contour.Residue.ChangeOfVariables
import TauCeti.Analysis.MellinInversion
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Residue
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# The integral `∫₀^∞ s^{p-1} e^{-s - x/s} ds` as a series

For `x > 0` and real `p` the integral

`∫₀^∞ s^{p - 1} e^{-s - x/s} ds = 2 x^{p/2} K_p(2 √x)`

is the Macdonald function in the reduced form of DLMF 10.32.10. This file proves that for
`0 < p < 1` it is the combination of reduced Bessel series

`∫₀^∞ s^{p - 1} e^{-s - x/s} ds = (π / sin pπ) (𝐅(1 - p, x) - x^p 𝐅(1 + p, x))`,

where `𝐅(b, x) = ∑ₙ xⁿ / (n! Γ(b + n))` is Mathlib's regularized `₀F₁`,
`Complex.regularizedHGFun 0 {b}`. In Bessel notation this is
`K_p = π (I_{-p} - I_p) / (2 sin pπ)` (DLMF 10.27.4) at the argument `2 √x`, with
`I_{±p}(2 √x) = x^{±p/2} 𝐅(1 ± p, x)`. Integrals of this shape arise from
`∫₀^∞ e^{-ζ cosh u} cosh(pu) du` by the substitution `s = (ζ/2) eᵘ`, with `x = ζ²/4`; this is how
integral representations of the form `z^{1/2} ∫₀^∞ e^{-ζ cosh u} cosh(pu) du`, such as that of
the generalized Airy functions with `p = 1/(n + 2)`, reduce to series in `𝐅`.

The proof is by Mellin transforms. By Fubini and Euler's integral, the Mellin transform of the
integral in `x` is `Γ(t) Γ(t + p)` for `Re t > max(0, -p)` (DLMF 10.43.19 in reduced form).
Mellin inversion recovers the integral from `Γ(t) Γ(t + p)` on the line `Re t = 1`, and this line
is shifted to `Re t = δ - N` with `δ = (1 - p)/2`, crossing the simple poles at `t = -k` and
`t = -p - k` for `k < N`. Their residues are the terms of the two series, by the reflection
formula, and the integral over the shifted line tends to `0` as `N → ∞`, since `Γ` decays like
`1/N!` across a vertical line `N` units to the left of the strip `0 < Re t < 1`.

## Main results

* `TauCeti.integrableOn_rpow_mul_exp_neg_sub_div`: `s ↦ s^{p-1} e^{-s - x/s}` is integrable on
  `(0, ∞)` for every real `p` and `x > 0`.
* `TauCeti.continuousOn_integral_rpow_mul_exp_neg_sub_div`: the integral is continuous in
  `x > 0`.
* `TauCeti.hasMellin_integral_rpow_mul_exp_neg_sub_div`: its Mellin transform is
  `Γ(t) Γ(t + p)` for `0 < Re t` and `0 < Re t + p`.
* `TauCeti.integral_rpow_mul_exp_neg_sub_div_Ioi`: the series evaluation above for `0 < p < 1`.

## References

* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §3.7 (6) and §6.22 (15).
* *NIST Digital Library of Mathematical Functions*, 10.27.4, 10.32.10 and 10.43.19,
  <https://dlmf.nist.gov/10>.
-/

public section

noncomputable section

open Set MeasureTheory Filter
open scoped Real Nat Topology
open Complex hiding exp continuous_exp

namespace TauCeti

/-! ### Integrability, continuity and the Mellin transform -/

/-- For every real `p` and `x > 0`, the integrand `s ↦ s^{p - 1} e^{-s - x/s}` is integrable on
`(0, ∞)`: the factor `e^{-x/s}` vanishes to infinite order at `0`, and `e^{-s}` decays at `∞`. -/
theorem integrableOn_rpow_mul_exp_neg_sub_div (p : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s : ℝ ↦ s ^ (p - 1) * Real.exp (-s - x / s)) (Ioi 0) := by
  -- `e^{-x/s} ≤ n! sⁿ / xⁿ` reduces the integrand to Euler's integrand for `Γ(p + n)`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < p + n :=
    ⟨⌈-p⌉₊ + 1, by push_cast; linarith [Nat.le_ceil (-p)]⟩
  refine ((Real.GammaIntegral_convergent hn).const_mul ((n ! : ℝ) / x ^ n)).mono'
    (by fun_prop : Measurable fun s : ℝ ↦ s ^ (p - 1) * Real.exp (-s - x / s)).aestronglyMeasurable
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
  have hexp : Real.exp (-s - x / s) * ((x / s) ^ n / n !) ≤ Real.exp (-s) := by
    rw [sub_eq_add_neg, Real.exp_add, mul_assoc]
    calc Real.exp (-s) * (Real.exp (-(x / s)) * ((x / s) ^ n / n !))
        ≤ Real.exp (-s) * (Real.exp (-(x / s)) * Real.exp (x / s)) := by
          gcongr; exact Real.pow_div_factorial_le_exp _ (div_pos hx hs).le n
      _ = Real.exp (-s) := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hfac : (0 : ℝ) < (x / s) ^ n / n ! := by positivity
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ (p - 1) * Real.exp (-s - x / s)),
    show p + n - 1 = (p - 1) + n by ring,
    Real.rpow_add hs, Real.rpow_natCast]
  calc s ^ (p - 1) * Real.exp (-s - x / s)
      ≤ s ^ (p - 1) * (Real.exp (-s) / ((x / s) ^ n / n !)) := by
        gcongr; rwa [le_div_iff₀ hfac]
    _ = (n ! : ℝ) / x ^ n * (Real.exp (-s) * (s ^ (p - 1) * s ^ n)) := by
        rw [div_pow]
        field_simp

/-- The integral `x ↦ ∫₀^∞ s^{p - 1} e^{-s - x/s} ds` is continuous on `x > 0`. -/
theorem continuousOn_integral_rpow_mul_exp_neg_sub_div (p : ℝ) :
    ContinuousOn (fun x : ℝ ↦ ∫ s in Ioi 0, s ^ (p - 1) * Real.exp (-s - x / s)) (Ioi 0) := by
  intro x (hx : 0 < x)
  refine ContinuousAt.continuousWithinAt <| continuousAt_of_dominated
    (bound := fun s ↦ s ^ (p - 1) * Real.exp (-s - x / 2 / s))
    (Eventually.of_forall fun y ↦ (by fun_prop : Measurable fun s : ℝ ↦
      s ^ (p - 1) * Real.exp (-s - y / s)).aestronglyMeasurable) ?_
    (integrableOn_rpow_mul_exp_neg_sub_div p (half_pos hx))
    (Eventually.of_forall fun s ↦ by fun_prop)
  filter_upwards [Ioi_mem_nhds (half_lt_self hx)] with y (hy : x / 2 < y)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ (p - 1) * Real.exp (-s - y / s))]
  gcongr

/-- The Mellin integrand of `∫₀^∞ s^{p - 1} e^{-s - x/s} ds` at `x`, as a function of `s > 0`,
splits off the factor `x^{t - 1} e^{-x/s}`. -/
private lemma cpow_mul_ofReal_rpow_mul_exp_eq (p : ℝ) (t : ℂ) (x : ℝ) {s : ℝ} (hs : 0 < s) :
    (x : ℂ) ^ (t - 1) * ((s ^ (p - 1) * Real.exp (-s - x / s) : ℝ) : ℂ) =
      ((s ^ (p - 1) * Real.exp (-s) : ℝ) : ℂ) *
        ((x : ℂ) ^ (t - 1) * cexp (-((s⁻¹ : ℝ) * (x : ℂ)))) := by
  rw [show -s - x / s = -s + -(s⁻¹ * x) by field_simp; ring, Real.exp_add]
  push_cast
  ring

/-- The double integrand `x^{t - 1} s^{p - 1} e^{-s - x/s}` is integrable on `(0, ∞)²` for
`0 < Re t` and `0 < Re t + p`: its `x`-integral is `Γ(Re t) s^{Re t + p - 1} e^{-s}` in norm. -/
private lemma integrable_uncurry_cpow_mul_rpow_mul_exp {p : ℝ} {t : ℂ} (ht : 0 < t.re)
    (htp : 0 < t.re + p) :
    Integrable (Function.uncurry fun x s : ℝ ↦
        (x : ℂ) ^ (t - 1) * ((s ^ (p - 1) * Real.exp (-s - x / s) : ℝ) : ℂ))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi 0))) := by
  have hnorm {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
      ‖(x : ℂ) ^ (t - 1) * ((s ^ (p - 1) * Real.exp (-s - x / s) : ℝ) : ℂ)‖ =
        s ^ (p - 1) * Real.exp (-s) * (x ^ (t.re - 1) * Real.exp (-(s⁻¹ * x))) := by
    rw [cpow_mul_ofReal_rpow_mul_exp_eq p t x hs, norm_mul, norm_mul, norm_real,
      Real.norm_of_nonneg (by positivity), norm_cpow_eq_rpow_re_of_pos hx, norm_exp]
    simp
  refine (integrable_prod_iff' (by fun_prop : Measurable _).aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := t.re - 1) (p := 1) (b := s⁻¹)
      (by linarith) one_pos (inv_pos.mpr hs)
    simp only [Real.rpow_one, neg_mul] at h
    refine (h.const_mul (s ^ (p - 1) * Real.exp (-s))).mono'
      (by fun_prop : Measurable _).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
    exact (hnorm hx hs).le
  · refine ((Real.GammaIntegral_convergent htp).const_mul (Real.Gamma t.re)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
    simp only [Function.uncurry_apply_pair]
    rw [setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ hnorm hx hs,
      integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ht (inv_pos.mpr hs), one_div,
      inv_inv, show t.re + p - 1 = (p - 1) + t.re by ring, Real.rpow_add hs]
    ring

/-- **The Mellin transform of `∫₀^∞ s^{p - 1} e^{-s - x/s} ds`.** For `0 < Re t` and
`0 < Re t + p`, the Mellin transform in `x` of the integral converges and equals
`Γ(t) Γ(t + p)`. -/
theorem hasMellin_integral_rpow_mul_exp_neg_sub_div {p : ℝ} {t : ℂ} (ht : 0 < t.re)
    (htp : 0 < t.re + p) :
    HasMellin (fun x : ℝ ↦ ((∫ s in Ioi 0, s ^ (p - 1) * Real.exp (-s - x / s) : ℝ) : ℂ)) t
      (Gamma t * Gamma (t + p)) := by
  have hK := integrable_uncurry_cpow_mul_rpow_mul_exp ht htp
  -- the Mellin integrand is the `s`-integral of the double integrand
  have houter (x : ℝ) : (x : ℂ) ^ (t - 1) •
      (((∫ s in Ioi 0, s ^ (p - 1) * Real.exp (-s - x / s) : ℝ) : ℂ)) =
        ∫ s in Ioi 0, (x : ℂ) ^ (t - 1) * ((s ^ (p - 1) * Real.exp (-s - x / s) : ℝ) : ℂ) := by
    rw [smul_eq_mul, ← integral_complex_ofReal, ← integral_const_mul]
  refine ⟨hK.integral_prod_left.congr (Eventually.of_forall fun x ↦ (houter x).symm), ?_⟩
  simp only [mellin]
  simp only [houter]
  -- Fubini, then Euler's integral in `x` and in `s`
  rw [integral_integral_swap hK, Gamma_eq_integral (show 0 < (t + p).re by simpa using htp),
    GammaIntegral, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
  rw [setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ cpow_mul_ofReal_rpow_mul_exp_eq p t x hs,
    integral_const_mul, integral_cpow_mul_exp_neg_mul_Ioi ht (inv_pos.mpr hs),
    show t + p - 1 = (p - 1 : ℂ) + t by ring, cpow_add _ _ (ofReal_ne_zero.mpr hs.ne')]
  push_cast
  rw [ofReal_cpow hs.le, one_div, inv_inv]
  push_cast
  ring

/-- On the line `Re s = δ - N`, with `0 < δ`, `0 < p` and `δ + p < 1`, the product
`Γ(s) Γ(s + p)` is bounded by `(1 + (Im s)²)⁻¹` times a constant multiple of `1 / (κ^N N!²)`,
where `κ = (1 - δ)(1 - δ - p)`. -/
private lemma norm_Gamma_mul_Gamma_add_le {p δ : ℝ} (hδ : 0 < δ) (hp : 0 < p) (hδp : δ + p < 1)
    (N : ℕ) (t : ℝ) :
    ‖Gamma (((δ - N : ℝ) : ℂ) + t * I) * Gamma (((δ - N : ℝ) : ℂ) + t * I + p)‖ ≤
      Real.Gamma (δ + 2) * Real.Gamma (δ + p) /
        (δ * ((1 - δ) * (1 - (δ + p))) ^ N * (N ! : ℝ) ^ 2) * (1 + t ^ 2)⁻¹ := by
  have h1 := norm_Gamma_mul_pow_mul_factorial_mul_le hδ (by linarith) N
    (s := ((δ - N : ℝ) : ℂ) + t * I) (by simp)
  have h2 := norm_Gamma_mul_pow_mul_factorial_le (a := δ + p) (by linarith) hδp N
    (s := ((δ - N : ℝ) : ℂ) + t * I + p) (by
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero,
        add_zero]
      ring)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add,
    add_zero] at h1
  have hD1 : 0 < (1 - δ) ^ N * (N ! : ℝ) * (δ * (1 + t ^ 2)) := by
    have : 0 < 1 - δ := by linarith
    positivity
  have hD2 : 0 < (1 - (δ + p)) ^ N * (N ! : ℝ) := by
    have : 0 < 1 - (δ + p) := by linarith
    positivity
  rw [norm_mul]
  calc ‖Gamma (((δ - N : ℝ) : ℂ) + t * I)‖ * ‖Gamma (((δ - N : ℝ) : ℂ) + t * I + p)‖
      ≤ Real.Gamma (δ + 2) / ((1 - δ) ^ N * (N ! : ℝ) * (δ * (1 + t ^ 2))) *
          (Real.Gamma (δ + p) / ((1 - (δ + p)) ^ N * (N ! : ℝ))) :=
        mul_le_mul ((le_div_iff₀ hD1).mpr h1) ((le_div_iff₀ hD2).mpr h2) (norm_nonneg _)
          (div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le hD1.le)
    _ = _ := by
        have : 0 < 1 - δ := by linarith
        have : 0 < 1 - (δ + p) := by linarith
        rw [mul_pow]
        field_simp

/-! ### Residues of `x^{-t} Γ(t) Γ(t + p)` -/

/-- The reflection formula at `c - k`: when `sin πc ≠ 0`,
`(-1)^k / k! · Γ(c - k) = (π / sin πc) / (k! Γ(1 - c + k))`. -/
private lemma neg_one_pow_div_factorial_mul_Gamma_sub_natCast {c : ℝ}
    (hc : Real.sin (π * c) ≠ 0) (k : ℕ) :
    (-1) ^ k / (k ! : ℝ) * Real.Gamma (c - k) =
      π / Real.sin (π * c) / (k ! * Real.Gamma (1 - c + k)) := by
  have hrefl := Real.Gamma_mul_Gamma_one_sub (c - k)
  rw [show π * (c - k) = π * c - k * π by ring, Real.sin_sub_nat_mul_pi,
    show 1 - (c - k) = 1 - c + k by ring] at hrefl
  have hsgn : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hG : Real.Gamma (1 - c + k) ≠ 0 := fun h ↦ by
    rw [h, mul_zero] at hrefl
    exact div_ne_zero Real.pi_ne_zero (mul_ne_zero hsgn hc) hrefl.symm
  rw [eq_div_iff (mul_ne_zero hsgn hc)] at hrefl
  set S := Real.sin (π * c)
  rw [← hrefl]
  field_simp

/-- The residue of `x^{-t} Γ(t) Γ(t + p)` at the pole `t = -k` of `Γ(t)`, written through the
reflection formula as the `k`th term of `(π / sin pπ) 𝐅(1 - p, x)`. -/
private lemma residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_natCast {p x : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hx : 0 < x) (k : ℕ) :
    Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * Gamma (z + p))) (-(k : ℂ)) =
      ((π / Real.sin (π * p) : ℝ) : ℂ) * ((x ^ k / (k ! * Real.Gamma (1 - p + k)) : ℝ) : ℂ) := by
  have hslit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hΓp : ∀ n : ℕ, -(k : ℂ) + p ≠ -n := by
    intro n h
    have h' := congrArg re h
    simp only [add_re, neg_re, natCast_re, ofReal_re] at h'
    exact Real.sub_natCast_ne_neg_natCast hp0 hp1 k n (by linarith)
  have hw : AnalyticAt ℂ (fun z ↦ (x : ℂ) ^ (-z) * Gamma (z + p)) (-(k : ℂ)) :=
    (analyticAt_const.cpow (by fun_prop) hslit).mul
      ((analyticAt_Gamma hΓp).comp (f := fun z : ℂ ↦ z + p) (x := -(k : ℂ)) (by fun_prop))
  have hfun : (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * Gamma (z + p))) =
      fun z ↦ Gamma z * ((x : ℂ) ^ (-z) * Gamma (z + p)) := funext fun z ↦ by ring
  rw [hfun, residue_Gamma_mul_neg_nat k hw, neg_neg, cpow_natCast,
    show -(k : ℂ) + p = ((p - k : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal]
  have hsin : Real.sin (π * p) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'
  have hreal : (-1) ^ k / (k ! : ℝ) * (x ^ k * Real.Gamma (p - k)) =
      π / Real.sin (π * p) * (x ^ k / (k ! * Real.Gamma (1 - p + k))) := by
    rw [mul_left_comm, neg_one_pow_div_factorial_mul_Gamma_sub_natCast hsin]
    ring
  exact_mod_cast hreal

/-- The residue of `x^{-t} Γ(t) Γ(t + p)` at the pole `t = -p - k` of `Γ(t + p)`, written through
the reflection formula as the `k`th term of `-(π / sin pπ) x^p 𝐅(1 + p, x)`. -/
private lemma residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_natCast {p x : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hx : 0 < x) (k : ℕ) :
    Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * Gamma (z + p))) (-(p : ℂ) - k) =
      -(((π / Real.sin (π * p) : ℝ) : ℂ) * (x : ℂ) ^ (p : ℂ)) *
        ((x ^ k / (k ! * Real.Gamma (1 + p + k)) : ℝ) : ℂ) := by
  have hslit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hΓ : ∀ n : ℕ, -(k : ℂ) - p ≠ -n := fun n h ↦
    Real.sub_natCast_ne_neg_natCast hp0 hp1 n k (by
      have := congrArg re h
      simp only [sub_re, neg_re, natCast_re, ofReal_re] at this
      linarith)
  have hw : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ (-(w - p)) * Gamma (w - p)) (-(k : ℂ)) :=
    (analyticAt_const.cpow (by fun_prop) hslit).mul
      ((analyticAt_Gamma hΓ).comp (f := fun w : ℂ ↦ w - p) (x := -(k : ℂ)) (by fun_prop))
  -- translate by `p`, moving the pole `-p - k` of `Γ(t + p)` to the pole `-k` of `Γ`
  have hfun : (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * Gamma (z + p))) =
      fun z ↦ Gamma (z + p) * ((x : ℂ) ^ (-(z + p - p)) * Gamma (z + p - p)) :=
    funext fun z ↦ by rw [add_sub_cancel_right]; ring
  rw [hfun, Contour.residue_comp_add_const
      (fun w : ℂ ↦ Gamma w * ((x : ℂ) ^ (-(w - p)) * Gamma (w - p))) (p : ℂ),
    show -(p : ℂ) - k + p = -(k : ℂ) by ring, residue_Gamma_mul_neg_nat k hw,
    show -(-(k : ℂ) - p) = p + k by ring, cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'),
    cpow_natCast, show -(k : ℂ) - p = ((-p - k : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal]
  have hsin : Real.sin (π * -p) ≠ 0 := by
    rw [mul_neg, Real.sin_neg, neg_ne_zero]
    exact (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])).ne'
  have hreal : (-1) ^ k / (k ! : ℝ) * (x ^ k * Real.Gamma (-p - k)) =
      -(π / Real.sin (π * p)) * (x ^ k / (k ! * Real.Gamma (1 + p + k))) := by
    rw [mul_left_comm, neg_one_pow_div_factorial_mul_Gamma_sub_natCast hsin, mul_neg,
      Real.sin_neg, sub_neg_eq_add]
    ring
  have hc : ((-1 : ℂ) ^ k / (k ! : ℂ)) * ((x : ℂ) ^ k * ((Real.Gamma (-p - k) : ℝ) : ℂ)) =
      -((π / Real.sin (π * p) : ℝ) : ℂ) * ((x ^ k / (k ! * Real.Gamma (1 + p + k)) : ℝ) : ℂ) := by
    exact_mod_cast hreal
  linear_combination (x : ℂ) ^ (p : ℂ) * hc

/-! ### Shifting the Mellin inversion contour -/

/-- In the half-plane `Re t ≥ (1 - p)/2 - N`, the poles of `Γ(t) Γ(t + p)` are the points `-k` and
`-p - k` with `k < N`; away from them the product is analytic. -/
private lemma analyticAt_Gamma_mul_Gamma_add {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {N : ℕ}
    {z : ℂ} (hz : (1 - p) / 2 - N ≤ z.re) (hA : ∀ k < N, z ≠ -(k : ℂ))
    (hB : ∀ k < N, z ≠ -(p : ℂ) - k) :
    AnalyticAt ℂ (fun w ↦ Gamma w * Gamma (w + p)) z := by
  have hlt {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (h : z.re = -(c + n)) : n < N := by
    have : (n : ℝ) < N := by linarith
    exact_mod_cast this
  have hΓ : ∀ n : ℕ, z ≠ -(n : ℂ) := fun n h ↦
    hA n (hlt le_rfl (by simp [h])) h
  have hΓp : ∀ n : ℕ, z + p ≠ -(n : ℂ) := fun n h ↦ by
    have hz' : z = -(p : ℂ) - n := by linear_combination h
    exact hB n (hlt hp0.le (by simp [hz']; ring)) hz'
  exact (analyticAt_Gamma hΓ).mul ((analyticAt_Gamma hΓp).comp (f := fun w : ℂ ↦ w + p)
    (by fun_prop))

/-- `Γ(t) Γ(t + p)` is integrable on the line `Re t = 1` for `0 ≤ p`. -/
private lemma verticalIntegrable_Gamma_mul_Gamma_add_one {p : ℝ} (hp : 0 ≤ p) :
    VerticalIntegrable (fun z ↦ Gamma z * Gamma (z + p)) 1 :=
  verticalIntegrable_Gamma_mul_Gamma_add
    (fun n h ↦ by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    (fun n h ↦ by rw [ofReal_re] at h; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- Shifting the Mellin inversion integral of `Γ(t) Γ(t + p)` from `Re t = 1` to
`Re t = (1 - p)/2 - N` crosses the poles `t = -k` and `t = -p - k` for `k < N`. -/
private lemma mellinInv_Gamma_mul_Gamma_add_eq {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) (N : ℕ) :
    mellinInv 1 (fun z ↦ Gamma z * Gamma (z + p)) x =
      mellinInv ((1 - p) / 2 - N) (fun z ↦ Gamma z * Gamma (z + p)) x +
        ∑ k ∈ Finset.range N,
          (((π / Real.sin (π * p) : ℝ) : ℂ) * ((x ^ k / (k ! * Real.Gamma (1 - p + k)) : ℝ) : ℂ) +
            -(((π / Real.sin (π * p) : ℝ) : ℂ) * (x : ℂ) ^ (p : ℂ)) *
              ((x ^ k / (k ! * Real.Gamma (1 + p + k)) : ℝ) : ℂ)) := by
  set δ : ℝ := (1 - p) / 2 with hδ_def
  have hδ0 : 0 < δ := by rw [hδ_def]; linarith
  have hδp : δ + p < 1 := by rw [hδ_def]; linarith
  set A : Finset ℂ := (Finset.range N).image fun k : ℕ ↦ -(k : ℂ)
  set B : Finset ℂ := (Finset.range N).image fun k : ℕ ↦ -(p : ℂ) - k
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr fun z hzA hzB ↦ ?_
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hzA
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hzB
    have h' := congrArg re hj
    simp only [sub_re, neg_re, ofReal_re, natCast_re] at h'
    exact Real.sub_natCast_ne_neg_natCast hp0 hp1 k j (by linarith)
  obtain ⟨C, -, hC⟩ := exists_norm_Gamma_mul_Gamma_add_le_div_pow_of_re_mem_Icc p (δ - N) 1 1
  have hshift := mellinInv_eq_mellinInv_add_sum_residue_of_norm_le (S := A ∪ B)
    (σ₀ := δ - N) (σ₁ := 1) (B := fun T ↦ C / T) (f := fun z ↦ Gamma z * Gamma (z + p))
    (by linarith) hx.le
    (fun z hz hzS ↦ analyticAt_Gamma_mul_Gamma_add hp0 hp1 hz.1
      (fun k hk h ↦ hzS (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨k, Finset.mem_range.mpr hk, h.symm⟩)))
      (fun k hk h ↦ hzS (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨k, Finset.mem_range.mpr hk, h.symm⟩))))
    (fun z _ ↦ (Meromorphic.Gamma z).mul ((Meromorphic.Gamma _).comp_analyticAt
      (g := fun w : ℂ ↦ w + p) (by fun_prop))) ?_
    (verticalIntegrable_Gamma_mul_Gamma_add
      (Real.sub_natCast_ne_neg_natCast hδ0 (by linarith) N)
      (fun n ↦ by
        rw [ofReal_re, sub_add_eq_add_sub]
        exact Real.sub_natCast_ne_neg_natCast (by linarith) hδp N n))
    (verticalIntegrable_Gamma_mul_Gamma_add_one hp0.le)
    (tendsto_const_nhds.div_atTop tendsto_id)
    (by
      filter_upwards [eventually_ge_atTop 1] with T hT u hu
      have key (z : ℂ) (hz : z.re = u) (him : |z.im| = T) : ‖Gamma z * Gamma (z + p)‖ ≤ C / T := by
        simpa [him] using hC z (hz ▸ hu) (him ▸ hT)
      have hT0 : (0 : ℝ) < T := by linarith
      exact ⟨key _ (by simp) (by simp [abs_of_pos hT0]),
        key _ (by simp) (by simp [abs_of_pos hT0])⟩)
  · rw [hshift, Finset.sum_union hAB, Finset.sum_image (fun _ _ _ _ h ↦ by simpa using h),
      Finset.sum_image (fun _ _ _ _ h ↦ by simpa using h), ← Finset.sum_add_distrib]
    simp only [residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_natCast hp0 hp1 hx,
      residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_natCast hp0 hp1 hx]
  · -- the poles `A ∪ B` lie inside the strip
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz <;> obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz <;>
      have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hk
    · simp only [neg_re, natCast_re, mem_Ioo]
      constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    · simp only [sub_re, neg_re, ofReal_re, natCast_re, mem_Ioo]
      constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The Mellin inversion integral of `Γ(t) Γ(t + p)` on the line `Re t = (1 - p)/2 - N` tends to
`0` as `N → ∞`. -/
private lemma tendsto_mellinInv_Gamma_mul_Gamma_add {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) :
    Tendsto (fun N : ℕ ↦ mellinInv ((1 - p) / 2 - N) (fun z ↦ Gamma z * Gamma (z + p)) x) atTop
      (𝓝 0) := by
  set δ : ℝ := (1 - p) / 2 with hδ_def
  have hδ0 : 0 < δ := by rw [hδ_def]; linarith
  have hδp : δ + p < 1 := by rw [hδ_def]; linarith
  set κ : ℝ := (1 - δ) * (1 - (δ + p))
  have hκ : 0 < κ := mul_pos (by linarith) (by linarith)
  set A : ℝ := Real.Gamma (δ + 2) * Real.Gamma (δ + p) / (2 * δ * x ^ δ)
  have : 0 ≤ A := by
    have := Real.Gamma_pos_of_pos (by linarith : 0 < δ + 2)
    have := Real.Gamma_pos_of_pos (by linarith : 0 < δ + p)
    positivity
  refine squeeze_zero_norm (a := fun N : ℕ ↦ A * ((x / κ) ^ N / N !)) (fun N ↦ ?_) ?_
  · set M : ℝ := Real.Gamma (δ + 2) * Real.Gamma (δ + p) / (δ * κ ^ N * (N ! : ℝ) ^ 2)
    have hint : ∫ t : ℝ, ‖Gamma (((δ - N : ℝ) : ℂ) + t * I) *
        Gamma (((δ - N : ℝ) : ℂ) + t * I + p)‖ ≤ M * π := by
      rw [← integral_univ_inv_one_add_sq, ← integral_const_mul]
      exact integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
        (integrable_inv_one_add_sq.const_mul M)
        (Eventually.of_forall fun t ↦ norm_Gamma_mul_Gamma_add_le hδ0 hp0 hδp N t)
    have hfac : (1 : ℝ) ≤ N ! := by exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos N)
    calc ‖mellinInv (δ - N) (fun z ↦ Gamma z * Gamma (z + p)) x‖
        ≤ x ^ (-(δ - N)) / (2 * π) * (M * π) :=
          (norm_mellinInv_le _ _ hx.le).trans (mul_le_mul_of_nonneg_left hint (by positivity))
      _ = A * ((x / κ) ^ N / N !) * (N ! : ℝ)⁻¹ := by
          rw [neg_sub, Real.rpow_sub hx, Real.rpow_natCast, div_pow]
          have : 0 < x ^ δ := Real.rpow_pos_of_pos hx δ
          simp only [M, A]
          field_simp
      _ ≤ A * ((x / κ) ^ N / N !) := by
          refine mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ hfac)
  · simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (x / κ)).const_mul A

/-! ### The series evaluation -/

/-- **The integral `∫₀^∞ s^{p - 1} e^{-s - x/s} ds` as a combination of `₀F₁` series.** For
`0 < p < 1` and `x > 0`,
`∫₀^∞ s^{p - 1} e^{-s - x/s} ds = (π / sin pπ) (𝐅(1 - p, x) - x^p 𝐅(1 + p, x))`, where
`𝐅(b, x) = ∑ₙ xⁿ / (n! Γ(b + n))` is the regularized `₀F₁`. In Bessel notation both sides are
`2 x^{p/2} K_p(2 √x)`, the right side being `(π / sin pπ) x^{p/2} (I_{-p}(2 √x) - I_p(2 √x))`. -/
theorem integral_rpow_mul_exp_neg_sub_div_Ioi {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) :
    ((∫ s in Ioi 0, s ^ (p - 1) * Real.exp (-s - x / s) : ℝ) : ℂ) =
      ((π / Real.sin (π * p) : ℝ) : ℂ) * (regularizedHGFun 0 {1 - (p : ℂ)} x -
        (x : ℂ) ^ (p : ℂ) * regularizedHGFun 0 {1 + (p : ℂ)} x) := by
  set G : ℝ → ℂ := fun y ↦ ((∫ s in Ioi 0, s ^ (p - 1) * Real.exp (-s - y / s) : ℝ) : ℂ)
  -- Mellin inversion on the line `Re t = 1`
  have hM (y : ℝ) : HasMellin G (((1 : ℝ) : ℂ) + y * I)
      (Gamma (((1 : ℝ) : ℂ) + y * I) * Gamma (((1 : ℝ) : ℂ) + y * I + p)) :=
    hasMellin_integral_rpow_mul_exp_neg_sub_div (by simp) (by simp; linarith)
  have hF1 := verticalIntegrable_Gamma_mul_Gamma_add_one hp0.le
  have hinv : G x = mellinInv 1 (fun z ↦ Gamma z * Gamma (z + p)) x := by
    have hcont : ContinuousAt G x := continuous_ofReal.continuousAt.comp
      ((continuousOn_integral_rpow_mul_exp_neg_sub_div p).continuousAt (Ioi_mem_nhds hx))
    rw [← mellinInv_mellin_eq 1 G hx (by simpa using (hM 0).1)
      (hF1.congr (Eventually.of_forall fun y ↦ (hM y).2.symm)) hcont, mellinInv, mellinInv]
    simp_rw [(hM _).2]
  -- the residue series
  have hA := (hasSum_ofReal_regularizedHGFun_zero_singleton (1 - p) x).mul_left
    ((π / Real.sin (π * p) : ℝ) : ℂ)
  have hB := (hasSum_ofReal_regularizedHGFun_zero_singleton (1 + p) x).mul_left
    (-(((π / Real.sin (π * p) : ℝ) : ℂ) * (x : ℂ) ^ (p : ℂ)))
  have hlim := (tendsto_mellinInv_Gamma_mul_Gamma_add hp0 hp1 hx).add
    (hA.add hB).tendsto_sum_nat
  rw [zero_add] at hlim
  have hG := tendsto_nhds_unique (tendsto_const_nhds.congr fun N ↦
    hinv.trans (mellinInv_Gamma_mul_Gamma_add_eq hp0 hp1 hx N)) (by
      simpa only [← Finset.sum_add_distrib] using hlim)
  refine hG.trans ?_
  rw [show (1 - (p : ℂ)) = ((1 - p : ℝ) : ℂ) by push_cast; ring,
    show (1 + (p : ℂ)) = ((1 + p : ℝ) : ℂ) by push_cast; ring]
  ring

end TauCeti
