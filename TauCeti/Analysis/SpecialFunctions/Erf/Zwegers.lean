/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Basic.Real.Sign
public import TauCeti.Analysis.SpecialFunctions.Erf.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Zwegers' error-function kernel

This file defines the two error-function kernels from which Zwegers builds the nonholomorphic
completions of Appell–Lerch sums and of indefinite theta series:

* the entire function `E(w) = 2 ∫₀ʷ exp (-π t²) dt` (`TauCeti.zwegersE`), the error function
  rescaled so that its derivative is `2 exp (-π w²)`;
* the tail `β(t) = ∫_t^∞ u^{-1/2} exp (-π u) du` (`TauCeti.zwegersBeta`).

On the real line they are the error function and its complement in another normalization:
`E(x) = erf (√π x)` and `β(t) = erfc (√(π t))`, so that `E(x) = sgn(x) (1 - β(x²))`.
The completion of a holomorphic `q`-series replaces the sign of a summation index by `E` of a
real argument, and the tail `β` measures the difference; the Gaussian decay of `β` makes the
completed series converge.

The function `E` is defined as Mathlib's `Complex.wedgeIntegral` of the entire Gaussian
`exp (-π t²)` from `0` to `w` (the primitive of Morera's theorem, due to Jauslin, Kontorovich and
Nash). Since the Gaussian is entire, `E` is entire with `E' = 2 exp (-π w²)`, and it is the unique
such function vanishing at `0` (`TauCeti.eq_zwegersE_of_hasDerivAt`); its oddness and its real
restriction follow from this uniqueness.

## Main results

* `TauCeti.hasDerivAt_zwegersE`: `E'(w) = 2 exp (-π w²)` for every complex `w`.
* `TauCeti.zwegersE_neg`: `E` is odd.
* `TauCeti.zwegersE_ofReal`: `E(x) = erf (√π x)` for real `x`.
* `TauCeti.zwegersBeta_eq_erfc`: `β(t) = erfc (√(π t))`.
* `TauCeti.zwegersE_ofReal_eq_sign_mul`: `E(x) = sgn(x) (1 - β(x²))` for real `x`.
* `TauCeti.zwegersBeta_le_exp_div`: for `x > 0`, `β(x) ≤ exp (-π x) / (π √x)`.

## References

* S. Zwegers, *Mock theta functions*, PhD thesis, Utrecht University, 2002, Definition 1.6,
  Lemma 1.7 and the proof of Lemma 1.8.
-/

public section

noncomputable section

open MeasureTheory Set Real

namespace TauCeti

/-! ### The entire kernel `E` -/

/-- Zwegers' error function `E(w) = 2 ∫₀ʷ exp (-π t²) dt`, the integral taken along the wedge
from `0` to `w` (horizontally to `Re w`, then vertically). Since the integrand is entire, this is
the primitive of `2 exp (-π t²)` vanishing at `0`; on the real line it is `erf (√π x)`
(`TauCeti.zwegersE_ofReal`). -/
def zwegersE (w : ℂ) : ℂ :=
  2 * Complex.wedgeIntegral 0 w fun t => Complex.exp (-π * t ^ 2)

/-- The defining wedge integral of `TauCeti.zwegersE`. -/
theorem zwegersE_def (w : ℂ) :
    zwegersE w = 2 * Complex.wedgeIntegral 0 w fun t => Complex.exp (-π * t ^ 2) := (rfl)

/-- The kernel `E` vanishes at the origin. -/
@[simp]
theorem zwegersE_zero : zwegersE 0 = 0 := by
  simp [zwegersE_def, Complex.wedgeIntegral]

/-- The derivative of `E` is `2 exp (-π w²)`. -/
theorem hasDerivAt_zwegersE (w : ℂ) :
    HasDerivAt zwegersE (2 * Complex.exp (-π * w ^ 2)) w := by
  have hf : Differentiable ℂ fun t : ℂ => Complex.exp (-π * t ^ 2) := by fun_prop
  have h : HasDerivAt (fun z => Complex.wedgeIntegral 0 z fun t => Complex.exp (-π * t ^ 2))
      (Complex.exp (-π * w ^ 2)) w :=
    (hf.differentiableOn (s := Metric.ball 0 (‖w‖ + 1))).isConservativeOn.hasDerivAt_wedgeIntegral
      hf.continuous.continuousOn (by simp)
  exact h.const_mul 2

/-- The derivative of `E`, in `deriv` form. -/
@[simp]
theorem deriv_zwegersE : deriv zwegersE = fun w => 2 * Complex.exp (-π * w ^ 2) :=
  funext fun w => (hasDerivAt_zwegersE w).deriv

/-- The kernel `E` is entire. -/
@[fun_prop]
theorem differentiable_zwegersE : Differentiable ℂ zwegersE := fun w =>
  (hasDerivAt_zwegersE w).differentiableAt

/-- The kernel `E` is continuous. -/
@[fun_prop]
theorem continuous_zwegersE : Continuous zwegersE := differentiable_zwegersE.continuous

/-- `E` is the unique function on `ℂ` with derivative `2 exp (-π w²)` vanishing at `0`. -/
theorem eq_zwegersE_of_hasDerivAt {f : ℂ → ℂ}
    (hf : ∀ w, HasDerivAt f (2 * Complex.exp (-π * w ^ 2)) w) (h0 : f 0 = 0) :
    f = zwegersE := by
  have hd (w : ℂ) : HasDerivAt (f - zwegersE) 0 w := by
    simpa using (hf w).sub (hasDerivAt_zwegersE w)
  funext w
  have h := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt) (fun w => (hd w).deriv)
    w 0
  simpa [h0, sub_eq_zero] using h

/-- The kernel `E` is odd. -/
@[simp]
theorem zwegersE_neg (w : ℂ) : zwegersE (-w) = -zwegersE w := by
  have hd (w : ℂ) : HasDerivAt (fun w => -zwegersE (-w)) (2 * Complex.exp (-π * w ^ 2)) w := by
    have h : HasDerivAt (fun w => -zwegersE (-w)) (-(2 * Complex.exp (-π * (-w) ^ 2) * -1)) w :=
      ((hasDerivAt_zwegersE (-w)).comp w (hasDerivAt_neg w)).neg
    rwa [neg_sq, mul_neg_one, neg_neg] at h
  rw [← congrFun (eq_zwegersE_of_hasDerivAt hd (by simp)) w, neg_neg]

/-- On the real line `E` is the error function: `E(x) = erf (√π x)`. -/
theorem zwegersE_ofReal (x : ℝ) : zwegersE x = (Real.erf (√π * x) : ℂ) := by
  have hd (y : ℝ) : HasDerivAt (fun y : ℝ => zwegersE y - (Real.erf (√π * y) : ℂ)) 0 y := by
    have hE := (hasDerivAt_zwegersE y).comp_ofReal
    have hR : HasDerivAt (fun y : ℝ => (Real.erf (√π * y) : ℂ))
        ((2 / √π * rexp (-(√π * y) ^ 2) * (√π * 1) : ℝ) : ℂ) y :=
      ((Real.hasDerivAt_erf (√π * y)).comp y ((hasDerivAt_id y).const_mul √π)).ofReal_comp
    have hval : ((2 / √π * rexp (-(√π * y) ^ 2) * (√π * 1) : ℝ) : ℂ) =
        2 * Complex.exp (-π * y ^ 2) := by
      have hπ0 : √π ≠ 0 := by positivity
      have h : 2 / √π * rexp (-(√π * y) ^ 2) * (√π * 1) = 2 * rexp (-π * y ^ 2) := by
        rw [mul_pow, Real.sq_sqrt pi_pos.le]
        field_simp
      rw [h]
      push_cast
      ring_nf
    have h := hE.sub hR
    rwa [hval, sub_self] at h
  have h := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv)
    x 0
  simpa [sub_eq_zero] using h

/-- On the real line `E` takes values in the open unit interval. -/
theorem norm_zwegersE_ofReal_lt_one (x : ℝ) : ‖zwegersE x‖ < 1 := by
  rw [zwegersE_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_erf_lt_one _

/-- For real `x > 0`, the real part of `E(x)` is positive. -/
theorem zwegersE_ofReal_re_pos {x : ℝ} (hx : 0 < x) : 0 < (zwegersE x).re := by
  rw [zwegersE_ofReal, Complex.ofReal_re]
  exact Real.erf_pos (by positivity)

/-- For real `x < 0`, the real part of `E(x)` is negative. -/
theorem zwegersE_ofReal_re_neg {x : ℝ} (hx : x < 0) : (zwegersE x).re < 0 := by
  rw [zwegersE_ofReal, Complex.ofReal_re, ← Real.erf_zero]
  exact Real.strictMono_erf (mul_neg_of_pos_of_neg (Real.sqrt_pos.2 pi_pos) hx)

/-- On the real line the real part of `E` is less than `1`. -/
theorem zwegersE_ofReal_re_lt_one (x : ℝ) : (zwegersE x).re < 1 := by
  rw [zwegersE_ofReal, Complex.ofReal_re]
  exact Real.erf_lt_one _

/-! ### The tail `β` -/

/-- Zwegers' tail `β(t) = ∫_t^∞ u^{-1/2} exp (-π u) du`. It equals `erfc (√(π t))`
(`TauCeti.zwegersBeta_eq_erfc`); for `t < 0` the integrand vanishes on `(t, 0]` and the value is
`β(0) = 1`. -/
def zwegersBeta (t : ℝ) : ℝ :=
  ∫ u in Ioi t, u ^ (-1 / 2 : ℝ) * rexp (-π * u)

/-- The defining tail integral of `TauCeti.zwegersBeta`. -/
theorem zwegersBeta_def (t : ℝ) :
    zwegersBeta t = ∫ u in Ioi t, u ^ (-1 / 2 : ℝ) * rexp (-π * u) := (rfl)

/-- The substitution `u = s² / π` turns the tail integral into a Gaussian tail. -/
private theorem zwegersBeta_eq_erfc_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    zwegersBeta t = Real.erfc √(π * t) := by
  set a := √(π * t)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = π * t := Real.sq_sqrt (by positivity)
  have himage : (fun s : ℝ => s ^ 2 / π) '' Ioi a = Ioi t := by
    ext u
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [mem_Ioi] at hs ⊢
      rw [lt_div_iff₀ pi_pos]
      nlinarith
    · intro hu
      rw [mem_Ioi] at hu
      refine ⟨√(π * u), Real.sqrt_lt_sqrt (by positivity) (by nlinarith [pi_pos]), ?_⟩
      dsimp only
      rw [Real.sq_sqrt (by nlinarith [pi_pos])]
      field_simp
  have hderiv (s : ℝ) (_ : s ∈ Ioi a) :
      HasDerivWithinAt (fun s : ℝ => s ^ 2 / π) (2 * s / π) (Ioi a) s := by
    simpa using ((hasDerivAt_pow 2 s).div_const π).hasDerivWithinAt
  have hinj : InjOn (fun s : ℝ => s ^ 2 / π) (Ioi a) := by
    intro s hs r hr hsr
    have hs0 : 0 ≤ s := ha0.trans (le_of_lt hs)
    have hr0 : 0 ≤ r := ha0.trans (le_of_lt hr)
    have : s ^ 2 = r ^ 2 := by simpa [div_left_inj₀ pi_pos.ne'] using hsr
    exact (pow_left_inj₀ hs0 hr0 two_ne_zero).1 this
  rw [zwegersBeta_def, ← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    hderiv hinj, Real.erfc_eq_integral_Ioi, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := ha0.trans_lt hs
  have hπ : √π ≠ 0 := by positivity
  have hroot : (s ^ 2 / π) ^ (-1 / 2 : ℝ) = √π / s := by
    rw [← Real.inv_sqrt_eq_rpow, Real.sqrt_div (sq_nonneg s), Real.sqrt_sq hs0.le, inv_div]
  simp only [smul_eq_mul, hroot, abs_of_pos (by positivity : 0 < 2 * s / π)]
  rw [show -π * (s ^ 2 / π) = -s ^ 2 by field_simp]
  field_simp
  exact Real.sq_sqrt pi_pos.le

/-- The tail is the complementary error function: `β(t) = erfc (√(π t))`. For `t < 0` both sides
equal `1`. -/
theorem zwegersBeta_eq_erfc (t : ℝ) : zwegersBeta t = Real.erfc √(π * t) := by
  rcases le_or_gt 0 t with ht | ht
  · exact zwegersBeta_eq_erfc_of_nonneg ht
  have h0 := zwegersBeta_eq_erfc_of_nonneg le_rfl
  rw [mul_zero, Real.sqrt_zero] at h0
  rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith [pi_pos]), ← h0, zwegersBeta_def, zwegersBeta_def]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi ht.le) fun u hu => ?_
  rw [← Real.inv_sqrt_eq_rpow, Real.sqrt_eq_zero_of_nonpos (not_lt.1 hu.2), inv_zero, zero_mul]

/-- The tail at the origin is the full Gaussian integral: `β(0) = 1`. -/
@[simp]
theorem zwegersBeta_zero : zwegersBeta 0 = 1 := by
  simp [zwegersBeta_eq_erfc]

/-- The tail is positive. -/
theorem zwegersBeta_pos (t : ℝ) : 0 < zwegersBeta t := by
  rw [zwegersBeta_eq_erfc]
  exact Real.erfc_pos _

/-- The tail is at most `β(0) = 1`. -/
theorem zwegersBeta_le_one (t : ℝ) : zwegersBeta t ≤ 1 := by
  rw [zwegersBeta_eq_erfc, ← Real.erfc_zero]
  exact Real.strictAnti_erfc.antitone (Real.sqrt_nonneg _)

/-- The derivative of the tail is minus its integrand, away from `0`. For `t < 0` both sides
vanish: `β` is constant there and `t ^ (-1/2) = 0` for Mathlib's power of a negative base. -/
theorem hasDerivAt_zwegersBeta {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt zwegersBeta (-(t ^ (-1 / 2 : ℝ) * rexp (-π * t))) t := by
  rw [show zwegersBeta = fun t => Real.erfc √(π * t) from funext zwegersBeta_eq_erfc]
  have h : HasDerivAt (fun t => Real.erfc √(π * t))
      (-(2 / √π * rexp (-√(π * t) ^ 2)) * (1 / (2 * √(π * t)) * (π * 1))) t :=
    (Real.hasDerivAt_erfc _).comp t
      ((Real.hasDerivAt_sqrt (mul_ne_zero pi_pos.ne' ht)).comp t ((hasDerivAt_id t).const_mul π))
  convert h using 1
  rcases ht.lt_or_gt with ht | ht
  · rw [Real.sqrt_eq_zero_of_nonpos (mul_neg_of_pos_of_neg pi_pos ht).le, ← Real.inv_sqrt_eq_rpow,
      Real.sqrt_eq_zero_of_nonpos ht.le]
    simp
  have hπt : 0 < π * t := by positivity
  have hπ : √π ≠ 0 := by positivity
  have ht' : √t ≠ 0 := by positivity
  rw [Real.sq_sqrt hπt.le, ← Real.inv_sqrt_eq_rpow, Real.sqrt_mul pi_pos.le]
  field_simp
  rw [Real.sq_sqrt pi_pos.le]

/-- **Gaussian tail bound**: for `x > 0`, `β(x) ≤ exp (-π x) / (π √x)`. -/
theorem zwegersBeta_le_exp_div {x : ℝ} (hx : 0 < x) :
    zwegersBeta x ≤ rexp (-π * x) / (π * √x) := by
  have hexp : IntegrableOn (fun u : ℝ => rexp (-π * u)) (Ioi x) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.2 pi_pos) x
  have hbound (u : ℝ) (hu : u ∈ Ioi x) :
      u ^ (-1 / 2 : ℝ) * rexp (-π * u) ≤ x ^ (-1 / 2 : ℝ) * rexp (-π * u) :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx (le_of_lt hu) (by norm_num))
      (exp_pos _).le
  have hint : IntegrableOn (fun u : ℝ => u ^ (-1 / 2 : ℝ) * rexp (-π * u)) (Ioi x) := by
    refine (hexp.const_mul (x ^ (-1 / 2 : ℝ))).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl (hx.trans hu).ne')).mul
        (by fun_prop)).continuousWithinAt
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      rw [Real.norm_of_nonneg (by have := hx.trans hu; positivity)]
      exact hbound u hu
  calc zwegersBeta x ≤ ∫ u in Ioi x, x ^ (-1 / 2 : ℝ) * rexp (-π * u) :=
        setIntegral_mono_on hint (hexp.const_mul _) measurableSet_Ioi hbound
    _ = rexp (-π * x) / (π * √x) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.2 pi_pos),
        ← Real.inv_sqrt_eq_rpow]
      have hπ : π ≠ 0 := pi_pos.ne'
      have hx' : √x ≠ 0 := by positivity
      field_simp

/-- On the real line `E` and `β` are related by `E(x) = sgn(x) (1 - β(x²))`, with `sgn 0 = 0`. -/
theorem zwegersE_ofReal_eq_sign_mul (x : ℝ) :
    zwegersE x = (Real.sign x * (1 - zwegersBeta (x ^ 2)) : ℝ) := by
  rw [zwegersE_ofReal, zwegersBeta_eq_erfc, Real.erfc_def, Real.sqrt_mul pi_pos.le,
    Real.sqrt_sq_eq_abs, sub_sub_cancel]
  congr 1
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx, mul_neg, Real.erf_neg]
    ring
  · simp
  · rw [Real.sign_of_pos hx, abs_of_pos hx, one_mul]

end TauCeti
