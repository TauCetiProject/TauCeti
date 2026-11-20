/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.MellinTransform.Convolution
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical

/-!
# Macdonald's integral and the Mellin–Barnes integral of `Γ(t) Γ(t + a)`

For a complex parameter `a` and `x > 0`, the integral

`∫₀^∞ s^{a - 1} e^{-s - x/s} ds`

converges absolutely, since the factor `e^{-x/s}` vanishes to every order at `s = 0`. It is
`2 x^{a/2} K_a(2 √x)`, with `K_a` Macdonald's function, the modified Bessel function of the second
kind (DLMF 10.32.10); we call it Macdonald's integral, but no Bessel function is defined or needed
here. As a function of `x` it is the multiplicative convolution of `s ↦ s^a e^{-s}` with
`s ↦ e^{-s}`, so by Fubini its Mellin transform is a product of two Gamma integrals:

`∫₀^∞ x^{t - 1} ∫₀^∞ s^{a - 1} e^{-s - x/s} ds dx = Γ(t) Γ(t + a)`
for `Re t > 0` and `Re (t + a) > 0`.

The product `Γ(t) Γ(t + a)` is integrable on every vertical line avoiding the poles of both
factors, so Mellin inversion gives the Mellin–Barnes integral of Macdonald's integral (compare
DLMF 10.32.13): for every `σ > max(0, -Re a)` and `x > 0`,

`(1 / 2π) ∫ x^{-(σ + i y)} Γ(σ + i y) Γ(σ + i y + a) dy = ∫₀^∞ s^{a - 1} e^{-s - x/s} ds`.

The substitution `s = (x/2) e^u` gives the hyperbolic form (DLMF 10.32.9–10.32.10)

`∫₀^∞ e^{-x cosh u} cosh(a u) du = ½ (x/2)^{-a} ∫₀^∞ s^{a - 1} e^{-s - x²/(4s)} ds`,

so the integral on the left, which appears in the integral representation of the generalized Airy
functions of Swanson and Headley (DLMF 9.13), is a Mellin–Barnes integral of `Γ(t) Γ(t + a)`
evaluated at `x²/4`. Moving the line of integration to the left across the poles of the Gamma
factors is what relates it to the power series of those functions.

## Main results

* `Complex.integrableOn_cpow_mul_exp_neg_sub_div`: Macdonald's integrand is integrable on
  `(0, ∞)` for every complex `a` and every `x > 0`.
* `Complex.continuousOn_integral_cpow_mul_exp_neg_sub_div`: Macdonald's integral is continuous
  in `x > 0`.
* `Complex.hasMellin_integral_cpow_mul_exp_neg_sub_div`: its Mellin transform converges at every
  `t` with `Re t > 0` and `Re (t + a) > 0` and equals `Γ(t) Γ(t + a)` there.
* `Complex.verticalIntegrable_Gamma_mul_Gamma_add`: `t ↦ Γ(t) Γ(t + a)` is integrable on every
  vertical line `Re t = σ` with neither `σ` nor `σ + Re a` a nonpositive integer.
* `Complex.mellinInv_Gamma_mul_Gamma_add`: Mellin inversion of `Γ(t) Γ(t + a)` on a vertical line
  `Re t = σ` with `σ > 0` and `σ + Re a > 0` is Macdonald's integral.
* `Complex.integrableOn_exp_neg_mul_cosh_mul_cosh` and `Complex.integral_exp_neg_mul_cosh_mul_cosh`:
  the hyperbolic form of Macdonald's integral.

## References

* NIST Digital Library of Mathematical Functions, equations 10.32.9, 10.32.10 and 10.32.13.
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, §6.22.
-/

public section

open Real Set MeasureTheory Filter
open Complex hiding exp continuous_exp
open scoped Nat

namespace Complex

/-- For `0 < c ≤ x`, Macdonald's integrand is dominated by `n! c⁻ⁿ e^{-s} s^{Re a + n - 1}`,
uniformly in `x`. -/
private lemma norm_cpow_mul_exp_neg_sub_div_le (a : ℂ) {c x s : ℝ} (hc : 0 < c) (hcx : c ≤ x)
    (hs : 0 < s) (n : ℕ) :
    ‖(s : ℂ) ^ (a - 1) * (Real.exp (-s - x / s) : ℂ)‖ ≤
      n ! / c ^ n * (Real.exp (-s) * s ^ (a.re + n - 1)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hs, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, sub_re, one_re]
  have hexp : Real.exp (-s - x / s) ≤ Real.exp (-s) * (n ! / c ^ n * s ^ n) := by
    rw [sub_eq_add_neg, Real.exp_add]
    gcongr
    calc Real.exp (-(x / s)) ≤ Real.exp (-(c / s)) := Real.exp_le_exp.mpr (neg_le_neg (by gcongr))
      _ ≤ n ! / (c / s) ^ n := TauCeti.exp_neg_le_factorial_div_pow (div_pos hc hs) n
      _ = n ! / c ^ n * s ^ n := by rw [div_pow]; field_simp
  have hpow : s ^ (a.re + n - 1) = s ^ (a.re - 1) * s ^ n := by
    rw [show a.re + n - 1 = (a.re - 1) + n by ring, Real.rpow_add hs, Real.rpow_natCast]
  calc s ^ (a.re - 1) * Real.exp (-s - x / s)
      ≤ s ^ (a.re - 1) * (Real.exp (-s) * (n ! / c ^ n * s ^ n)) := by gcongr
    _ = n ! / c ^ n * (Real.exp (-s) * s ^ (a.re + n - 1)) := by rw [hpow]; ring

/-- Macdonald's integrand is continuous on `(0, ∞)`. -/
private lemma continuousOn_cpow_mul_exp_neg_sub_div (a : ℂ) (x : ℝ) :
    ContinuousOn (fun s : ℝ ↦ (s : ℂ) ^ (a - 1) * (Real.exp (-s - x / s) : ℂ)) (Ioi 0) := by
  intro s hs
  have hs' : s ≠ 0 := (mem_Ioi.mp hs).ne'
  refine ContinuousAt.continuousWithinAt ?_
  refine (continuousAt_ofReal_cpow_const s (a - 1) (Or.inr hs')).mul ?_
  exact continuous_ofReal.continuousAt.comp (by fun_prop (disch := exact hs'))

/-- The dominating function `n! c⁻ⁿ e^{-s} s^{Re a + n - 1}` is integrable on `(0, ∞)` once
`Re a + n > 0`. -/
private lemma integrableOn_bound (a : ℂ) (c : ℝ) {n : ℕ} (hn : -a.re < n) :
    IntegrableOn (fun s : ℝ ↦ n ! / c ^ n * (Real.exp (-s) * s ^ (a.re + n - 1))) (Ioi 0) :=
  (Real.GammaIntegral_convergent (by linarith)).const_mul _

/-- **Macdonald's integrand is integrable.** For every complex `a` and every `x > 0`, the
function `s ↦ s^{a - 1} e^{-s - x/s}` is integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_exp_neg_sub_div (a : ℂ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s : ℝ ↦ (s : ℂ) ^ (a - 1) * (Real.exp (-s - x / s) : ℂ)) (Ioi 0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-a.re)
  refine (integrableOn_bound a x hn).mono'
    ((continuousOn_cpow_mul_exp_neg_sub_div a x).aestronglyMeasurable measurableSet_Ioi) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun s hs ↦ norm_cpow_mul_exp_neg_sub_div_le a hx le_rfl hs n)

/-- **Macdonald's integral is continuous.** For every complex `a`, the function
`x ↦ ∫₀^∞ s^{a - 1} e^{-s - x/s} ds` is continuous on `(0, ∞)`. -/
theorem continuousOn_integral_cpow_mul_exp_neg_sub_div (a : ℂ) :
    ContinuousOn (fun x : ℝ ↦ ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * (Real.exp (-s - x / s) : ℂ))
      (Ioi 0) := by
  intro x₀ hx₀
  have hx₀' : 0 < x₀ / 2 := half_pos hx₀
  obtain ⟨n, hn⟩ := exists_nat_gt (-a.re)
  refine (continuousAt_of_dominated (Eventually.of_forall fun x ↦
      (continuousOn_cpow_mul_exp_neg_sub_div a x).aestronglyMeasurable measurableSet_Ioi) ?_
      (integrableOn_bound a (x₀ / 2) hn) ?_).continuousWithinAt
  · filter_upwards [lt_mem_nhds (half_lt_self hx₀)] with x hx
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun s hs ↦ norm_cpow_mul_exp_neg_sub_div_le a hx₀' hx.le hs n)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs ↦ ?_)
    have hs' : s ≠ 0 := (mem_Ioi.mp hs).ne'
    exact continuous_const.continuousAt.mul
      (continuous_ofReal.continuousAt.comp (by fun_prop (disch := exact hs')))

/-- **The Mellin transform of Macdonald's integral.** For `Re t > 0` and `Re (t + a) > 0` the
Mellin transform of `x ↦ ∫₀^∞ s^{a - 1} e^{-s - x/s} ds` converges absolutely at `t` and equals
`Γ(t) Γ(t + a)`. -/
theorem hasMellin_integral_cpow_mul_exp_neg_sub_div {a t : ℂ} (ht : 0 < t.re)
    (hta : 0 < (t + a).re) :
    HasMellin (fun x : ℝ ↦ ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * (Real.exp (-s - x / s) : ℂ)) t
      (Gamma t * Gamma (t + a)) := by
  have he := TauCeti.hasMellin_exp_neg ht
  have hf : HasMellin (fun y : ℝ ↦ (y : ℂ) ^ a • (Real.exp (-y) : ℂ)) t (Gamma (t + a)) :=
    ⟨MellinConvergent.cpow_smul.mpr (TauCeti.hasMellin_exp_neg hta).1,
      by rw [mellin_cpow_smul, (TauCeti.hasMellin_exp_neg hta).2]⟩
  have h := TauCeti.hasMellin_integral_mul_div hf.1 he.1
  rw [hf.2, he.2, mul_comm] at h
  convert h using 2 with x
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr (mem_Ioi.mp hs).ne'
  rw [smul_eq_mul, cpow_sub _ _ hs', cpow_one, sub_eq_add_neg, Real.exp_add, ofReal_mul,
    ← neg_div]
  ring

/-- On every vertical line `Re t = σ` with neither `σ` nor `σ + Re a` a nonpositive integer, the
product `Γ(t) Γ(t + a)` is integrable. -/
theorem verticalIntegrable_Gamma_mul_Gamma_add {a : ℂ} {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n)
    (hσa : ∀ n : ℕ, σ + a.re ≠ -n) :
    VerticalIntegrable (fun t ↦ Gamma t * Gamma (t + a)) σ :=
  (verticalIntegrable_Gamma hσ).mul_Gamma_comp hσa (by fun_prop) fun y ↦ by simp

/-- **The Mellin–Barnes integral of Macdonald's integral.** On every vertical line `Re t = σ` with
`σ > 0` and `σ + Re a > 0`, Mellin inversion of `Γ(t) Γ(t + a)` gives, for `x > 0`,
`(1 / 2π) ∫ x^{-(σ + i y)} Γ(σ + i y) Γ(σ + i y + a) dy = ∫₀^∞ s^{a - 1} e^{-s - x/s} ds`. -/
theorem mellinInv_Gamma_mul_Gamma_add {a : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσa : 0 < σ + a.re) {x : ℝ}
    (hx : 0 < x) :
    mellinInv σ (fun t ↦ Gamma t * Gamma (t + a)) x =
      ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * (Real.exp (-s - x / s) : ℂ) := by
  set F : ℝ → ℂ := fun x ↦ ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * (Real.exp (-s - x / s) : ℂ)
  have hM (y : ℝ) : HasMellin F (σ + y * I) (Gamma (σ + y * I) * Gamma (σ + y * I + a)) :=
    hasMellin_integral_cpow_mul_exp_neg_sub_div (by simpa using hσ) (by simpa using hσa)
  have hline (y : ℝ) : Gamma (σ + y * I) * Gamma (σ + y * I + a) = mellin F (σ + y * I) :=
    (hM y).2.symm
  have hint : VerticalIntegrable (mellin F) σ :=
    (verticalIntegrable_Gamma_mul_Gamma_add (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])).congr (Eventually.of_forall hline)
  have hconv : MellinConvergent F σ := by simpa using (hM 0).1
  rw [mellinInv]
  simp_rw [hline]
  rw [← mellinInv, mellinInv_mellin_eq σ F hx hconv hint
    ((continuousOn_integral_cpow_mul_exp_neg_sub_div a).continuousAt (Ioi_mem_nhds hx))]

/-- Under `s = (x/2) e^{-u}`, the logarithmic-coordinate Mellin integrand of `s ↦ e^{-s - x²/(4s)}`
at `a` becomes `(x/2)^a e^{-a u} e^{-x cosh u}`. -/
private lemma cexp_smul_exp_neg_sub_sq_div {x : ℝ} (hx : 0 < x) (a : ℂ) (u : ℝ) :
    cexp (-a * ↑(u - Real.log (x / 2))) •
        (Real.exp (-Real.exp (-(u - Real.log (x / 2))) -
          x ^ 2 / 4 / Real.exp (-(u - Real.log (x / 2)))) : ℂ) =
      ((x / 2 : ℝ) : ℂ) ^ a * (cexp (-a * u) * (Real.exp (-(x * Real.cosh u)) : ℂ)) := by
  have hb : 0 < x / 2 := half_pos hx
  have hreal : -Real.exp (-(u - Real.log (x / 2))) -
      x ^ 2 / 4 / Real.exp (-(u - Real.log (x / 2))) = -(x * Real.cosh u) := by
    rw [neg_sub, Real.exp_sub, Real.exp_log hb, Real.cosh_eq, Real.exp_neg]
    field_simp
    ring
  rw [hreal, smul_eq_mul, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hb.ne'), ← ofReal_log hb.le,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- In logarithmic coordinates shifted by `log (x/2)`, Macdonald's integral at `x²/4` is
`(x/2)^a ∫_ℝ e^{-a u} e^{-x cosh u} du`, the integrand being integrable on `ℝ`. -/
private lemma integrable_and_integral_cexp_mul_exp_neg_mul_cosh {x : ℝ} (hx : 0 < x) (a : ℂ) :
    Integrable (fun u : ℝ ↦ cexp (-a * u) * (Real.exp (-(x * Real.cosh u)) : ℂ)) ∧
      ∫ u : ℝ, cexp (-a * u) * (Real.exp (-(x * Real.cosh u)) : ℂ) =
        (((x / 2 : ℝ) : ℂ) ^ a)⁻¹ *
          ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * (Real.exp (-s - x ^ 2 / 4 / s) : ℂ) := by
  set g : ℝ → ℂ := fun s ↦ (Real.exp (-s - x ^ 2 / 4 / s) : ℂ)
  set b : ℂ := ((x / 2 : ℝ) : ℂ) ^ a
  have hb : b ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr (half_pos hx).ne'))
  have hsub (u : ℝ) : cexp (-a * ↑(u - Real.log (x / 2))) • g (Real.exp (-(u - Real.log (x / 2))))
      = b * (cexp (-a * u) * (Real.exp (-(x * Real.cosh u)) : ℂ)) :=
    cexp_smul_exp_neg_sub_sq_div hx a u
  have hconv : MellinConvergent g a := by
    simpa only [MellinConvergent, smul_eq_mul] using
      integrableOn_cpow_mul_exp_neg_sub_div a (x := x ^ 2 / 4) (by positivity)
  refine ⟨?_, ?_⟩
  · have h : Integrable fun u : ℝ ↦ b⁻¹ * (cexp (-a * ↑(u - Real.log (x / 2))) •
        g (Real.exp (-(u - Real.log (x / 2))))) :=
      (((TauCeti.mellinConvergent_iff_integrable_exp_smul g a).mp hconv).comp_sub_right
        (Real.log (x / 2))).const_mul _
    simpa only [hsub, inv_mul_cancel_left₀ hb] using h
  · have h := TauCeti.mellin_eq_integral_exp_smul g a
    rw [← integral_sub_right_eq_self _ (Real.log (x / 2))] at h
    simp only [hsub, integral_const_mul, mellin, smul_eq_mul] at h
    rw [h, inv_mul_cancel_left₀ hb]

/-- Twice the even part of `u ↦ e^{-a u} e^{-x cosh u}` is `2 e^{-x cosh u} cosh(a u)`. -/
private lemma cexp_mul_exp_neg_mul_cosh_even (a : ℂ) (x u : ℝ) :
    cexp (-a * ↑(-u)) * (Real.exp (-(x * Real.cosh (-u))) : ℂ) +
        cexp (-a * u) * (Real.exp (-(x * Real.cosh u)) : ℂ) =
      2 * ((Real.exp (-(x * Real.cosh u)) : ℂ) * Complex.cosh (a * u)) := by
  simp only [Real.cosh_neg, ofReal_neg, mul_neg, neg_mul, neg_neg]
  rw [Complex.cosh]
  ring

/-- For every complex `a` and every `x > 0`, the function `u ↦ e^{-x cosh u} cosh(a u)` is
integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_mul_cosh_mul_cosh (a : ℂ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ ↦ (Real.exp (-(x * Real.cosh u)) : ℂ) * Complex.cosh (a * u))
      (Ioi 0) := by
  have hG := (integrable_and_integral_cexp_mul_exp_neg_mul_cosh hx a).1
  refine ((hG.comp_neg.add hG).div_const 2).integrableOn.congr_fun (fun u _ ↦ ?_)
    measurableSet_Ioi
  simp only [Pi.add_apply, cexp_mul_exp_neg_mul_cosh_even]
  ring

/-- **Macdonald's integral in hyperbolic form** (DLMF 10.32.9–10.32.10). For every complex `a` and
every `x > 0`,
`∫₀^∞ e^{-x cosh u} cosh(a u) du = ½ (x/2)^{-a} ∫₀^∞ s^{a - 1} e^{-s - x²/(4s)} ds`. -/
theorem integral_exp_neg_mul_cosh_mul_cosh (a : ℂ) {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi (0 : ℝ), (Real.exp (-(x * Real.cosh u)) : ℂ) * Complex.cosh (a * u) =
      ((x / 2 : ℝ) : ℂ) ^ (-a) / 2 *
        ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (a - 1) * (Real.exp (-s - x ^ 2 / 4 / s) : ℂ) := by
  obtain ⟨hG, hint⟩ := integrable_and_integral_cexp_mul_exp_neg_mul_cosh hx a
  -- the integral over `ℝ` is the integral over `(0, ∞)` of the even part, doubled
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := 0) hG.integrableOn hG.integrableOn
  -- reflect the integral over `(-∞, 0]` to one over `(0, ∞)`
  have hneg := integral_comp_neg_Ioi (0 : ℝ)
    fun u : ℝ ↦ cexp (-a * u) * (Real.exp (-(x * Real.cosh u)) : ℂ)
  simp only [neg_zero] at hneg
  rw [← hneg, ← integral_add hG.comp_neg.integrableOn hG.integrableOn, hint] at hsplit
  simp only [cexp_mul_exp_neg_mul_cosh_even, integral_const_mul] at hsplit
  rw [cpow_neg]
  linear_combination hsplit / 2

end Complex
