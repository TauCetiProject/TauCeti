/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral

/-!
# Barnes's integral for Euler's hypergeometric integral

Barnes's integral (DLMF 15.6.6) represents the regularized Gauss function at a negative argument
`-x`, `x > 0`, as a vertical integral of Gamma functions,

`𝐅(a, b; c; -x) = (1 / (2π Γ(a) Γ(b))) ∫ Γ(a + t) Γ(b + t) Γ(-t) / Γ(c + t) x^t dy`,

along the line `t = σ + i y`, `y ∈ ℝ`, with `-min(Re a, Re b) < σ < 0`. The line separates the
poles `t = -a - k`, `t = -b - k` of the first two factors from the poles `t = k` of `Γ(-t)`. This
file proves the identity for Euler's normalized integral `Complex.eulerIntegral a b c (-x)`, which
represents `𝐅(a, b; c; -x)` where `0 < Re b < Re c` (DLMF 15.6.1), so `Re b < Re c` is assumed as
well; the vertical integral converges there.

The proof inserts the Mellin–Barnes integral of `(1 + u)^{-a}`
(`Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_sub`), read along the line `Re t = σ`, into
Euler's integral at `u = x r`, exchanges the two integrals by Fubini and evaluates the inner
integral over `r ∈ (0, 1]` as the Beta integral `B(b + t, c - b) = Γ(b + t) Γ(c - b) / Γ(c + t)`.
The norm of the double integrand is a product of the Beta weight `r^{Re b + σ - 1}
(1 - r)^{Re(c - b) - 1}` and `x^σ ‖Γ(a + t) Γ(-t)‖`, both integrable, which justifies Fubini and
shows that the vertical integral converges.

## Main results

* `Complex.verticalIntegrable_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_cpow`: for `σ < 0`,
  `-σ < Re a`, `-σ < Re b < Re c` and `x > 0`, the integrand
  `Γ(a + t) Γ(b + t) Γ(-t) Γ(c + t)⁻¹ x^t` of DLMF 15.6.6 is integrable along the line
  `t = σ + i y`.
* `Complex.eulerIntegral_neg_eq_mellinBarnes`: DLMF 15.6.6 for Euler's integral at the
  negative argument `-x`.

## References

* NIST Digital Library of Mathematical Functions, equations 15.6.1 and 15.6.6,
  <https://dlmf.nist.gov/15.6>.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.5.
-/

public section

open Real Set MeasureTheory
open Complex hiding exp continuous_exp log

namespace Complex

/-- The Mellin–Barnes integral of `(1 + u)^{-a}` read along the line `t = σ + i y` with `σ < 0`:
`∫ Γ(a + t) Γ(-t) u^t dy = 2π Γ(a) (1 + u)^{-a}` for `u > 0` and `-σ < Re a`. -/
private lemma integral_Gamma_add_mul_Gamma_neg_mul_cpow {a : ℂ} {σ : ℝ} (hσ : σ < 0)
    (hσa : -σ < a.re) {u : ℝ} (hu : 0 < u) :
    ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * (u : ℂ) ^ (σ + y * I) =
      2 * π * (Gamma a * (1 + (u : ℂ)) ^ (-a)) := by
  rw [← integral_cpow_neg_mul_Gamma_mul_Gamma_sub (neg_pos.mpr hσ) hσa hu,
    ← integral_neg_eq_self]
  congr 1
  ext y
  have h : (σ : ℂ) + ((-y : ℝ) : ℂ) * I = -(((-σ : ℝ) : ℂ) + y * I) := by push_cast; ring
  rw [h, neg_neg, ← sub_eq_add_neg]
  ring

/-- Along the line `t = σ + i y` with `σ < 0` and `-σ < Re a`, the product `Γ(a + t) Γ(-t) x^t`
is integrable for `x > 0`: `Γ(a + t) Γ(-t)` is `Γ(s) Γ(a - s)` at `s = -t` and `‖x^t‖ = x^σ`. -/
private lemma verticalIntegrable_Gamma_add_mul_Gamma_neg_mul_cpow {a : ℂ} {σ x : ℝ} (hσ : σ < 0)
    (hσa : -σ < a.re) (hx : 0 < x) :
    VerticalIntegrable (fun t ↦ Gamma (a + t) * Gamma (-t) * (x : ℂ) ^ t) σ := by
  have hG : Integrable fun y : ℝ ↦ Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) := by
    refine (verticalIntegrable_Gamma_mul_Gamma_sub (a := a) (σ := -σ)
      (fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)])).comp_neg.congr
      (ae_of_all _ fun y ↦ ?_)
    have h : ((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I = -(σ + y * I) := by push_cast; ring
    simp only [h, sub_neg_eq_add]
    ring
  refine hG.mul_bdd (c := x ^ σ) (Continuous.aestronglyMeasurable ?_) (ae_of_all _ fun y ↦ ?_)
  · exact (by fun_prop : Continuous fun y : ℝ ↦ (σ : ℂ) + y * I).const_cpow
      (.inl (ofReal_ne_zero.mpr hx.ne'))
  · rw [norm_cpow_eq_rpow_re_of_pos hx]
    simp

/-- The integrand of DLMF 15.6.6 inserted into Euler's integral at `-x`: on `ℝ × (0, 1]`, the
function `(y, r) ↦ r^{b + t - 1} (1 - r)^{c - b - 1} Γ(a + t) Γ(-t) x^t` with `t = σ + i y` is
integrable. Its norm is the product of the Beta weight `‖r^{b + σ - 1} (1 - r)^{c - b - 1}‖` and
`‖Γ(a + t) Γ(-t) x^t‖`. -/
private lemma integrable_eulerMellinBarnesIntegrand {a b c : ℂ} {σ x : ℝ} (hσ : σ < 0)
    (hσa : -σ < a.re) (hσb : -σ < b.re) (hbc : b.re < c.re) (hx : 0 < x) :
    Integrable (Function.uncurry fun (y r : ℝ) ↦
        (r : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (r : ℂ)) ^ (c - b - 1) *
          (Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * (x : ℂ) ^ (σ + y * I)))
      (volume.prod (volume.restrict (Ioc 0 1))) := by
  have hH : Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * (x : ℂ) ^ (σ + y * I) :=
    verticalIntegrable_Gamma_add_mul_Gamma_neg_mul_cpow hσ hσa hx
  have hbσ : 0 < (b + σ).re := by simp; linarith
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hβ := ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (betaIntegral_convergent hbσ hcb)).norm
  -- for `r > 0`, the `r`-factor has the norm of the Beta integrand at `(b + σ, c - b)`
  have hnorm {r : ℝ} (hr : 0 < r) (y : ℝ) :
      ‖(r : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (r : ℂ)) ^ (c - b - 1)‖ =
        ‖(r : ℂ) ^ (b + σ - 1) * (1 - (r : ℂ)) ^ (c - b - 1)‖ := by
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hr, norm_cpow_eq_rpow_re_of_pos hr]
    simp
  refine (integrable_prod_iff' ?meas).mpr ⟨?_, ?_⟩
  case meas =>
    exact (Measurable.aestronglyMeasurable (by fun_prop)).mul hH.aestronglyMeasurable.comp_fst
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hH.bdd_mul (Measurable.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun y ↦ (hnorm hr.1 y).le)
  refine (hβ.mul_const (∫ y : ℝ, ‖Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) *
    (x : ℂ) ^ (σ + y * I)‖)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simp_rw [Function.uncurry_apply_pair, norm_mul _ (Gamma _ * _ * _), hnorm hr.1]
  rw [integral_const_mul]

/-- The inner Beta integral of the Mellin–Barnes proof: integrating the `r`-factor of the double
integrand over `(0, 1]` gives `B(b + t, c - b) = Γ(b + t) Γ(c - b) / Γ(c + t)`. -/
private lemma integral_Ioc_eulerMellinBarnesIntegrand {a b c : ℂ} {σ x : ℝ} (hσb : -σ < b.re)
    (hbc : b.re < c.re) (y : ℝ) :
    ∫ r in Ioc (0 : ℝ) 1, (r : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (r : ℂ)) ^ (c - b - 1) *
        (Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * (x : ℂ) ^ (σ + y * I)) =
      Gamma (c - b) * (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I)) := by
  have hbt : 0 < (b + (σ + y * I)).re := by simp; linarith
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  rw [integral_mul_const, ← intervalIntegral.integral_of_le zero_le_one, ← betaIntegral,
    betaIntegral_eq_Gamma_mul_div _ _ hbt hcb, show b + (σ + y * I) + (c - b) = c + (σ + y * I) by
      ring]
  ring

/-- **Convergence of the Mellin–Barnes integral** (DLMF 15.6.6) in the region of Euler's
integral: for `σ < 0`, `-σ < Re a`, `-σ < Re b`, `Re b < Re c` and `x > 0`, the integrand
`Γ(a + t) Γ(b + t) Γ(-t) Γ(c + t)⁻¹ x^t` is integrable along the line `t = σ + i y`. -/
theorem verticalIntegrable_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_cpow {a b c : ℂ}
    {σ x : ℝ} (hσ : σ < 0) (hσa : -σ < a.re) (hσb : -σ < b.re) (hbc : b.re < c.re) (hx : 0 < x) :
    VerticalIntegrable
      (fun t ↦ Gamma (a + t) * Gamma (b + t) * Gamma (-t) * (Gamma (c + t))⁻¹ * (x : ℂ) ^ t) σ := by
  have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hbc)
  refine (((integrable_eulerMellinBarnesIntegrand hσ hσa hσb hbc hx).integral_prod_left).const_mul
    (Gamma (c - b))⁻¹).congr (ae_of_all _ fun y ↦ ?_)
  simp only [Function.uncurry_apply_pair]
  rw [integral_Ioc_eulerMellinBarnesIntegrand hσb hbc, inv_mul_cancel_left₀ hGcb]

/-- **The Mellin–Barnes integral** (DLMF 15.6.6) for Euler's integral at a negative argument. For
`x > 0`, `σ < 0`, `-σ < Re a`, `-σ < Re b` and `Re b < Re c`,
`eulerIntegral a b c (-x) = (2π Γ(a) Γ(b))⁻¹ ∫ Γ(a + t) Γ(b + t) Γ(-t) Γ(c + t)⁻¹ x^t dy`
along the line `t = σ + i y`. -/
theorem eulerIntegral_neg_eq_mellinBarnes {a b c : ℂ} {σ x : ℝ} (hσ : σ < 0) (hσa : -σ < a.re)
    (hσb : -σ < b.re) (hbc : b.re < c.re) (hx : 0 < x) :
    eulerIntegral a b c (-x) = (2 * π * Gamma a * Gamma b)⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I) := by
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hbc)
  -- the inner integral in `y` is the Mellin–Barnes integral of `(1 + x r)^{-a}`
  have hinner : ∀ r ∈ Ioc (0 : ℝ) 1, (r : ℂ) ^ (b - 1) * (1 - (r : ℂ)) ^ (c - b - 1) *
      (1 - (-x : ℂ) * r) ^ (-a) = (2 * π * Gamma a)⁻¹ * ∫ y : ℝ,
        (r : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (r : ℂ)) ^ (c - b - 1) *
          (Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * (x : ℂ) ^ (σ + y * I)) := by
    intro r hr
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.1.ne'
    have hsplit (y : ℝ) : (r : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (r : ℂ)) ^ (c - b - 1) *
        (Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * (x : ℂ) ^ (σ + y * I)) =
        (r : ℂ) ^ (b - 1) * (1 - (r : ℂ)) ^ (c - b - 1) * (Gamma (a + (σ + y * I)) *
          Gamma (-(σ + y * I)) * ((x * r : ℝ) : ℂ) ^ (σ + y * I)) := by
      rw [ofReal_mul, ofReal_mul_cpow hx.le,
        show b + (σ + y * I) - 1 = b - 1 + (σ + y * I) by ring, cpow_add _ _ hr0]
      ring
    simp_rw [hsplit]
    rw [integral_const_mul, integral_Gamma_add_mul_Gamma_neg_mul_cpow hσ hσa
      (mul_pos hx hr.1), show (1 - (-x : ℂ) * r) = 1 + ((x * r : ℝ) : ℂ) by push_cast; ring]
    field_simp
  rw [eulerIntegral_def, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_congr_fun measurableSet_Ioc hinner, integral_const_mul,
    ← integral_integral_swap (integrable_eulerMellinBarnesIntegrand hσ hσa hσb hbc hx)]
  simp_rw [integral_Ioc_eulerMellinBarnesIntegrand hσb hbc]
  rw [integral_const_mul, ← mul_assoc, ← mul_assoc]
  congr 1
  field_simp

end Complex
