/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Basic
import TauCeti.Analysis.MellinTransform.Beta
import TauCeti.Analysis.MellinTransform.Convolution
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes

/-!
# The Mellin transform of Euler's integral at negative argument

For `0 < Re s < min (Re a) (Re b)` and `Re b < Re c`, the Mellin transform of
`x ↦ E(a, b, c, -x)`, Euler's normalized integral (DLMF 15.6.1) at negative argument, is

`∫₀^∞ x^{s - 1} E(a, b, c, -x) dx = Γ(s) Γ(a - s) Γ(b - s) / (Γ(a) Γ(b) Γ(c - s))`.

This is DLMF 15.14.1 in the region `0 < Re b < Re c` where Euler's integral represents the
regularized Gauss function `𝐅(a, b; c; -x)`. The proof writes `E(a, b, c, -x)` as
`(Γ(b) Γ(c - b))⁻¹` times the integral `∫₀^∞ f(t) h(x t) dt` of the Beta weight
`f(t) = t^{b - 1} (1 - t)^{c - b - 1}` on `(0, 1]`, extended by zero to `(1, ∞)`, against
`h(u) = (1 + u)^{-a}` (the Mellin convolution of `y ↦ f(1/y)/y` with `h`), and applies
`TauCeti.hasMellin_integral_mul_comp_mul`: the Mellin transform of `h` at `s` is the Beta integral
of the second kind `Complex.hasMellin_one_add_cpow_neg` (DLMF 5.12.3), and that of `f` at `1 - s`
is the Beta integral `B(b - s, c - b)` by `TauCeti.hasMellin_cpow_mul_one_sub_cpow_Ioc`.

## Main results

* `Complex.hasMellin_eulerIntegral_neg`: for `0 < Re s < Re a`, `Re s < Re b` and `Re b < Re c`,
  the Mellin transform of `x ↦ eulerIntegral a b c (-x)` converges at `s` and equals
  `Γ(s) Γ(a - s) Γ(b - s) / (Γ(a) Γ(b) Γ(c - s))`.

## References

* NIST Digital Library of Mathematical Functions, equations 15.6.1 and 15.14.1,
  <https://dlmf.nist.gov/15.14>.
-/

public section

open Real Set MeasureTheory
open Complex hiding exp continuous_exp log

namespace Complex

/-- **The Mellin transform of Euler's integral at negative argument** (DLMF 15.14.1 in the region
of DLMF 15.6.1). For `0 < Re s < Re a`, `Re s < Re b` and `Re b < Re c`, the Mellin transform of
`x ↦ eulerIntegral a b c (-x)` converges at `s` and equals
`Γ(s) Γ(a - s) Γ(b - s) / (Γ(a) Γ(b) Γ(c - s))`. -/
theorem hasMellin_eulerIntegral_neg {a b c s : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re)
    (hsb : s.re < b.re) (hbc : b.re < c.re) :
    HasMellin (fun x : ℝ ↦ eulerIntegral a b c (-x)) s
      (Gamma s * Gamma (a - s) * Gamma (b - s) / (Gamma a * Gamma b * Gamma (c - s))) := by
  have hbs : 0 < (b - s).re := by simpa using hsb
  have hcb : 0 < (c - b).re := by simpa using hbc
  -- the Beta parameters of the weight `t^{b - 1} (1 - t)^{c - b - 1}` at `1 - s`
  have hu : 1 - s + (b - 1) = b - s := by ring
  have hv : c - b - 1 + 1 = c - b := by ring
  have hf := TauCeti.hasMellin_cpow_mul_one_sub_cpow_Ioc (s := 1 - s) (a := b - 1) (b := c - b - 1)
    (hu ▸ hbs) (by simp only [sub_re, one_re]; linarith)
  rw [hu, hv] at hf
  have hB : betaIntegral (b - s) (c - b) = Gamma (b - s) * Gamma (c - b) / Gamma (c - s) := by
    have hw : b - s + (c - b) = c - s := by ring
    rw [betaIntegral_eq_Gamma_mul_div _ _ hbs hcb, hw]
  have hh := hasMellin_one_add_cpow_neg hs hsa
  -- Euler's integral at `-x` is the integral of its Beta weight `f` against `h(xt)`, where
  -- `h(u) = (1 + u)^{-a}`: the Mellin convolution of `y ↦ f(1/y)/y` with `h`
  have heuler : (fun x : ℝ ↦ eulerIntegral a b c (-x)) = fun x : ℝ ↦
      (Gamma b * Gamma (c - b))⁻¹ • ∫ t in Ioi 0,
        (Ioc 0 1).indicator (fun t : ℝ ↦ (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) t *
          (1 + ((x * t : ℝ) : ℂ)) ^ (-a) := by
    ext x
    have h := setIntegral_indicator (μ := volume) (s := Ioi 0)
      (measurableSet_Ioc (a := 0) (b := 1)) (f := fun t : ℝ ↦
        (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 + ((x * t : ℝ) : ℂ)) ^ (-a))
    rw [inter_eq_right.mpr Ioc_subset_Ioi_self,
      ← intervalIntegral.integral_of_le zero_le_one] at h
    simp only [indicator_mul_left _
      fun t : ℝ ↦ (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)] at h
    rw [eulerIntegral_def, smul_eq_mul, h]
    simp only [ofReal_mul, neg_mul, sub_neg_eq_add]
  have hconv := TauCeti.hasMellin_integral_mul_comp_mul hf.1 hh.1
  have hmel := hasMellin_const_smul hconv.1 (Gamma b * Gamma (c - b))⁻¹
  rw [← heuler, hconv.2, hf.2, hh.2, hB, smul_eq_mul] at hmel
  convert hmel using 1
  field_simp [Gamma_ne_zero_of_re_pos (hs.trans hsb), Gamma_ne_zero_of_re_pos hcb]

end Complex
