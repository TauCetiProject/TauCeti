/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform
public import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral

/-!
# The Mellin transform of Euler's integral along the negative real axis

For `0 < Re s < min(Re a, Re b)` and `Re b < Re c`, the function `x ↦ E(a, b, c, -x)`, where
`E = Complex.eulerIntegral` is Euler's normalized integral (DLMF 15.6.1), has a convergent Mellin
transform at `s`, and

`∫₀^∞ x^{s - 1} E(a, b, c, -x) dx = Γ(s) Γ(a - s) Γ(b - s) / (Γ(a) Γ(b) Γ(c - s))`.

Euler's integral represents the regularized Gauss function `𝐅(a, b; c; ·)` in this parameter
range (DLMF 15.6.1), so this is DLMF 15.14.1 there. The proof inserts Euler's integral, exchanges
the two integrals by Fubini, evaluates the inner integral over `x` by the Beta integral of the
second kind `Complex.hasMellin_one_add_cpow_neg` (DLMF 5.12.3) after scaling `x ↦ t x`, and
evaluates the remaining integral over `t` as the Beta integral `B(b - s, c - b)`.

## Main results

* `Complex.hasMellin_eulerIntegral_neg`: the Mellin transform of `x ↦ E(a, b, c, -x)`.

## References

* NIST Digital Library of Mathematical Functions, equations 5.12.3, 15.6.1 and 15.14.1.
-/

public section

open Real Set MeasureTheory Filter
open Complex hiding exp continuous_exp log

namespace Complex

/-- Scaling `x ↦ t x` in the Mellin integrand of `(1 + x)^{-a}`: for `t > 0` and `x ≥ 0`,
`x^{s - 1} (1 + x t)^{-a} = t^{1 - s} ((t x)^{s - 1} (1 + t x)^{-a})`. -/
private lemma cpow_mul_one_add_mul_cpow_neg_eq (s a : ℂ) {t x : ℝ} (ht : 0 < t)
    (hx : 0 ≤ x) :
    (x : ℂ) ^ (s - 1) * (1 + x * t) ^ (-a) =
      (t : ℂ) ^ (1 - s) * (((t * x : ℝ) : ℂ) ^ (s - 1) * (1 + ((t * x : ℝ) : ℂ)) ^ (-a)) := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have h1 : (t : ℂ) ^ (1 - s) * (t : ℂ) ^ (s - 1) = 1 := by
    rw [← cpow_add _ _ ht', show 1 - s + (s - 1) = 0 by ring, cpow_zero]
  rw [ofReal_mul, mul_cpow_ofReal_nonneg ht.le hx, mul_comm (x : ℂ) (t : ℂ)]
  linear_combination (-((x : ℂ) ^ (s - 1) * (1 + t * x) ^ (-a))) * h1

/-- The Mellin transform of `(1 + x t)^{-a}` for `t > 0` and `0 < Re s < Re a`, by scaling the
Beta integral of the second kind. -/
private lemma hasMellin_one_add_mul_cpow_neg {s a : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re)
    {t : ℝ} (ht : 0 < t) :
    HasMellin (fun x : ℝ ↦ (1 + (x : ℂ) * t) ^ (-a)) s
      ((t : ℂ) ^ (-s) * (Gamma s * Gamma (a - s) / Gamma a)) := by
  simpa only [ofReal_mul, smul_eq_mul] using (hasMellin_one_add_cpow_neg hs hsa).comp_mul_right ht

/-- The integral of the norm of the Mellin integrand of `(1 + x t)^{-a}` scales as
`t^{-Re s}`. -/
private lemma integral_norm_cpow_mul_one_add_mul_cpow_neg (s a : ℂ) {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) * (1 + x * t) ^ (-a)‖ =
      t ^ (-s.re) * ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) * (1 + x) ^ (-a)‖ := by
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x : ℝ ↦
      t ^ (1 - s.re) * ‖((t * x : ℝ) : ℂ) ^ (s - 1) * (1 + ((t * x : ℝ) : ℂ)) ^ (-a)‖)
      fun x hx ↦ by
        rw [cpow_mul_one_add_mul_cpow_neg_eq s a ht (le_of_lt hx), norm_mul,
          norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re],
    integral_const_mul, integral_comp_mul_left_Ioi
      (fun u : ℝ ↦ ‖(u : ℂ) ^ (s - 1) * (1 + (u : ℂ)) ^ (-a)‖) 0 ht, mul_zero, smul_eq_mul,
    ← mul_assoc, ← rpow_neg_one, ← rpow_add ht]
  ring_nf

/-- Multiplying the Beta weight of Euler's integral by `t^{-s}` shifts its first parameter. -/
private lemma cpow_mul_one_sub_cpow_mul_cpow_neg (b c s : ℂ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (t : ℂ) ^ (-s) =
      (t : ℂ) ^ (b - s - 1) * (1 - (t : ℂ)) ^ (c - b - 1) := by
  rw [show b - s - 1 = b - 1 + -s by ring, cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')]
  ring

/-- The integrand of the Mellin transform of Euler's integral, as a function of `(x, t)`, is
absolutely integrable on `(0, ∞) × (0, 1]` when `0 < Re s < min(Re a, Re b)` and
`Re b < Re c`. -/
private lemma integrable_cpow_mul_eulerIntegrand {a b c s : ℂ} (hs : 0 < s.re)
    (hsa : s.re < a.re) (hsb : s.re < b.re) (hbc : b.re < c.re) :
    Integrable (fun p : ℝ × ℝ ↦ (p.1 : ℂ) ^ (s - 1) *
        ((p.2 : ℂ) ^ (b - 1) * (1 - (p.2 : ℂ)) ^ (c - b - 1) * (1 + (p.1 : ℂ) * p.2) ^ (-a)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 1))) := by
  have hbeta := betaIntegral_convergent (u := b - s) (v := c - b) (by simpa using hsb)
    (by simpa using hbc)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hbeta
  refine (integrable_prod_iff' (by fun_prop)).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    refine (((hasMellin_one_add_mul_cpow_neg hs hsa ht.1).1).const_mul
      ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1))).congr
      (Eventually.of_forall fun x ↦ ?_)
    simp only [smul_eq_mul]
    ring
  · -- the inner integral of the norm is `t^{-Re s}` times a constant
    refine (hbeta.norm.mul_const
        (∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) * (1 + x) ^ (-a)‖)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hnorm (x : ℝ) : ‖(x : ℂ) ^ (s - 1) *
        ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 + (x : ℂ) * t) ^ (-a))‖ =
          ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖ *
            ‖(x : ℂ) ^ (s - 1) * (1 + (x : ℂ) * t) ^ (-a)‖ := by
      simp only [norm_mul]
      ring
    simp only [hnorm]
    rw [integral_const_mul, integral_norm_cpow_mul_one_add_mul_cpow_neg s a ht.1,
      ← cpow_mul_one_sub_cpow_mul_cpow_neg b c s ht.1, norm_mul (_ * _),
      norm_cpow_eq_rpow_re_of_pos ht.1 (-s), neg_re]
    ring

/-- **The Mellin transform of Euler's integral along the negative real axis** (DLMF 15.14.1 for
`𝐅(a, b; c; ·)` represented by Euler's integral). For `0 < Re s < min(Re a, Re b)` and
`Re b < Re c`, the Mellin transform of `x ↦ E(a, b, c, -x)` converges at `s` and equals
`Γ(s) Γ(a - s) Γ(b - s) / (Γ(a) Γ(b) Γ(c - s))`. -/
theorem hasMellin_eulerIntegral_neg {a b c s : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re)
    (hsb : s.re < b.re) (hbc : b.re < c.re) :
    HasMellin (fun x : ℝ ↦ eulerIntegral a b c (-x)) s
      (Gamma s * Gamma (a - s) * Gamma (b - s) / (Gamma a * Gamma b * Gamma (c - s))) := by
  have hbs : 0 < (b - s).re := by simpa using hsb
  have hcb : 0 < (c - b).re := by simpa using hbc
  have hFint := integrable_cpow_mul_eulerIntegrand hs hsa hsb hbc
  -- the Mellin integrand is the `t`-integral of the joint integrand
  have houter : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) • eulerIntegral a b c (-x) =
      (Gamma b * Gamma (c - b))⁻¹ * ∫ t in Ioc (0 : ℝ) 1, (x : ℂ) ^ (s - 1) *
        ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 + (x : ℂ) * t) ^ (-a)) := by
    intro x _
    rw [eulerIntegral_def, intervalIntegral.integral_of_le zero_le_one, smul_eq_mul,
      mul_left_comm, ← integral_const_mul]
    simp only [neg_mul, sub_neg_eq_add]
  -- the inner integral in `x`, at each `t ∈ (0, 1]`, is a scaled Beta integral of the second kind
  have hinner : ∀ t ∈ Ioc (0 : ℝ) 1, ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) *
      ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 + (x : ℂ) * t) ^ (-a)) =
      Gamma s * Gamma (a - s) / Gamma a *
        ((t : ℂ) ^ (b - s - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) := by
    intro t ht
    have h := (hasMellin_one_add_mul_cpow_neg hs hsa ht.1).2
    simp only [mellin, smul_eq_mul] at h
    simp only [mul_left_comm ((_ : ℂ) ^ (s - 1))]
    rw [integral_const_mul, h, ← cpow_mul_one_sub_cpow_mul_cpow_neg b c s ht.1]
    ring
  refine ⟨?_, ?_⟩
  · refine ((hFint.integral_prod_left).const_mul (Gamma b * Gamma (c - b))⁻¹).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (houter x hx).symm
  · rw [mellin, setIntegral_congr_fun measurableSet_Ioi houter, integral_const_mul,
      integral_integral_swap hFint, setIntegral_congr_fun measurableSet_Ioc hinner,
      integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one, ← betaIntegral,
      betaIntegral_eq_Gamma_mul_div _ _ hbs hcb, show b - s + (c - b) = c - s by ring]
    field_simp [Gamma_ne_zero_of_re_pos (hs.trans hsb), Gamma_ne_zero_of_re_pos hcb]

end Complex
