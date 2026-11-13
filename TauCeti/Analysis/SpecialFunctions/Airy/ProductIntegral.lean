/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.SpecialFunctions.Gamma.Multiplication
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Integral representation and Maclaurin series of `Ai(z)² + Bi(z)²`

The sum of squares `airyAi z ^ 2 + airyBi z ^ 2` — whose restriction to the real axis is the
squared Airy modulus `M(x)²` — admits an everywhere absolutely convergent Laplace-type integral
representation on `(0, ∞)` (DLMF 9.11.4):

$$\operatorname{Ai}(z)^2 + \operatorname{Bi}(z)^2
  = \pi^{-3/2} \int_0^\infty \exp\!\left(z t - \frac{t^3}{12}\right) t^{-1/2} \, dt.$$

Expanding `airyAi` and `airyBi` through the reduced Bessel series `₀F₁(; 2 / 3; z³ / 9)` and
`₀F₁(; 4 / 3; z³ / 9)` expresses `Ai(z)² + Bi(z)²` as a linear combination of three `₀F₁`
products, while expanding `exp(z t)` in the integral produces the full Maclaurin series of
`Ai(z)² + Bi(z)²` with Gamma numerators `Γ((m + 1 / 2) / 3)`. Differentiating under the integral
yields integral representations for all iterated derivatives `deriv^[n] (Ai² + Bi²)` and shows
that `Ai² + Bi²` solves the third-order product differential equation `w''' − 4 z w' − 2 w = 0`
(DLMF 9.8.18, 9.11.1).

## Main results

* `TauCeti.airyAi_sq_add_airyBi_sq_eq_regularizedHGFun` — `Ai(z)² + Bi(z)²` in terms of products
  of `₀F₁(; 2 / 3; z³ / 9)` and `₀F₁(; 4 / 3; z³ / 9)`.
* `TauCeti.integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow` and
  `TauCeti.integrableOn_cexp_sub_cube_div_twelve_mul_cpow` — absolute Bochner integrability of the
  integrand of DLMF 9.11.4 and all of its `tⁿ` moments on `(0, ∞)`.
* `TauCeti.airyAi_sq_add_airyBi_sq_eq_integral` and `TauCeti.airyAi_sq_add_airyBi_sq_ofReal` —
  DLMF 9.11.4 for complex and real arguments.
* `TauCeti.hasSum_airyAi_sq_add_airyBi_sq` — the everywhere convergent Maclaurin series of
  `Ai(z)² + Bi(z)²`, absolutely convergent by `TauCeti.summable_norm_airyAi_sq_add_airyBi_sq`.
* `TauCeti.four_mul_airyAi_zero_sq` — the origin identity
  `4 Ai(0)² = π^{−3/2} 12^{1/6} Γ(1 / 6) / 3`.
* `TauCeti.hasDerivAt_integral_pow_mul_cexp_sub_cube_div_twelve_mul_cpow` and
  `TauCeti.iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral` — iterated derivatives of
  `Ai² + Bi²` as moment integrals on `(0, ∞)`.
* `TauCeti.airyAi_sq_add_airyBi_sq_productEquation` — `Ai² + Bi²` satisfies
  `w''' − 4 z w' − 2 w = 0`.

## References

* NIST Digital Library of Mathematical Functions, §§9.8(iii), 9.11(i)–(ii),
  <https://dlmf.nist.gov/9.8>, <https://dlmf.nist.gov/9.11>.
* O. Vallée and M. Soares, *Airy Functions and Applications to Physics*, Imperial College Press,
  2004, §3.4.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Nat Real Topology

namespace TauCeti

/-! ### Hypergeometric expansion and values at the origin -/

/-- The sum of squares `Ai(z)² + Bi(z)²` expressed through products of the reduced Bessel series
`₀F₁(; 2 / 3; z³ / 9)` and `₀F₁(; 4 / 3; z³ / 9)`. -/
theorem airyAi_sq_add_airyBi_sq_eq_regularizedHGFun (z : ℂ) :
    airyAi z ^ 2 + airyBi z ^ 2 =
      4 * (3 : ℂ) ^ (-4 / 3 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) ^ 2 +
      4 / 9 * z *
        regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) *
        regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) +
      4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2 *
        regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) ^ 2 := by
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have hc₀ : ((3 : ℂ) ^ (-2 / 3 : ℂ)) ^ 2 + ((3 : ℂ) ^ (-1 / 6 : ℂ)) ^ 2 =
      4 * (3 : ℂ) ^ (-4 / 3 : ℂ) := by
    have h₁ : ((3 : ℂ) ^ (-2 / 3 : ℂ)) ^ 2 = (3 : ℂ) ^ (-4 / 3 : ℂ) := by
      rw [sq, ← cpow_add _ _ h3]; norm_num
    have h₂ : ((3 : ℂ) ^ (-1 / 6 : ℂ)) ^ 2 = 3 * (3 : ℂ) ^ (-4 / 3 : ℂ) := by
      nth_rw 2 [← cpow_one (3 : ℂ)]
      rw [sq, ← cpow_add _ _ h3, ← cpow_add _ _ h3]; norm_num
    linear_combination h₁ + h₂
  have hc₁ : -2 * ((3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (-4 / 3 : ℂ)) +
      2 * ((3 : ℂ) ^ (-1 / 6 : ℂ) * (3 : ℂ) ^ (-5 / 6 : ℂ)) = 4 / 9 := by
    have h₁ : (3 : ℂ) ^ (-2 / 3 : ℂ) * (3 : ℂ) ^ (-4 / 3 : ℂ) = 1 / 9 := by
      have hexp : (-2 / 3 : ℂ) + (-4 / 3 : ℂ) = -(2 : ℕ) := by norm_num
      rw [← cpow_add _ _ h3, hexp, cpow_neg, cpow_natCast]; norm_num
    have h₂ : (3 : ℂ) ^ (-1 / 6 : ℂ) * (3 : ℂ) ^ (-5 / 6 : ℂ) = 1 / 3 := by
      have hexp : (-1 / 6 : ℂ) + (-5 / 6 : ℂ) = -1 := by norm_num
      rw [← cpow_add _ _ h3, hexp, cpow_neg_one]; norm_num
    rw [h₁, h₂]; norm_num
  have hc₂ : ((3 : ℂ) ^ (-4 / 3 : ℂ)) ^ 2 + ((3 : ℂ) ^ (-5 / 6 : ℂ)) ^ 2 =
      4 * (3 : ℂ) ^ (-8 / 3 : ℂ) := by
    have h₁ : ((3 : ℂ) ^ (-4 / 3 : ℂ)) ^ 2 = (3 : ℂ) ^ (-8 / 3 : ℂ) := by
      rw [sq, ← cpow_add _ _ h3]; norm_num
    have h₂ : ((3 : ℂ) ^ (-5 / 6 : ℂ)) ^ 2 = 3 * (3 : ℂ) ^ (-8 / 3 : ℂ) := by
      nth_rw 2 [← cpow_one (3 : ℂ)]
      rw [sq, ← cpow_add _ _ h3, ← cpow_add _ _ h3]; norm_num
    linear_combination h₁ + h₂
  set F₁ := regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)
  set F₂ := regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)
  rw [airyAi_def, airyBi_def]
  linear_combination F₁ ^ 2 * hc₀ + z * F₁ * F₂ * hc₁ + z ^ 2 * F₂ ^ 2 * hc₂

/-- At the origin, `Bi(0)² = 3 Ai(0)²`. -/
theorem airyBi_zero_sq : airyBi 0 ^ 2 = 3 * airyAi 0 ^ 2 := by
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have hpow : ((3 : ℂ) ^ (-1 / 6 : ℂ)) ^ 2 = 3 * ((3 : ℂ) ^ (-2 / 3 : ℂ)) ^ 2 := by
    nth_rw 2 [← cpow_one (3 : ℂ)]
    rw [sq, sq, ← cpow_add _ _ h3, ← cpow_add _ _ h3, ← cpow_add _ _ h3]
    norm_num
  rw [airyAi_zero, airyBi_zero, div_pow, div_pow, hpow, mul_div_assoc]

/-- At the origin, `Ai(0)² + Bi(0)² = 4 Ai(0)²`. -/
theorem airyAi_zero_sq_add_airyBi_zero_sq : airyAi 0 ^ 2 + airyBi 0 ^ 2 = 4 * airyAi 0 ^ 2 := by
  rw [airyBi_zero_sq]; ring

/-! ### Integrability and moment evaluation on `(0, ∞)` -/

private theorem ofReal_cpow_neg_half {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (-1 / 2 : ℂ) = ((t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
  have hexp : (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, ofReal_cpow ht.le]

private theorem norm_pow_mul_cexp_sub_cube_div_twelve_mul_cpow {t : ℝ} (ht : 0 < t) (n : ℕ)
    (z : ℂ) :
    ‖(t : ℂ) ^ n * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)‖ =
      t ^ ((n : ℝ) - 1 / 2) * Real.exp (z.re * t - 1 / 12 * t ^ (3 : ℝ)) := by
  have hre : (z * (t : ℂ) - (t : ℂ) ^ 3 / 12).re = z.re * t - 1 / 12 * t ^ (3 : ℝ) := by
    have hcube : ((t : ℂ) ^ 3 / 12).re = 1 / 12 * t ^ (3 : ℝ) := by
      have ht3 : (t : ℂ) ^ 3 / 12 = ((t ^ 3 / 12 : ℝ) : ℂ) := by push_cast; ring
      rw [ht3, ofReal_re, Real.rpow_ofNat]
      ring
    rw [sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, hcube]
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_of_nonneg ht.le, Complex.norm_exp, hre,
    ofReal_cpow_neg_half ht, Complex.norm_of_nonneg (Real.rpow_pos_of_pos ht _).le,
    ← Real.rpow_natCast t n, mul_right_comm, ← Real.rpow_add ht]
  congr 2
  ring

/-- For every complex `z` and natural number `n`, the `n`-th moment integrand
`t ↦ tⁿ exp(z t − t³ / 12) t^{−1/2}` is Bochner integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ n * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (Ioi 0) := by
  have hmajor := integrableOn_rpow_mul_exp_mul_sub_mul_rpow
    (p := 3) (q := (n : ℝ) - 1 / 2) (b := 1 / 12)
    (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)]) (by norm_num) z.re
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ n * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t (ht : 0 < t)
    refine ContinuousAt.continuousWithinAt ?_
    exact (((continuous_ofReal.pow n).mul
      (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_ofReal).sub
          ((continuous_ofReal.pow 3).div_const 12)))).continuousAt).mul
      (continuousAt_ofReal_cpow_const t (-1 / 2) (Or.inr ht.ne'))
  refine hmajor.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_pow_mul_cexp_sub_cube_div_twelve_mul_cpow ht]

/-- The integrand `t ↦ exp(z t − t³ / 12) t^{−1/2}` of DLMF 9.11.4 is Bochner integrable on
`(0, ∞)` for every complex `z`. -/
theorem integrableOn_cexp_sub_cube_div_twelve_mul_cpow (z : ℂ) :
    IntegrableOn
      (fun t : ℝ => cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (Ioi 0) := by
  simpa only [pow_zero, one_mul] using integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow 0 z

private theorem integral_pow_mul_cexp_neg_cube_div_twelve_mul_cpow (m : ℕ) :
    ∫ t in Ioi (0 : ℝ),
        (t : ℂ) ^ m * cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ (-1 / 2 : ℂ) =
      (12 : ℂ) ^ (((m : ℂ) + 1 / 2) / 3) * Gamma (((m : ℂ) + 1 / 2) / 3) / 3 := by
  have hcongr : EqOn
      (fun t : ℝ => (t : ℂ) ^ m * cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (fun t : ℝ => ((t ^ ((m : ℝ) - 1 / 2) * Real.exp (-(1 / 12) * t ^ (3 : ℝ)) : ℝ) : ℂ))
      (Ioi 0) := by
    intro t (ht : 0 < t)
    dsimp only
    have hexp : -((t : ℂ) ^ 3 / 12) = ((-(1 / 12) * t ^ (3 : ℝ) : ℝ) : ℂ) := by
      rw [Real.rpow_ofNat]; push_cast; ring
    rw [ofReal_cpow_neg_half ht, hexp, ← ofReal_exp, ← ofReal_pow, ← ofReal_mul, ← ofReal_mul]
    congr 1
    rw [← Real.rpow_natCast t m, mul_right_comm, ← Real.rpow_add ht]
    congr 2
    ring
  have hreal := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := 3) (q := (m : ℝ) - 1 / 2) (b := 1 / 12)
    (by norm_num) (by linarith [m.cast_nonneg (α := ℝ)]) (by norm_num)
  have hs : ((m : ℝ) - 1 / 2 + 1) / 3 = ((m : ℝ) + 1 / 2) / 3 := by ring
  have h12 : (1 / 12 : ℝ) ^ (-((m : ℝ) - 1 / 2 + 1) / 3) =
      (12 : ℝ) ^ (((m : ℝ) + 1 / 2) / 3) := by
    have hinv : (1 / 12 : ℝ) = (12 : ℝ)⁻¹ := one_div 12
    rw [hinv, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_complex_ofReal, hreal, hs, h12]
  have hcast : ((((m : ℝ) + 1 / 2) / 3 : ℝ) : ℂ) = ((m : ℂ) + 1 / 2) / 3 := by push_cast; ring
  push_cast
  rw [ofReal_cpow (by norm_num : (0 : ℝ) ≤ 12), ← Gamma_ofReal, hcast]
  push_cast
  ring

private theorem hasSum_integral_airy_product_series (z : ℂ) :
    HasSum
      (fun m : ℕ =>
        (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ (((m : ℂ) + 1 / 2) / 3) *
          Gamma (((m : ℂ) + 1 / 2) / 3) / (3 * m !) * z ^ m)
      ((π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ),
          cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) := by
  let F : ℕ → ℝ → ℂ := fun m t =>
    (z ^ m / m !) * ((t : ℂ) ^ m * cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ (-1 / 2 : ℂ))
  let bound : ℕ → ℝ → ℝ := fun m t =>
    (‖z‖ * t) ^ m / m ! * (t ^ (-1 / 2 : ℝ) * Real.exp (-(1 / 12 * t ^ (3 : ℝ))))
  have hmeas (m : ℕ) : AEStronglyMeasurable (F m) (volume.restrict (Ioi 0)) := by
    have hint := (integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow m 0).const_mul
      (z ^ m / m !)
    refine hint.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    simp [F]
  have hbound (m : ℕ) : ∀ᵐ t ∂volume.restrict (Ioi 0), ‖F m t‖ ≤ bound m t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    have h0 := norm_pow_mul_cexp_sub_cube_div_twelve_mul_cpow ht m 0
    simp only [zero_re, zero_mul, zero_sub] at h0
    have hexp : (m : ℝ) - 1 / 2 = (m : ℝ) + (-1 / 2 : ℝ) := by ring
    rw [norm_mul, h0, norm_div, norm_pow, Complex.norm_natCast, hexp, Real.rpow_add ht,
      Real.rpow_natCast]
    dsimp only [bound]
    rw [mul_pow]
    exact le_of_eq (by ring)
  have hsum_bound : ∀ᵐ t ∂volume.restrict (Ioi 0), Summable fun m => bound m t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    exact (Real.summable_pow_div_factorial (‖z‖ * t)).mul_right _
  have hint_bound : Integrable (fun t => ∑' m, bound m t) (volume.restrict (Ioi 0)) := by
    have hmajor := integrableOn_rpow_mul_exp_mul_sub_mul_rpow
      (p := 3) (q := -1 / 2) (b := 1 / 12) (by norm_num) (by norm_num) (by norm_num) ‖z‖
    refine hmajor.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    have hexp := NormedSpace.expSeries_div_hasSum_exp (‖z‖ * t)
    rw [← Real.exp_eq_exp_ℝ] at hexp
    rw [(hexp.mul_right _).tsum_eq, mul_left_comm, ← Real.exp_add, sub_eq_add_neg]
  have hlim : ∀ᵐ t ∂volume.restrict (Ioi 0),
      HasSum (fun m => F m t)
        (cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    have hexp := (NormedSpace.expSeries_div_hasSum_exp (z * t)).mul_right
      (cexp (-((t : ℂ) ^ 3 / 12)) * (t : ℂ) ^ (-1 / 2 : ℂ))
    rw [← Complex.exp_eq_exp_ℂ, ← mul_assoc, ← Complex.exp_add, ← sub_eq_add_neg] at hexp
    refine hexp.congr_fun fun m => ?_
    simp only [F, mul_pow]
    ring
  have hdc := (hasSum_integral_of_dominated_convergence bound hmeas hbound hsum_bound
    hint_bound hlim).mul_left ((π : ℂ) ^ (-3 / 2 : ℂ))
  refine hdc.congr_fun fun m => ?_
  dsimp only [F]
  rw [integral_const_mul, integral_pow_mul_cexp_neg_cube_div_twelve_mul_cpow]
  ring

/-! ### Duplication–triplication identification of the Maclaurin coefficients -/

private theorem real_airy_product_coeff (m : ℕ) :
    4 * (3 : ℝ) ^ (-2 * (((m : ℝ) + 1 / 2) / 3) - 1) *
        Real.Gamma (2 * (((m : ℝ) + 1 / 2) / 3)) /
      (Real.Gamma (((m : ℝ) + 1 / 2) / 3 + 1 / 2) *
        (Real.Gamma (((m : ℝ) + 1 / 2) / 3 + 1 / 6) *
          Real.Gamma (((m : ℝ) + 1 / 2) / 3 + 1 / 2) *
          Real.Gamma (((m : ℝ) + 1 / 2) / 3 + 5 / 6))) =
      Real.pi ^ (-3 / 2 : ℝ) * (12 : ℝ) ^ (((m : ℝ) + 1 / 2) / 3) *
        Real.Gamma (((m : ℝ) + 1 / 2) / 3) / (3 * m !) := by
  set s : ℝ := ((m : ℝ) + 1 / 2) / 3
  have : 0 < s := by positivity
  have hdup := Real.Gamma_mul_Gamma_add_half s
  have htrip := Real.prod_Gamma_add_div (m := 3) (by norm_num) (s + 1 / 6)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, zero_div, add_zero] at htrip
  have ha₁ : s + 1 / 6 + 1 / 3 = s + 1 / 2 := by ring
  have ha₂ : s + 1 / 6 + 2 / 3 = s + 5 / 6 := by ring
  have ha₃ : (1 : ℝ) / 2 - 3 * (s + 1 / 6) = -3 * s := by ring
  have ha₄ : 3 * (s + 1 / 6) = (m : ℝ) + 1 := by simp only [s]; ring
  have ha₅ : ((3 : ℝ) - 1) / 2 = 1 := by norm_num
  rw [ha₁, ha₂, ha₃, ha₄, ha₅, Real.rpow_one, Real.Gamma_nat_eq_factorial] at htrip
  have h2s_eq : (2 : ℝ) ^ (1 - 2 * s) = 2 / (2 : ℝ) ^ (2 * s) := by
    rw [Real.rpow_sub two_pos, Real.rpow_one]
  have h12 : (12 : ℝ) ^ s = (2 : ℝ) ^ (2 * s) * (3 : ℝ) ^ s := by
    have h4 : (4 : ℝ) ^ s = (2 : ℝ) ^ (2 * s) := by
      have h22 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h22, ← Real.rpow_mul zero_le_two]
    rw [← h4, ← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  have h3pow : (3 : ℝ) ^ (-2 * s - 1) = (3 : ℝ) ^ (-3 * s) * (3 : ℝ) ^ s / 3 := by
    have hexp : -2 * s - 1 = -3 * s + s - 1 := by ring
    rw [hexp, Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_add (by norm_num)]
  have h2s : (2 : ℝ) ^ (1 - 2 * s) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
  have hpis : √Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have : Real.pi ≠ 0 := Real.pi_ne_zero
  have : (m ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hpi_eq : Real.pi ^ (-3 / 2 : ℝ) = (√Real.pi * Real.pi)⁻¹ := by
    have hprod : √Real.pi * Real.pi * Real.pi ^ (-3 / 2 : ℝ) = 1 := by
      rw [Real.sqrt_eq_rpow]
      nth_rw 2 [← Real.rpow_one Real.pi]
      rw [← Real.rpow_add Real.pi_pos, ← Real.rpow_add Real.pi_pos]
      norm_num
    exact eq_inv_of_mul_eq_one_right hprod
  have hG2 : Real.Gamma (2 * s) =
      Real.Gamma s * Real.Gamma (s + 1 / 2) / ((2 : ℝ) ^ (1 - 2 * s) * √Real.pi) := by
    rw [hdup, mul_assoc (Real.Gamma (2 * s)), mul_div_cancel_right₀ _ (mul_ne_zero h2s hpis)]
  rw [htrip, h3pow, h12, hG2, h2s_eq, hpi_eq]
  field_simp
  ring

private theorem real_pochhammer_airy_coeff_mod_zero (n : ℕ) :
    4 * (3 : ℝ) ^ (-4 / 3 : ℝ) *
      ((ascPochhammer ℝ n).eval (2 / 3 + 2 / 3 + (n : ℝ) - 1) /
        (n ! * Real.Gamma (2 / 3 + n) * Real.Gamma (2 / 3 + n)) * (1 / 9 : ℝ) ^ n) =
    Real.pi ^ (-3 / 2 : ℝ) * (12 : ℝ) ^ ((((3 * n : ℕ) : ℝ) + 1 / 2) / 3) *
      Real.Gamma ((((3 * n : ℕ) : ℝ) + 1 / 2) / 3) / (3 * (3 * n)!) := by
  set s : ℝ := (((3 * n : ℕ) : ℝ) + 1 / 2) / 3
  have hx : ∀ k : ℕ, (n : ℝ) + 1 / 3 ≠ -k := fun k =>
    ne_of_gt (by linarith [n.cast_nonneg (α := ℝ), k.cast_nonneg (α := ℝ)])
  have hp : (2 / 3 : ℝ) + 2 / 3 + n - 1 = n + 1 / 3 := by ring
  have hp2 : (n : ℝ) + 1 / 3 + n = 2 * s := by simp only [s]; push_cast; ring
  have hasc : (ascPochhammer ℝ n).eval (2 / 3 + 2 / 3 + (n : ℝ) - 1) =
      Real.Gamma (2 * s) / Real.Gamma (s + 1 / 6) := by
    have hs1 : (n : ℝ) + 1 / 3 = s + 1 / 6 := by simp only [s]; push_cast; ring
    rw [hp, ← Real.Gamma_add_nat_div_Gamma_eq _ hx, hp2, hs1]
  have h9 : (3 : ℝ) ^ (-4 / 3 : ℝ) * (1 / 9 : ℝ) ^ n = (3 : ℝ) ^ (-2 * s - 1) := by
    have h9n : (1 / 9 : ℝ) ^ n = (3 : ℝ) ^ (-(2 * (n : ℝ))) := by
      have h19 : (1 / 9 : ℝ) = ((3 : ℝ) ^ (2 : ℝ))⁻¹ := by norm_num
      rw [← Real.rpow_natCast, h19, Real.inv_rpow (by norm_num),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    rw [h9n, ← Real.rpow_add (by norm_num)]
    congr 1; simp only [s]; push_cast; ring
  have hg₁ : (2 / 3 : ℝ) + n = s + 1 / 2 := by simp only [s]; push_cast; ring
  have hg₂ : (n ! : ℝ) = Real.Gamma (s + 5 / 6) := by
    have hs5 : s + 5 / 6 = (n : ℝ) + 1 := by simp only [s]; push_cast; ring
    rw [hs5, Real.Gamma_nat_eq_factorial]
  rw [← real_airy_product_coeff (3 * n), hasc, hg₁, hg₂,
    ← mul_assoc (4 * (3 : ℝ) ^ (-4 / 3 : ℝ)), mul_right_comm (4 * (3 : ℝ) ^ (-4 / 3 : ℝ)),
    mul_assoc 4, h9]
  ring

private theorem real_pochhammer_airy_coeff_mod_one (n : ℕ) :
    4 / 9 *
      ((ascPochhammer ℝ n).eval (2 / 3 + 4 / 3 + (n : ℝ) - 1) /
        (n ! * Real.Gamma (2 / 3 + n) * Real.Gamma (4 / 3 + n)) * (1 / 9 : ℝ) ^ n) =
    Real.pi ^ (-3 / 2 : ℝ) * (12 : ℝ) ^ ((((3 * n + 1 : ℕ) : ℝ) + 1 / 2) / 3) *
      Real.Gamma ((((3 * n + 1 : ℕ) : ℝ) + 1 / 2) / 3) / (3 * (3 * n + 1)!) := by
  set s : ℝ := (((3 * n + 1 : ℕ) : ℝ) + 1 / 2) / 3
  have hx : ∀ k : ℕ, (n : ℝ) + 1 ≠ -k := fun k =>
    ne_of_gt (by linarith [n.cast_nonneg (α := ℝ), k.cast_nonneg (α := ℝ)])
  have hp : (2 / 3 : ℝ) + 4 / 3 + n - 1 = n + 1 := by ring
  have hp2 : (n : ℝ) + 1 + n = 2 * s := by simp only [s]; push_cast; ring
  have hasc : (ascPochhammer ℝ n).eval (2 / 3 + 4 / 3 + (n : ℝ) - 1) =
      Real.Gamma (2 * s) / Real.Gamma (s + 1 / 2) := by
    have hs1 : (n : ℝ) + 1 = s + 1 / 2 := by simp only [s]; push_cast; ring
    rw [hp, ← Real.Gamma_add_nat_div_Gamma_eq _ hx, hp2, hs1]
  have h9 : (1 / 9 : ℝ) * (1 / 9 : ℝ) ^ n = (3 : ℝ) ^ (-2 * s - 1) := by
    have h9n : (1 / 9 : ℝ) ^ (n + 1) = (3 : ℝ) ^ (-(2 * ((n : ℝ) + 1))) := by
      have h19 : (1 / 9 : ℝ) = ((3 : ℝ) ^ (2 : ℝ))⁻¹ := by norm_num
      rw [← Real.rpow_natCast, h19, Real.inv_rpow (by norm_num),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num), Nat.cast_succ]
    rw [← pow_succ', h9n]
    congr 1; simp only [s]; push_cast; ring
  have hg₁ : (2 / 3 : ℝ) + n = s + 1 / 6 := by simp only [s]; push_cast; ring
  have hg₂ : (n ! : ℝ) = Real.Gamma (s + 1 / 2) := by
    have hs5 : s + 1 / 2 = (n : ℝ) + 1 := by simp only [s]; push_cast; ring
    rw [hs5, Real.Gamma_nat_eq_factorial]
  have hg₃ : (4 / 3 : ℝ) + n = s + 5 / 6 := by simp only [s]; push_cast; ring
  have h49 : (4 / 9 : ℝ) = 4 * (1 / 9 : ℝ) := by norm_num
  rw [← real_airy_product_coeff (3 * n + 1), hasc, hg₁, hg₂, hg₃, h49,
    ← mul_assoc (4 * (1 / 9 : ℝ)), mul_right_comm (4 * (1 / 9 : ℝ)), mul_assoc 4, h9]
  ring

private theorem real_pochhammer_airy_coeff_mod_two (n : ℕ) :
    4 * (3 : ℝ) ^ (-8 / 3 : ℝ) *
      ((ascPochhammer ℝ n).eval (4 / 3 + 4 / 3 + (n : ℝ) - 1) /
        (n ! * Real.Gamma (4 / 3 + n) * Real.Gamma (4 / 3 + n)) * (1 / 9 : ℝ) ^ n) =
    Real.pi ^ (-3 / 2 : ℝ) * (12 : ℝ) ^ ((((3 * n + 2 : ℕ) : ℝ) + 1 / 2) / 3) *
      Real.Gamma ((((3 * n + 2 : ℕ) : ℝ) + 1 / 2) / 3) / (3 * (3 * n + 2)!) := by
  set s : ℝ := (((3 * n + 2 : ℕ) : ℝ) + 1 / 2) / 3
  have hx : ∀ k : ℕ, (n : ℝ) + 5 / 3 ≠ -k := fun k =>
    ne_of_gt (by linarith [n.cast_nonneg (α := ℝ), k.cast_nonneg (α := ℝ)])
  have hp : (4 / 3 : ℝ) + 4 / 3 + n - 1 = n + 5 / 3 := by ring
  have hp2 : (n : ℝ) + 5 / 3 + n = 2 * s := by simp only [s]; push_cast; ring
  have hasc : (ascPochhammer ℝ n).eval (4 / 3 + 4 / 3 + (n : ℝ) - 1) =
      Real.Gamma (2 * s) / Real.Gamma (s + 5 / 6) := by
    have hs1 : (n : ℝ) + 5 / 3 = s + 5 / 6 := by simp only [s]; push_cast; ring
    rw [hp, ← Real.Gamma_add_nat_div_Gamma_eq _ hx, hp2, hs1]
  have h9 : (3 : ℝ) ^ (-8 / 3 : ℝ) * (1 / 9 : ℝ) ^ n = (3 : ℝ) ^ (-2 * s - 1) := by
    have h9n : (1 / 9 : ℝ) ^ n = (3 : ℝ) ^ (-(2 * (n : ℝ))) := by
      have h19 : (1 / 9 : ℝ) = ((3 : ℝ) ^ (2 : ℝ))⁻¹ := by norm_num
      rw [← Real.rpow_natCast, h19, Real.inv_rpow (by norm_num),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    rw [h9n, ← Real.rpow_add (by norm_num)]
    congr 1; simp only [s]; push_cast; ring
  have hg₁ : (4 / 3 : ℝ) + n = s + 1 / 2 := by simp only [s]; push_cast; ring
  have hg₂ : (n ! : ℝ) = Real.Gamma (s + 1 / 6) := by
    have hs5 : s + 1 / 6 = (n : ℝ) + 1 := by simp only [s]; push_cast; ring
    rw [hs5, Real.Gamma_nat_eq_factorial]
  rw [← real_airy_product_coeff (3 * n + 2), hasc, hg₁, hg₂,
    ← mul_assoc (4 * (3 : ℝ) ^ (-8 / 3 : ℝ)), mul_right_comm (4 * (3 : ℝ) ^ (-8 / 3 : ℝ)),
    mul_assoc 4, h9]
  ring

private theorem cast_airy_product_rhs (m : ℕ) :
    ((Real.pi ^ (-3 / 2 : ℝ) * (12 : ℝ) ^ (((m : ℝ) + 1 / 2) / 3) *
        Real.Gamma (((m : ℝ) + 1 / 2) / 3) / (3 * m !) : ℝ) : ℂ) =
      (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ (((m : ℂ) + 1 / 2) / 3) *
        Gamma (((m : ℂ) + 1 / 2) / 3) / (3 * m !) := by
  have hpi : ((-3 / 2 : ℝ) : ℂ) = (-3 / 2 : ℂ) := by push_cast; ring
  have hm : ((((m : ℝ) + 1 / 2) / 3 : ℝ) : ℂ) = ((m : ℂ) + 1 / 2) / 3 := by push_cast; ring
  push_cast
  rw [ofReal_cpow Real.pi_nonneg, ofReal_cpow (by norm_num : (0 : ℝ) ≤ 12), ← Gamma_ofReal, hpi, hm]
  push_cast
  rfl

private theorem eval_ascPochhammer_ofReal (c : ℝ) (n : ℕ) :
    (ascPochhammer ℂ n).eval (c : ℂ) = (((ascPochhammer ℝ n).eval c : ℝ) : ℂ) := by
  simpa using Polynomial.eval_map_apply Complex.ofRealHom c (p := ascPochhammer ℝ n)

private theorem hasSum_airyAi_sq_add_airyBi_sq_grouped (z : ℂ) :
    HasSum
      (fun n : ℕ =>
        (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ ((((3 * n : ℕ) : ℂ) + 1 / 2) / 3) *
            Gamma ((((3 * n : ℕ) : ℂ) + 1 / 2) / 3) / (3 * (3 * n)!) * z ^ (3 * n) +
          (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ ((((3 * n + 1 : ℕ) : ℂ) + 1 / 2) / 3) *
            Gamma ((((3 * n + 1 : ℕ) : ℂ) + 1 / 2) / 3) / (3 * (3 * n + 1)!) * z ^ (3 * n + 1) +
          (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ ((((3 * n + 2 : ℕ) : ℂ) + 1 / 2) / 3) *
            Gamma ((((3 * n + 2 : ℕ) : ℂ) + 1 / 2) / 3) / (3 * (3 * n + 2)!) * z ^ (3 * n + 2))
      (airyAi z ^ 2 + airyBi z ^ 2) := by
  have h₀ := (hasSum_regularizedHGFun_zero_singleton_mul (2 / 3) (2 / 3) (z ^ 3 / 9)).mul_left
    (4 * (3 : ℂ) ^ (-4 / 3 : ℂ))
  have h₁ := (hasSum_regularizedHGFun_zero_singleton_mul (2 / 3) (4 / 3) (z ^ 3 / 9)).mul_left
    (4 / 9 * z)
  have h₂ := (hasSum_regularizedHGFun_zero_singleton_mul (4 / 3) (4 / 3) (z ^ 3 / 9)).mul_left
    (4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2)
  have hsum := (h₀.add h₁).add h₂
  have hsum_val :
      4 * (3 : ℂ) ^ (-4 / 3 : ℂ) *
          (regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) *
            regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)) +
        4 / 9 * z *
          (regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) *
            regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) +
        4 * (3 : ℂ) ^ (-8 / 3 : ℂ) * z ^ 2 *
          (regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) *
            regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) =
      airyAi z ^ 2 + airyBi z ^ 2 := by
    rw [airyAi_sq_add_airyBi_sq_eq_regularizedHGFun]
    ring
  rw [hsum_val] at hsum
  refine hsum.congr_fun fun n => ?_
  have hc₀ := congrArg (fun x : ℝ => (x : ℂ) * z ^ (3 * n)) (real_pochhammer_airy_coeff_mod_zero n)
  have hc₁ := congrArg (fun x : ℝ => (x : ℂ) * z ^ (3 * n + 1))
    (real_pochhammer_airy_coeff_mod_one n)
  have hc₂ := congrArg (fun x : ℝ => (x : ℂ) * z ^ (3 * n + 2))
    (real_pochhammer_airy_coeff_mod_two n)
  rw [cast_airy_product_rhs] at hc₀ hc₁ hc₂
  have hz9 : (z ^ 3 / 9) ^ n = ((1 / 9 : ℝ) ^ n : ℂ) * z ^ (3 * n) := by
    rw [div_eq_mul_inv, mul_pow, ← pow_mul, mul_comm]
    push_cast; ring
  have h3a : (3 : ℂ) ^ (-4 / 3 : ℂ) = (((3 : ℝ) ^ (-4 / 3 : ℝ) : ℝ) : ℂ) := by
    have he : (-4 / 3 : ℂ) = ((-4 / 3 : ℝ) : ℂ) := by push_cast; ring
    rw [he, ofReal_cpow (by norm_num)]
    push_cast
    rfl
  have h3b : (3 : ℂ) ^ (-8 / 3 : ℂ) = (((3 : ℝ) ^ (-8 / 3 : ℝ) : ℝ) : ℂ) := by
    have he : (-8 / 3 : ℂ) = ((-8 / 3 : ℝ) : ℂ) := by push_cast; ring
    rw [he, ofReal_cpow (by norm_num)]
    push_cast
    rfl
  have hp₀ : (2 / 3 : ℂ) + 2 / 3 + n - 1 = ((2 / 3 + 2 / 3 + (n : ℝ) - 1 : ℝ) : ℂ) := by
    push_cast; ring
  have hp₁ : (2 / 3 : ℂ) + 4 / 3 + n - 1 = ((2 / 3 + 4 / 3 + (n : ℝ) - 1 : ℝ) : ℂ) := by
    push_cast; ring
  have hp₂ : (4 / 3 : ℂ) + 4 / 3 + n - 1 = ((4 / 3 + 4 / 3 + (n : ℝ) - 1 : ℝ) : ℂ) := by
    push_cast; ring
  have hg₂₃ : (2 / 3 : ℂ) + n = ((2 / 3 + (n : ℝ) : ℝ) : ℂ) := by push_cast; ring
  have hg₄₃ : (4 / 3 : ℂ) + n = ((4 / 3 + (n : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [← hc₀, ← hc₁, ← hc₂, hz9, h3a, h3b, hp₀, hp₁, hp₂, hg₂₃, hg₄₃,
    eval_ascPochhammer_ofReal, eval_ascPochhammer_ofReal, eval_ascPochhammer_ofReal,
    Gamma_ofReal, Gamma_ofReal, pow_add, pow_one]
  push_cast
  ring

/-! ### DLMF 9.11.4 and the Maclaurin series of `Ai(z)² + Bi(z)²` -/

/-- **DLMF 9.11.4**: for every complex `z`,
`Ai(z)² + Bi(z)² = π^{−3/2} ∫₀^∞ exp(z t − t³ / 12) t^{−1/2} dt`. -/
theorem airyAi_sq_add_airyBi_sq_eq_integral (z : ℂ) :
    airyAi z ^ 2 + airyBi z ^ 2 =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ),
          cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) := by
  have hint := hasSum_integral_airy_product_series z
  have hmod := ((Nat.divModEquiv 3).symm.hasSum_iff.mpr hint).prod_fiberwise fun n =>
    hasSum_fintype _
  refine (hasSum_airyAi_sq_add_airyBi_sq_grouped z).unique (hmod.congr_fun fun n => ?_)
  rw [Fin.sum_univ_three]
  simp only [Function.comp_apply, Nat.divModEquiv_symm_apply, Fin.val_zero, Fin.val_one,
    Fin.val_two, add_zero, mul_comm n 3]

/-- **DLMF 9.11.4** on the real axis: for every real `x`, `Ai(x)² + Bi(x)²` is the coercion of
`π^{−3/2} ∫₀^∞ exp(x t − t³ / 12) t^{−1/2} dt`. -/
theorem airyAi_sq_add_airyBi_sq_ofReal (x : ℝ) :
    airyAi x ^ 2 + airyBi x ^ 2 =
      ((π ^ (-3 / 2 : ℝ) *
        ∫ t in Ioi (0 : ℝ),
          Real.exp (x * t - t ^ 3 / 12) * t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [airyAi_sq_add_airyBi_sq_eq_integral]
  have hcongr : EqOn
      (fun t : ℝ => cexp ((x : ℂ) * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (fun t : ℝ => ((Real.exp (x * t - t ^ 3 / 12) * t ^ (-1 / 2 : ℝ) : ℝ) : ℂ))
      (Ioi 0) := by
    intro t (ht : 0 < t)
    dsimp only
    have hexp : (x : ℂ) * t - (t : ℂ) ^ 3 / 12 = ((x * t - t ^ 3 / 12 : ℝ) : ℂ) := by
      push_cast; ring
    rw [ofReal_cpow_neg_half ht, hexp, ← ofReal_exp, ← ofReal_mul]
  have hpi : (π : ℂ) ^ (-3 / 2 : ℂ) = ((π ^ (-3 / 2 : ℝ) : ℝ) : ℂ) := by
    have he : (-3 / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [he, ofReal_cpow Real.pi_nonneg]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_complex_ofReal, hpi, ← ofReal_mul]

/-- The everywhere convergent Maclaurin series of `Ai(z)² + Bi(z)²`. -/
theorem hasSum_airyAi_sq_add_airyBi_sq (z : ℂ) :
    HasSum
      (fun m : ℕ =>
        (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ (((m : ℂ) + 1 / 2) / 3) *
          Gamma (((m : ℂ) + 1 / 2) / 3) / (3 * m !) * z ^ m)
      (airyAi z ^ 2 + airyBi z ^ 2) := by
  rw [airyAi_sq_add_airyBi_sq_eq_integral]
  exact hasSum_integral_airy_product_series z

/-- The Maclaurin series of `Ai(z)² + Bi(z)²` converges absolutely at every complex `z`. -/
theorem summable_norm_airyAi_sq_add_airyBi_sq (z : ℂ) :
    Summable fun m : ℕ =>
      ‖(π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ (((m : ℂ) + 1 / 2) / 3) *
        Gamma (((m : ℂ) + 1 / 2) / 3) / (3 * m !) * z ^ m‖ := by
  have hsum := (hasSum_re (hasSum_airyAi_sq_add_airyBi_sq (‖z‖ : ℂ))).summable
  refine hsum.congr fun m => ?_
  have hpos : 0 ≤ Real.pi ^ (-3 / 2 : ℝ) * (12 : ℝ) ^ (((m : ℝ) + 1 / 2) / 3) *
      Real.Gamma (((m : ℝ) + 1 / 2) / 3) / (3 * m !) := by positivity
  rw [← cast_airy_product_rhs m, ← ofReal_pow, ← ofReal_mul, ofReal_re, norm_mul,
    Complex.norm_of_nonneg hpos, norm_pow]

/-- DLMF 9.11.4 at the origin: `4 Ai(0)² = π^{−3/2} 12^{1/6} Γ(1 / 6) / 3`. -/
theorem four_mul_airyAi_zero_sq :
    4 * airyAi 0 ^ 2 =
      (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ (1 / 6 : ℂ) * Gamma (1 / 6) / 3 := by
  have h0 := hasSum_airyAi_sq_add_airyBi_sq 0
  rw [airyAi_zero_sq_add_airyBi_zero_sq] at h0
  refine (h0.unique (hasSum_single 0 fun m hm => ?_)).trans ?_
  · simp [zero_pow hm]
  · have h16 : (((0 : ℕ) : ℂ) + 1 / 2) / 3 = 1 / 6 := by norm_num
    rw [h16, Nat.factorial_zero, Nat.cast_one, mul_one, pow_zero, mul_one]

/-! ### Iterated derivatives and the product differential equation -/

/-- Differentiating `w ↦ ∫₀^∞ tⁿ exp(w t − t³ / 12) t^{−1/2} dt` under the integral sign multiplies
the integrand by `t`. -/
theorem hasDerivAt_integral_pow_mul_cexp_sub_cube_div_twelve_mul_cpow (n : ℕ) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ =>
        ∫ t in Ioi (0 : ℝ),
          (t : ℂ) ^ n * cexp (w * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (∫ t in Ioi (0 : ℝ),
        (t : ℂ) ^ (n + 1) * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      z := by
  let F : ℂ → ℝ → ℂ := fun w t =>
    (t : ℂ) ^ n * cexp (w * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)
  let F' : ℂ → ℝ → ℂ := fun w t =>
    (t : ℂ) ^ (n + 1) * cexp (w * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)
  let bound : ℝ → ℝ := fun t =>
    t ^ (((n + 1 : ℕ) : ℝ) - 1 / 2) * Real.exp ((‖z‖ + 1) * t - 1 / 12 * t ^ (3 : ℝ))
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) :=
    integrableOn_rpow_mul_exp_mul_sub_mul_rpow
      (p := 3) (q := ((n + 1 : ℕ) : ℝ) - 1 / 2) (b := 1 / 12)
      (by norm_num) (by linarith [(n + 1).cast_nonneg (α := ℝ)]) (by norm_num) (‖z‖ + 1)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (bound := bound)
    (Metric.ball_mem_nhds z zero_lt_one)
    (.of_forall fun w => (integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow n w).1)
    (integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow n z)
    (integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow (n + 1) z).1
    ?_ hbound_int ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    have hw_re : w.re ≤ ‖z‖ + 1 := by
      have hdist : ‖w - z‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hw
      have hnorm : ‖w‖ ≤ ‖z‖ + 1 := by
        linarith [norm_sub_rev w z, norm_sub_norm_le w z]
      exact (Complex.re_le_norm w).trans hnorm
    dsimp only [F', bound]
    rw [norm_pow_mul_cexp_sub_cube_div_twelve_mul_cpow ht (n + 1) w]
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ w _
    have hd := ((((hasDerivAt_id w).mul_const (t : ℂ)).sub_const ((t : ℂ) ^ 3 / 12)).cexp.const_mul
      ((t : ℂ) ^ n)).mul_const ((t : ℂ) ^ (-1 / 2 : ℂ))
    refine hd.congr_deriv ?_
    dsimp only [F', id]
    rw [pow_succ]
    ring

/-- Every iterated derivative of `Ai(z)² + Bi(z)²` is represented by the corresponding `tⁿ` moment
of the integral of DLMF 9.11.4. -/
theorem iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral (n : ℕ) (z : ℂ) :
    deriv^[n] (fun w => airyAi w ^ 2 + airyBi w ^ 2) z =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ),
          (t : ℂ) ^ n * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) := by
  induction n generalizing z with
  | zero =>
    simpa only [Function.iterate_zero_apply, pow_zero, one_mul] using
      airyAi_sq_add_airyBi_sq_eq_integral z
  | succ n ih =>
    rw [Function.iterate_succ_apply', funext ih]
    exact ((hasDerivAt_integral_pow_mul_cexp_sub_cube_div_twelve_mul_cpow n z).const_mul
      ((π : ℂ) ^ (-3 / 2 : ℂ))).deriv

private theorem integral_product_equation_kernel (z : ℂ) :
    ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ 3 - 4 * z * t - 2) *
          cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) = 0 := by
  let g : ℝ → ℂ := fun t => -4 * (Real.sqrt t : ℂ) * cexp (z * t - (t : ℂ) ^ 3 / 12)
  have hcont : Continuous g :=
    (continuous_const.mul (continuous_ofReal.comp Real.continuous_sqrt)).mul
      (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_ofReal).sub
          ((continuous_ofReal.pow 3).div_const 12)))
  have hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt g
        (((t : ℂ) ^ 3 - 4 * z * t - 2) *
          cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) t := by
    intro t (ht : 0 < t)
    have hsqrt_deriv : HasDerivAt (fun s : ℝ => (Real.sqrt s : ℂ))
        ((1 / (2 * Real.sqrt t) : ℝ) : ℂ) t :=
      (Real.hasDerivAt_sqrt ht.ne').ofReal_comp
    have hexp_arg : HasDerivAt (fun s : ℝ => z * (s : ℂ) - (s : ℂ) ^ 3 / 12)
        (z - (t : ℂ) ^ 2 / 4) t := by
      refine (((hasDerivAt_id (t : ℂ)).const_mul z).sub
        ((hasDerivAt_pow 3 (t : ℂ)).div_const (12 : ℂ))).comp_ofReal.congr_deriv ?_
      push_cast
      ring
    have hd := (hsqrt_deriv.const_mul (-4 : ℂ)).mul hexp_arg.cexp
    refine hd.congr_deriv ?_
    have hcpow : (t : ℂ) ^ (-1 / 2 : ℂ) = (Real.sqrt t : ℂ)⁻¹ := by
      have hnh : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
      rw [ofReal_cpow_neg_half ht, hnh, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow, ofReal_inv]
    have hmul : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne')
    have hsq : (Real.sqrt t : ℂ) = (t : ℂ) * (Real.sqrt t : ℂ)⁻¹ := by
      have hst : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
        rw [← ofReal_mul, Real.mul_self_sqrt ht.le]
      calc (Real.sqrt t : ℂ) = (Real.sqrt t : ℂ) * 1 := (mul_one _).symm
        _ = (Real.sqrt t : ℂ) * ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)⁻¹) := by rw [hmul]
        _ = (t : ℂ) * (Real.sqrt t : ℂ)⁻¹ := by rw [← mul_assoc, hst]
    rw [hcpow]
    push_cast
    linear_combination -4 * (z - (t : ℂ) ^ 2 / 4) * cexp (z * t - (t : ℂ) ^ 3 / 12) * hsq
  have hint : IntegrableOn
      (fun t : ℝ =>
        ((t : ℂ) ^ 3 - 4 * z * t - 2) *
          cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (Ioi 0) := by
    have h3 := integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow 3 z
    have h1 := (integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow 1 z).const_mul (4 * z)
    have h0 := (integrableOn_cexp_sub_cube_div_twelve_mul_cpow z).const_mul (2 : ℂ)
    refine ((h3.sub h1).sub h0).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, pow_one]
    ring
  have htend : Tendsto g atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun t : ℝ => 4 * t * Real.exp (-t)) atTop (𝓝 0) := by
      have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 4
      simp only [pow_one, mul_zero] at h0
      exact h0.congr fun t => by ring
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop (12 * (|z.re| + 1))] with t ht
    have ht1 : 1 ≤ t := by linarith [abs_nonneg z.re]
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    have hre : (z * (t : ℂ) - (t : ℂ) ^ 3 / 12).re ≤ -t := by
      have hcube : ((t : ℂ) ^ 3 / 12).re = t ^ 3 / 12 := by
        have ht3 : (t : ℂ) ^ 3 / 12 = ((t ^ 3 / 12 : ℝ) : ℂ) := by push_cast; ring
        rw [ht3, ofReal_re]
      rw [sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, hcube]
      have hzt : z.re * t ≤ |z.re| * t := mul_le_mul_of_nonneg_right (le_abs_self _) ht0.le
      have ht2 : t ≤ t ^ 2 := by nlinarith
      nlinarith [ht.trans ht2]
    have hsqrt_le : Real.sqrt t ≤ t := by
      rw [Real.sqrt_le_iff]
      exact ⟨ht0.le, by nlinarith⟩
    dsimp only [g]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_ofNat,
      Complex.norm_of_nonneg (Real.sqrt_nonneg t), Complex.norm_exp]
    gcongr
  have hibp := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt hderiv hint htend
  simpa [g] using hibp

/-- `Ai(z)² + Bi(z)²` satisfies the third-order product differential equation
`w''' − 4 z w' − 2 w = 0` (DLMF 9.8.18, 9.11.1). -/
theorem airyAi_sq_add_airyBi_sq_productEquation (z : ℂ) :
    deriv^[3] (fun w => airyAi w ^ 2 + airyBi w ^ 2) z -
      4 * z * deriv (fun w => airyAi w ^ 2 + airyBi w ^ 2) z -
      2 * (airyAi z ^ 2 + airyBi z ^ 2) = 0 := by
  have hd3 := iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral 3 z
  have hd1 := iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral 1 z
  rw [Function.iterate_one] at hd1
  rw [hd3, hd1, airyAi_sq_add_airyBi_sq_eq_integral]
  have h3 := integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow 3 z
  have h1 := (integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow 1 z).const_mul (4 * z)
  have h31 : IntegrableOn
      (fun t : ℝ =>
        (t : ℂ) ^ 3 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) -
          4 * z * ((t : ℂ) ^ 1 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)))
      (Ioi 0) := h3.sub h1
  have h0 := (integrableOn_cexp_sub_cube_div_twelve_mul_cpow z).const_mul (2 : ℂ)
  have hcomb :
      (∫ t in Ioi (0 : ℝ),
          (t : ℂ) ^ 3 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) -
        4 * z *
          (∫ t in Ioi (0 : ℝ),
            (t : ℂ) ^ 1 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) -
        2 *
          (∫ t in Ioi (0 : ℝ),
            cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) =
      ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ 3 - 4 * z * t - 2) *
          cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) := by
    rw [← integral_const_mul (4 * z), ← integral_const_mul (2 : ℂ), ← integral_sub h3 h1,
      ← integral_sub h31 h0]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [pow_one]
    ring
  calc (π : ℂ) ^ (-3 / 2 : ℂ) * _ - 4 * z * ((π : ℂ) ^ (-3 / 2 : ℂ) * _) -
        2 * ((π : ℂ) ^ (-3 / 2 : ℂ) * _)
      = (π : ℂ) ^ (-3 / 2 : ℂ) *
          ((∫ t in Ioi (0 : ℝ),
              (t : ℂ) ^ 3 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) -
            4 * z *
              (∫ t in Ioi (0 : ℝ),
                (t : ℂ) ^ 1 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) -
            2 *
              (∫ t in Ioi (0 : ℝ),
                cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))) := by ring
    _ = (π : ℂ) ^ (-3 / 2 : ℂ) * 0 := by rw [hcomb, integral_product_equation_kernel]
    _ = 0 := mul_zero _

end TauCeti
