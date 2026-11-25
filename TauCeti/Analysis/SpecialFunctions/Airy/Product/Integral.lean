/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.SpecialFunctions.Gamma.Multiplication
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.MeasureTheory.Integral.Exp.PowerDecay
import TauCeti.MeasureTheory.Integral.Exp.PowerLaplace

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
* `TauCeti.airyAi_sq_add_airyBi_sq_eq_integral` and
  `TauCeti.airyAi_sq_add_airyBi_sq_ofReal_eq_integral` — DLMF 9.11.4 for complex and real
  arguments.
* `TauCeti.hasSum_airyAi_sq_add_airyBi_sq` — the everywhere convergent Maclaurin series of
  `Ai(z)² + Bi(z)²`, absolutely convergent by `TauCeti.summable_norm_airyAi_sq_add_airyBi_sq`.
* `TauCeti.four_mul_airyAi_zero_sq` — the origin identity
  `4 Ai(0)² = π^{−3/2} 12^{1/6} Γ(1 / 6) / 3`.
* `TauCeti.hasDerivAt_integral_pow_mul_cexp_sub_cube_div_twelve_mul_cpow` and
  `TauCeti.iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral` — iterated derivatives of
  `Ai² + Bi²` as moment integrals on `(0, ∞)`.
* `TauCeti.airyAi_sq_add_airyBi_sq_differential_equation` — `Ai² + Bi²` satisfies
  `w''' − 4 z w' − 2 w = 0`.

## References

* NIST Digital Library of Mathematical Functions, §§9.8(ii), 9.11(i)–(iii),
  <https://dlmf.nist.gov/9.8>, <https://dlmf.nist.gov/9.11>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 11.
* O. Vallée and M. Soares, *Airy Functions and Applications to Physics*, Imperial College Press,
  2004, §3.4.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Nat Real Topology

namespace TauCeti

/-! ### Hypergeometric expansion -/

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

/-! ### Integrability and moment evaluation on `(0, ∞)` -/

/-- On `(0, ∞)` the moment integrand of DLMF 9.11.4 is the power-decay kernel with `p = 3`,
`q = n - 1/2` and `b = 1/12`. -/
private theorem pow_mul_cexp_sub_cube_div_twelve_mul_cpow_eq {t : ℝ} (ht : 0 < t) (n : ℕ)
    (z : ℂ) :
    (t : ℂ) ^ n * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) =
      (t : ℂ) ^ (((n : ℝ) - 1 / 2 : ℝ) : ℂ) *
        cexp (z * t - ((1 / 12 * t ^ (3 : ℝ) : ℝ) : ℂ)) := by
  have hpow : (t : ℂ) ^ n * (t : ℂ) ^ (-1 / 2 : ℂ) = (t : ℂ) ^ (((n : ℝ) - 1 / 2 : ℝ) : ℂ) := by
    rw [← cpow_natCast, ← cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')]
    push_cast
    ring_nf
  rw [mul_right_comm, hpow, Real.rpow_ofNat]
  push_cast
  ring_nf

private theorem norm_pow_mul_cexp_sub_cube_div_twelve_mul_cpow {t : ℝ} (ht : 0 < t) (n : ℕ)
    (z : ℂ) :
    ‖(t : ℂ) ^ n * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)‖ =
      t ^ ((n : ℝ) - 1 / 2) * Real.exp (z.re * t - 1 / 12 * t ^ (3 : ℝ)) := by
  rw [pow_mul_cexp_sub_cube_div_twelve_mul_cpow_eq ht, norm_cpow_mul_cexp_mul_sub_mul_rpow ht]

/-- For every complex `z` and natural number `n`, the `n`-th moment integrand
`t ↦ tⁿ exp(z t − t³ / 12) t^{−1/2}` is Bochner integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ n * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (Ioi 0) :=
  (integrableOn_cpow_mul_cexp_mul_sub_mul_rpow (p := 3) (q := (n : ℝ) - 1 / 2) (b := 1 / 12)
    (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)]) (by norm_num) z).congr_fun
    (fun _ ht => (pow_mul_cexp_sub_cube_div_twelve_mul_cpow_eq ht n z).symm) measurableSet_Ioi

/-- The integrand `t ↦ exp(z t − t³ / 12) t^{−1/2}` of DLMF 9.11.4 is Bochner integrable on
`(0, ∞)` for every complex `z`. -/
theorem integrableOn_cexp_sub_cube_div_twelve_mul_cpow (z : ℂ) :
    IntegrableOn
      (fun t : ℝ => cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (Ioi 0) := by
  simpa only [pow_zero, one_mul] using integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow 0 z

private theorem hasSum_integral_airy_product_series (z : ℂ) :
    HasSum
      (fun m : ℕ =>
        (π : ℂ) ^ (-3 / 2 : ℂ) * (12 : ℂ) ^ (((m : ℂ) + 1 / 2) / 3) *
          Gamma (((m : ℂ) + 1 / 2) / 3) / (3 * m !) * z ^ m)
      ((π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ),
          cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) := by
  have hsum := (hasSum_integral_cpow_mul_cexp_mul_sub_mul_cpow_Ioi
    (p := 3) (b := 1 / 12) (s := -1 / 2) (by norm_num) (by norm_num) (by norm_num) z).mul_left
    ((π : ℂ) ^ (-3 / 2 : ℂ))
  have hint :
      ∫ t in Ioi (0 : ℝ),
          (t : ℂ) ^ (-1 / 2 : ℂ) * cexp (z * t - (1 / 12 : ℂ) * (t : ℂ) ^ ((3 : ℝ) : ℂ)) =
        ∫ t in Ioi (0 : ℝ), cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    have h := (pow_mul_cexp_sub_cube_div_twelve_mul_cpow_eq ht 0 z).symm
    have h12 : (1 / 12 : ℂ) * (t : ℂ) ^ ((3 : ℝ) : ℂ) = ((1 / 12 * t ^ (3 : ℝ) : ℝ) : ℂ) := by
      rw [← ofReal_cpow ht.le]; push_cast; ring
    have hs : (((((0 : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ)) = (-1 / 2 : ℂ) := by push_cast; ring
    rw [pow_zero, one_mul] at h
    conv_lhs => rw [h12, ← hs]
    exact h
  rw [hint] at hsum
  refine hsum.congr_fun fun m => ?_
  have harg : ((-1 / 2 : ℂ) + m + 1) / ((3 : ℝ) : ℂ) = ((m : ℂ) + 1 / 2) / 3 := by
    push_cast; ring
  have h12 : (1 / 12 : ℂ) ^ (-((-1 / 2 : ℂ) + m + 1) / ((3 : ℝ) : ℂ)) =
      (12 : ℂ) ^ (((m : ℂ) + 1 / 2) / 3) := by
    rw [neg_div, harg, one_div, ← ofReal_ofNat 12,
      inv_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 12), cpow_neg, inv_inv, ofReal_ofNat]
  rw [h12, harg, ofReal_ofNat]
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
  -- Combine the three `₀F₁` Cauchy product series corresponding to `z ^ (3 * n + r)`.
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
  -- Match each residue-class coefficient with the Gamma moment formula cast from `ℝ` to `ℂ`.
  refine hsum.congr_fun fun n => ?_
  have hc₀ := congrArg (fun x : ℝ => (x : ℂ) * z ^ (3 * n)) (real_pochhammer_airy_coeff_mod_zero n)
  have hc₁ := congrArg (fun x : ℝ => (x : ℂ) * z ^ (3 * n + 1))
    (real_pochhammer_airy_coeff_mod_one n)
  have hc₂ := congrArg (fun x : ℝ => (x : ℂ) * z ^ (3 * n + 2))
    (real_pochhammer_airy_coeff_mod_two n)
  rw [cast_airy_product_rhs] at hc₀ hc₁ hc₂
  have heval (c : ℝ) :
      (ascPochhammer ℂ n).eval (c : ℂ) = (((ascPochhammer ℝ n).eval c : ℝ) : ℂ) := by
    simpa using Polynomial.eval_map_apply Complex.ofRealHom c (p := ascPochhammer ℝ n)
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
    heval, heval, heval, Gamma_ofReal, Gamma_ofReal, pow_add, pow_one]
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
theorem airyAi_sq_add_airyBi_sq_ofReal_eq_integral (x : ℝ) :
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
    have hnh : (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by push_cast; ring
    have hexp : (x : ℂ) * t - (t : ℂ) ^ 3 / 12 = ((x * t - t ^ 3 / 12 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hnh, ← ofReal_cpow ht.le, hexp, ← ofReal_exp, ← ofReal_mul]
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

/-- The derivative of `w ↦ ∫₀^∞ tⁿ exp(w t − t³ / 12) t^{−1/2} dt` is obtained by multiplying the
integrand by `t`. -/
theorem hasDerivAt_integral_pow_mul_cexp_sub_cube_div_twelve_mul_cpow (n : ℕ) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ =>
        ∫ t in Ioi (0 : ℝ),
          (t : ℂ) ^ n * cexp (w * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      (∫ t in Ioi (0 : ℝ),
        (t : ℂ) ^ (n + 1) * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
      z := by
  have h := hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_rpow (p := 3) (q := (n : ℝ) - 1 / 2)
    (b := 1 / 12) (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)]) (by norm_num) z
  -- The exponent `q + 1` of the derivative kernel is `(n + 1) - 1/2`.
  have hcast : (((n : ℝ) - 1 / 2 : ℝ) : ℂ) + 1 = ((((n + 1 : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hF (k : ℕ) (w : ℂ) :
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ k * cexp (w * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) =
        ∫ t in Ioi (0 : ℝ),
          (t : ℂ) ^ (((k : ℝ) - 1 / 2 : ℝ) : ℂ) *
            cexp (w * t - ((1 / 12 * t ^ (3 : ℝ) : ℝ) : ℂ)) :=
    setIntegral_congr_fun measurableSet_Ioi fun _ ht =>
      pow_mul_cexp_sub_cube_div_twelve_mul_cpow_eq ht k w
  rw [hcast] at h
  simpa only [hF] using h

/-- Every iterated derivative of `Ai(z)² + Bi(z)²` is represented by the corresponding `tⁿ` moment
of the integral of DLMF 9.11.4. -/
theorem iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral (n : ℕ) (z : ℂ) :
    deriv^[n] (fun w => airyAi w ^ 2 + airyBi w ^ 2) z =
      (π : ℂ) ^ (-3 / 2 : ℂ) *
        ∫ t in Ioi (0 : ℝ),
          (t : ℂ) ^ n * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) := by
  -- The moment integrals form a tower of successive derivatives starting at `Ai² + Bi²`.
  have htower := iteratedDeriv_eq_of_derivative_tower
    (F := fun k w => (π : ℂ) ^ (-3 / 2 : ℂ) *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ k * cexp (w * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))
    (fun k w => (hasDerivAt_integral_pow_mul_cexp_sub_cube_div_twelve_mul_cpow k w).const_mul
      ((π : ℂ) ^ (-3 / 2 : ℂ))) n
  have h0 : (fun w => (π : ℂ) ^ (-3 / 2 : ℂ) *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 0 * cexp (w * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) =
      fun w => airyAi w ^ 2 + airyBi w ^ 2 := by
    funext w
    simpa only [pow_zero, one_mul] using (airyAi_sq_add_airyBi_sq_eq_integral w).symm
  rw [h0, iteratedDeriv_eq_iterate] at htower
  rw [htower]

/-- For `0 < t`, the combination `M₃ − 4 z M₁ − 2 M₀` of the moment integrands of DLMF 9.11.4 is
the derivative of `t ↦ -4 √t exp(z t - t³ / 12)`. -/
private theorem hasDerivAt_neg_four_mul_sqrt_mul_cexp_sub_cube_div_twelve {t : ℝ} (ht : 0 < t)
    (z : ℂ) :
    HasDerivAt (fun s : ℝ => -4 * (Real.sqrt s : ℂ) * cexp (z * s - (s : ℂ) ^ 3 / 12))
      ((t : ℂ) ^ 3 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) -
          4 * z * ((t : ℂ) ^ 1 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) -
        2 * (cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))) t := by
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
    have hnh : (-1 / 2 : ℂ) = ((-(1 / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hnh, ← ofReal_cpow ht.le, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow, ofReal_inv]
  have hsq : (Real.sqrt t : ℂ) = (t : ℂ) * (Real.sqrt t : ℂ)⁻¹ := by
    simpa only [div_eq_mul_inv, ofReal_mul, ofReal_inv] using
      congrArg (fun x : ℝ => (x : ℂ)) (Real.div_sqrt (x := t)).symm
  rw [hcpow]
  push_cast
  linear_combination -4 * (z - (t : ℂ) ^ 2 / 4) * cexp (z * t - (t : ℂ) ^ 3 / 12) * hsq

/-- The kernel identity behind the product differential equation: the combination
`M₃ − 4 z M₁ − 2 M₀` of the moment integrands of DLMF 9.11.4 integrates to zero. -/
private theorem integral_product_equation_kernel (z : ℂ) :
    ∫ t in Ioi (0 : ℝ),
        ((t : ℂ) ^ 3 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) -
            4 * z * ((t : ℂ) ^ 1 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) -
          2 * (cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ))) = 0 := by
  -- Express the integrand as the derivative of `g(t) = -4 √t exp(z t - t³ / 12)`, which vanishes
  -- at `0` and `∞`, and apply the fundamental theorem of calculus on `(0, ∞)`.
  let g : ℝ → ℂ := fun t => -4 * (Real.sqrt t : ℂ) * cexp (z * t - (t : ℂ) ^ 3 / 12)
  have hcont : Continuous g :=
    (continuous_const.mul (continuous_ofReal.comp Real.continuous_sqrt)).mul
      (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_ofReal).sub
          ((continuous_ofReal.pow 3).div_const 12)))
  have hint := ((integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow 3 z).sub
    ((integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow 1 z).const_mul (4 * z))).sub
    ((integrableOn_cexp_sub_cube_div_twelve_mul_cpow z).const_mul (2 : ℂ))
  -- `g` is `-4` times the power-decay kernel with `p = 3`, `q = 1/2` and `b = 1/12`.
  have htend : Tendsto g atTop (𝓝 0) := by
    have h := (tendsto_cpow_mul_cexp_mul_sub_mul_rpow_atTop (q := 1 / 2) (p := 3) (b := 1 / 12)
      (by norm_num) (by norm_num) z).const_mul (-4)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hsqrt : ((Real.sqrt t : ℝ) : ℂ) = (t : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow, ofReal_cpow ht.le]
    have hexp : z * t - (t : ℂ) ^ 3 / 12 = z * t - ((1 / 12 * t ^ (3 : ℝ) : ℝ) : ℂ) := by
      rw [Real.rpow_ofNat]
      push_cast
      ring
    dsimp only [g]
    rw [hsqrt, hexp]
    ring
  have hibp := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt
    (fun t (ht : 0 < t) => hasDerivAt_neg_four_mul_sqrt_mul_cexp_sub_cube_div_twelve ht z) hint
    htend
  simpa [g] using hibp

/-- `Ai(z)² + Bi(z)²` satisfies the third-order product differential equation
`w''' − 4 z w' − 2 w = 0` (DLMF 9.8.18, 9.11.1). -/
theorem airyAi_sq_add_airyBi_sq_differential_equation (z : ℂ) :
    deriv^[3] (fun w => airyAi w ^ 2 + airyBi w ^ 2) z -
      4 * z * deriv (fun w => airyAi w ^ 2 + airyBi w ^ 2) z -
      2 * (airyAi z ^ 2 + airyBi z ^ 2) = 0 := by
  have hd3 := iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral 3 z
  have hd1 := iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral 1 z
  rw [Function.iterate_one] at hd1
  have h3 := integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow 3 z
  have h1 := (integrableOn_pow_mul_cexp_sub_cube_div_twelve_mul_cpow 1 z).const_mul (4 * z)
  have h0 := (integrableOn_cexp_sub_cube_div_twelve_mul_cpow z).const_mul (2 : ℂ)
  have h31 : IntegrableOn
      (fun t : ℝ =>
        (t : ℂ) ^ 3 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ) -
          4 * z * ((t : ℂ) ^ 1 * cexp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)))
      (Ioi 0) := h3.sub h1
  have hk := integral_product_equation_kernel z
  rw [integral_sub h31 h0, integral_sub h3 h1, integral_const_mul,
    integral_const_mul] at hk
  rw [hd3, hd1, airyAi_sq_add_airyBi_sq_eq_integral]
  linear_combination (π : ℂ) ^ (-3 / 2 : ℂ) * hk

end TauCeti
