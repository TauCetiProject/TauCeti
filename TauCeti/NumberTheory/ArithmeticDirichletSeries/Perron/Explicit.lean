/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron.Formula
public import TauCeti.Analysis.Asymptotics.BigOStar
import TauCeti.Analysis.Complex.Coordinates
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The explicit truncated Perron formula

For an `L`-series `F(s) = ∑ aₙ n⁻ˢ` converging absolutely on the line `Re s = c > 0`, the
truncated Perron integral `(2πi)⁻¹ ∫_{c-iT}^{c+iT} F(s) xˢ ds / s` approximates the summatory
function `∑_{n ≤ x} aₙ`. This file gives the error with explicit constants, in the two forms
of the explicit literature. Both hold at every `x ≥ 0`, including an integer `x` carrying a
nonzero coefficient, which the smoothed-step estimate
`TauCeti.norm_truncatedPerron_LSeries_sub_sum_le` excludes.

The input is a bound for the truncated Perron kernel `K(y) = TauCeti.truncatedPerronKernel y c T`
against the right-continuous step `1_{y ≥ 1}`. Besides the smoothed-step estimate
`|K(y) - 1_{y ≥ 1}| ≤ y ^ c / (π T |log y|)`, valid for `y ≠ 1`, the kernel is compared with
`y ^ c` times its value `π⁻¹ arctan (T / c)` at `y = 1`, to within `T |log y| y ^ c / π`; this
uses `|e^{iθ} - 1| ≤ |θ|` on the line of integration. Switching between the two estimates at
`T |log y| = θ'`, where `θ' = 2 / (√(π ^ 2 + 4) + π)` is the positive root of `θ ^ 2 + π θ = 1`,
gives the uniform bound `|K(y) - 1_{y ≥ 1}| ≤ y ^ c / (π max(θ', T |log y|))`. Weighting it by
`|aₙ|` at `y = x / n` and summing gives the explicit formula.

## Main results

* `TauCeti.perronKernelCutoff`: the constant `θ'`, with `θ' ^ 2 + π θ' = 1`.
* `TauCeti.norm_truncatedPerronKernel_sub_rpow_mul_arctan_le`: the comparison of the kernel with
  `y ^ c` times its endpoint value.
* `TauCeti.norm_truncatedPerronKernel_sub_ite_le`: the uniform bound for the kernel against the
  step `1_{y ≥ 1}` (Cully-Hugill and Johnston, Lemma 2.2).
* `TauCeti.bigOStar_sum_truncatedPerron_LSeries`: the explicit Perron formula with the error
  `∑ₙ (|aₙ| / n ^ c) x ^ c / (π max(θ', T |log (x / n)|))`.
* `TauCeti.bigOStar_sum_truncatedPerron_LSeries_integral_Ioi`: Ramaré's form, with the error
  `∫_{1/T}^∞ ∑_{|log (x / n)| ≤ u} (|aₙ| / n ^ c) 2 x ^ c du / (T u²)` (Ramaré, Theorem 7.1).
* `TauCeti.bigOStar_sum_truncatedPerron_LSeries_cutoff`: the form with a free cut-off `L > 0`
  (Cully-Hugill and Johnston, Theorem 2.1).

## References

* O. Ramaré, *Eigenvalues in the large sieve inequality*, Funct. Approx. Comment. Math. 37
  (2007), Theorem 7.1.
* M. Cully-Hugill and D. R. Johnston, *On the error term in the explicit formula of Riemann–von
  Mangoldt*, arXiv:2111.10001, Lemma 2.2 and Theorem 2.1.
-/

public section

namespace TauCeti

open Complex Filter MeasureTheory Set

open scoped Real

/-! ### The cut-off -/

/-- The cut-off `θ' = 2 / (√(π ^ 2 + 4) + π) = 0.29130…` of Cully-Hugill and Johnston, the
positive root of `θ ^ 2 + π θ = 1`. The truncated Perron kernel at a ratio `y` is estimated
through its endpoint value when `T |log y| < θ'` and through the smoothed-step bound otherwise;
the two estimates agree at `T |log y| = θ'`. -/
noncomputable def perronKernelCutoff : ℝ :=
  2 / (√(π ^ 2 + 4) + π)

/-- Defining equation of `TauCeti.perronKernelCutoff`. -/
theorem perronKernelCutoff_def : perronKernelCutoff = 2 / (√(π ^ 2 + 4) + π) :=
  (rfl)

/-- `θ'` is positive. -/
theorem perronKernelCutoff_pos : 0 < perronKernelCutoff := by
  rw [perronKernelCutoff_def]
  positivity

/-- `θ'` is a root of `θ ^ 2 + π θ = 1`. -/
theorem perronKernelCutoff_sq_add_pi_mul :
    perronKernelCutoff ^ 2 + π * perronKernelCutoff = 1 := by
  have hs : √(π ^ 2 + 4) ^ 2 = π ^ 2 + 4 := Real.sq_sqrt (by positivity)
  rw [perronKernelCutoff_def]
  field_simp
  linear_combination -hs

/-! ### The truncated Perron kernel -/

/-- On the line `Re s = c`, the Perron integrand at a positive ratio `y` differs from `y ^ c`
times its value at `y = 1` by at most `y ^ c |log y|`, uniformly in the height. -/
private theorem norm_perronIntegrand_sub_rpow_mul_le {y c : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖perronIntegrand y c t - ((y ^ c : ℝ) : ℂ) * perronIntegrand 1 c t‖ ≤
      y ^ c * |Real.log y| := by
  by_cases hz : (c : ℂ) + t * I = 0
  · simp only [perronIntegrand_def, hz, div_zero, mul_zero, sub_zero, norm_zero]
    positivity
  have hz' : 0 < ‖(c : ℂ) + t * I‖ := norm_pos_iff.2 hz
  have hnum : perronIntegrand y c t - ((y ^ c : ℝ) : ℂ) * perronIntegrand 1 c t =
      ((y ^ c : ℝ) : ℂ) * (exp (I * (t * Real.log y : ℝ)) - 1) / ((c : ℂ) + t * I) := by
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
    have hpow : (y : ℂ) ^ ((c : ℂ) + t * I) =
        ((y ^ c : ℝ) : ℂ) * exp (I * (t * Real.log y : ℝ)) := by
      rw [cpow_add _ _ hy0, ← ofReal_cpow hy.le, cpow_def_of_ne_zero hy0, ← ofReal_log hy.le]
      push_cast
      ring_nf
    rw [perronIntegrand_def, perronIntegrand_one, hpow]
    field_simp
  have him : |t| ≤ ‖(c : ℂ) + t * I‖ := by
    simpa using abs_im_le_norm ((c : ℂ) + t * I)
  have hexp := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * Real.log y)
  rw [Real.norm_eq_abs, abs_mul] at hexp
  rw [hnum, norm_div, norm_mul, norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hy.le c),
    div_le_iff₀ hz']
  calc y ^ c * ‖exp (I * (t * Real.log y : ℝ)) - 1‖ ≤ y ^ c * (|t| * |Real.log y|) := by gcongr
    _ ≤ y ^ c * (‖(c : ℂ) + t * I‖ * |Real.log y|) := by gcongr
    _ = y ^ c * |Real.log y| * ‖(c : ℂ) + t * I‖ := by ring

/-- **The truncated Perron kernel against its endpoint value** (Cully-Hugill and Johnston,
Lemma 2.2, second bound). At a ratio `y ≥ 0` the kernel of height `T ≥ 0` differs from
`y ^ c` times its value `π⁻¹ arctan (T / c)` at `y = 1` by at most `T |log y| y ^ c / π`. -/
theorem norm_truncatedPerronKernel_sub_rpow_mul_arctan_le {y c T : ℝ} (hy : 0 ≤ y) (hc : c ≠ 0)
    (hT : 0 ≤ T) :
    ‖truncatedPerronKernel y c T - ((y ^ c * (π⁻¹ * Real.arctan (T / c)) : ℝ) : ℂ)‖ ≤
      T * |Real.log y| * y ^ c / π := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [Real.zero_rpow hc]
  have hsplit : truncatedPerronKernel y c T - ((y ^ c * (π⁻¹ * Real.arctan (T / c)) : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T,
        (perronIntegrand y c t - ((y ^ c : ℝ) : ℂ) * perronIntegrand 1 c t) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_perronIntegrand hy.ne' hc _ _)
      ((intervalIntegrable_perronIntegrand one_ne_zero hc _ _).const_mul _),
      intervalIntegral.integral_const_mul, ofReal_mul, ← truncatedPerronKernel_one hc T,
      truncatedPerronKernel_def, truncatedPerronKernel_def]
    ring
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T) fun t _ ↦ norm_perronIntegrand_sub_rpow_mul_le (c := c) hy t
  rw [show |T - -T| = 2 * T by rw [abs_of_nonneg (by linarith)]; ring] at hbound
  rw [hsplit, norm_mul, norm_inv, norm_real, Real.norm_of_nonneg (by positivity)]
  calc (2 * π)⁻¹ * ‖∫ t in -T..T, (perronIntegrand y c t -
        ((y ^ c : ℝ) : ℂ) * perronIntegrand 1 c t)‖
      ≤ (2 * π)⁻¹ * (y ^ c * |Real.log y| * (2 * T)) := by gcongr
    _ = T * |Real.log y| * y ^ c / π := by
      field_simp

/-- The real number `y ^ c π⁻¹ arctan (T / c)` lies within `y ^ c` of the step `1_{y ≥ 1}`. -/
private theorem norm_rpow_mul_arctan_sub_ite_le {y c T : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c)
    (hT : 0 ≤ T) :
    ‖((y ^ c * (π⁻¹ * Real.arctan (T / c)) : ℝ) : ℂ) - (if 1 ≤ y then 1 else 0)‖ ≤ y ^ c := by
  have ha0 : 0 ≤ π⁻¹ * Real.arctan (T / c) :=
    mul_nonneg (inv_nonneg.2 Real.pi_pos.le) (Real.arctan_nonneg.2 (div_nonneg hT hc))
  have ha1 : π⁻¹ * Real.arctan (T / c) ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ Real.pi_pos]
    linarith [Real.arctan_lt_pi_div_two (T / c)]
  have hyc := Real.rpow_nonneg hy c
  split_ifs with h1
  · have h1' : 1 ≤ y ^ c := Real.one_le_rpow h1 hc
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  · rw [sub_zero, norm_real, Real.norm_of_nonneg (by positivity)]
    nlinarith

/-- **The truncated Perron kernel against the step `1_{y ≥ 1}`** (Cully-Hugill and Johnston,
Lemma 2.2). For `y > 0`, `c > 0` and `T > 0`,
`|K(y) - 1_{y ≥ 1}| ≤ y ^ c / (π max(θ', T |log y|))`, where `K` is the truncated Perron kernel
and `θ'` is `TauCeti.perronKernelCutoff`. When `T |log y| ≥ θ'` this is the smoothed-step bound
`TauCeti.norm_truncatedPerronKernel_sub_step_le`; below the cut-off, the endpoint comparison
`TauCeti.norm_truncatedPerronKernel_sub_rpow_mul_arctan_le` gives `y ^ c (1 + θ' / π)`, which is
`y ^ c / (π θ')`. Unlike the smoothed-step bound it also holds at `y = 1`. -/
theorem norm_truncatedPerronKernel_sub_ite_le {y c T : ℝ} (hy : 0 ≤ y) (hc : 0 < c)
    (hT : 0 ≤ T) :
    ‖truncatedPerronKernel y c T - (if 1 ≤ y then 1 else 0)‖ ≤
      y ^ c / (π * max perronKernelCutoff (T * |Real.log y|)) := by
  have hθ := perronKernelCutoff_pos
  rcases hy.eq_or_lt with rfl | hy
  · simp [Real.zero_rpow hc.ne']
  rcases le_or_gt perronKernelCutoff (T * |Real.log y|) with h | h
  · rw [max_eq_right h, ← mul_assoc]
    have hpos : 0 < T * |Real.log y| := hθ.trans_le h
    have hy1 : y ≠ 1 := by
      rintro rfl
      simp at hpos
    have hT' : 0 < T := pos_of_mul_pos_left hpos (abs_nonneg _)
    have hstep : perronStep y = if 1 ≤ y then 1 else 0 := by
      rcases hy1.lt_or_gt with h1 | h1
      · rw [perronStep_of_lt_one h1, ite_eq_right (not_le.2 h1)]
      · rw [perronStep_of_one_lt h1, ite_eq_left h1.le]
    rw [← hstep]
    exact norm_truncatedPerronKernel_sub_step_le hy hy1 hc hT'
  · rw [max_eq_left h.le]
    have hK := norm_truncatedPerronKernel_sub_rpow_mul_arctan_le hy.le hc.ne' hT
    have hid := perronKernelCutoff_sq_add_pi_mul
    calc ‖truncatedPerronKernel y c T - (if 1 ≤ y then 1 else 0)‖
        ≤ ‖truncatedPerronKernel y c T - ((y ^ c * (π⁻¹ * Real.arctan (T / c)) : ℝ) : ℂ)‖ +
          ‖((y ^ c * (π⁻¹ * Real.arctan (T / c)) : ℝ) : ℂ) - (if 1 ≤ y then 1 else 0)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ T * |Real.log y| * y ^ c / π + y ^ c :=
          add_le_add hK (norm_rpow_mul_arctan_sub_ite_le hy.le hc.le hT)
      _ ≤ perronKernelCutoff * y ^ c / π + y ^ c := by gcongr
      _ = y ^ c / (π * perronKernelCutoff) := by
          field_simp
          linear_combination hid

/-! ### The explicit Perron formula -/

/-- At each index the step and the kernel, weighted by `f n`, differ by at most
`|f n| / n ^ c` times `x ^ c / (π max(θ', T |log (x / n)|))`. The index `0` contributes
nothing on either side. -/
private theorem norm_mul_ite_sub_mul_truncatedPerronKernel_le {f : ℕ → ℂ} {x c T : ℝ}
    (hx : 0 ≤ x) (hc : 0 < c) (hT : 0 ≤ T) (n : ℕ) :
    ‖f n * (if 1 ≤ x / n then 1 else 0) - f n * truncatedPerronKernel (x / n) c T‖ ≤
      ‖LSeries.term f c n‖ *
        (x ^ c / (π * max perronKernelCutoff (T * |Real.log (x / n)|))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [← mul_sub, norm_mul, norm_sub_rev, LSeries.norm_term_eq, ite_eq_right hn.ne', ofReal_re]
  calc ‖f n‖ * ‖truncatedPerronKernel (x / n) c T - (if 1 ≤ x / n then 1 else 0)‖
      ≤ ‖f n‖ * ((x / n) ^ c / (π * max perronKernelCutoff (T * |Real.log (x / n)|))) := by
        gcongr
        exact norm_truncatedPerronKernel_sub_ite_le (div_nonneg hx hcast.le) hc hT
    _ = ‖f n‖ / n ^ c *
        (x ^ c / (π * max perronKernelCutoff (T * |Real.log (x / n)|))) := by
        rw [Real.div_rpow hx hcast.le]
        ring

/-- The error series of `TauCeti.bigOStar_sum_truncatedPerron_LSeries` converges: its terms are
at most `(|f n| / n ^ c) x ^ c / (π θ')`. -/
private theorem summable_perronError {f : ℕ → ℂ} {c : ℝ} (h : LSeriesSummable f c) (x T : ℝ) :
    Summable fun n : ℕ ↦ ‖LSeries.term f c n‖ *
      (x ^ c / (π * max perronKernelCutoff (T * |Real.log (x / n)|))) := by
  have hθ := perronKernelCutoff_pos
  refine Summable.of_norm_bounded
    ((summable_norm_iff.2 h).mul_right (|x ^ c| / (π * perronKernelCutoff))) fun n ↦ ?_
  have hM : 0 < max perronKernelCutoff (T * |Real.log (x / n)|) := lt_max_of_lt_left hθ
  rw [norm_mul, norm_norm, norm_div, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hM.le,
    Real.norm_of_nonneg Real.pi_pos.le]
  gcongr
  exact le_max_left _ _

/-- **The explicit truncated Perron formula.** Let the `L`-series of `f` converge absolutely on
the line `Re s = c > 0`, and let `x ≥ 0` and `T ≥ 0`. Then
`∑_{n ≤ x} f n = (2πi)⁻¹ ∫_{c-iT}^{c+iT} L(f, s) xˢ ds / s + O*(E)` with
`E = ∑ₙ (|f n| / n ^ c) x ^ c / (π max(θ', T |log (x / n)|))`, where `θ'` is
`TauCeti.perronKernelCutoff`; the term of index `n` is `‖LSeries.term f c n‖` times the bound
`TauCeti.norm_truncatedPerronKernel_sub_ite_le` at `y = x / n`. A natural number `x` enters the
sum with full weight, and its term in `E` is finite. -/
theorem bigOStar_sum_truncatedPerron_LSeries {f : ℕ → ℂ} {x c T : ℝ} (hx : 0 ≤ x) (hc : 0 < c)
    (hT : 0 ≤ T) (h : LSeriesSummable f c) :
    BigOStar (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n)
      (((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, LSeries f ((c : ℂ) + t * I) * perronIntegrand x c t)
      (∑' n : ℕ, ‖LSeries.term f c n‖ *
        (x ^ c / (π * max perronKernelCutoff (T * |Real.log (x / n)|)))) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp [Real.zero_rpow hc.ne']
  have herr := summable_perronError h x T
  have hstep := norm_mul_ite_sub_mul_truncatedPerronKernel_le (f := f) hx hc hT
  have hDnorm := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hstep herr
  have hzero : ∀ n ∉ Finset.Icc 1 ⌊x⌋₊, f n * (if 1 ≤ x / n then 1 else 0) = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    have hfl : ⌊x⌋₊ < n := by
      simp only [Finset.mem_Icc, not_and, not_le] at hn
      exact hn hn0
    rw [ite_eq_right (not_le.2 ((div_lt_one hcast).2 ((Nat.floor_lt hx).1 hfl))), mul_zero]
  have hB : Summable fun n : ℕ ↦ f n * (if 1 ≤ x / n then 1 else 0) :=
    summable_of_ne_finset_zero hzero
  have hsum : ∑' n : ℕ, f n * (if 1 ≤ x / n then 1 else 0) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n := by
    rw [tsum_eq_sum hzero]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [Finset.mem_Icc] at hn
    have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn.1
    rw [ite_eq_left ((one_le_div hcast).2 ((Nat.le_floor_iff hx).1 hn.2)), mul_one]
  have hA : Summable fun n : ℕ ↦ f n * truncatedPerronKernel (x / n) c T := by
    simpa using hB.sub hDnorm.of_norm
  rw [bigOStar_iff, truncatedPerron_LSeries hx' hc hT h, ← hsum, ← hB.tsum_sub hA]
  exact (norm_tsum_le_tsum_norm hDnorm).trans (hDnorm.tsum_le_tsum hstep herr)

/-- The weight of the explicit Perron formula is at most that of Ramaré's form:
`X / (π max(θ', T ℓ)) ≤ (2 X / T) (max(T⁻¹, ℓ))⁻¹`, because `2 π θ' ≥ 1`. -/
private theorem div_pi_mul_max_perronKernelCutoff_le {X T ℓ : ℝ} (hX : 0 ≤ X) (hT : 0 < T) :
    X / (π * max perronKernelCutoff (T * ℓ)) ≤ 2 * X / T * (max T⁻¹ ℓ)⁻¹ := by
  have hθ := perronKernelCutoff_pos
  have hid := perronKernelCutoff_sq_add_pi_mul
  have hpi := Real.two_le_pi
  have h1 : 1 ≤ 2 * π * perronKernelCutoff := by nlinarith
  have hM : perronKernelCutoff ≤ max perronKernelCutoff (T * ℓ) := le_max_left _ _
  have hkey : T * max T⁻¹ ℓ ≤ 2 * π * max perronKernelCutoff (T * ℓ) := by
    rw [mul_max_of_nonneg _ _ hT.le, mul_inv_cancel₀ hT.ne']
    refine max_le (h1.trans (by gcongr)) ?_
    nlinarith [le_max_right perronKernelCutoff (T * ℓ)]
  calc X / (π * max perronKernelCutoff (T * ℓ))
      = 2 * X / (2 * π * max perronKernelCutoff (T * ℓ)) := by
        field_simp
    _ ≤ 2 * X / (T * max T⁻¹ ℓ) := by gcongr
    _ = 2 * X / T * (max T⁻¹ ℓ)⁻¹ := by ring

/-- **Ramaré's explicit truncated Perron formula** (Ramaré, Theorem 7.1). Let the `L`-series of
`f` converge absolutely on the line `Re s = c > 0`, and let `x ≥ 0` and `T > 0`. Then
`∑_{n ≤ x} f n = (2πi)⁻¹ ∫_{c-iT}^{c+iT} L(f, s) xˢ ds / s + O*(E)` with
`E = ∫_{1/T}^∞ ∑_{|log (x / n)| ≤ u} (|f n| / n ^ c) 2 x ^ c du / (T u²)`; here
`‖LSeries.term f c n‖` is `|f n| / n ^ c`, and is `0` at `n = 0`. -/
theorem bigOStar_sum_truncatedPerron_LSeries_integral_Ioi {f : ℕ → ℂ} {x c T : ℝ} (hx : 0 ≤ x)
    (hc : 0 < c) (hT : 0 < T) (h : LSeriesSummable f c) :
    BigOStar (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n)
      (((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, LSeries f ((c : ℂ) + t * I) * perronIntegrand x c t)
      (∫ u in Ioi T⁻¹, ∑' n : ℕ, if |Real.log (x / n)| ≤ u then
        ‖LSeries.term f c n‖ * (2 * x ^ c / (T * u ^ 2)) else 0) := by
  have hT' : 0 < T⁻¹ := inv_pos.2 hT
  have hxc := Real.rpow_nonneg hx c
  have hint : IntegrableOn (fun u : ℝ ↦ (u ^ 2)⁻¹) (Ioi T⁻¹) := by
    simpa using integrableOn_Ioi_inv_pow_succ le_rfl hT'
  -- The integral of `u⁻²` over the part `u ≥ b` of `(T⁻¹, ∞)` is `(max T⁻¹ b)⁻¹`.
  have hwin (b : ℝ) :
      ∫ u in Ioi T⁻¹, (Ici b).indicator (fun u : ℝ ↦ (u ^ 2)⁻¹) u = (max T⁻¹ b)⁻¹ := by
    rw [setIntegral_indicator measurableSet_Ici]
    rcases le_or_gt b T⁻¹ with hb | hb
    · rw [inter_eq_left.2 (Ioi_subset_Ici hb), max_eq_left hb]
      simpa using integral_Ioi_inv_pow_succ le_rfl hT'
    · rw [inter_eq_right.2 (Ici_subset_Ioi.2 hb), max_eq_right hb.le,
        integral_Ici_eq_integral_Ioi]
      simpa using integral_Ioi_inv_pow_succ le_rfl (hT'.trans hb)
  have hF (n : ℕ) (u : ℝ) : (if |Real.log (x / n)| ≤ u then
      ‖LSeries.term f c n‖ * (2 * x ^ c / (T * u ^ 2)) else 0) =
        ‖LSeries.term f c n‖ * (2 * x ^ c / T) *
          (Ici |Real.log (x / n)|).indicator (fun u : ℝ ↦ (u ^ 2)⁻¹) u := by
    simp only [indicator_apply, mem_Ici]
    split_ifs <;> ring
  simp only [hF]
  have hval (n : ℕ) : ∫ u in Ioi T⁻¹, ‖LSeries.term f c n‖ * (2 * x ^ c / T) *
      (Ici |Real.log (x / n)|).indicator (fun u : ℝ ↦ (u ^ 2)⁻¹) u =
        ‖LSeries.term f c n‖ * (2 * x ^ c / T) * (max T⁻¹ |Real.log (x / n)|)⁻¹ := by
    rw [integral_const_mul, hwin]
  have hsum : Summable fun n : ℕ ↦
      ‖LSeries.term f c n‖ * (2 * x ^ c / T) * (max T⁻¹ |Real.log (x / n)|)⁻¹ := by
    refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_)
      (((summable_norm_iff.2 h).mul_right (2 * x ^ c / T)).mul_right T)
    gcongr
    exact (inv_anti₀ hT' (le_max_left _ _)).trans_eq (inv_inv T)
  have hnorm : Summable fun n : ℕ ↦ ∫ u in Ioi T⁻¹, ‖‖LSeries.term f c n‖ * (2 * x ^ c / T) *
      (Ici |Real.log (x / n)|).indicator (fun u : ℝ ↦ (u ^ 2)⁻¹) u‖ := by
    refine hsum.congr fun n ↦ ?_
    rw [← hval]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ (Real.norm_of_nonneg ?_).symm
    exact mul_nonneg (by positivity) (indicator_nonneg (fun u _ ↦ by positivity) u)
  rw [← integral_tsum_of_summable_integral_norm
    (fun n ↦ (hint.indicator measurableSet_Ici).const_mul _) hnorm]
  simp only [hval]
  refine (bigOStar_sum_truncatedPerron_LSeries hx hc hT.le h).weaken ?_
  refine (summable_perronError h x T).tsum_le_tsum (fun n ↦ ?_) hsum
  rw [mul_assoc]
  gcongr
  exact div_pi_mul_max_perronKernelCutoff_le hxc hT

/-- The integrand of the cut-off form of the explicit Perron formula is integrable on `(a, L]`
for `a > 0`: it is the restriction to `u ≥ |log (x / n)|` of the continuous function
`|f n| e^{c u} / u²`. -/
private theorem integrableOn_Ioc_ite_norm_mul_exp_div_sq {f : ℕ → ℂ} {x c a L : ℝ} (ha : 0 < a)
    (n : ℕ) :
    IntegrableOn (fun u : ℝ ↦ if 0 < n ∧ |Real.log (x / n)| ≤ u then
      ‖f n‖ * Real.exp (c * u) / u ^ 2 else 0) (Ioc a L) := by
  by_cases hn : 0 < n
  · have hcont : ContinuousOn (fun u : ℝ ↦ ‖f n‖ * Real.exp (c * u) / u ^ 2) (Icc a L) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu ↦
        pow_ne_zero 2 (ha.trans_le hu.1).ne'
    have hi : IntegrableOn (fun u : ℝ ↦ ‖f n‖ * Real.exp (c * u) / u ^ 2) (Ioc a L) :=
      hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    convert hi.indicator (measurableSet_Ici (a := |Real.log (x / n)|)) using 1
    ext u
    simp [indicator_apply, hn]
  · simp [hn]

/-- Beyond `n = ⌊x e^L⌋₊` the integrand of the cut-off form vanishes on `u ≤ L`: there
`|log (x / n)| > L`. -/
private theorem ite_norm_mul_exp_div_sq_eq_zero {f : ℕ → ℂ} {x c L u : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : ⌊x * Real.exp L⌋₊ < n) (hu : u ≤ L) :
    (if 0 < n ∧ |Real.log (x / n)| ≤ u then ‖f n‖ * Real.exp (c * u) / u ^ 2 else 0) = 0 := by
  refine ite_eq_right fun ⟨hn0, hlog⟩ ↦ ?_
  have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hlt : x * Real.exp L < n := (Nat.floor_lt (by positivity)).1 hn
  have hxn : Real.log (x / n) < -L := by
    rw [Real.log_lt_iff_lt_exp (div_pos hx hcast), div_lt_iff₀ hcast, Real.exp_neg,
      inv_mul_eq_div, lt_div_iff₀ (Real.exp_pos L)]
    exact hlt
  linarith [neg_abs_le (Real.log (x / n)), hlog]

/-- Lower bound for the integral of the cut-off form at an index `n > 0`: on `(p, L]`, where
`u ≥ p ≥ |log (x / n)|`, the integrand is at least `|f n| (x / n) ^ c u⁻²`. -/
private theorem mul_sub_le_integral_Ioc_ite_norm_mul_exp_div_sq {f : ℕ → ℂ} {x c a p L : ℝ}
    {n : ℕ} (hn : 0 < n) (hx : 0 < x) (hc : 0 ≤ c) (ha : 0 < a) (hap : a ≤ p)
    (hℓp : |Real.log (x / n)| ≤ p) (hpL : p ≤ L) :
    ‖f n‖ * (x / n) ^ c * (p⁻¹ - L⁻¹) ≤ ∫ u in Ioc a L,
      (if 0 < n ∧ |Real.log (x / n)| ≤ u then ‖f n‖ * Real.exp (c * u) / u ^ 2 else 0) := by
  have hp : 0 < p := ha.trans_le hap
  have hy : 0 < x / n := div_pos hx (Nat.cast_pos.2 hn)
  have hsq : IntegrableOn (fun u : ℝ ↦ (u ^ 2)⁻¹) (Ioi p) := by
    simpa using integrableOn_Ioi_inv_pow_succ le_rfl hp
  have hsq' : IntegrableOn (fun u : ℝ ↦ (u ^ 2)⁻¹) (Ioi a) := by
    simpa using integrableOn_Ioi_inv_pow_succ le_rfl ha
  have hval : ∫ u in Ioc a L, (Ioc p L).indicator (fun u : ℝ ↦ ‖f n‖ * (x / n) ^ c * (u ^ 2)⁻¹) u =
      ‖f n‖ * (x / n) ^ c * (p⁻¹ - L⁻¹) := by
    rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 (Ioc_subset_Ioc_left hap),
      integral_const_mul, ← intervalIntegral.integral_of_le hpL,
      ← intervalIntegral.integral_Ioi_sub_Ioi hsq hpL]
    simp only [integral_Ioi_inv_pow_succ le_rfl hp,
      integral_Ioi_inv_pow_succ le_rfl (hp.trans_le hpL), Nat.cast_one, one_mul, pow_one]
  rw [← hval]
  refine setIntegral_mono_on
    (((hsq'.mono_set Ioc_subset_Ioi_self).const_mul _).indicator measurableSet_Ioc)
    (integrableOn_Ioc_ite_norm_mul_exp_div_sq ha n) measurableSet_Ioc fun u _ ↦ ?_
  simp only [indicator_apply, mem_Ioc]
  split_ifs with h1 h2
  · have hu : 0 < u := hp.trans h1.1
    rw [Real.rpow_def_of_pos hy, mul_comm (Real.log (x / n)) c, ← div_eq_mul_inv]
    gcongr
    linarith [le_abs_self (Real.log (x / n)), h1.1]
  · exact absurd ⟨hn, hℓp.trans h1.1.le⟩ h2
  · positivity
  · exact le_rfl

/-- At each index the weight of the explicit Perron formula is at most that of the cut-off form:
when `max(θ', T |log (x / n)|) < T L`, the integral over `u` recovers the difference between the
two. -/
private theorem perronError_le_cutoff {f : ℕ → ℂ} {x c T L : ℝ} (hx : 0 < x) (hc : 0 < c)
    (hT : 0 < T) (hL : 0 < L) (n : ℕ) :
    ‖LSeries.term f c n‖ * (x ^ c / (π * max perronKernelCutoff (T * |Real.log (x / n)|))) ≤
      x ^ c / (π * L * T) * ‖LSeries.term f c n‖ +
        (π * T)⁻¹ * ∫ u in Ioc (perronKernelCutoff / T) L, (if 0 < n ∧ |Real.log (x / n)| ≤ u
          then ‖f n‖ * Real.exp (c * u) / u ^ 2 else 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hcast : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hθ := perronKernelCutoff_pos
  have ha : 0 < perronKernelCutoff / T := div_pos hθ hT
  set y := x / n with hy_def
  set ℓ := |Real.log y|
  set M := max perronKernelCutoff (T * ℓ)
  have hM : 0 < M := lt_max_of_lt_left hθ
  set K := ‖f n‖ * y ^ c with hK_def
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (div_pos hx hcast).le _)
  have hterm : ‖LSeries.term f c n‖ * x ^ c = K := by
    rw [LSeries.norm_term_eq, ite_eq_right hn.ne', ofReal_re, hK_def, hy_def,
      Real.div_rpow hx.le hcast.le]
    ring
  have hlhs : ‖LSeries.term f c n‖ * (x ^ c / (π * M)) = K / (π * M) := by
    rw [← hterm]; ring
  have hfirst : x ^ c / (π * L * T) * ‖LSeries.term f c n‖ = K / (π * L * T) := by
    rw [← hterm]; ring
  rw [hlhs, hfirst]
  rcases le_or_gt (T * L) M with hML | hML
  · calc K / (π * M) ≤ K / (π * L * T) := by
          rw [mul_assoc]
          exact div_le_div_of_nonneg_left hK (by positivity)
            (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · -- Below `T L`, the integrand dominates `K u⁻²` on `(M / T, L]`.
    set p := M / T with hp_def
    have hap : perronKernelCutoff / T ≤ p := div_le_div_of_nonneg_right (le_max_left _ _) hT.le
    have hℓp : ℓ ≤ p := by rw [le_div_iff₀ hT, mul_comm]; exact le_max_right _ _
    have hpL : p < L := by rw [div_lt_iff₀ hT, mul_comm]; exact hML
    have hlow := mul_sub_le_integral_Ioc_ite_norm_mul_exp_div_sq (f := f) hn hx hc.le ha hap
      hℓp hpL.le
    calc K / (π * M) = K / (π * L * T) + (π * T)⁻¹ * (K * (p⁻¹ - L⁻¹)) := by
          rw [hp_def]
          field_simp
          ring
      _ ≤ _ := by gcongr

/-- **The explicit truncated Perron formula with a free cut-off** (Cully-Hugill and Johnston,
Theorem 2.1). Let the `L`-series of `f` converge absolutely on the line `Re s = c > 0`, and let
`x ≥ 0`, `T > 0` and `L > 0`. Then
`∑_{n ≤ x} f n = (2πi)⁻¹ ∫_{c-iT}^{c+iT} L(f, s) xˢ ds / s + O*(E)` with
`E = (x ^ c / (π L T)) ∑ₙ |f n| / n ^ c + (π T)⁻¹ ∫_{θ'/T}^{L} S(u) du / u²` and
`S(u) = ∑_{|log (x / n)| ≤ u} |f n| e^{c u}`, where `θ'` is `TauCeti.perronKernelCutoff` and
`‖LSeries.term f c n‖` is `|f n| / n ^ c`. The integral is over `(θ'/T, L]`, so that it vanishes
when `L ≤ θ'/T`; the source assumes `L ≥ θ'/T`. -/
theorem bigOStar_sum_truncatedPerron_LSeries_cutoff {f : ℕ → ℂ} {x c T L : ℝ} (hx : 0 ≤ x)
    (hc : 0 < c) (hT : 0 < T) (hL : 0 < L) (h : LSeriesSummable f c) :
    BigOStar (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n)
      (((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in -T..T, LSeries f ((c : ℂ) + t * I) * perronIntegrand x c t)
      (x ^ c / (π * L * T) * ∑' n : ℕ, ‖LSeries.term f c n‖ +
        (π * T)⁻¹ * ∫ u in Ioc (perronKernelCutoff / T) L, ∑' n : ℕ,
          if 0 < n ∧ |Real.log (x / n)| ≤ u then ‖f n‖ * Real.exp (c * u) / u ^ 2 else 0) := by
  rcases hx.eq_or_lt with rfl | hx'
  · -- At `x = 0` both sides of the comparison vanish and the error is nonnegative.
    refine (bigOStar_sum_truncatedPerron_LSeries le_rfl hc hT.le h).weaken ?_
    simp only [Real.zero_rpow hc.ne', zero_div, mul_zero, tsum_zero]
    exact add_nonneg (mul_nonneg (by positivity) (tsum_nonneg fun _ ↦ norm_nonneg _))
      (mul_nonneg (by positivity) (integral_nonneg fun u ↦ tsum_nonneg fun n ↦ by
        split_ifs <;> positivity))
  have ha : 0 < perronKernelCutoff / T := div_pos perronKernelCutoff_pos hT
  -- Only the indices `n ≤ x e^L` contribute to the integral over `u ≤ L`.
  have hzero (n : ℕ) (hn : n ∉ Finset.range (⌊x * Real.exp L⌋₊ + 1)) (u : ℝ)
      (hu : u ∈ Ioc (perronKernelCutoff / T) L) :
      (if 0 < n ∧ |Real.log (x / n)| ≤ u then ‖f n‖ * Real.exp (c * u) / u ^ 2 else 0) = 0 :=
    ite_norm_mul_exp_div_sq_eq_zero hx' (by simpa [Nat.lt_succ_iff] using hn) hu.2
  have hS : Summable fun n : ℕ ↦ ∫ u in Ioc (perronKernelCutoff / T) L,
      (if 0 < n ∧ |Real.log (x / n)| ≤ u then ‖f n‖ * Real.exp (c * u) / u ^ 2 else 0) :=
    summable_of_ne_finset_zero fun n hn ↦ by
      rw [setIntegral_congr_fun measurableSet_Ioc (hzero n hn), integral_zero]
  have hSnorm : Summable fun n : ℕ ↦ ∫ u in Ioc (perronKernelCutoff / T) L,
      ‖if 0 < n ∧ |Real.log (x / n)| ≤ u then ‖f n‖ * Real.exp (c * u) / u ^ 2 else 0‖ :=
    summable_of_ne_finset_zero fun n hn ↦ by
      rw [setIntegral_congr_fun measurableSet_Ioc fun u hu ↦ by rw [hzero n hn u hu, norm_zero],
        integral_zero]
  rw [← integral_tsum_of_summable_integral_norm
    (fun n ↦ integrableOn_Ioc_ite_norm_mul_exp_div_sq ha n) hSnorm, ← tsum_mul_left,
    ← tsum_mul_left, ← Summable.tsum_add ((summable_norm_iff.2 h).mul_left _) (hS.mul_left _)]
  refine (bigOStar_sum_truncatedPerron_LSeries hx hc hT.le h).weaken
    ((summable_perronError h x T).tsum_le_tsum (fun n ↦ perronError_le_cutoff hx' hc hT hL n)
      (((summable_norm_iff.2 h).mul_left _).add (hS.mul_left _)))

end TauCeti
