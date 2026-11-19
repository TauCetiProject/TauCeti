/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Mellin inversion, Perron kernels and vertical-line bounds

Mathlib's `mellinInv σ f y` is `(1 / 2π) ∫ y^{-(σ + i t)} • f(σ + i t) dt`. This file records that
the integrand is integrable whenever `f` is integrable on the vertical line `Re s = σ` and
`y > 0`, since `t ↦ y^{-(σ + i t)}` is continuous of constant norm `y^{-σ}`.

## Main results

* `Complex.VerticalIntegrable.integrable_cpow_smul`: the integrand of the Mellin inversion
  integral of a vertically integrable function is integrable.
* `TauCeti.integrable_and_integral_norm_cpow_div_ascPochhammer_le`: absolute convergence and a
  full-line L¹ bound for all-order Perron kernels, with separate first/last-factor margins.
* `TauCeti.mellinInv_inv_mul_add_one`: the inverse Mellin transform of `1 / (s(s+1))` is
  `max (1 - x) 0` for positive `x`, on every line `Re s = c > 0`.
* `TauCeti.integral_cpow_div_mul_add_one`: its integral is `2π * max (1 - 1/x) 0` for
  positive `x` and `c`. At the cutoff `x = 1` this value is zero.

The first-order kernel is used for sums smoothed by `1 - n/x`. Its migration is motivated by
the Prime Number Theorem and more project by Alex Kontorovich, Terence Tao and contributors,
`PrimeNumberTheoremAnd/PerronFormula.lean` (`Perron.formulaLtOne`, `Perron.formulaGtOne`). The proof
here composes Mathlib's interval-power Mellin transforms and Mellin inversion, independently of
that project's contour argument. The vertical-line bound generalizes the first-order estimates
`Perron.vertIntBound` and `Perron.vertIntBoundLeft` in the same PNT+ development. Its two endpoint
margins preserve unequal coefficients and give Cauchy-integral control of outward real lines.
-/

public section

open Real MeasureTheory Filter
open Complex hiding exp continuous_exp

namespace Complex

/-- If `f` is integrable on the vertical line `Re s = σ`, then so is the integrand
`t ↦ y^{-(σ + i t)} • f(σ + i t)` of the Mellin inversion integral `mellinInv σ f y`, for
`y > 0`. -/
theorem VerticalIntegrable.integrable_cpow_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {σ : ℝ} (hf : VerticalIntegrable f σ) {y : ℝ} (hy : 0 < y) :
    Integrable fun t : ℝ ↦ (y : ℂ) ^ (-(σ + t * I)) • f (σ + t * I) := by
  -- `t ↦ y^{-(σ + i t)}` is continuous of constant norm `y^{-σ}`
  refine hf.bdd_smul (y ^ (-σ)) ?_ (Eventually.of_forall fun t ↦ ?_)
  · exact (Continuous.const_cpow (by fun_prop)
      (Or.inl (ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · rw [norm_cpow_eq_rpow_re_of_pos hy]
    simp

end Complex

namespace TauCeti

private lemma sqrt_endpoint_le_norm {a c t : ℝ} (ha : 0 ≤ a) (hac : a ≤ |c|) :
    Real.sqrt (a ^ 2 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ := by
  apply (Real.sqrt_le_left (norm_nonneg _)).mpr
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  nlinarith only [ha, hac, sq_abs c]

private lemma mixed_le_cauchy {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    1 / (Real.sqrt (a ^ 2 + t ^ 2) * Real.sqrt (b ^ 2 + t ^ 2)) ≤
      ((min a b) ^ 2 + t ^ 2)⁻¹ := by
  have hd : 0 < min a b := lt_min ha hb
  rw [one_div]
  apply inv_anti₀ (add_pos_of_pos_of_nonneg (sq_pos_of_pos hd) (sq_nonneg t))
  calc
    (min a b) ^ 2 + t ^ 2 =
        Real.sqrt ((min a b) ^ 2 + t ^ 2) * Real.sqrt ((min a b) ^ 2 + t ^ 2) :=
      (Real.mul_self_sqrt (by positivity)).symm
    _ ≤ _ := by
      gcongr <;> nlinarith [min_le_left a b, min_le_right a b]

private lemma mixed_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun t : ℝ ↦ 1 /
      (Real.sqrt (a ^ 2 + t ^ 2) * Real.sqrt (b ^ 2 + t ^ 2))) := by
  have hdcont : Continuous (fun t : ℝ ↦
      Real.sqrt (a ^ 2 + t ^ 2) * Real.sqrt (b ^ 2 + t ^ 2)) :=
    (continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))).mul
      (continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2)))
  have hcont : Continuous (fun t : ℝ ↦ 1 /
      (Real.sqrt (a ^ 2 + t ^ 2) * Real.sqrt (b ^ 2 + t ^ 2))) :=
    continuous_const.div hdcont (fun t ↦ by
      exact (mul_pos (Real.sqrt_pos.2 (by positivity))
        (Real.sqrt_pos.2 (by positivity))).ne')
  have hC : Integrable (fun t : ℝ ↦ ((min a b) ^ 2 + t ^ 2)⁻¹) := by
    simpa only [add_comm] using TauCeti.integrable_inv_sq_add_sq (lt_min ha hb).ne'
  refine hC.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact mixed_le_cauchy ha hb t

private lemma endpoints_le_pochhammer (j : ℕ) (hj : 1 ≤ j) (c t : ℝ)
    (hmid : ∀ k : ℕ, 0 < k → k < j → 1 ≤ |c + k|) :
    ‖(c : ℂ) + t * I‖ * ‖((c + j : ℝ) : ℂ) + t * I‖ ≤
      ‖(ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I)‖ := by
  have hprefix : ∀ n : ℕ, 1 ≤ n → n ≤ j →
      ‖(c : ℂ) + t * I‖ ≤ ‖(ascPochhammer ℂ n).eval ((c : ℂ) + t * I)‖ := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn hnj
      rcases n.eq_zero_or_pos with rfl | hn0
      · simp
      have hfactor : 1 ≤ ‖(c : ℂ) + t * I + n‖ := by
        calc
          1 ≤ |c + n| := hmid n hn0 (by omega)
          _ ≤ ‖(c : ℂ) + t * I + n‖ := by
            simpa using Complex.abs_re_le_norm ((c : ℂ) + t * I + n)
      rw [ascPochhammer_succ_eval, norm_mul]
      exact (ih hn0 (by omega)).trans
        (le_mul_of_one_le_right (norm_nonneg _) hfactor)
  rw [ascPochhammer_succ_eval, norm_mul]
  have heq : (c : ℂ) + t * I + j = ((c + j : ℝ) : ℂ) + t * I := by
    push_cast
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (hprefix j hj le_rfl) (norm_nonneg _)

/-- The all-order Perron kernel is integrable and its full-line L¹ norm is bounded by the
mixed square-root majorant determined by its first and last factors.

The positive margins `a` and `b` bound `|c|` and `|c + j|` from below. Every intermediate real
factor has absolute value at least one, so discarding those factors only increases the bound.
The real part `c` may be positive or negative. For `j = 1` the intermediate condition is empty,
and every line away from `0` and `-1` admits such margins. Zero input is included.

Keeping both margins separate preserves unequal majorants; taking their minimum gives a
scaled Cauchy majorant useful when the vertical line moves outwards. -/
theorem integrable_and_integral_norm_cpow_div_ascPochhammer_le
    (j : ℕ) (hj : 1 ≤ j) {x c a b : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (hb : 0 < b)
    (hac : a ≤ |c|) (hbc : b ≤ |c + j|)
    (hmid : ∀ k : ℕ, 0 < k → k < j → 1 ≤ |c + k|) :
    Integrable (fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + t * I) /
      (ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I)) ∧
    (∫ t : ℝ, ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
      (ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I)‖) ≤
      x ^ c * ∫ t : ℝ, 1 /
        (Real.sqrt (a ^ 2 + t ^ 2) * Real.sqrt (b ^ 2 + t ^ 2)) := by
  have hc : c ≠ 0 := abs_pos.mp (ha.trans_le hac)
  have hden (t : ℝ) : Real.sqrt (a ^ 2 + t ^ 2) * Real.sqrt (b ^ 2 + t ^ 2) ≤
      ‖(ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I)‖ :=
    (mul_le_mul (sqrt_endpoint_le_norm ha.le hac) (sqrt_endpoint_le_norm hb.le hbc)
      (Real.sqrt_nonneg _) (norm_nonneg _)).trans (endpoints_le_pochhammer j hj c t hmid)
  have hne (t : ℝ) : (ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I) ≠ 0 := by
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le (by positivity) (hden t)
  rcases hx.eq_or_lt with rfl | hx
  · have hz (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
      intro h
      exact hc (by simpa using congrArg Complex.re h)
    simp only [Complex.ofReal_zero, Complex.zero_cpow (hz _), zero_div, norm_zero,
      integral_zero, Real.zero_rpow hc, zero_mul]
    exact ⟨integrable_zero ℝ ℂ volume, le_rfl⟩
  have hmajor := (mixed_integrable ha hb).const_mul (x ^ c)
  have hcont : Continuous (fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + t * I) /
      (ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I)) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hx.ne'))).div
      ((Polynomial.continuous _).comp (by fun_prop)) hne
  have hpoint (t : ℝ) : ‖(x : ℂ) ^ ((c : ℂ) + t * I) /
      (ascPochhammer ℂ (j + 1)).eval ((c : ℂ) + t * I)‖ ≤
      x ^ c * (1 / (Real.sqrt (a ^ 2 + t ^ 2) * Real.sqrt (b ^ 2 + t ^ 2))) := by
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx]
    simp only [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (by positivity) (hden t)
  have hint := hmajor.mono' hcont.aestronglyMeasurable (Eventually.of_forall hpoint)
  refine ⟨hint, ?_⟩
  simpa only [integral_const_mul] using
    integral_mono hint.norm hmajor hpoint

/-- The inverse Mellin transform of `1 / (s(s+1))` is the continuous first-order cutoff. -/
theorem mellinInv_inv_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    mellinInv c (fun s : ℂ ↦ (s * (s + 1))⁻¹) x = (max (1 - x) 0 : ℝ) := by
  have hm (t : ℝ) : mellin (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) ((c : ℂ) + t * I) =
      ((((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))⁻¹) :=
    (hasMellin_max_one_sub_zero (by simpa using hc)).2
  have hv : VerticalIntegrable (mellin (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ))) c := by
    have hint := integrable_and_integral_norm_cpow_div_ascPochhammer_le 1 (by decide)
      (x := 1) (by norm_num) hc (by linarith : 0 < c + 1)
      (le_abs_self c) (by simpa only [Nat.cast_one] using le_abs_self (c + 1))
      (by intro k hk hk1; omega)
    simpa [VerticalIntegrable, hm, ascPochhammer_succ_eval, ascPochhammer_zero, one_div]
      using hint.1
  have h := mellinInv_mellin_eq c (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) hx
    (hasMellin_max_one_sub_zero (by simpa using hc)).1 hv (by fun_prop)
  rw [mellinInv] at h ⊢
  simpa only [hm] using h

private lemma riesz_integrand_eq {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ (-s) • (s * (s + 1))⁻¹ = (x : ℂ) ^ s / (s * (s + 1)) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx, Complex.cpow_neg, inv_inv,
    smul_eq_mul, ← div_eq_mul_inv]

/-- The integral of `x^s / (s(s+1))` on a positive vertical line is the continuous cutoff
weight times `2π`. In particular, its value at `x = 1` is zero. -/
theorem integral_cpow_div_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) =
      ((2 * π : ℝ) : ℂ) * (max (1 - x⁻¹) 0 : ℝ) := by
  have h := mellinInv_inv_mul_add_one hc (inv_pos.mpr hx)
  simp only [mellinInv, riesz_integrand_eq hx.le] at h
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero pi_ne_zero
  apply (inv_mul_eq_iff_eq_mul₀ hπ).mp
  simpa only [Complex.real_smul, one_div, Complex.ofReal_inv] using h

end TauCeti
