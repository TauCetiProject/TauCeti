/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import TauCeti.Analysis.Complex.Coordinates
import TauCeti.Analysis.Complex.NormSq
import TauCeti.Analysis.MellinInversion
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.LSeries.Continuity

/-!
# Perron–Riesz inversion for Dirichlet series

On any pole-free vertical line `Re s = c` (`c ≠ 0` and `c ≠ 1`), for `0 ≤ x`, the Perron–Riesz
kernel

`TauCeti.perronRieszKernel x c t = x ^ (c + i t) / ((c + i t) * (c + i t - 1))`

is continuous and absolutely integrable over `t ∈ ℝ` (being
`O((min |c| |c - 1|)² + t²)⁻¹`), and at every non-pole height decomposes by partial fractions as
`x * perronIntegrand x (c - 1) t - perronIntegrand x c t`. For `0 ≤ x` and `c > 1`, shifting `c` by
`1` to the Mellin inversion integral `TauCeti.integral_cpow_div_mul_add_one` yields

`((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, perronRieszKernel x c t = if 1 ≤ x then x - 1 else 0`.

For `0 ≤ y` and `c > 1`, summing termwise against an absolutely convergent Dirichlet series
`LSeriesSummable a (c : ℂ)` via `MeasureTheory.integral_tsum` gives the absolutely convergent
inversion formula for the first Riesz sum:

`((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, LSeries a (c + i t) * perronRieszKernel y c t =`
`  TauCeti.rieszSum a y`.

## Main definitions

* `TauCeti.perronRieszKernel`: the Perron–Riesz kernel
  `x ^ (c + i t) / ((c + i t) * (c + i t - 1))`.

## Main results

* `TauCeti.perronRieszKernel_eq_sub`: partial-fraction decomposition into `TauCeti.perronIntegrand`.
* `TauCeti.norm_perronRieszKernel_le`: quadratic decay bound in height `t` for `0 ≤ x`.
* `TauCeti.integrable_perronRieszKernel`, `TauCeti.inv_mul_integral_perronRieszKernel`: full-line
  integrability for `0 ≤ x`, `c ≠ 0`, `c ≠ 1` and evaluation against `if 1 ≤ x then x - 1 else 0`
  for `0 ≤ x`, `1 < c`.
* `TauCeti.integrable_LSeries_mul_perronRieszKernel`,
  `TauCeti.inv_mul_integral_LSeries_mul_perronRieszKernel_eq_rieszSum`:
  absolute integrability along pole-free lines (`0 ≤ y`, `c ≠ 0`, `c ≠ 1`) and the Perron–Riesz
  inversion formula (`0 ≤ y`, `1 < c`).

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Chapter 5.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, §3.12 and §9.
* Alex Kontorovich, Terence Tao et al., *Prime Number Theorem and more*,
  `PrimeNumberTheoremAnd/PerronFormula.lean` (`Perron.formulaLtOne`, `Perron.formulaGtOne`) as
  the cutoff precedent; `TauCeti.integral_cpow_div_mul_add_one` proves the first-order Mellin
  cutoff directly via Mellin inversion rather than contour shifts.
-/

public section

open Complex Filter MeasureTheory
open scoped Real Topology

namespace TauCeti

/-- The **Perron–Riesz kernel** at ratio `x`, abscissa `c`, and height `t`:
`x ^ (c + i t) / ((c + i t) * (c + i t - 1))`. -/
noncomputable def perronRieszKernel (x c t : ℝ) : ℂ :=
  (x : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I - 1))

/-- Defining equation of `TauCeti.perronRieszKernel`. -/
theorem perronRieszKernel_def (x c t : ℝ) :
    perronRieszKernel x c t =
      (x : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I - 1)) :=
  (rfl)

/-- At ratio zero, the Perron–Riesz kernel vanishes. -/
@[simp]
theorem perronRieszKernel_zero (c t : ℝ) : perronRieszKernel 0 c t = 0 := by
  by_cases hline : (c : ℂ) + t * I = 0
  · simp [perronRieszKernel_def, hline]
  · rw [perronRieszKernel_def, Complex.ofReal_zero, Complex.zero_cpow hline, zero_div]

/-- At ratio one, the Perron–Riesz kernel equals `((c + i t) * (c + i t - 1))⁻¹`. -/
@[simp]
theorem perronRieszKernel_one (c t : ℝ) :
    perronRieszKernel 1 c t = (((c : ℂ) + t * I) * ((c : ℂ) + t * I - 1))⁻¹ := by
  rw [perronRieszKernel_def, Complex.ofReal_one, Complex.one_cpow, one_div]

private theorem perronRieszKernel_eq_mul_shifted (x c t : ℝ) :
    perronRieszKernel x c t = (x : ℂ) * ((x : ℂ) ^ (((c - 1 : ℝ) : ℂ) + t * I) /
      ((((c - 1 : ℝ) : ℂ) + t * I) * ((((c - 1 : ℝ) : ℂ) + t * I) + 1))) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [perronRieszKernel_def, mul_div_assoc', ← Complex.ofReal_add_mul_I_sub_one c t,
      Complex.mul_cpow_sub_one (Complex.ofReal_ne_zero.mpr hx)]
    congr 1
    ring

/-- Partial-fraction decomposition of the Perron–Riesz kernel in terms of `TauCeti.perronIntegrand`
away from the two poles `0` and `1`. -/
theorem perronRieszKernel_eq_sub (x c t : ℝ) (h0 : (c : ℂ) + t * I ≠ 0)
    (h1 : (c : ℂ) + t * I ≠ 1) :
    perronRieszKernel x c t = (x : ℂ) * perronIntegrand x (c - 1) t - perronIntegrand x c t := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h1' : (c : ℂ) + t * I - 1 ≠ 0 := sub_ne_zero.mpr h1
    rw [perronRieszKernel_def, perronIntegrand_def, perronIntegrand_def, mul_div_assoc',
      ← Complex.ofReal_add_mul_I_sub_one c t,
      Complex.mul_cpow_sub_one (Complex.ofReal_ne_zero.mpr hx)]
    field_simp
    ring

/-- Pointwise quadratic decay of the Perron–Riesz kernel for `0 ≤ x`:
`‖perronRieszKernel x c t‖ ≤ x ^ c / ((min |c| |c - 1|) ^ 2 + t ^ 2)`. -/
theorem norm_perronRieszKernel_le {x : ℝ} (hx : 0 ≤ x) (c t : ℝ) :
    ‖perronRieszKernel x c t‖ ≤ x ^ c / ((min |c| |c - 1|) ^ 2 + t ^ 2) := by
  set δ : ℝ := min |c| |c - 1|
  have hδ : 0 ≤ δ := le_min (abs_nonneg c) (abs_nonneg (c - 1))
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · rw [perronRieszKernel_zero c t, norm_zero]
    exact div_nonneg (Real.rpow_nonneg hx c) (by positivity)
  · rcases eq_or_lt_of_le (show 0 ≤ δ ^ 2 + t ^ 2 by positivity) with h0 | hpos
    · have ht : t = 0 := by nlinarith [sq_nonneg δ, sq_nonneg t]
      have hδ0 : δ = 0 := by nlinarith [sq_nonneg δ, sq_nonneg t]
      subst ht
      have hker : perronRieszKernel x c 0 = 0 := by
        rcases min_choice |c| |c - 1| with hmin | hmin
        · have hc : c = 0 := abs_eq_zero.mp (hmin ▸ hδ0)
          simp [perronRieszKernel_def, hc]
        · have hc : c = 1 := sub_eq_zero.mp (abs_eq_zero.mp (hmin ▸ hδ0))
          simp [perronRieszKernel_def, hc]
      rw [hker, norm_zero, ← h0, div_zero]
    · have hnum : ‖(x : ℂ) ^ ((c : ℂ) + t * I)‖ = x ^ c := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
        simp
      have hn1 : Real.sqrt (δ ^ 2 + t ^ 2) ≤ ‖(c : ℂ) + t * I‖ :=
        Complex.sqrt_sq_add_sq_le_norm_add_mul_I hδ (min_le_left _ _)
      have hn2 : Real.sqrt (δ ^ 2 + t ^ 2) ≤ ‖(c : ℂ) + t * I - 1‖ := by
        rw [Complex.ofReal_add_mul_I_sub_one c t]
        exact Complex.sqrt_sq_add_sq_le_norm_add_mul_I hδ (min_le_right _ _)
      have hden : δ ^ 2 + t ^ 2 ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I - 1‖ := by
        calc δ ^ 2 + t ^ 2
            = Real.sqrt (δ ^ 2 + t ^ 2) * Real.sqrt (δ ^ 2 + t ^ 2) :=
              (Real.mul_self_sqrt (by positivity)).symm
          _ ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I - 1‖ :=
              mul_le_mul hn1 hn2 (Real.sqrt_nonneg _) (norm_nonneg _)
      rw [perronRieszKernel_def, norm_div, norm_mul, hnum]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx c) hpos hden

/-- The Perron–Riesz kernel is continuous in the height `t` on any pole-free line `c ≠ 0, c ≠ 1`. -/
theorem continuous_perronRieszKernel (x : ℝ) {c : ℝ} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    Continuous (perronRieszKernel x c) := by
  rcases eq_or_ne x 0 with rfl | hx
  · have : perronRieszKernel 0 c = 0 := funext fun t ↦ perronRieszKernel_zero c t
    rw [this]
    exact continuous_const
  · have hsub : perronRieszKernel x c =
        fun t : ℝ ↦ (x : ℂ) * perronIntegrand x (c - 1) t - perronIntegrand x c t :=
      funext fun t ↦ perronRieszKernel_eq_sub x c t (Complex.ofReal_add_mul_I_ne_zero hc0 t)
        (fun h ↦ Complex.ofReal_add_mul_I_sub_one_ne_zero hc1 t (sub_eq_zero.mpr h))
    rw [hsub]
    exact (continuous_const.mul (continuous_perronIntegrand hx (sub_ne_zero.mpr hc1))).sub
      (continuous_perronIntegrand hx hc0)

/-- The Perron–Riesz kernel `t ↦ perronRieszKernel x c t` is integrable over `ℝ` for `0 ≤ x` on
any pole-free line `c ≠ 0, c ≠ 1`. -/
theorem integrable_perronRieszKernel {x c : ℝ} (hx : 0 ≤ x) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    Integrable (perronRieszKernel x c) := by
  have hc1' : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  have hint := (TauCeti.integrable_and_integral_norm_cpow_div_ascPochhammer_le 1 le_rfl
    (c := c - 1) hx (abs_pos.mpr hc1') (abs_pos.mpr hc0) le_rfl (by simp)
    (by intro k hk hk1; omega)).1.const_mul (x : ℂ)
  refine hint.congr (.of_forall fun t ↦ ?_)
  rw [perronRieszKernel_eq_mul_shifted x c t]
  simp [ascPochhammer_succ_eval]

/-- **Evaluation of the Perron–Riesz kernel**: for `0 ≤ x` and `1 < c`,
`((2 * π)⁻¹) * ∫ t : ℝ, perronRieszKernel x c t = if 1 ≤ x then x - 1 else 0`. -/
theorem inv_mul_integral_perronRieszKernel {x c : ℝ} (hx : 0 ≤ x) (hc : 1 < c) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, perronRieszKernel x c t =
      if 1 ≤ x then (x : ℂ) - 1 else 0 := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp
  · have hshift : (fun t : ℝ ↦ perronRieszKernel x c t) = fun t : ℝ ↦
        (x : ℂ) * ((x : ℂ) ^ (((c - 1 : ℝ) : ℂ) + t * I) /
          ((((c - 1 : ℝ) : ℂ) + t * I) * ((((c - 1 : ℝ) : ℂ) + t * I) + 1))) :=
      funext fun t ↦ perronRieszKernel_eq_mul_shifted x c t
    have hint := integral_cpow_div_mul_add_one (sub_pos.mpr hc) hxpos
    rw [hshift, integral_const_mul, hint]
    have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hcancel : ((2 * π : ℝ) : ℂ)⁻¹ * (x : ℂ) *
        (((2 * π : ℝ) : ℂ) * ((max (1 - x⁻¹) 0 : ℝ) : ℂ)) =
        (x : ℂ) * ((max (1 - x⁻¹) 0 : ℝ) : ℂ) := by
      field_simp
    rw [← mul_assoc, hcancel]
    by_cases hx1 : 1 ≤ x
    · have hnn : 0 ≤ 1 - x⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hx1)
      have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
      simp only [hx1, ↓reduceIte, max_eq_left hnn, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_inv]
      field_simp
    · have hle : 1 - x⁻¹ ≤ 0 := sub_nonpos.mpr ((one_le_inv₀ hxpos).mpr (not_le.mp hx1).le)
      simp [hx1, max_eq_right hle]

/-- Collecting the `n`-th `L`-series term into `TauCeti.perronRieszKernel`. -/
theorem term_mul_perronRieszKernel (y c : ℝ) (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t =
      a n * perronRieszKernel (y / n) c t := by
  rcases eq_or_ne n 0 with rfl | hn
  · by_cases h0 : (c : ℂ) + t * I = 0 <;> simp [perronRieszKernel_def, h0]
  · rw [LSeries.term_of_ne_zero hn, perronRieszKernel_def, perronRieszKernel_def,
      Complex.ofReal_div, div_ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
    ring

private theorem lintegral_norm_term_mul_perronRieszKernel_ne_top {a : ℕ → ℂ} {y c : ℝ} (hy : 0 ≤ y)
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) (h : LSeriesSummable a (c : ℂ)) :
    ∑' n : ℕ, ∫⁻ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t‖ₑ ≠ ⊤ := by
  have hk := integrable_perronRieszKernel hy hc0 hc1
  set I0 : ENNReal := ∫⁻ t : ℝ, ‖perronRieszKernel y c t‖ₑ
  have hI0 : I0 < ⊤ := hk.hasFiniteIntegral
  have hstep : ∀ n : ℕ, ∫⁻ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t‖ₑ ≤
      ‖LSeries.term a (c : ℂ) n‖ₑ * I0 := by
    intro n
    have hle : ∀ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t‖ₑ ≤
        ‖LSeries.term a (c : ℂ) n‖ₑ * ‖perronRieszKernel y c t‖ₑ := fun t ↦ by
      rw [eNorm_mul, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm]
      refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by positivity)
      exact LSeries.norm_term_le_of_re_le_re a (by simp) n
    calc ∫⁻ t : ℝ, ‖LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t‖ₑ
        ≤ ∫⁻ t : ℝ, ‖LSeries.term a (c : ℂ) n‖ₑ * ‖perronRieszKernel y c t‖ₑ :=
          lintegral_mono hle
      _ = ‖LSeries.term a (c : ℂ) n‖ₑ * I0 :=
          lintegral_const_mul'' _ hk.aestronglyMeasurable.eNorm
  refine ne_of_lt (lt_of_le_of_lt (tsum_le_tsum hstep) ?_)
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_lt_top ?_ hI0
  have hfin : ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖ₑ =
      ENNReal.ofReal (∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖) := by
    simp_rw [← ofReal_norm]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ norm_nonneg _) h.norm).symm
  rw [hfin]
  exact ENNReal.ofReal_lt_top

/-- **Integrability in Perron–Riesz inversion**: for `0 ≤ y` on any pole-free line `c ≠ 0, c ≠ 1`,
`t ↦ LSeries a (c + i t) * perronRieszKernel y c t` is integrable on `ℝ` (when `LSeriesSummable`
fails at `c`, `LSeries` vanishes along the line so the integrand is zero). -/
theorem integrable_LSeries_mul_perronRieszKernel (a : ℕ → ℂ) {y c : ℝ} (hy : 0 ≤ y)
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    Integrable fun t : ℝ ↦ LSeries a ((c : ℂ) + t * I) * perronRieszKernel y c t := by
  by_cases h : LSeriesSummable a (c : ℂ)
  · exact (integrable_perronRieszKernel hy hc0 hc1).bdd_mul
      (TauCeti.LSeries.continuous_vertical a (c : ℂ)).aestronglyMeasurable
      (.of_forall fun t ↦ h.norm_LSeries_le (by simp))
  · have hzero : (fun t : ℝ ↦ LSeries a ((c : ℂ) + t * I) * perronRieszKernel y c t) = 0 := by
      ext t
      have hz : LSeries a ((c : ℂ) + t * I) = 0 :=
        LSeries.eq_zero_of_not_LSeriesSummable _ _ fun hs ↦
          h ((LSeriesSummable_iff_of_re_eq_re (by simp)).mp hs)
      simp [hz]
    rw [hzero]
    exact integrable_zero ℝ ℂ volume

/-- **Perron–Riesz inversion formula**: for `1 < c`, `0 ≤ y`, and
`LSeriesSummable a (c : ℂ)`,
`((2 * π)⁻¹) * ∫ t : ℝ, LSeries a (c + i t) * perronRieszKernel y c t = TauCeti.rieszSum a y`. -/
theorem inv_mul_integral_LSeries_mul_perronRieszKernel_eq_rieszSum {a : ℕ → ℂ} {y c : ℝ}
    (hy : 0 ≤ y) (hc : 1 < c) (h : LSeriesSummable a (c : ℂ)) :
    ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * perronRieszKernel y c t =
      rieszSum a y := by
  have hc0 : c ≠ 0 := by linarith
  have hc1 : c ≠ 1 := by linarith
  have htsum : ∀ t : ℝ, LSeries a ((c : ℂ) + t * I) * perronRieszKernel y c t =
      ∑' n : ℕ, LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t :=
    fun t ↦ tsum_mul_right.symm
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun t : ℝ ↦ LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t) := fun n ↦
    ((TauCeti.LSeries.continuous_term_vertical a (c : ℂ) n).mul
      (continuous_perronRieszKernel y hc0 hc1)).aestronglyMeasurable
  simp_rw [htsum]
  rw [MeasureTheory.integral_tsum hmeas
    (lintegral_norm_term_mul_perronRieszKernel_ne_top hy hc0 hc1 h), ← tsum_mul_left]
  have hterm : ∀ n : ℕ, ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, LSeries.term a ((c : ℂ) + t * I) n * perronRieszKernel y c t =
      if 1 ≤ n ∧ (n : ℝ) ≤ y then a n * ((y : ℂ) / n - 1) else 0 := by
    intro n
    simp_rw [term_mul_perronRieszKernel y c a n]
    rw [integral_const_mul, mul_left_comm,
      inv_mul_integral_perronRieszKernel (div_nonneg hy (Nat.cast_nonneg n)) hc]
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      simp only [hn1, true_and, one_le_div hnpos]
      split_ifs <;> simp [Complex.ofReal_div]
  simp_rw [hterm]
  exact tsum_ite_mul_div_sub_one_eq_rieszSum a y

end TauCeti
