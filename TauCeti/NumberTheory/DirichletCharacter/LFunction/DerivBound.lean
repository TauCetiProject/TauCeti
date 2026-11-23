/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.NumberTheory.DirichletCharacter.Basic

/-!
# Derivative bounds for continued Dirichlet L-functions near one

Bounding `L'(σ, χ)` uniformly on `[1 - 1 / log N, 1]` controls the slope of the continued
`L`-function near `1`, allowing lower bounds on `L(1, χ)` to be converted via the mean value
theorem into zero-free intervals and effective real-zero separation from `1`. Throughout, `N` is
any nonzero level (`[NeZero N]`), `χ` is any nonprincipal complex Dirichlet character modulo `N`
(not necessarily primitive, so `N` need not be `χ.conductor`), and `DirichletCharacter.LFunction`
denotes the meromorphic continuation rather than the Dirichlet series (which need not converge on
`0 < Re(s) ≤ 1`).

Differentiating the partial-summation continuation
`L(s, χ) = s ∫_1^∞ A(⌊t⌋₊) t ^ (-(s + 1)) dt` gives the absolutely convergent integral
representation

`L'(s, χ) = ∫_1^∞ (∑_{k=1}^{⌊t⌋₊} χ(k)) (1 - s log t) t ^ (-(s + 1)) dt`

on the whole half-plane `Re(s) > 0`, without any zero-free hypothesis. Estimating `(1, N]` and
`(N, ∞)` separately bounds `‖L'(s, χ)‖` throughout `Re(s) > 0` with an explicit `N ^ (1 - Re(s))`
dependence, yields the uniform real-segment bound `‖L'(σ, χ)‖ ≤ 81 (log N) ^ 2` for
`σ ∈ [1 - 1 / log N, 1]`, and combines with nonvanishing on `Re(s) ≥ 1` and the mean value theorem
to give `Re L(1, χ) / (81 (log N) ^ 2) ≤ 1 - β` for every real zero `β` of `L(s, χ)`.

## Main results

* `DirichletCharacter.hasDerivAt_LFunction_of_re_pos`,
  `DirichletCharacter.deriv_LFunction_eq_integral`, and
  `DirichletCharacter.integrableOn_sum_Icc_mul_one_sub_mul_log_mul_cpow`: integral representation
  and absolute integrability of `L'(s, χ)` on `Re(s) > 0` for `χ ≠ 1`.
* `DirichletCharacter.norm_deriv_LFunction_le_of_re_pos`: explicit right-half-plane bound for
  `‖L'(s, χ)‖` when `χ ≠ 1` and `Re(s) > 0`.
* `DirichletCharacter.norm_deriv_LFunction_le_mul_log_sq`: uniform bound
  `‖L'(σ, χ)‖ ≤ 81 * (log N) ^ 2` for `χ ≠ 1` and `σ ∈ [1 - 1 / log N, 1]`.
* `DirichletCharacter.LFunction_one_re_div_log_sq_le_one_sub_of_LFunction_eq_zero`:
  unconditional real-zero separation `Re L(1, χ) / (81 (log N) ^ 2) ≤ 1 - β` for any real zero `β`
  of any nonprincipal character `χ` of nonzero level `N`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  American Mathematical Society, 2019, Lemma 11.2, p. 113, and (12.11), p. 124.
-/

public section

open Finset Filter MeasureTheory Complex Asymptotics
open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- For a nonprincipal character `χ` of nonzero level `N` and `Re(s) > 0`, `χ.LFunction` has
complex derivative `∫_1^∞ (∑_{k=1}^{⌊t⌋₊} χ(k)) (1 - s log t) t ^ (-(s + 1)) dt` at `s`. -/
theorem hasDerivAt_LFunction_of_re_pos (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt χ.LFunction
      (∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1))) s := by
  have heq : χ.LFunction =ᶠ[𝓝 s] fun z : ℂ ↦
      z * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(z + 1)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact χ.LFunction_eq_mul_integral hχ hz
  exact (TauCeti.LSeries.hasDerivAt_mul_integral_of_isBigO _
    (by simpa only [Real.rpow_zero] using χ.isBigO_sum_Icc_one hχ) hs).congr_of_eventuallyEq heq

/-- Integral formula for the complex derivative of the continued L-function of a nonprincipal
character on `Re(s) > 0`. -/
theorem deriv_LFunction_eq_integral (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    deriv χ.LFunction s =
      ∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1)) :=
  (χ.hasDerivAt_LFunction_of_re_pos hχ hs).deriv

/-- For a nonprincipal character `χ` of nonzero level `N` and `Re(s) > 0`, the derivative integrand
`t ↦ (∑_{k=1}^{⌊t⌋₊} χ(k)) (1 - s log t) t ^ (-(s + 1))` appearing in
`deriv_LFunction_eq_integral` is integrable on `(1, ∞)`. -/
theorem integrableOn_sum_Icc_mul_one_sub_mul_log_mul_cpow (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ ↦ (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1)))
      (Set.Ioi 1) :=
  TauCeti.LSeries.integrableOn_sum_mul_one_sub_mul_log_mul_cpow_of_isBigO _
    (by simpa only [Real.rpow_zero] using χ.isBigO_sum_Icc_one hχ) hs

/-- Initial-range estimate on `(1, N]`, using the trivial partial-sum bound `‖∑_{k≤t} χ(k)‖ ≤ t`. -/
private lemma norm_integral_Ioc_le (hχ : χ ≠ 1) {s : ℂ} :
    ‖∫ t in Set.Ioc (1 : ℝ) N,
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1))‖ ≤
      max 1 ((N : ℝ) ^ (1 - s.re)) * (1 + ‖s‖ * Real.log N) * Real.log N := by
  have hN3 := χ.three_le_level_of_ne_one hχ
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  set C := max 1 ((N : ℝ) ^ (1 - s.re)) * (1 + ‖s‖ * Real.log N)
  have hC_int : IntegrableOn (fun t : ℝ ↦ C * t⁻¹) (Set.Ioc (1 : ℝ) N) :=
    (ContinuousOn.integrableOn_Icc (a := (1 : ℝ)) (b := (N : ℝ))
      (continuousOn_const.mul (continuousOn_inv₀.mono fun t (ht : t ∈ Set.Icc (1 : ℝ) N) ↦
        (zero_lt_one.trans_le ht.1).ne'))).mono_set Set.Ioc_subset_Icc_self
  calc
    _ ≤ ∫ t in Set.Ioc (1 : ℝ) N, C * t⁻¹ := by
      refine norm_integral_le_of_norm_le hC_int ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := zero_lt_one.trans ht.1
      have hsum : ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ k‖ ≤ t := by
        calc
          ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ k‖ ≤ ∑ _ ∈ Icc 1 ⌊t⌋₊, (1 : ℝ) :=
            (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ χ.norm_le_one k)
          _ = (⌊t⌋₊ : ℝ) := by simp
          _ ≤ t := Nat.floor_le ht0.le
      have hlog : ‖(1 : ℂ) - s * Real.log t‖ ≤ 1 + ‖s‖ * Real.log N := by
        calc
          ‖(1 : ℂ) - s * Real.log t‖ ≤ ‖(1 : ℂ)‖ + ‖s * (Real.log t : ℂ)‖ := norm_sub_le _ _
          _ = 1 + ‖s‖ * Real.log t := by
            rw [norm_one, norm_mul, Complex.norm_real,
              Real.norm_of_nonneg (Real.log_nonneg ht.1.le)]
          _ ≤ 1 + ‖s‖ * Real.log N := by
            linarith [mul_le_mul_of_nonneg_left (Real.log_le_log ht0 ht.2) (norm_nonneg s)]
      have hpow_max : t ^ (1 - s.re) ≤ max 1 ((N : ℝ) ^ (1 - s.re)) := by
        rcases le_total 0 (1 - s.re) with hle | hle
        · exact (Real.rpow_le_rpow ht0.le ht.2 hle).trans (le_max_right _ _)
        · exact (Real.rpow_le_one_of_one_le_of_nonpos ht.1.le hle).trans (le_max_left _ _)
      have ht_eq : t * t ^ (-(s.re + 1)) = t ^ (1 - s.re) * t⁻¹ := by
        calc
          t * t ^ (-(s.re + 1)) = t ^ (1 : ℝ) * t ^ (-(s.re + 1)) := by rw [Real.rpow_one]
          _ = t ^ (1 - s.re + -1) := by rw [← Real.rpow_add ht0]; congr 1; ring
          _ = t ^ (1 - s.re) * t⁻¹ := by rw [Real.rpow_add ht0, Real.rpow_neg_one]
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [neg_re, add_re, one_re]
      calc
        ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ k‖ * ‖(1 : ℂ) - s * Real.log t‖ * t ^ (-(s.re + 1))
            ≤ (t * (1 + ‖s‖ * Real.log N)) * t ^ (-(s.re + 1)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hsum hlog (norm_nonneg _) ht0.le) (Real.rpow_nonneg ht0.le _)
        _ = (t * t ^ (-(s.re + 1))) * (1 + ‖s‖ * Real.log N) := by ring
        _ = (t ^ (1 - s.re) * (1 + ‖s‖ * Real.log N)) * t⁻¹ := by rw [ht_eq]; ring
        _ ≤ C * t⁻¹ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpow_max (by positivity)) (inv_nonneg.mpr ht0.le)
    _ = C * Real.log N := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le hN1.le,
        integral_inv_of_pos zero_lt_one (zero_lt_one.trans hN1), div_one]

/-- Tail estimate on `(N, ∞)`, using period cancellation `‖∑_{k≤t} χ(k)‖ ≤ N`. -/
private lemma norm_integral_Ioi_le (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (N : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (1 - s * Real.log t) * (t : ℂ) ^ (-(s + 1))‖ ≤
      (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ * Real.log N) / s.re + ‖s‖ / s.re ^ 2) := by
  have hN3 := χ.three_le_level_of_ne_one hχ
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans hN1
  have ha : -(s.re + 1) < -1 := by linarith
  have h_int₁ := (integrableOn_Ioi_rpow_of_lt ha hN0).const_mul (N : ℝ)
  have h_int₂ := (TauCeti.integrableOn_Ioi_rpow_mul_log_of_lt ha hN0).const_mul ((N : ℝ) * ‖s‖)
  calc
    _ ≤ ∫ t in Set.Ioi (N : ℝ),
        ((N : ℝ) * t ^ (-(s.re + 1)) + (N : ℝ) * ‖s‖ * (t ^ (-(s.re + 1)) * Real.log t)) := by
      refine norm_integral_le_of_norm_le (h_int₁.add h_int₂) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : (N : ℝ) < t)
      have ht1 : 1 < t := hN1.trans ht
      have ht0 : 0 < t := zero_lt_one.trans ht1
      have hlog : ‖(1 : ℂ) - s * Real.log t‖ ≤ 1 + ‖s‖ * Real.log t := by
        calc
          ‖(1 : ℂ) - s * Real.log t‖ ≤ ‖(1 : ℂ)‖ + ‖s * (Real.log t : ℂ)‖ := norm_sub_le _ _
          _ = 1 + ‖s‖ * Real.log t := by
            rw [norm_one, norm_mul, Complex.norm_real,
              Real.norm_of_nonneg (Real.log_nonneg ht1.le)]
      rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [neg_re, add_re, one_re]
      calc
        ‖∑ k ∈ Icc 1 ⌊t⌋₊, χ k‖ * ‖(1 : ℂ) - s * Real.log t‖ * t ^ (-(s.re + 1))
            ≤ ((N : ℝ) * (1 + ‖s‖ * Real.log t)) * t ^ (-(s.re + 1)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (χ.norm_sum_Icc_le_level hχ _) hlog (norm_nonneg _) hN0.le)
            (Real.rpow_nonneg ht0.le _)
        _ = (N : ℝ) * t ^ (-(s.re + 1)) +
              (N : ℝ) * ‖s‖ * (t ^ (-(s.re + 1)) * Real.log t) := by ring
    _ = (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ * Real.log N) / s.re + ‖s‖ / s.re ^ 2) := by
      rw [integral_add h_int₁ h_int₂, integral_const_mul, integral_const_mul,
        integral_Ioi_rpow_of_lt ha hN0, TauCeti.integral_Ioi_rpow_mul_log_of_lt ha hN0]
      have hN_pow : (N : ℝ) * (N : ℝ) ^ (-(s.re + 1) + 1) = (N : ℝ) ^ (1 - s.re) := by
        calc
          (N : ℝ) * (N : ℝ) ^ (-(s.re + 1) + 1) =
              (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(s.re + 1) + 1) := by rw [Real.rpow_one]
          _ = (N : ℝ) ^ (1 - s.re) := by rw [← Real.rpow_add hN0]; congr 1; ring
      have hre : s.re ≠ 0 := hs.ne'
      have hre' : -(s.re + 1) + 1 = -s.re := by ring
      rw [hre'] at hN_pow ⊢
      calc
        (N : ℝ) * (-(N : ℝ) ^ (-s.re) / -s.re) +
            (N : ℝ) * ‖s‖ * ((N : ℝ) ^ (-s.re) * (1 - -s.re * Real.log N) / (-s.re) ^ 2)
            = ((N : ℝ) * (N : ℝ) ^ (-s.re)) *
                (-1 / -s.re + ‖s‖ * (1 - -s.re * Real.log N) / (-s.re) ^ 2) := by ring
        _ = (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ * Real.log N) / s.re + ‖s‖ / s.re ^ 2) := by
          rw [hN_pow]
          congr 1
          field_simp
          ring

/-- **Right-half-plane bound for `L'(s, χ)`.** For any nonprincipal character `χ` of nonzero level
`N` and any `s` with `Re(s) > 0`, `‖L'(s, χ)‖` is bounded above by
`max 1 (N ^ (1 - Re(s))) * (1 + ‖s‖ log N) * log N` plus
`N ^ (1 - Re(s)) * ((1 + ‖s‖ log N) / Re(s) + ‖s‖ / Re(s) ^ 2)`. -/
theorem norm_deriv_LFunction_le_of_re_pos (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖deriv χ.LFunction s‖ ≤
      max 1 ((N : ℝ) ^ (1 - s.re)) * (1 + ‖s‖ * Real.log N) * Real.log N +
        (N : ℝ) ^ (1 - s.re) * ((1 + ‖s‖ * Real.log N) / s.re + ‖s‖ / s.re ^ 2) := by
  have hN3 := χ.three_le_level_of_ne_one hχ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hint := χ.integrableOn_sum_Icc_mul_one_sub_mul_log_mul_cpow hχ hs
  rw [χ.deriv_LFunction_eq_integral hχ hs, ← Set.Ioc_union_Ioi_eq_Ioi hN1,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hN1))]
  exact (norm_add_le _ _).trans
    (add_le_add (χ.norm_integral_Ioc_le hχ) (χ.norm_integral_Ioi_le hχ hs))

/-- **Near-one derivative bound for Dirichlet L-functions** (Koukoulopoulos, Lemma 11.2).
Uniformly for any nonprincipal character `χ` of nonzero level `N` and any real
`σ ∈ [1 - 1 / log N, 1]`, we have `‖L'(σ, χ)‖ ≤ 81 (log N) ^ 2`. -/
theorem norm_deriv_LFunction_le_mul_log_sq (hχ : χ ≠ 1) {σ : ℝ}
    (hσ₁ : 1 - 1 / Real.log N ≤ σ) (hσ₂ : σ ≤ 1) :
    ‖deriv χ.LFunction σ‖ ≤ 81 * Real.log N ^ 2 := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast χ.three_le_level_of_ne_one hχ
  have hL3 : (12 : ℝ) / 11 < Real.log N :=
    (by linarith [Real.log_three_gt_d9] : (12 : ℝ) / 11 < Real.log 3).trans_le
      (Real.log_le_log (by norm_num) hN3)
  have hL1 : 1 < Real.log N := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have h_inv_L : 1 / Real.log N < 11 / 12 := by
    rw [div_lt_div_iff₀ hL0 (by norm_num)]; linarith
  have hσ_low : (1 : ℝ) / 12 < σ := by linarith
  have hσ0 : 0 < σ := by linarith
  have h_inv_σ : 1 / σ ≤ 12 := by rw [div_le_iff₀ hσ0]; linarith
  -- On `[1 - 1 / log N, 1]`, `1 ≤ N ^ (1 - σ) ≤ e < 3`.
  have hN_ge_one : 1 ≤ (N : ℝ) ^ (1 - σ) :=
    Real.one_le_rpow (by linarith) (by linarith)
  have hN_le_three : (N : ℝ) ^ (1 - σ) ≤ 3 := by
    rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < N), mul_comm]
    have hprod : (1 - σ) * Real.log N ≤ 1 := by
      have : 1 - σ ≤ 1 / Real.log N := by linarith
      exact (mul_le_mul_of_nonneg_right this hL0.le).trans (one_div_mul_cancel hL0.ne').le
    exact (Real.exp_le_exp.mpr hprod).trans (by linarith [Real.exp_one_lt_d9])
  have hmain := χ.norm_deriv_LFunction_le_of_re_pos hχ (s := (σ : ℂ)) (by simpa using hσ0)
  have hnorm_σ : ‖(σ : ℂ)‖ = σ := by rw [Complex.norm_real, Real.norm_of_nonneg hσ0.le]
  simp only [ofReal_re, hnorm_σ, max_eq_right hN_ge_one] at hmain
  have h_tail_simp : (1 + σ * Real.log N) / σ + σ / σ ^ 2 = 2 * (1 / σ) + Real.log N := by
    field_simp
    ring
  rw [h_tail_simp] at hmain
  have h_init : (N : ℝ) ^ (1 - σ) * (1 + σ * Real.log N) * Real.log N ≤ 6 * Real.log N ^ 2 := by
    have hfac : (N : ℝ) ^ (1 - σ) * (1 + σ * Real.log N) ≤ 6 * Real.log N :=
      (mul_le_mul hN_le_three (by nlinarith : 1 + σ * Real.log N ≤ 2 * Real.log N)
        (by positivity) (by norm_num)).trans_eq (by ring)
    exact (mul_le_mul_of_nonneg_right hfac hL0.le).trans_eq (by ring)
  have h_tail : (N : ℝ) ^ (1 - σ) * (2 * (1 / σ) + Real.log N) ≤ 75 * Real.log N ^ 2 := by
    nlinarith [sq_nonneg (Real.log N - 1)]
  linarith

/-- **Unconditional real-zero separation from `L(1, χ)`** (Koukoulopoulos, (12.11)). For any
nonprincipal character `χ` of nonzero level `N` (not necessarily primitive or quadratic) and any
real zero `β` of `L(s, χ)`, `Re L(1, χ) / (81 (log N) ^ 2) ≤ 1 - β`. -/
theorem LFunction_one_re_div_log_sq_le_one_sub_of_LFunction_eq_zero
    (hχ : χ ≠ 1) {β : ℝ} (hβ : χ.LFunction β = 0) :
    (χ.LFunction 1).re / (81 * Real.log N ^ 2) ≤ 1 - β := by
  have hβ1 : β < 1 :=
    not_le.mp fun h ↦ χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by simpa using h) hβ
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast χ.three_le_level_of_ne_one hχ
  have hL1 : 1 < Real.log N :=
    (by linarith [Real.log_three_gt_d9] : (1 : ℝ) < Real.log 3).trans_le
      (Real.log_le_log (by norm_num) hN3)
  have : 0 < Real.log N := zero_lt_one.trans hL1
  rcases le_or_gt (1 - 1 / Real.log N) β with hnear | hfar
  · -- Near `1`, apply Lagrange's mean value theorem to `σ ↦ Re L(σ, χ)` on `[β, 1]`.
    have hf' (σ : ℝ) :
        HasDerivAt (fun x : ℝ ↦ (χ.LFunction x).re) (deriv χ.LFunction σ).re σ :=
      reCLM.hasFDerivAt.comp_hasDerivAt σ
        ((differentiable_LFunction hχ).differentiableAt.hasDerivAt.comp_ofReal)
    have hfc : ContinuousOn (fun x : ℝ ↦ (χ.LFunction x).re) (Set.Icc β 1) :=
      fun x _ ↦ (hf' x).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
      (fun x : ℝ ↦ (χ.LFunction x).re) (fun x : ℝ ↦ (deriv χ.LFunction x).re)
      hβ1 hfc (fun x _ ↦ hf' x)
    have hc_le : (deriv χ.LFunction c).re ≤ 81 * Real.log N ^ 2 :=
      (Complex.re_le_norm _).trans
        (χ.norm_deriv_LFunction_le_mul_log_sq hχ (hnear.trans hc.1.le) hc.2.le)
    rw [ofReal_one, hβ, zero_re, sub_zero] at hslope
    rw [div_le_iff₀ (by positivity)]
    have hmul := (div_le_iff₀ (sub_pos.mpr hβ1)).mp (hslope ▸ hc_le)
    linarith
  · -- Left of `1 - 1 / log N`, use `Re L(1, χ) ≤ 1 + log N ≤ 81 log N`.
    calc
      (χ.LFunction 1).re / (81 * Real.log N ^ 2)
          ≤ (1 + Real.log N) / (81 * Real.log N ^ 2) :=
        div_le_div_of_nonneg_right
          ((Complex.re_le_norm _).trans (χ.norm_LFunction_one_le_one_add_log hχ)) (by positivity)
      _ ≤ 81 * Real.log N / (81 * Real.log N ^ 2) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / Real.log N := by field_simp
      _ ≤ 1 - β := by linarith

end DirichletCharacter
