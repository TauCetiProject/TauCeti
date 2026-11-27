/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.Analysis.SpecialFunctions.Gaussian.Mellin

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic
import TauCeti.NumberTheory.LSeries.Dilation

/-!
# Gaussian theta series with bounded coefficients

The even and odd Gaussian weights are `exp (-π x²)` and `x * exp (-π x²)`. We sum the
rescaled weights against coefficients indexed by the positive integers, and multiply by the
square root of the scale to form the normalized theta series. A single geometric majorant
gives absolute convergence and the bound `3 * exp (-u) / √u` for positive scales `u`.

The Mellin transform of the Gaussian weight is evaluated using the Gamma function.

## Dirichlet coefficients

For a sequence `a`, consider the sum of `a n (n t)^j exp(-π (n t)^2)` over positive integers
`n`. Its Mellin transform factors into the Dirichlet series of `a` and `Γℝ(s+j)/2`. On the
line `Re s = 2`, truncating the Mellin integral below `r ≥ 0` incurs an error linear in `r`
for uniformly bounded coefficients.

This is the unscaled theta sum: `Lib/Analytic/DirichletTheta` of lsernau/grh-lean (`72fead1`)
multiplies it by `t^(1/2)` and shifts the Mellin argument by `-1/2`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), commit `72fead102f663d5c7a407964a13dc0cf9d977207`. The file
`grh/src/Lib/Analytic/DirichletTheta.lean` supplies `New.gaussianMonomial`, `New.gaussianTheta`,
`New.thetaSeries` and `New.gaussianMellin`. The geometric comparison follows
`New.norm_gaussianMonomial_le` and `New.summable_and_norm_gaussianTheta_le` from that file.
Here the weight bound uses the absolute value of the argument, and the coefficient bound
is imposed only at positive indices.
-/

public section

noncomputable section

namespace TauCeti

section ThetaSeries

open MeasureTheory Real Set
open scoped ComplexConjugate

/-- The Gaussian weight of parity `j ∈ {0, 1}`. -/
def gaussianMonomial (j : Fin 2) (x : ℝ) : ℝ := x ^ j.val * exp (-π * x ^ 2)

/-- The even Gaussian weight is the Gaussian itself. -/
@[simp] theorem gaussianMonomial_zero (x : ℝ) : gaussianMonomial 0 x = exp (-π * x ^ 2) := by
  simp [gaussianMonomial]

/-- The odd Gaussian weight is the Gaussian multiplied by its argument. -/
@[simp] theorem gaussianMonomial_one (x : ℝ) : gaussianMonomial 1 x = x * exp (-π * x ^ 2) := by
  simp [gaussianMonomial]

/-- The sum of the parity-weighted Gaussians against the positive-index coefficients of `c`. -/
def gaussianTheta (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑' n : ℕ+, c n * gaussianMonomial j (n * u)

/-- Expand the theta sum over the positive integers. -/
theorem gaussianTheta_def (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) :
    gaussianTheta j c u = ∑' n : ℕ+, c n * gaussianMonomial j (n * u) := by
  unfold gaussianTheta
  rfl

/-- The Gaussian theta series with square-root normalization. -/
def gaussianThetaSeries (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  (√u : ℝ) * gaussianTheta j c u

/-- The normalized theta series is the theta sum times the square root of the scale. -/
theorem gaussianThetaSeries_def (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) :
    gaussianThetaSeries j c u = (√u : ℝ) * gaussianTheta j c u := by
  unfold gaussianThetaSeries
  rfl

/-- Conjugating the coefficients conjugates the Gaussian theta sum. -/
@[simp] theorem gaussianTheta_conj (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) :
    gaussianTheta j (fun n ↦ conj (c n)) u = conj (gaussianTheta j c u) := by
  simp only [gaussianTheta_def, Complex.conj_tsum, map_mul, Complex.conj_ofReal]

/-- Conjugating the coefficients conjugates the normalized Gaussian theta series. -/
@[simp] theorem gaussianThetaSeries_conj (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) :
    gaussianThetaSeries j (fun n ↦ conj (c n)) u = conj (gaussianThetaSeries j c u) := by
  simp only [gaussianThetaSeries_def, gaussianTheta_conj, map_mul, Complex.conj_ofReal]

/-- The Mellin transform of the Gaussian weight of parity `j`. -/
def gaussianMellin (j : Fin 2) : ℂ → ℂ := mellin fun x ↦ (gaussianMonomial j x : ℂ)

/-- Express the Gaussian Mellin weight as a Mellin transform. -/
theorem gaussianMellin_def (j : Fin 2) :
    gaussianMellin j = mellin (fun x ↦ (gaussianMonomial j x : ℂ)) := by
  unfold gaussianMellin
  rfl

variable {j : Fin 2} {c : ℕ → ℂ}

/-- The Mellin transform of the parity-`j` Gaussian in its half-plane of convergence. -/
theorem gaussianMellin_eq {s : ℂ} (hs : -(j.val : ℝ) < s.re) :
    gaussianMellin j s =
      (1 / 2 : ℂ) * (π : ℂ) ^ (-(s + j.val) / 2) * Complex.Gamma ((s + j.val) / 2) := by
  let f : ℝ → ℂ := fun x ↦ (exp (-(π * x)) : ℂ)
  let a : ℂ := (s + j.val) / 2
  have ha : 0 < a.re := by
    dsimp [a]
    rw [Complex.div_ofNat_re, Complex.add_re, Complex.natCast_re]
    linarith
  calc
    gaussianMellin j s = mellin (fun x : ℝ ↦ (x : ℂ) ^ (j.val : ℂ) • f (x ^ (2 : ℝ))) s := by
      rw [gaussianMellin_def]
      congr 1
      funext x
      simp [gaussianMonomial, f, Complex.cpow_natCast, neg_mul, smul_eq_mul]
    _ = (1 / 2 : ℂ) * mellin f a := by
      rw [mellin_cpow_smul, mellin_comp_rpow]
      norm_num [a, smul_eq_mul, Complex.real_smul, one_div]
    _ = _ := by
      have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi ha pi_pos
      have hmellin : mellin f a = (1 / (π : ℂ)) ^ a * Complex.Gamma a := by
        simpa only [mellin, f, smul_eq_mul, Complex.ofReal_exp, Complex.ofReal_neg,
          Complex.ofReal_mul] using h
      rw [hmellin]
      simp only [one_div, Complex.inv_cpow_ofReal_nonneg pi_nonneg, ← Complex.cpow_neg,
        a, neg_div, mul_assoc]

/-- The unnormalized Gaussian theta series is measurable in the scale. -/
@[fun_prop] theorem measurable_gaussianTheta : Measurable (gaussianTheta j c) := by
  rw [funext (gaussianTheta_def j c)]
  fun_prop [gaussianMonomial]

/-- The square-root-normalized Gaussian theta series is measurable in the scale. -/
@[fun_prop] theorem measurable_gaussianThetaSeries : Measurable (gaussianThetaSeries j c) := by
  rw [funext (gaussianThetaSeries_def j c)]
  exact (Complex.measurable_ofReal.comp continuous_sqrt.measurable).mul measurable_gaussianTheta

/-- A pointwise exponential majorant for the Gaussian weights of both parities. -/
private theorem norm_gaussianMonomial_le (j : Fin 2) (x : ℝ) :
    ‖gaussianMonomial j x‖ ≤ 3 * exp (-|x|) ^ 2 := by
  have hpow : |x| ^ j.val ≤ exp |x| :=
    calc |x| ^ j.val ≤ |x| + 1 := by fin_cases j <;> simp
      _ ≤ exp |x| := add_one_le_exp _
  have hexp : |x| + -π * x ^ 2 ≤ 1 + (-|x| + -|x|) := by
    rw [← sq_abs x]
    nlinarith [pi_gt_three, sq_nonneg (|x| - 2⁻¹), sq_nonneg |x|]
  calc ‖gaussianMonomial j x‖ = |x| ^ j.val * exp (-π * x ^ 2) := by
        simp [gaussianMonomial]
    _ ≤ exp |x| * exp (-π * x ^ 2) := by gcongr
    _ ≤ exp (1 + (-|x| + -|x|)) := by rw [← Real.exp_add]; gcongr
    _ = exp 1 * exp (-|x|) ^ 2 := by rw [Real.exp_add, Real.exp_add, sq]
    _ ≤ 3 * exp (-|x|) ^ 2 := by gcongr; exact exp_one_lt_three.le

/-- The Mellin integral of the parity-`j` Gaussian converges for `-j < re s`. -/
theorem mellinConvergent_gaussianMonomial {s : ℂ} (hs : -(j.val : ℝ) < s.re) :
    MellinConvergent (fun x ↦ (gaussianMonomial j x : ℂ)) s := by
  rw [MellinConvergent]
  have hmeas : Measurable (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) • (gaussianMonomial j x : ℂ)) := by
    fun_prop [gaussianMonomial]
  refine (integrable_norm_iff hmeas.aestronglyMeasurable).mp <|
    (integrableOn_rpow_mul_exp_neg_mul_sq pi_pos (s := s.re - 1 + j.val)
      (by linarith)).congr_fun (fun x (hx : 0 < x) ↦ ?_) measurableSet_Ioi
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re,
    Complex.norm_real, gaussianMonomial, norm_mul, norm_of_nonneg (pow_nonneg hx.le _),
    norm_of_nonneg (exp_nonneg _), ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hx]

private theorem norm_gaussianTheta_term_le (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) (u : ℝ)
    (n : ℕ+) :
    ‖c n * gaussianMonomial j (n * u)‖ ≤ 3 * (exp (-|u|) ^ 2) ^ (n : ℕ) := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  grw [norm_mul, hc, Complex.norm_real, norm_gaussianMonomial_le, abs_mul, abs_of_nonneg hn]
  simp [← Real.exp_natCast_mul, field]

private theorem hasSum_gaussianTheta_majorant {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ+ ↦ 3 * (exp (-u) ^ 2) ^ (n : ℕ))
      (3 * (exp (-u) ^ 2 / (1 - exp (-u) ^ 2))) := by
  have hr : ‖exp (-u) ^ 2‖ < 1 := by simpa using hu
  exact (hasSum_geometric_pnat hr).mul_left 3

/-- The Gaussian theta sum converges absolutely at positive scales for unit-bounded
coefficients. -/
theorem summable_gaussianTheta (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℕ+ ↦ c n * gaussianMonomial j (n * u) := by
  refine (hasSum_gaussianTheta_majorant hu).summable.of_norm_bounded fun n ↦ ?_
  simpa only [abs_of_pos hu] using norm_gaussianTheta_term_le (j := j) hc u n

/-- At positive scales the unnormalized theta sum is bounded by `3 * exp (-u) / u`
for coefficients of norm at most one. -/
theorem norm_gaussianTheta_le (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) {u : ℝ} (hu : 0 < u) :
    ‖gaussianTheta j c u‖ ≤ 3 * exp (-u) / u := by
  let r : ℝ := exp (-u) ^ 2
  have hexp_mul : exp u * exp (-u) = 1 := by simp [← Real.exp_add]
  have hdenom : u * exp (-u) ≤ 1 - r := by
    nlinarith [add_one_le_exp u, exp_pos (-u), exp_le_one_iff.2 (neg_nonpos.2 hu.le), hexp_mul]
  have hsum : 3 * (r / (1 - r)) ≤ 3 * exp (-u) / u := by
    calc 3 * (r / (1 - r)) ≤ 3 * (r / (u * exp (-u))) := by gcongr
      _ = 3 * exp (-u) / u := by simp [r, field]
  rw [gaussianTheta_def]
  refine (tsum_of_norm_bounded (hasSum_gaussianTheta_majorant hu) fun n ↦ ?_).trans hsum
  simpa only [abs_of_pos hu] using norm_gaussianTheta_term_le (j := j) hc u n

/-- The normalized theta series satisfies the bound `3 * exp (-u) / √u`.
At nonpositive scales both sides vanish under the real square-root convention. -/
theorem norm_gaussianThetaSeries_le (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) (u : ℝ) :
    ‖gaussianThetaSeries j c u‖ ≤ 3 * exp (-u) / √u := by
  obtain hu | hu := le_or_gt u 0
  · simp [gaussianThetaSeries_def, sqrt_eq_zero_of_nonpos hu]
  rw [gaussianThetaSeries_def, norm_mul, Complex.norm_real, norm_of_nonneg (sqrt_nonneg u)]
  calc √u * ‖gaussianTheta j c u‖ ≤ √u * (3 * exp (-u) / u) := by
        gcongr
        exact norm_gaussianTheta_le hc hu
    _ = 3 * exp (-u) * (√u / u) := by ring
    _ = 3 * exp (-u) / √u := by rw [sqrt_div_self', mul_one_div]

/-- The norm of the normalized theta series is integrable against `du / u` on a positive tail. -/
theorem integrableOn_norm_gaussianThetaSeries_div (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) {r : ℝ}
    (hr : 0 < r) : IntegrableOn (fun u ↦ ‖gaussianThetaSeries j c u‖ / u) (Ioi r) := by
  have hmajorant : IntegrableOn (fun u ↦ 3 * exp (-u) / √r / r) (Ioi r) :=
    (((integrableOn_exp_neg_Ioi r).const_mul 3).div_const √r).div_const r
  refine hmajorant.mono'
    (measurable_gaussianThetaSeries.norm.div measurable_id).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu ↦ ?_
  have hrle : r ≤ u := le_of_lt hu
  have hu0 : 0 < u := hr.trans_le hrle
  grw [norm_of_nonneg (by positivity), norm_gaussianThetaSeries_le hc]
  gcongr

end ThetaSeries

open Complex in
open scoped Real in
/-- Poisson summation for the parity-weighted Gaussian on a shifted integer lattice.
This is the even or odd Hurwitz theta transformation, with the width written as `v`. -/
theorem hasSum_gaussianMonomial_add_mul (j : Fin 2) (a : ℝ) {v : ℝ} (hv : 0 < v) :
    HasSum (fun n : ℤ ↦ (gaussianMonomial j ((n + a) * v) : ℂ))
      ((v : ℂ)⁻¹ * (-I) ^ j.val *
        ∑' n : ℤ, exp (2 * π * I * a * n) * gaussianMonomial j (n * v⁻¹)) := by
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
  have hi : 0 < 1 / v ^ 2 := by positivity
  have hp₁ : (v ^ 2) ^ (1 / 2 : ℝ) = v := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hv.le]
  have hp₃ : (v ^ 2) ^ (3 / 2 : ℝ) = v ^ 3 := by
    have hsplit : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [hsplit, Real.rpow_add hv2, Real.rpow_one, hp₁]
    ring
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hj with rfl | rfl
  · have h₁ := hasSum_ofReal.mpr (HurwitzZeta.hasSum_int_evenKernel a hv2)
    have h₂ := HurwitzZeta.hasSum_int_cosKernel a hi
    rw [HurwitzZeta.evenKernel_functional_equation, hp₁, one_div, ofReal_mul, ofReal_inv,
      ← h₂.tsum_eq] at h₁
    simp only [Fin.val_zero, pow_zero, mul_one]
    convert h₁ using 1
    · funext n
      simp [mul_pow, mul_assoc]
    · congr 1
      exact tsum_congr fun n ↦ by simp [mul_pow, div_eq_mul_inv, mul_assoc]
  · have h₁ := (hasSum_ofReal.mpr (HurwitzZeta.hasSum_int_oddKernel a hv2)).mul_left (v : ℂ)
    have h₂ := HurwitzZeta.hasSum_int_sinKernel a hi
    rw [HurwitzZeta.oddKernel_functional_equation, hp₃, one_div, ofReal_mul, ofReal_inv,
      ← h₂.tsum_eq] at h₁
    convert h₁ using 1
    · funext n
      simp only [gaussianMonomial_one, mul_pow, ofReal_mul]
      ac_rfl
    · simp only [Fin.val_one, pow_one, ← tsum_mul_left]
      refine tsum_congr fun n ↦ ?_
      rw [gaussianMonomial_one, mul_pow, inv_pow, ← div_eq_mul_inv]
      push_cast
      field_simp

section DirichletTheta

open Complex MeasureTheory Set

/-- The positive-index Gaussian theta sum with coefficients `a` and monomial weight of degree
`j`. The value of `a 0` does not enter the sum. -/
noncomputable def gaussianDirichletTheta (j : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, a (n + 1) * (((n + 1 : ℕ) * t) ^ j * Real.exp (-Real.pi * ((n + 1 : ℕ) * t) ^ 2) : ℝ)

/-- The defining sum over strictly positive integers. -/
theorem gaussianDirichletTheta_def (j : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    gaussianDirichletTheta j a t =
    ∑' n : ℕ, a (n + 1) *
      (((n + 1 : ℕ) * t) ^ j * Real.exp (-Real.pi * ((n + 1 : ℕ) * t) ^ 2) : ℝ) :=
  (rfl)

/-- The theta sum with the zero coefficient sequence vanishes. -/
@[simp] theorem gaussianDirichletTheta_zero (j : ℕ) (t : ℝ) :
    gaussianDirichletTheta j 0 t = 0 := by
  simp [gaussianDirichletTheta_def]

/-- A geometric bound for each summand of a Gaussian theta sum with bounded coefficients. -/
private theorem norm_gaussianDirichletTheta_term_le (j : ℕ) {a : ℕ → ℂ} {M t : ℝ}
    {n : ℕ} (ha : ‖a (n + 1)‖ ≤ M) :
    ‖a (n + 1) * (((n + 1 : ℕ) * t) ^ j * Real.exp (-Real.pi * ((n + 1 : ℕ) * t) ^ 2) : ℝ)‖ ≤
      (M * (j.factorial : ℝ) * Real.exp 1) * Real.exp (-|t|) ^ (n + 1) := by
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  calc
    _ ≤ M * ((j.factorial : ℝ) * Real.exp 1 * Real.exp (-|((n + 1 : ℕ) : ℝ) * t|)) :=
      mul_le_mul ha (abs_pow_mul_exp_neg_pi_mul_sq_le j _) (abs_nonneg _) ((norm_nonneg _).trans ha)
    _ = _ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ)),
        ← Real.exp_natCast_mul, mul_neg]
      ring

/-- For bounded coefficients the Gaussian theta sum converges absolutely at every positive
argument. -/
theorem summable_norm_gaussianDirichletTheta (j : ℕ) {a : ℕ → ℂ} {M t : ℝ}
    (ha : ∀ n ≠ 0, ‖a n‖ ≤ M) (ht : 0 < t) :
    Summable fun n : ℕ ↦ ‖a (n + 1) *
      (((n + 1 : ℕ) * t) ^ j * Real.exp (-Real.pi * ((n + 1 : ℕ) * t) ^ 2) : ℝ)‖ := by
  have hgeom := (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (Real.exp_nonneg (-t))
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)))
  exact (hgeom.mul_left (M * (j.factorial : ℝ) * Real.exp 1)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun n ↦ by
      simpa only [abs_of_pos ht] using
        norm_gaussianDirichletTheta_term_le j (t := t) (ha _ (Nat.succ_ne_zero n))

/-- For coefficients of norm at most `M`, the theta sum at `t > 0` is at most
`M j! e / (exp t − 1)` in norm. -/
theorem norm_gaussianDirichletTheta_le (j : ℕ) {a : ℕ → ℂ} {M t : ℝ}
    (ha : ∀ n ≠ 0, ‖a n‖ ≤ M) (ht : 0 < t) :
    ‖gaussianDirichletTheta j a t‖ ≤ M * (j.factorial : ℝ) * Real.exp 1 / (Real.exp t - 1) := by
  have hq := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have hgeom := summable_geometric_of_lt_one (Real.exp_nonneg (-t)) hq
  have hnorm := summable_norm_gaussianDirichletTheta j ha ht
  rw [gaussianDirichletTheta_def]
  refine (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum
    (fun n ↦ by simpa only [abs_of_pos ht] using
      norm_gaussianDirichletTheta_term_le j (t := t) (ha _ (Nat.succ_ne_zero n)))
    (((summable_nat_add_iff 1).2 hgeom).mul_left _)).trans_eq ?_)
  simp_rw [tsum_mul_left, pow_succ, tsum_mul_right, tsum_geometric_of_lt_one (Real.exp_nonneg _) hq,
    Real.exp_neg]
  have he := Real.exp_pos t
  field_simp [he.ne', ne_of_gt (Real.one_lt_exp_iff.mpr ht), ne_of_gt hq]

/-- The Mellin transform of the Gaussian theta sum is `LSeries a s` multiplied by
`Γℝ(s+j)/2` in the common domain of absolute convergence. -/
theorem hasMellin_gaussianDirichletTheta (j : ℕ) {a : ℕ → ℂ} {s : ℂ}
    (ha : LSeriesSummable a s) (hs : 0 < s.re + j) :
    HasMellin (gaussianDirichletTheta j a) s (LSeries a s * (Gammaℝ (s + j) / 2)) := by
  have h := hasMellin_pow_mul_exp_neg_pi_mul_sq j hs
  simpa only [funext (gaussianDirichletTheta_def j a), h.2] using ha.hasMellin_tsum_dilate h.1

/-- At `Re s = 2`, cutting off the integral for the Gaussian theta sum at `r ≥ 0` changes its
Mellin transform by at most `M j! e r`, uniformly in the imaginary part. -/
theorem norm_integral_gaussianDirichletTheta_sub (j : ℕ) {a : ℕ → ℂ} {M r : ℝ}
    (ha : ∀ n ≠ 0, ‖a n‖ ≤ M) (hr : 0 ≤ r) {s : ℂ} (hs : s.re = 2) :
    ‖(∫ t : ℝ in Ioi r, (t : ℂ) ^ (s - 1) * gaussianDirichletTheta j a t) -
      LSeries a s * (Gammaℝ (s + j) / 2)‖ ≤ M * (j.factorial : ℝ) * Real.exp 1 * r := by
  obtain ⟨hint, hval⟩ := hasMellin_gaussianDirichletTheta j
    (LSeriesSummable_of_bounded_of_one_lt_re ha (s := s) (by linarith)) (by linarith)
  simp only [MellinConvergent, mellin, smul_eq_mul] at hint hval
  rw [← hval, ← Ioc_union_Ioi_eq_Ioi hr, setIntegral_union
    Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hr)), add_comm (_ : ℂ),
    sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 r),
      ‖(t : ℂ) ^ (s - 1) * gaussianDirichletTheta j a t‖ ≤ M * (j.factorial : ℝ) * Real.exp 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1, sub_re, hs, one_re]
    norm_num
    have hden : 0 < Real.exp t - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ht.1)
    have hM : 0 ≤ M := (norm_nonneg _).trans (ha 1 one_ne_zero)
    calc
      _ ≤ t * (M * (j.factorial : ℝ) * Real.exp 1 / (Real.exp t - 1)) :=
        mul_le_mul_of_nonneg_left (norm_gaussianDirichletTheta_le j ha ht.1) ht.1.le
      _ ≤ _ := by
        rw [mul_comm t, div_mul_eq_mul_div, div_le_iff₀ hden]
        exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp t]) (by positivity)
  simpa [hr, mul_comm] using norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    measure_Ioc_lt_top hbound

end DirichletTheta

end TauCeti
