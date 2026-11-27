/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import TauCeti.Analysis.Analytic.TaylorSeries
public import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Calculus.DSlope.Iterate
import TauCeti.Analysis.Calculus.DSlope.Parametric
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference
import TauCeti.Analysis.SpecialFunctions.Exp.InvSubOne
import TauCeti.Analysis.SpecialFunctions.Exp.TaylorSeries

/-!
# Exponential-Bernoulli kernel and uniform Taylor remainder for Hurwitz continuation

The Mellin-Laplace integrand for the complex Hurwitz zeta function involves the generating kernel
`F_c(z) = z * exp (-c * z) / (1 - exp (-z))`, defined globally via `oneSubExpNegDivSelf ℂ z`
(which agrees everywhere with `dslope Complex.exp 0 (-z)`). This fills in the removable singularity
at `z = 0` (`hurwitzKernel c 0 = 1`), whereas at the nonzero poles `z = 2 * π * I * k`
(`k : ℤ`, `k ≠ 0`), `dslope Complex.exp 0 (-z)` and `oneSubExpNegDivSelf ℂ z` vanish and
`hurwitzKernel c z` takes the totalized value `0`. Accordingly, `(c, z) ↦ hurwitzKernel c z` is
jointly analytic on the full nonvanishing locus `{p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0}`
(and in particular on `Set.univ ×ˢ Metric.ball 0 (2 * π)` and
`Set.univ ×ˢ (Complex.ofReal '' Set.univ)`). For the specialization `hurwitzKernel 1 (t : ℂ) =
(bernoulliKernel t : ℂ)` on real `t`, see
`TauCeti.NumberTheory.LSeries.HurwitzZeta.BernoulliKernel`.

On the nonvanishing locus `{z : ℂ | dslope Complex.exp 0 (-z) ≠ 0}` (in particular near `z = 0`),
multiplying by `exp z - 1` yields `hurwitzKernel c z * (exp z - 1) = z * exp ((1 - c) * z)`.
Comparing Taylor series at `z = 0` with `Polynomial.bernoulli_generating_function (1 - c)`
identifies the Taylor coefficients at `0` as `hurwitzBernoulliCoeff k c = (-1) ^ k * B_k(c) / k!`.

Iterating divided differences at `z = 0` defines the order-`M` Taylor remainder quotient
`hurwitzTaylorQuot M c z = (Function.swap dslope 0)^[M + 1] (hurwitzKernel c) z`, which is
jointly analytic on `{p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0}` (as are its partial
`c`-derivatives of every fixed order `d`) and satisfies the exact identity
`hurwitzKernel c z - ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c * z ^ k =
z ^ (M + 1) * hurwitzTaylorQuot M c z` for all `c, z : ℂ`. Compactness then gives uniform
bounds on `‖iteratedDeriv d (fun w => hurwitzTaylorQuot M w z) c‖` and Taylor remainder bounds
`‖∂_c^d F_c(z) - ∑_{k ≤ M} ∂_c^d b_k(c) z^k‖ ≤ C * ‖z‖ ^ (M + 1)` on any compact subset `S`
of `{p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0}` (specializing to `d = 0` for the undifferentiated
remainder).

## Main definitions and results

* `TauCeti.hurwitzKernel`: the generating kernel `exp (-c * z) / oneSubExpNegDivSelf ℂ z`.
* `TauCeti.analyticAt_hurwitzKernel_zero`: analyticity of `hurwitzKernel c` at `0`.
* `TauCeti.hurwitzBernoulliCoeff`: the Taylor coefficient `(-1) ^ k * B_k(c) / k!`.
* `TauCeti.iteratedDeriv_hurwitzKernel_zero`: identification of
  `iteratedDeriv n (hurwitzKernel c) 0` with `(-1) ^ n * B_n(c)`.
* `TauCeti.coeff_taylorSeries_hurwitzKernel_zero`: identification of the `k`-th formal Taylor
  coefficient of `hurwitzKernel c` at `0` with `hurwitzBernoulliCoeff k c`.
* `TauCeti.iterate_dslope_hurwitzKernel_zero`: `@[simp]` evaluation of the `k`-fold divided
  difference `(Function.swap dslope 0)^[k] (hurwitzKernel c) 0 = hurwitzBernoulliCoeff k c`.
* `TauCeti.hurwitzTaylorQuot`, `TauCeti.hurwitzTaylorQuot_of_ne_zero`,
  `TauCeti.hurwitzKernel_sub_sum_eq_pow_mul_hurwitzTaylorQuot`,
  `TauCeti.iteratedDeriv_hurwitzKernel_sub_sum_eq_pow_mul`,
  `TauCeti.analyticOnNhd_iteratedDeriv_hurwitzTaylorQuot`, and
  `TauCeti.analyticAt_hurwitzTaylorQuot_ofReal`: jointly analytic iterated-`dslope` remainder
  quotient, away-from-zero quotient formula, exact Taylor decomposition (and its `c`-differentiated
  form), joint analyticity of `c`-derivatives, and real-axis analyticity.
* `TauCeti.exists_norm_iteratedDeriv_hurwitzTaylorQuot_le`,
  `TauCeti.exists_norm_hurwitzTaylorQuot_le`,
  `TauCeti.exists_norm_hurwitzTaylorQuot_le_on_Icc`,
  `TauCeti.exists_norm_iteratedDeriv_hurwitzKernel_sub_sum_le`, and
  `TauCeti.exists_norm_hurwitzKernel_sub_sum_le`: compact-uniform Taylor quotient and remainder
  estimates (for arbitrary fixed `c`-derivative order `d` and at `d = 0`) on compact subsets of
  `{p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0}` and `K ×ˢ Icc 0 1`.

## References

* J. C. Lagarias and W. C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  **24** (2012), 49–84, §9.
* F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, §§24.2, 25.11.
-/

public section

open Complex Set Filter Metric
open scoped Topology Real

namespace TauCeti

/-- The exponential-Bernoulli generating kernel `z * exp (-c * z) / (1 - exp (-z))`, defined via
the filled-in exponential quotient `oneSubExpNegDivSelf ℂ z`. This fills in the removable
singularity at `z = 0` (`hurwitzKernel c 0 = 1`); at the nonzero poles `z = 2 * π * I * k`
(`k : ℤ`, `k ≠ 0`), where `oneSubExpNegDivSelf ℂ z = 0`, Lean's division by zero gives the
totalized value `0`. -/
noncomputable def hurwitzKernel (c z : ℂ) : ℂ :=
  Complex.exp (-c * z) / oneSubExpNegDivSelf ℂ z

/-- Defining equation for `hurwitzKernel`. -/
theorem hurwitzKernel_def (c z : ℂ) :
    hurwitzKernel c z = Complex.exp (-c * z) / oneSubExpNegDivSelf ℂ z := (rfl)

@[simp]
theorem hurwitzKernel_zero_right (c : ℂ) : hurwitzKernel c 0 = 1 := by
  simp [hurwitzKernel]

/-- For `z ≠ 0`, `hurwitzKernel c z` equals `z * exp (-c * z) / (1 - exp (-z))`. At the nonzero
poles `z = 2 * π * I * k` (`k : ℤ`, `k ≠ 0`), both denominators vanish and this equality holds as a
totalized Lean identity `0 = 0`. -/
theorem hurwitzKernel_of_ne_zero (c : ℂ) {z : ℂ} (hz : z ≠ 0) :
    hurwitzKernel c z = z * Complex.exp (-c * z) / (1 - Complex.exp (-z)) := by
  have hmul : z * oneSubExpNegDivSelf ℂ z = 1 - Complex.exp (-z) := by
    simp [Complex.exp_eq_exp_ℂ]
  rw [hurwitzKernel, ← hmul, mul_div_mul_left _ _ hz]

/-- Whenever `dslope Complex.exp 0 (-z) ≠ 0`,
`hurwitzKernel c z * (exp z - 1) = z * exp ((1 - c) * z)`. -/
theorem hurwitzKernel_mul_exp_sub_one (c : ℂ) {z : ℂ} (hz : dslope Complex.exp 0 (-z) ≠ 0) :
    hurwitzKernel c z * (Complex.exp z - 1) = z * Complex.exp ((1 - c) * z) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · have hne : Complex.exp z - 1 ≠ 0 := by
      rw [Complex.exp_sub_one_eq_exp_mul_one_sub_exp_neg]
      refine mul_ne_zero (Complex.exp_ne_zero z) ?_
      rw [← Complex.oneSubExpNegDivSelf_eq_dslope_exp_zero_neg] at hz
      simpa [Complex.exp_eq_exp_ℂ] using mul_ne_zero hz0 hz
    rw [hurwitzKernel_of_ne_zero c hz0, mul_div_assoc, Complex.exp_neg_mul_div_one_sub_exp_neg,
      mul_assoc, div_mul_cancel₀ _ hne]

/-- `(c, z) ↦ hurwitzKernel c z` is jointly analytic on the full nonvanishing locus
`{p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0}`. -/
theorem analyticOnNhd_hurwitzKernel :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzKernel p.1 p.2)
      {p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0} := by
  have heq : (fun p : ℂ × ℂ => hurwitzKernel p.1 p.2) =
      fun p : ℂ × ℂ => Complex.exp (-p.1 * p.2) / dslope Complex.exp 0 (-p.2) := by
    ext p
    simp [hurwitzKernel, Complex.oneSubExpNegDivSelf_eq_dslope_exp_zero_neg]
  rw [heq]
  intro p hp
  exact (((analyticAt_fst.neg).mul analyticAt_snd).cexp).div
    (AnalyticAt.comp (g := dslope Complex.exp 0) (f := fun p : ℂ × ℂ => -p.2)
      (((analyticOnNhd_cexp (u := univ)).dslope 0) (-p.2) trivial) analyticAt_snd.neg)
    hp

/-- For fixed `c : ℂ`, `hurwitzKernel c` is analytic on
`{z : ℂ | dslope Complex.exp 0 (-z) ≠ 0}`. -/
theorem analyticOnNhd_hurwitzKernel_right (c : ℂ) :
    AnalyticOnNhd ℂ (hurwitzKernel c) {z : ℂ | dslope Complex.exp 0 (-z) ≠ 0} := fun z hz =>
  (analyticOnNhd_hurwitzKernel (c, z) hz).comp (analyticAt_const.prod analyticAt_id)

/-- For fixed `c : ℂ`, `hurwitzKernel c` is analytic at `0`. -/
theorem analyticAt_hurwitzKernel_zero (c : ℂ) : AnalyticAt ℂ (hurwitzKernel c) 0 :=
  analyticOnNhd_hurwitzKernel_right c 0 (by simp)

/-- The `k`-th Taylor coefficient `(-1) ^ k * B_k(c) / k!` of `hurwitzKernel c` at `z = 0`. -/
noncomputable def hurwitzBernoulliCoeff (k : ℕ) (c : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * Polynomial.aeval c (Polynomial.bernoulli k) / k.factorial

/-- Defining equation for `hurwitzBernoulliCoeff`. -/
theorem hurwitzBernoulliCoeff_def (k : ℕ) (c : ℂ) :
    hurwitzBernoulliCoeff k c =
      (-1 : ℂ) ^ k * Polynomial.aeval c (Polynomial.bernoulli k) / k.factorial := (rfl)

/-- Each Bernoulli coefficient `c ↦ hurwitzBernoulliCoeff k c` is an entire polynomial in `c`. -/
theorem differentiable_hurwitzBernoulliCoeff (k : ℕ) :
    Differentiable ℂ (hurwitzBernoulliCoeff k) := by
  unfold hurwitzBernoulliCoeff
  exact ((Polynomial.bernoulli k).differentiable_aeval.const_mul ((-1 : ℂ) ^ k)).div_const
    (k.factorial : ℂ)

@[simp]
theorem hurwitzBernoulliCoeff_zero (c : ℂ) : hurwitzBernoulliCoeff 0 c = 1 := by
  simp [hurwitzBernoulliCoeff]

/-- The linear Bernoulli Taylor coefficient is `hurwitzBernoulliCoeff 1 c = 1 / 2 - c`, pinning
the `B_1(c) = c - 1 / 2` sign convention. -/
@[simp]
theorem hurwitzBernoulliCoeff_one (c : ℂ) : hurwitzBernoulliCoeff 1 c = 1 / 2 - c := by
  rw [hurwitzBernoulliCoeff, Polynomial.bernoulli_one]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C, eq_ratCast]
  push_cast; ring

example (c : ℂ) : hurwitzBernoulliCoeff 2 c = (c ^ 2 - c + 1 / 6) / 2 := by
  simp [hurwitzBernoulliCoeff_def, Polynomial.bernoulli_def, Finset.sum_range_succ]
  ring

private theorem iteratedDeriv_hurwitzKernel_zero_eq_aeval_one_sub (m : ℕ) (c : ℂ) :
    iteratedDeriv m (hurwitzKernel c) 0 =
      Polynomial.aeval (1 - c) (Polynomial.bernoulli m) := by
  have hf := analyticAt_hurwitzKernel_zero c
  have hid_an : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hexp1 : AnalyticAt ℂ (fun z => Complex.exp z - 1) 0 := by fun_prop
  have hexp2 : AnalyticAt ℂ (fun z => Complex.exp ((1 - c) * z)) 0 := by fun_prop
  have heq : (hurwitzKernel c * fun z => Complex.exp z - 1) =ᶠ[𝓝 0]
      ((fun z : ℂ => z) * fun z => Complex.exp ((1 - c) * z)) :=
    eventually_of_mem (ball_mem_nhds 0 Real.two_pi_pos) fun z hz =>
      hurwitzKernel_mul_exp_sub_one c (Complex.dslope_exp_ne_zero_of_mem_ball (by simpa using hz))
  have ht := taylorSeries_congr heq
  rw [taylorSeries_mul hf hexp1, taylorSeries_mul hid_an hexp2] at ht
  have hid : taylorSeries (fun z : ℂ => z) 0 = PowerSeries.X := by
    simpa only [sub_zero] using taylorSeries_sub_const (𝕜 := ℂ) (a := (0 : ℂ))
  simp only [Complex.exp_eq_exp_ℂ] at ht
  rw [hid, NormedSpace.taylorSeries_exp_sub_one_at_zero,
    NormedSpace.taylorSeries_exp_const_mul_at_zero (1 - c),
    ← Polynomial.bernoulli_generating_function (A := ℂ) (1 - c)] at ht
  have hne : PowerSeries.exp ℂ - (1 : PowerSeries ℂ) ≠ 0 := fun h0 => by
    have := congrArg (PowerSeries.coeff 1) h0
    simp [PowerSeries.coeff_exp] at this
  have hcoeff := congrArg (PowerSeries.coeff m) (mul_right_cancel₀ hne ht)
  rw [hf.coeff_taylorSeries_eq_inv_factorial_smul_iteratedDeriv m,
    PowerSeries.coeff_mk] at hcoeff
  have hfm : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  apply mul_left_cancel₀ hfm
  simp only [smul_eq_mul, map_smul, Rat.smul_def, Rat.cast_div, Rat.cast_one,
    Rat.cast_natCast] at hcoeff
  rw [inv_mul_eq_iff_eq_mul₀ hfm] at hcoeff
  rw [hcoeff]
  field_simp

/-- The `n`-th derivative of `hurwitzKernel c` at `0` is `(-1) ^ n * B_n(c)`. -/
@[simp]
theorem iteratedDeriv_hurwitzKernel_zero (n : ℕ) (c : ℂ) :
    iteratedDeriv n (hurwitzKernel c) 0 =
      (-1 : ℂ) ^ n * Polynomial.aeval c (Polynomial.bernoulli n) := by
  rw [iteratedDeriv_hurwitzKernel_zero_eq_aeval_one_sub]
  simpa [Polynomial.aeval_comp, Algebra.smul_def] using
    congrArg (Polynomial.aeval c) (Polynomial.bernoulli_comp_one_sub_X n)

/-- The `k`-th formal Taylor coefficient of `hurwitzKernel c` at `0` is
`hurwitzBernoulliCoeff k c`. -/
theorem coeff_taylorSeries_hurwitzKernel_zero (k : ℕ) (c : ℂ) :
    PowerSeries.coeff k (TauCeti.taylorSeries (hurwitzKernel c) 0) =
      hurwitzBernoulliCoeff k c := by
  rw [(analyticAt_hurwitzKernel_zero c).coeff_taylorSeries_eq_inv_factorial_smul_iteratedDeriv k,
    smul_eq_mul, iteratedDeriv_hurwitzKernel_zero, hurwitzBernoulliCoeff]
  ring

/-- The `k`-fold divided difference of `hurwitzKernel c` at `0` equals
`hurwitzBernoulliCoeff k c`. -/
@[simp]
theorem iterate_dslope_hurwitzKernel_zero (k : ℕ) (c : ℂ) :
    (Function.swap dslope (0 : ℂ))^[k] (hurwitzKernel c) 0 = hurwitzBernoulliCoeff k c := by
  rw [← TauCeti.coeff_taylorSeries, coeff_taylorSeries_hurwitzKernel_zero]

/-- The order-`M` Taylor remainder quotient of `hurwitzKernel c` at `z = 0`, defined as the
`(M + 1)`-fold divided difference `(Function.swap dslope 0)^[M + 1] (hurwitzKernel c) z`. -/
noncomputable def hurwitzTaylorQuot (M : ℕ) (c z : ℂ) : ℂ :=
  (Function.swap dslope (0 : ℂ))^[M + 1] (hurwitzKernel c) z

/-- Defining equation for `hurwitzTaylorQuot`. -/
theorem hurwitzTaylorQuot_def (M : ℕ) (c z : ℂ) :
    hurwitzTaylorQuot M c z =
      (Function.swap dslope (0 : ℂ))^[M + 1] (hurwitzKernel c) z := (rfl)

/-- `(c, z) ↦ hurwitzTaylorQuot M c z` is jointly analytic on the full nonvanishing locus
`{p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0}`. -/
theorem analyticOnNhd_hurwitzTaylorQuot (M : ℕ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzTaylorQuot M p.1 p.2)
      {p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0} := by
  simpa only [hurwitzTaylorQuot_def] using
    analyticOnNhd_hurwitzKernel.iterate_dslope_snd (fun _ _ => by simp) (M + 1)

/-- Exact order-`M` Taylor decomposition of `hurwitzKernel c z`. -/
theorem hurwitzKernel_sub_sum_eq_pow_mul_hurwitzTaylorQuot (M : ℕ) (c z : ℂ) :
    hurwitzKernel c z - ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c * z ^ k =
      z ^ (M + 1) * hurwitzTaylorQuot M c z := by
  have h := TauCeti.sum_add_pow_sub_smul_iterate_dslope (hurwitzKernel c) 0 z (M + 1)
  simp only [sub_zero, smul_eq_mul, iterate_dslope_hurwitzKernel_zero] at h
  have hsum : ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c * z ^ k =
      ∑ j ∈ Finset.range (M + 1), z ^ j * hurwitzBernoulliCoeff j c :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hurwitzTaylorQuot_def, hsum, ← h, add_sub_cancel_left]

/-- At `z = 0`, the order-`M` Taylor remainder quotient equals the next Taylor coefficient
`hurwitzBernoulliCoeff (M + 1) c`. -/
@[simp]
theorem hurwitzTaylorQuot_zero_right (M : ℕ) (c : ℂ) :
    hurwitzTaylorQuot M c 0 = hurwitzBernoulliCoeff (M + 1) c :=
  iterate_dslope_hurwitzKernel_zero (M + 1) c

/-- Away from `z = 0`, `hurwitzTaylorQuot M c z` is the order-`M` Taylor remainder divided by
`z ^ (M + 1)`. -/
theorem hurwitzTaylorQuot_of_ne_zero (M : ℕ) (c : ℂ) {z : ℂ} (hz : z ≠ 0) :
    hurwitzTaylorQuot M c z =
      (hurwitzKernel c z -
        ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k c * z ^ k) / z ^ (M + 1) := by
  rw [hurwitzKernel_sub_sum_eq_pow_mul_hurwitzTaylorQuot,
    mul_div_cancel_left₀ _ (pow_ne_zero (M + 1) hz)]

/-- Step relation between consecutive Taylor remainder quotients. -/
theorem hurwitzTaylorQuot_eq_add_mul_succ (M : ℕ) (c z : ℂ) :
    hurwitzTaylorQuot M c z =
      hurwitzBernoulliCoeff (M + 1) c + z * hurwitzTaylorQuot (M + 1) c z := by
  have h := eq_add_of_sub_eq'
    (sub_smul_dslope ((Function.swap dslope (0 : ℂ))^[M + 1] (hurwitzKernel c)) 0 z).symm
  simpa only [sub_zero, smul_eq_mul, iterate_dslope_hurwitzKernel_zero,
    Function.iterate_succ_apply', hurwitzTaylorQuot_def] using h

private theorem analyticOnNhd_iteratedDeriv_fst {F : ℂ × ℂ → ℂ} {S : Set (ℂ × ℂ)}
    (hF : AnalyticOnNhd ℂ F S) :
    ∀ d : ℕ, AnalyticOnNhd ℂ (fun p : ℂ × ℂ => iteratedDeriv d (fun c => F (c, p.2)) p.1) S
  | 0 => by simpa only [iteratedDeriv_zero] using hF
  | d + 1 => by
      have hderiv : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => deriv (fun c => F (c, p.2)) p.1) S := by
        intro p hp
        have hf := hF p hp
        have hf_fderiv : AnalyticAt ℂ (fun q : ℂ × ℂ => fderiv ℂ F q ((1 : ℂ), (0 : ℂ))) p :=
          ((ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : ℂ))).analyticAt _).comp hf.fderiv
        refine hf_fderiv.congr ?_
        filter_upwards [hf.eventually_analyticAt] with q hq
        have h := ((hq.differentiableAt.hasFDerivAt).comp q.1
          (hasFDerivAt_prodMk_left q.1 q.2)).hasDerivAt.deriv
        simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.inl_apply] using h.symm
      simpa only [iteratedDeriv_succ'] using analyticOnNhd_iteratedDeriv_fst hderiv d

/-- For every fixed `c`-derivative order `d`,
`(c, z) ↦ iteratedDeriv d (fun w => hurwitzTaylorQuot M w z) c` is jointly analytic on
`{p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0}`. -/
theorem analyticOnNhd_iteratedDeriv_hurwitzTaylorQuot (M d : ℕ) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => iteratedDeriv d (fun c => hurwitzTaylorQuot M c p.2) p.1)
      {p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0} :=
  analyticOnNhd_iteratedDeriv_fst (analyticOnNhd_hurwitzTaylorQuot M) d

/-- Compact-uniform bound on a compact subset `S` of the nonvanishing locus for the `d`-th
`c`-derivative `iteratedDeriv d (fun c => hurwitzTaylorQuot M c p.2) p.1`. -/
theorem exists_norm_iteratedDeriv_hurwitzTaylorQuot_le {S : Set (ℂ × ℂ)} (hS : IsCompact S)
    (hS_sub : S ⊆ {p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0}) (M d : ℕ) :
    ∃ B ≥ 0, ∀ p ∈ S, ‖iteratedDeriv d (fun c => hurwitzTaylorQuot M c p.2) p.1‖ ≤ B := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
    ((analyticOnNhd_iteratedDeriv_hurwitzTaylorQuot M d).continuousOn.mono hS_sub)
  exact ⟨max B 0, le_max_right _ _, fun p hp => (hB p hp).trans (le_max_left _ _)⟩

/-- Compact-uniform bound on a compact subset `S` of the nonvanishing locus for
`hurwitzTaylorQuot M p.1 p.2`. -/
theorem exists_norm_hurwitzTaylorQuot_le {S : Set (ℂ × ℂ)} (hS : IsCompact S)
    (hS_sub : S ⊆ {p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0}) (M : ℕ) :
    ∃ B ≥ 0, ∀ p ∈ S, ‖hurwitzTaylorQuot M p.1 p.2‖ ≤ B := by
  simpa only [iteratedDeriv_zero] using
    exists_norm_iteratedDeriv_hurwitzTaylorQuot_le hS hS_sub M 0

/-- At any `(c, (t : ℂ))` with real `t`, `hurwitzTaylorQuot M` is jointly analytic. -/
theorem analyticAt_hurwitzTaylorQuot_ofReal (M : ℕ) (c : ℂ) (t : ℝ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => hurwitzTaylorQuot M p.1 p.2) (c, t) :=
  analyticOnNhd_hurwitzTaylorQuot M (c, t)
    (Complex.abs_im_snd_lt_subset_dslope_exp_neg_ne_zero (by simp [Real.pi_pos]))

/-- Uniform bound for `‖hurwitzTaylorQuot M c t‖` on `K × [0, 1]` for any compact `K ⊆ ℂ`. -/
theorem exists_norm_hurwitzTaylorQuot_le_on_Icc {K : Set ℂ} (hK : IsCompact K) (M : ℕ) :
    ∃ B ≥ 0, ∀ c ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ‖hurwitzTaylorQuot M c t‖ ≤ B := by
  let S : Set (ℂ × ℂ) := K ×ˢ (Complex.ofReal '' Icc (0 : ℝ) 1)
  have hS_comp : IsCompact S := hK.prod (isCompact_Icc.image continuous_ofReal)
  have hS_sub : S ⊆ {p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0} :=
    (by rintro ⟨_, _⟩ ⟨_, _, _, rfl⟩; simp [Real.pi_pos] :
      S ⊆ {p : ℂ × ℂ | |p.2.im| < 2 * π}).trans Complex.abs_im_snd_lt_subset_dslope_exp_neg_ne_zero
  obtain ⟨B, hB0, hB⟩ := exists_norm_hurwitzTaylorQuot_le hS_comp hS_sub M
  exact ⟨B, hB0, fun c hc t ht => hB (c, t) ⟨hc, t, ht, rfl⟩⟩

/-- Exact order-`M` Taylor decomposition after `d` derivatives in `c`, for `z` in the
nonvanishing locus `{z : ℂ | dslope Complex.exp 0 (-z) ≠ 0}`. -/
theorem iteratedDeriv_hurwitzKernel_sub_sum_eq_pow_mul (M d : ℕ) (c : ℂ) {z : ℂ}
    (hz : dslope Complex.exp 0 (-z) ≠ 0) :
    iteratedDeriv d (fun w => hurwitzKernel w z) c -
        ∑ k ∈ Finset.range (M + 1), iteratedDeriv d (hurwitzBernoulliCoeff k) c * z ^ k =
      z ^ (M + 1) * iteratedDeriv d (fun w => hurwitzTaylorQuot M w z) c := by
  have hk : ContDiffAt ℂ d (fun w : ℂ => hurwitzKernel w z) c :=
    ((analyticOnNhd_hurwitzKernel (c, z) hz).comp (f := fun w : ℂ => (w, z))
      (analyticAt_id.prod analyticAt_const)).contDiffAt
  have hterm : ∀ k ∈ Finset.range (M + 1),
      ContDiffAt ℂ d (fun w : ℂ => hurwitzBernoulliCoeff k w * z ^ k) c := fun k _ =>
    ((((contDiff_const.mul ((Polynomial.bernoulli k).contDiff_aeval d)).div_const
      (k.factorial : ℂ) : ContDiff ℂ d (hurwitzBernoulliCoeff k)).mul contDiff_const).contDiffAt)
  have heq : (fun w : ℂ => hurwitzKernel w z -
        ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k w * z ^ k) =
      fun w : ℂ => z ^ (M + 1) * hurwitzTaylorQuot M w z :=
    funext fun w => hurwitzKernel_sub_sum_eq_pow_mul_hurwitzTaylorQuot M w z
  have hderiv := congrArg (fun f : ℂ → ℂ => iteratedDeriv d f c) heq
  rw [iteratedDeriv_fun_sub hk (.sum hterm), iteratedDeriv_fun_sum hterm,
    iteratedDeriv_const_mul_field] at hderiv
  simpa only [iteratedDeriv_mul_const_field] using hderiv

/-- Compact-uniform Taylor remainder estimate on a compact subset `S` of the nonvanishing locus
after taking `d` derivatives in the shift parameter `c`. -/
theorem exists_norm_iteratedDeriv_hurwitzKernel_sub_sum_le {S : Set (ℂ × ℂ)} (hS : IsCompact S)
    (hS_sub : S ⊆ {p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0}) (M d : ℕ) :
    ∃ C ≥ 0, ∀ p ∈ S,
      ‖iteratedDeriv d (fun c => hurwitzKernel c p.2) p.1 -
          ∑ k ∈ Finset.range (M + 1), iteratedDeriv d (hurwitzBernoulliCoeff k) p.1 * p.2 ^ k‖ ≤
        C * ‖p.2‖ ^ (M + 1) := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_iteratedDeriv_hurwitzTaylorQuot_le hS hS_sub M d
  refine ⟨B, hB0, fun p hp => ?_⟩
  rw [iteratedDeriv_hurwitzKernel_sub_sum_eq_pow_mul M d p.1 (hS_sub hp), norm_mul, norm_pow,
    mul_comm (‖p.2‖ ^ (M + 1))]
  exact mul_le_mul_of_nonneg_right (hB p hp) (pow_nonneg (norm_nonneg _) _)

/-- Compact-uniform Taylor remainder estimate on a compact subset `S` of the nonvanishing locus
for `hurwitzKernel p.1 p.2`. -/
theorem exists_norm_hurwitzKernel_sub_sum_le {S : Set (ℂ × ℂ)} (hS : IsCompact S)
    (hS_sub : S ⊆ {p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0}) (M : ℕ) :
    ∃ C ≥ 0, ∀ p ∈ S,
      ‖hurwitzKernel p.1 p.2 -
          ∑ k ∈ Finset.range (M + 1), hurwitzBernoulliCoeff k p.1 * p.2 ^ k‖ ≤
        C * ‖p.2‖ ^ (M + 1) := by
  simpa only [iteratedDeriv_zero] using
    exists_norm_iteratedDeriv_hurwitzKernel_sub_sum_le hS hS_sub M 0

end TauCeti

end
