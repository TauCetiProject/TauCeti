/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.IntegrableExpMul
import TauCeti.MeasureTheory.Function.L1Space.Integrable

/-!
# Probability-generating functions

This file defines the probability-generating function of a natural-number-valued random variable
and establishes its basic measure-theoretic API.  The central results relate it to Mathlib's
moment-generating function and show that it turns sums of independent random variables into
products.  The file then identifies the generating function of a finite measure on `ℕ` with the
sum of the power series carrying its singleton masses, so that the generating function is analytic
on `(-1, 1)` and its Taylor coefficients at the origin recover those masses;
consequently a law on `ℕ` is determined by its generating function near `0`.

## Main declarations

* `TauCeti.Probability.pgf` — the probability-generating function.
* `TauCeti.Probability.pgf_exp` — evaluation at `exp t` is a moment-generating function, and
  `TauCeti.Probability.mgf_id_map_natCast` restates this for the real cast of a law on `ℕ`.
* `TauCeti.Probability.integrable_pow_of_abs_le_one` — on `[-1, 1]` the integrand is
  integrable under a finite measure.
* `TauCeti.Probability.IndepFun.pgf_add` and `TauCeti.Probability.iIndepFun.pgf_sum` —
  multiplicativity over binary and finite sums of independent random variables when the factor
  integrands are integrable.
* `TauCeti.Probability.IndepFun.pgf_add_of_abs_le_one` and
  `TauCeti.Probability.iIndepFun.pgf_sum_of_abs_le_one` — the corresponding formulas on the
  interval `[-1, 1]`, where integrability is automatic.
* `Measure.pgf_conv` and `Measure.pgf_conv_of_abs_le_one` — convolution becomes
  multiplication under the natural integrability hypotheses, and for finite measures on
  `[-1, 1]`.
* `TauCeti.Probability.hasSum_pgf` and `TauCeti.Probability.pgf_eq_tsum` — the power-series
  expansion in the singleton masses, valid on `[-1, 1]`.
* `TauCeti.Probability.hasFPowerSeriesOnBall_pgf` and `TauCeti.Probability.analyticOnNhd_pgf` —
  analyticity on the open unit ball.
* `TauCeti.Probability.iteratedDeriv_pgf_one` — under a positive exponential moment, the
  derivatives at one are the factorial moments.
* `TauCeti.Probability.tendsto_iteratedDeriv_pgf_nhdsLT_one` — under a finite factorial moment,
  the corresponding derivative tends to that moment as the argument tends to one from below.
* `TauCeti.Probability.iteratedDeriv_pgf_zero` — the Taylor coefficients at the origin are the
  singleton masses, with `TauCeti.Probability.pgf_zero` and `TauCeti.Probability.deriv_pgf_zero`
  reading off the first two.
* `TauCeti.Probability.measure_eq_of_pgf_eventuallyEq` and
  `TauCeti.Probability.identDistrib_of_pgf_eventuallyEq` — uniqueness of the law from the germ of
  the generating function at `0`, with the corollaries
  `TauCeti.Probability.measure_eq_of_pgf_eqOn` and `TauCeti.Probability.identDistrib_of_pgf_eqOn`
  reading the hypothesis off `(-1, 1)`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The probability-generating function of a natural-number-valued random variable `X` with
respect to a measure `μ`. -/
def pgf (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  ∫ ω, t ^ X ω ∂μ

/-- The defining integral formula for the probability-generating function.  This is the canonical
way to unfold `pgf`, which is otherwise sealed. -/
-- The parentheses around `rfl` opt this proof out of the exported-theorem exposure check, which
-- keeps `pgf` itself sealed.
theorem pgf_def (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) : pgf X μ t = ∫ ω, t ^ X ω ∂μ := (rfl)

/-- The probability-generating function is unchanged by replacing the random variable almost
everywhere. -/
theorem pgf_congr_ae {X Y : Ω → ℕ} (hXY : X =ᵐ[μ] Y) : pgf X μ = pgf Y μ := by
  funext t
  exact integral_congr_ae (hXY.fun_comp fun n => t ^ n)

/-- The probability-generating function of the zero measure vanishes. -/
@[simp]
theorem pgf_zero_measure (X : Ω → ℕ) : pgf X (0 : Measure Ω) = 0 := by
  funext t
  simp [pgf_def]

/-- Evaluation of a probability-generating function at one gives the total mass. -/
@[simp]
theorem pgf_one (X : Ω → ℕ) : pgf X μ 1 = μ.real Set.univ := by
  simp [pgf_def]

/-- A constant natural-number-valued random variable has the expected monomial generating
function. -/
@[simp]
theorem pgf_const (n : ℕ) (t : ℝ) : pgf (fun _ : Ω => n) μ t = μ.real Set.univ * t ^ n := by
  simp [pgf_def]

/-- The probability-generating function can be computed on the law of the random variable. -/
theorem pgf_map {X : Ω → ℕ} (hX : AEMeasurable X μ) (t : ℝ) :
    pgf id (μ.map X) t = pgf X μ t := by
  rw [pgf_def, pgf_def, integral_map hX (measurable_id.const_pow t).aestronglyMeasurable]
  simp only [id_eq]

/-- Random variables with a given law have the same probability-generating function as that law. -/
theorem HasLaw.pgf_eq {X : Ω → ℕ} {ν : Measure ℕ} (hX : HasLaw X ν μ) (t : ℝ) :
    pgf X μ t = pgf id ν t := by
  rw [← hX.map_eq, pgf_map hX.aemeasurable]

/-- Evaluating the probability-generating function at `exp t` recovers the moment-generating
function of the real-valued cast of the random variable. -/
theorem pgf_exp (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) :
    pgf X μ (Real.exp t) = mgf (fun ω => (X ω : ℝ)) μ t := by
  simp only [pgf_def, mgf, ← Real.exp_nat_mul]
  congr 1
  funext ω
  rw [Nat.cast_comm, mul_comm]

/-- The moment-generating function of the real cast of a law on `ℕ` is its
probability-generating function evaluated at `exp t`. -/
theorem mgf_id_map_natCast (ν : Measure ℕ) (t : ℝ) :
    mgf id (ν.map (Nat.cast : ℕ → ℝ)) t = pgf id ν (Real.exp t) := by
  rw [pgf_exp, mgf_id_map .of_discrete]
  simp only [id_eq]

/-- For a finite measure, the integrand of a probability-generating function is integrable on
`[-1, 1]`. -/
theorem integrable_pow_of_abs_le_one [IsFiniteMeasure μ] {X : Ω → ℕ} (hX : AEMeasurable X μ)
    {t : ℝ} (ht : |t| ≤ 1) : Integrable (fun ω => t ^ X ω) μ := by
  refine (integrable_const (1 : ℝ)).mono' (hX.const_pow t).aestronglyMeasurable ?_
  filter_upwards with ω
  simpa only [Real.norm_eq_abs, abs_pow, norm_one] using pow_le_one₀ (abs_nonneg t) ht

/-- The probability-generating function of a sum of two independent natural-number-valued random
variables is the product of their generating functions whenever both factor integrands are
integrable.

The integrability hypotheses deliberately restrict the public statement so that it expresses a
product of genuine expectations.  Mathlib's totalized integral gives the same equality without
these hypotheses, but in the non-integrable cases it is merely an artifact of totalization. -/
theorem IndepFun.pgf_add {X Y : Ω → ℕ} (hXY : IndepFun X Y μ) (t : ℝ)
    (hXt : Integrable (fun ω => t ^ X ω) μ) (hYt : Integrable (fun ω => t ^ Y ω) μ) :
    pgf (X + Y) μ t = pgf X μ t * pgf Y μ t := by
  have hindep : IndepFun (fun ω => t ^ X ω) (fun ω => t ^ Y ω) μ :=
    hXY.comp (measurable_id.const_pow t) (measurable_id.const_pow t)
  simp_rw [pgf_def, Pi.add_apply, pow_add]
  exact hindep.integral_mul_eq_mul_integral hXt.aestronglyMeasurable
    hYt.aestronglyMeasurable

/-- Under a finite measure, on `[-1, 1]` the probability-generating function of a
sum of two independent natural-number-valued random variables is the product of their generating
functions. -/
theorem IndepFun.pgf_add_of_abs_le_one [IsFiniteMeasure μ] {X Y : Ω → ℕ}
    (hXY : IndepFun X Y μ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) {t : ℝ}
    (ht : |t| ≤ 1) : pgf (X + Y) μ t = pgf X μ t * pgf Y μ t :=
  IndepFun.pgf_add hXY t (integrable_pow_of_abs_le_one hX ht)
    (integrable_pow_of_abs_le_one hY ht)

/-- The probability-generating function sends convolution to multiplication whenever both factor
integrands are integrable. -/
theorem _root_.MeasureTheory.Measure.pgf_conv (μ ν : Measure ℕ) [SFinite μ] [SFinite ν]
    (t : ℝ) (hμ : Integrable (fun k => t ^ k) μ) (hν : Integrable (fun k => t ^ k) ν) :
    pgf id (μ ∗ ν) t = pgf id μ t * pgf id ν t := by
  have hconv : Integrable (fun k : ℕ => t ^ k) (μ ∗ ν) := by
    rw [Measure.conv, integrable_map_measure .of_discrete .of_discrete]
    convert hμ.mul_prod hν using 1
    ext z
    simp [pow_add]
  rw [pgf_def]
  simp only [id_eq]
  rw [integral_conv hconv]
  simp_rw [pow_add, integral_const_mul]
  rw [integral_mul_const, ← pgf_def, ← pgf_def]
  rfl

/-- On `[-1, 1]`, the probability-generating function sends convolution of finite measures to
multiplication. -/
theorem _root_.MeasureTheory.Measure.pgf_conv_of_abs_le_one (μ ν : Measure ℕ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {t : ℝ} (ht : |t| ≤ 1) :
    pgf id (μ ∗ ν) t = pgf id μ t * pgf id ν t :=
  Measure.pgf_conv μ ν t (integrable_pow_of_abs_le_one aemeasurable_id ht)
    (integrable_pow_of_abs_le_one aemeasurable_id ht)

/-- A probability-generating function turns a finite sum of independent random variables into the
product of their generating functions whenever every factor integrand is integrable. -/
theorem iIndepFun.pgf_sum {ι : Type*} {X : ι → Ω → ℕ} (h_indep : iIndepFun X μ)
    (s : Finset ι) (t : ℝ)
    (h_int : ∀ i ∈ s, Integrable (fun ω => t ^ X i ω) μ) :
    pgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, pgf (X i) μ t := by
  classical
  let Y : s → Ω → ℝ := fun i ω => t ^ X i ω
  have hY_indep : iIndepFun Y μ := by
    have hXs : iIndepFun (fun i : s => X i) μ :=
      iIndepFun.precomp Subtype.val_injective h_indep
    simpa only [Y, Function.comp_def] using
      hXs.comp (fun (_ : s) (n : ℕ) => t ^ n) fun _ => measurable_id.const_pow t
  have hY_meas : ∀ i, AEStronglyMeasurable (Y i) μ :=
    fun i => (h_int i i.property).aestronglyMeasurable
  calc
    pgf (∑ i ∈ s, X i) μ t = ∫ ω, ∏ i : s, Y i ω ∂μ := by
      rw [pgf_def]
      apply integral_congr_ae
      filter_upwards with ω
      simp only [Y, Finset.prod_pow_eq_pow_sum, Finset.sum_apply]
      exact congrArg (fun n : ℕ => t ^ n)
        (Finset.sum_coe_sort s fun i => X i ω).symm
    _ = ∏ i : s, ∫ ω, Y i ω ∂μ := hY_indep.integral_fun_prod_eq_prod_integral hY_meas
    _ = ∏ i ∈ s, pgf (X i) μ t := by
      simpa only [Y, pgf_def] using
        (Finset.prod_coe_sort s fun i => pgf (X i) μ t)

/-- On `[-1, 1]`, a probability-generating function turns a finite sum of
independent random variables into the product of their generating functions. -/
theorem iIndepFun.pgf_sum_of_abs_le_one {ι : Type*} {X : ι → Ω → ℕ}
    (h_indep : iIndepFun X μ) (s : Finset ι)
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ) {t : ℝ}
    (ht : |t| ≤ 1) : pgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, pgf (X i) μ t := by
  have := h_indep.isProbabilityMeasure
  exact iIndepFun.pgf_sum h_indep s t fun i hi =>
    integrable_pow_of_abs_le_one (h_meas i hi) ht

/-! ### Coefficient recovery and uniqueness

A finite measure on `ℕ` is the weighted sum of Dirac masses `∑ ν {n} • δ n`, so its
generating function is the sum of the power series `∑ ν.real {n} * t ^ n`.  The masses are
bounded by the total mass, so that series converges on the whole open unit ball and the generating
function is analytic there.  Reading its Taylor coefficients at the origin returns the masses, and
hence a finite measure on `ℕ`, in particular a probability measure, is determined by its generating
function near `0`. -/

section Coefficients

open FormalMultilinearSeries

/-- If the monomial integrand is integrable, the probability-generating function is the sum of
the power series whose coefficients are the singleton masses. -/
theorem hasSum_pgf_of_integrable (ν : Measure ℕ) {t : ℝ}
    (ht : Integrable (fun n : ℕ => t ^ n) ν) :
    HasSum (fun n => ν.real {n} * t ^ n) (pgf id ν t) := by
  have hsum : Summable (fun n : ℕ => ν.real {n} * ‖t ^ n‖) :=
    summable_measureReal_mul_norm_of_integrable ht
  rw [pgf_def]
  simp only [id_eq]
  rw [integral_countable ht]
  have hsum' : Summable (fun n : ℕ => ν.real {n} * t ^ n) := by
    apply Summable.of_norm
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using hsum
  simpa only [smul_eq_mul] using hsum'.hasSum

/-- Under a finite measure on `ℕ`, the probability-generating function is the sum of the power
series whose coefficients are the singleton masses, on `[-1, 1]`. -/
theorem hasSum_pgf (ν : Measure ℕ) [IsFiniteMeasure ν] {t : ℝ} (ht : |t| ≤ 1) :
    HasSum (fun n => ν.real {n} * t ^ n) (pgf id ν t) := by
  exact hasSum_pgf_of_integrable ν (integrable_pow_of_abs_le_one aemeasurable_id ht)

/-- The power-series expansion of the probability-generating function of a finite measure on `ℕ`
on `[-1, 1]`. -/
theorem pgf_eq_tsum (ν : Measure ℕ) [IsFiniteMeasure ν] {t : ℝ} (ht : |t| ≤ 1) :
    pgf id ν t = ∑' n : ℕ, ν.real {n} * t ^ n :=
  (hasSum_pgf ν ht).tsum_eq.symm

/-- An exponential moment extends the power-series representation of a
probability-generating function to the open ball of radius `exp t`. -/
theorem hasFPowerSeriesOnBall_pgf_of_integrable_exp_mul_natCast {ν : Measure ℕ} {t : ℝ}
    (hExp : Integrable (fun k : ℕ => Real.exp (t * (k : ℝ))) ν) :
    HasFPowerSeriesOnBall (pgf id ν) (ofScalars ℝ fun k => ν.real {k}) 0
      (ENNReal.ofReal (Real.exp t)) := by
  let p := ofScalars ℝ fun k => ν.real {k}
  have hexp (k : ℕ) : Real.exp (t * (k : ℝ)) = Real.exp t ^ k := by
    rw [mul_comm t, Real.exp_nat_mul]
  have hsum_exp : Summable (fun k : ℕ => ν.real {k} * ‖Real.exp (t * (k : ℝ))‖) :=
    summable_measureReal_mul_norm_of_integrable hExp
  have hp_radius : ENNReal.ofReal (Real.exp t) ≤ p.radius := by
    have hr := p.le_radius_of_summable_norm (r := Real.toNNReal (Real.exp t)) (by
      apply hsum_exp.congr
      intro n
      simp only [p, ofScalars_norm, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      rw [abs_of_pos (Real.exp_pos _), hexp n,
        Real.coe_toNNReal _ (Real.exp_pos t).le])
    simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ (Real.exp_pos t).le] using hr
  refine ⟨hp_radius, by positivity, ?_⟩
  intro z hz
  have hz_lt : |z| < Real.exp t := by
    rw [mem_eball_zero_iff, ← ofReal_norm,
      ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos t)] at hz
    simpa only [Real.norm_eq_abs] using hz
  have hz_int : Integrable (fun k : ℕ => z ^ k) ν := by
    refine hExp.mono' (by fun_prop) <| Filter.Eventually.of_forall fun k => ?_
    calc
      ‖z ^ k‖ = |z| ^ k := by simp
      _ ≤ Real.exp t ^ k := pow_le_pow_left₀ (abs_nonneg z) hz_lt.le k
      _ = Real.exp (t * (k : ℝ)) := (hexp k).symm
  simpa only [p, ofScalars_apply_eq, smul_eq_mul, zero_add] using
    hasSum_pgf_of_integrable ν hz_int

/-- The probability-generating function of a finite measure on `ℕ` has, at the origin, the formal
power series whose coefficients are the singleton masses, and that series converges on the open
unit ball. -/
theorem hasFPowerSeriesOnBall_pgf (ν : Measure ℕ) [IsFiniteMeasure ν] :
    HasFPowerSeriesOnBall (pgf id ν) (ofScalars ℝ fun n => ν.real {n}) 0 1 := by
  simpa using hasFPowerSeriesOnBall_pgf_of_integrable_exp_mul_natCast (ν := ν) (t := 0)
    (by simpa only [zero_mul, Real.exp_zero] using integrable_const (μ := ν) (1 : ℝ))

/-- An integrable `n`th power of a natural-number-valued function makes its `n`th falling
factorial integrable. -/
theorem integrable_descFactorial_of_integrable_pow_natCast {ν : Measure ℕ} {n : ℕ}
    (h : Integrable (fun k : ℕ => (k : ℝ) ^ n) ν) :
    Integrable (fun k : ℕ => (k.descFactorial n : ℝ)) ν := by
  refine h.mono' (by fun_prop) <| Filter.Eventually.of_forall fun k => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast k.descFactorial_le_pow n

/-- A positive exponential moment makes every natural falling factorial integrable. -/
theorem integrable_descFactorial_of_integrable_exp_mul_natCast {ν : Measure ℕ} {t : ℝ}
    (ht : 0 < t) (hExp : Integrable (fun k : ℕ => Real.exp (t * (k : ℝ))) ν) (n : ℕ) :
    Integrable (fun k : ℕ => (k.descFactorial n : ℝ)) ν := by
  let _ : IsFiniteMeasure ν := isFiniteMeasure_of_integrable_of_one_le hExp <|
    Filter.Eventually.of_forall fun k => by
      rw [Real.norm_eq_abs, Real.abs_exp]
      exact Real.one_le_exp (mul_nonneg ht.le (Nat.cast_nonneg k))
  have hExpNeg : Integrable (fun k : ℕ => Real.exp (-t * (k : ℝ))) ν := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) <|
      Filter.Eventually.of_forall fun k => ?_
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le)
        (Nat.cast_nonneg k))
  have hpow : Integrable (fun k : ℕ => (k : ℝ) ^ n) ν :=
    integrable_pow_of_integrable_exp_mul ht.ne' hExp hExpNeg n
  exact integrable_descFactorial_of_integrable_pow_natCast hpow

/-- If a measure on `ℕ` has a positive exponential moment, then the `n`th derivative at one of
its probability-generating function is its `n`th factorial moment. -/
theorem iteratedDeriv_pgf_one {ν : Measure ℕ} {t : ℝ} (ht : 0 < t)
    (hExp : Integrable (fun k : ℕ => Real.exp (t * (k : ℝ))) ν) (n : ℕ) :
    iteratedDeriv n (pgf id ν) 1 = ∫ k : ℕ, (k.descFactorial n : ℝ) ∂ν := by
  let p := ofScalars ℝ fun k => ν.real {k}
  have hp : HasFPowerSeriesOnBall (pgf id ν) p 0 (ENNReal.ofReal (Real.exp t)) := by
    simpa only [p] using hasFPowerSeriesOnBall_pgf_of_integrable_exp_mul_natCast hExp
  have h_one_ball : (1 : ℝ≥0∞) < ENNReal.ofReal (Real.exp t) := by
    rw [← ENNReal.ofReal_one,
      ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos t)]
    exact Real.one_lt_exp_iff.mpr ht
  have hdesc_int := integrable_descFactorial_of_integrable_exp_mul_natCast ht hExp n
  rw [hp.iteratedDeriv_eq_tsum_descFactorial_mul_pow (by simpa using h_one_ball) n,
    integral_countable hdesc_int]
  simp only [one_pow, mul_one]
  simp only [smul_eq_mul, mul_comm]

/-- If a finite measure on `ℕ` has a finite `n`th factorial moment, then the `n`th derivative of
its probability-generating function tends to that moment as the argument tends to one from
below. -/
theorem tendsto_iteratedDeriv_pgf_nhdsLT_one {ν : Measure ℕ} [IsFiniteMeasure ν] {n : ℕ}
    (hdesc : Integrable (fun k : ℕ => (k.descFactorial n : ℝ)) ν) :
    Tendsto (fun z => iteratedDeriv n (pgf id ν) z) (𝓝[<] 1)
      (𝓝 (∫ k : ℕ, (k.descFactorial n : ℝ) ∂ν)) := by
  have hnorm {z : ℝ} (hz : |z| ≤ 1) (k : ℕ) :
      ‖(k.descFactorial n : ℝ) * z ^ (k - n)‖ ≤ (k.descFactorial n : ℝ) := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), norm_pow,
      Real.norm_eq_abs]
    calc
      (k.descFactorial n : ℝ) * |z| ^ (k - n) ≤ (k.descFactorial n : ℝ) * 1 := by
        gcongr
        exact pow_le_one₀ (abs_nonneg z) hz
      _ = (k.descFactorial n : ℝ) := mul_one _
  have h_integral :
      Tendsto (fun z : ℝ => ∫ k : ℕ, (k.descFactorial n : ℝ) * z ^ (k - n) ∂ν)
        (𝓝[<] 1) (𝓝 (∫ k : ℕ, (k.descFactorial n : ℝ) ∂ν)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun k : ℕ => (k.descFactorial n : ℝ))
    · filter_upwards with z
      fun_prop
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with z hz
      exact Filter.Eventually.of_forall fun k => hnorm (abs_le.mpr
        ⟨(neg_nonpos.mpr (zero_le_one : (0 : ℝ) ≤ 1)).trans hz.1.le, hz.2.le⟩) k
    · exact hdesc
    · filter_upwards with k
      have h_id : Tendsto (fun z : ℝ => z) (𝓝[<] 1) (𝓝 1) :=
        tendsto_id'.2 nhdsWithin_le_nhds
      simpa only [one_pow, mul_one] using
        (h_id.pow (k - n)).const_mul (k.descFactorial n : ℝ)
  apply h_integral.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with z hz
  have hz_abs : |z| < 1 := by simpa [abs_of_pos hz.1] using hz.2
  have hz_ball : ‖z‖ₑ < (1 : ℝ≥0∞) := by
    rw [← ofReal_norm, ENNReal.ofReal_lt_one]
    simpa only [Real.norm_eq_abs] using hz_abs
  have hz_int : Integrable (fun k : ℕ => (k.descFactorial n : ℝ) * z ^ (k - n)) ν :=
    hdesc.mono' (by fun_prop) (Filter.Eventually.of_forall (hnorm hz_abs.le))
  rw [(hasFPowerSeriesOnBall_pgf ν).iteratedDeriv_eq_tsum_descFactorial_mul_pow hz_ball n,
    integral_countable hz_int]
  congr 1
  funext k
  simp only [smul_eq_mul]
  ring

/-- If a finite measure on `ℕ` has a finite `n`th ordinary moment, then the `n`th derivative of
its probability-generating function tends to the `n`th factorial moment as the argument tends to
one from below. -/
theorem tendsto_iteratedDeriv_pgf_nhdsLT_one_of_integrable_pow_natCast {ν : Measure ℕ}
    [IsFiniteMeasure ν] {n : ℕ} (hn : Integrable (fun k : ℕ => (k : ℝ) ^ n) ν) :
    Tendsto (fun z => iteratedDeriv n (pgf id ν) z) (𝓝[<] 1)
      (𝓝 (∫ k : ℕ, (k.descFactorial n : ℝ) ∂ν)) :=
  tendsto_iteratedDeriv_pgf_nhdsLT_one
    (integrable_descFactorial_of_integrable_pow_natCast hn)

/-- The probability-generating function of a finite measure on `ℕ` is analytic on `(-1, 1)`. -/
theorem analyticOnNhd_pgf (ν : Measure ℕ) [IsFiniteMeasure ν] :
    AnalyticOnNhd ℝ (pgf id ν) (Set.Ioo (-1) 1) :=
  (hasFPowerSeriesOnBall_pgf ν).analyticOnNhd.mono fun x hx => by
    rw [mem_eball_zero_iff, ← ofReal_norm, ENNReal.ofReal_lt_one]
    simpa [abs_lt] using hx

/-- The Taylor coefficients at the origin of the probability-generating function of a finite
measure on `ℕ` are its singleton masses. -/
@[simp]
theorem iteratedDeriv_pgf_zero (ν : Measure ℕ) [IsFiniteMeasure ν] (n : ℕ) :
    iteratedDeriv n (pgf id ν) 0 = (n.factorial : ℝ) * ν.real {n} := by
  have h₁ : HasFPowerSeriesAt (pgf id ν) (ofScalars ℝ fun k => ν.real {k}) 0 :=
    ⟨1, hasFPowerSeriesOnBall_pgf ν⟩
  have hcoeff := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff n)
    (h₁.eq_formalMultilinearSeries h₁.analyticAt.hasFPowerSeriesAt)
  simp only [coeff_ofScalars] at hcoeff
  rw [eq_comm, div_eq_iff (Nat.cast_ne_zero.mpr n.factorial_ne_zero)] at hcoeff
  rw [hcoeff, mul_comm]

/-- Evaluating at the origin the probability-generating function of a finite measure on `ℕ` gives
the mass of `{0}`.  This is the `n = 0` case of `iteratedDeriv_pgf_zero`, which `simp` normalises
away from `iteratedDeriv`. -/
@[simp]
theorem pgf_zero (ν : Measure ℕ) [IsFiniteMeasure ν] : pgf id ν 0 = ν.real {0} := by
  have h := iteratedDeriv_pgf_zero ν 0
  rwa [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul] at h

/-- The derivative at the origin of the probability-generating function of a finite measure on `ℕ`
is the mass of `{1}`.  This is the `n = 1` case of `iteratedDeriv_pgf_zero`, which `simp`
normalises away from `iteratedDeriv`. -/
@[simp]
theorem deriv_pgf_zero (ν : Measure ℕ) [IsFiniteMeasure ν] : deriv (pgf id ν) 0 = ν.real {1} := by
  rw [← iteratedDeriv_one, iteratedDeriv_pgf_zero]
  simp

/-- A finite measure on `ℕ`, in particular a probability measure, is determined by the germ at the
origin of its probability-generating function. -/
theorem measure_eq_of_pgf_eventuallyEq {ν ν' : Measure ℕ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h : pgf id ν =ᶠ[nhds 0] pgf id ν') : ν = ν' := by
  refine ext_iff_measureReal_singleton.mpr fun n => ?_
  have hderiv := h.iteratedDeriv_eq n
  rw [iteratedDeriv_pgf_zero, iteratedDeriv_pgf_zero] at hderiv
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero) hderiv

/-- A finite measure on `ℕ`, in particular a probability measure, is determined by its
probability-generating function on `(-1, 1)`. -/
theorem measure_eq_of_pgf_eqOn {ν ν' : Measure ℕ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h : Set.EqOn (pgf id ν) (pgf id ν') (Set.Ioo (-1) 1)) : ν = ν' :=
  measure_eq_of_pgf_eventuallyEq
    (Filter.eventuallyEq_of_mem (Ioo_mem_nhds (by norm_num) (by norm_num)) h)

/-- Two natural-number-valued random variables whose probability-generating functions agree near
the origin are identically distributed. -/
theorem identDistrib_of_pgf_eventuallyEq {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω}
    {Q : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure Q] {X : Ω → ℕ} {Y : Ω' → ℕ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q) (h : pgf X P =ᶠ[nhds 0] pgf Y Q) :
    IdentDistrib X Y P Q := by
  have := P.isFiniteMeasure_map X
  have := Q.isFiniteMeasure_map Y
  refine ⟨hX, hY, measure_eq_of_pgf_eventuallyEq ?_⟩
  filter_upwards [h] with t ht
  rw [pgf_map hX, pgf_map hY]
  exact ht

/-- Two natural-number-valued random variables whose probability-generating functions agree on
`(-1, 1)` are identically distributed. -/
theorem identDistrib_of_pgf_eqOn {Ω' : Type*} [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsFiniteMeasure P] [IsFiniteMeasure Q] {X : Ω → ℕ} {Y : Ω' → ℕ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (h : Set.EqOn (pgf X P) (pgf Y Q) (Set.Ioo (-1) 1)) : IdentDistrib X Y P Q :=
  identDistrib_of_pgf_eventuallyEq hX hY
    (Filter.eventuallyEq_of_mem (Ioo_mem_nhds (by norm_num) (by norm_num)) h)

end Coefficients

end Probability

end TauCeti
