/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import TauCeti.MeasureTheory.Group.Convolution.Power
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.Integration
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.MeasureTheory.Measure.Typeclasses.Probability

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
* `TauCeti.Probability.pgf_dirac` — the probability-generating function of a natural-number-valued
  statistic under a Dirac measure.
* `TauCeti.Probability.pgf_exp` — evaluation at `exp t` is a moment-generating function, and
  `TauCeti.Probability.mgf_id_map_natCast` restates this for the real cast of a law on `ℕ`.
* `TauCeti.Probability.integrable_pow_of_abs_le_one` — on `[-1, 1]` the integrand is
  integrable under a finite measure.
* `TauCeti.Probability.abs_pgf_le` — on `[-1, 1]` the generating function is bounded by the total
  mass.
* `TauCeti.Probability.IndepFun.pgf_add` and `TauCeti.Probability.iIndepFun.pgf_sum` —
  multiplicativity over binary and finite sums of independent random variables when the factor
  integrands are integrable.
* `TauCeti.Probability.IndepFun.pgf_add_of_abs_le_one` and
  `TauCeti.Probability.iIndepFun.pgf_sum_of_abs_le_one` — the corresponding formulas on the
  interval `[-1, 1]`, where integrability is automatic.
* `Measure.pgf_conv` and `Measure.pgf_conv_of_abs_le_one` — convolution becomes
  multiplication under the natural integrability hypotheses, and for finite measures on
  `[-1, 1]`; `Measure.pgf_convolutionPower_of_abs_le_one` is the version for convolution powers.
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
* `TauCeti.Probability.continuousOn_pgf`, `TauCeti.Probability.monotoneOn_pgf`,
  `TauCeti.Probability.convexOn_pgf` and `TauCeti.Probability.strictConvexOn_pgf` — the shape of
  the generating function of a finite measure on `ℕ`: continuous on `[-1, 1]`, nondecreasing and
  convex on `[0, 1]`, and strictly convex there when the measure charges some `k ≥ 2`, with
  `TauCeti.Probability.strictConvexOn_pgf_of_add_lt_one` for the hypothesis `ν {0} + ν {1} < 1`;
  `TauCeti.Probability.pgf_eq_of_add_eq_one` gives the affine generating function in the remaining
  case `ν {0} + ν {1} = 1`, and `TauCeti.Probability.mapsTo_pgf_Icc` says that for a probability
  measure it maps `[0, 1]` into itself.
* `TauCeti.Probability.hasSum_deriv_pgf`, `TauCeti.Probability.monotoneOn_deriv_pgf` and
  `TauCeti.Probability.tendsto_ofReal_deriv_pgf_nhdsLT_one` — the derivative on `(-1, 1)` is the
  termwise derivative of the power series; it is nondecreasing on `[0, 1)` and increases to the
  mean `∫⁻ k, k`, taken in `[0, ∞]`, as the argument increases to `1`, also when the mean is
  infinite; `TauCeti.Probability.ofReal_deriv_pgf_le` bounds it by the mean on `[0, 1)`.
* `TauCeti.Probability.monotone_iterate_pgf_zero` and `TauCeti.Probability.iterate_pgf_zero_le` —
  for a probability measure on `ℕ`, the iterates `f^[n] 0` of its generating function `f` increase
  and lie below every nonnegative fixed point of `f`.
* `TauCeti.Probability.isLeast_of_tendsto_iterate_pgf_zero` and
  `TauCeti.Probability.isLeast_iSup_iterate_pgf_zero` — the limit of these iterates is the least
  fixed point of `f` in `[0, 1]`.
* `TauCeti.Probability.setOf_pgf_eq_self_eq_pair` — unless `ν {1} = 1`, the fixed points of `f`
  in `[0, 1]` are the least one and `1`, using `TauCeti.Probability.pgf_lt_self_of_add_lt_one` and
  `TauCeti.Probability.eq_one_of_pgf_eq_self_of_add_eq_one` for the two cases that
  `MeasureTheory.Measure.measure_singleton_add_measure_singleton_le` leaves.

## References

The fixed-point section follows the classical analysis of the extinction probability of a
Galton–Watson process:

* R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press (2016),
  Section 5.1, Proposition 5.4 and Corollary 5.3.
* R. Durrett, *Probability: Theory and Examples*, fifth edition, Cambridge University Press
  (2019), Section 4.3.4, Theorems 4.3.10 to 4.3.12.
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

/-- The probability-generating function of a natural-number-valued statistic under a Dirac
measure is a monomial. -/
@[simp]
theorem pgf_dirac [MeasurableSingletonClass Ω] (X : Ω → ℕ) (ω : Ω) (z : ℝ) :
    pgf X (Measure.dirac ω) z = z ^ X ω := by
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

/-- Random variables with a given law have the same exponential-integrability domain as that
law. -/
theorem HasLaw.integrableExpSet_eq {X : Ω → ℝ} {ν : Measure ℝ} (hX : HasLaw X ν μ) :
    integrableExpSet X μ = integrableExpSet id ν := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq]
  rw [← hX.map_eq, integrable_map_measure (by fun_prop) hX.aemeasurable]
  rfl

/-- Evaluating the probability-generating function at `exp t` recovers the moment-generating
function of the real-valued cast of the random variable. -/
theorem pgf_exp (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) :
    pgf X μ (Real.exp t) = mgf (fun ω => (X ω : ℝ)) μ t := by
  simp only [pgf_def, mgf, ← Real.exp_natCast_mul]
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

/-- On `[-1, 1]` the probability-generating function of a random variable under a finite measure
is bounded in absolute value by the total mass; for a probability measure it maps `[-1, 1]` into
itself. -/
theorem abs_pgf_le [IsFiniteMeasure μ] (X : Ω → ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    |pgf X μ t| ≤ μ.real Set.univ := by
  rw [pgf_def, ← Real.norm_eq_abs, ← one_mul (μ.real Set.univ)]
  refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun ω => ?_)
  simpa only [Real.norm_eq_abs, abs_pow] using pow_le_one₀ (abs_nonneg t) ht

/-- For a probability law on `ℕ`, the error in the approximation
`pgf id ν z ≈ 1 + (z - 1) * ν.real {1}` is bounded by twice the multiple-occurrence probability.
The estimate holds on the entire interval `[-1, 1]`. -/
theorem _root_.MeasureTheory.Measure.abs_pgf_sub_one_sub_mul_le
    (ν : Measure ℕ) [IsProbabilityMeasure ν]
    {z : ℝ} (hz : |z| ≤ 1) :
    |pgf id ν z - 1 - (z - 1) * ν.real {1}| ≤ 2 * ν.real (Set.Ici 2) := by
  let b : ℕ → ℝ := Set.indicator {1} (fun _ ↦ 1)
  have hb : Integrable b ν := (integrable_const 1).indicator (measurableSet_singleton 1)
  have hbint : ∫ k, b k ∂ν = ν.real {1} := by
    dsimp only [b]
    rw [integral_indicator (measurableSet_singleton 1)]
    simp [measureReal_def]
  have hp := integrable_pow_of_abs_le_one (μ := ν) aemeasurable_id hz
  simp only [id_eq] at hp
  have heq (k : ℕ) : z ^ k - 1 - (z - 1) * b k =
      Set.indicator (Set.Ici 2) (fun k ↦ z ^ k - 1) k := by
    rcases k with _ | _ | k
    · simp [b]
    · simp [b]
    · simp [b]
  have hint : pgf id ν z - 1 - (z - 1) * ν.real {1} =
      ∫ k in Set.Ici 2, (z ^ k - 1) ∂ν := by
    rw [← integral_indicator measurableSet_Ici]
    simp_rw [← heq]
    rw [integral_sub (f := fun k : ℕ ↦ z ^ k - 1)
      (hp.sub (integrable_const 1)) (hb.const_mul _),
      integral_sub hp (integrable_const 1), integral_const_mul]
    simp [hbint, pgf_def]
  rw [hint, ← Real.norm_eq_abs]
  have hbound : ∀ k : ℕ, ‖z ^ k - 1‖ ≤ 2 := fun k ↦ by
    calc
      ‖z ^ k - 1‖ ≤ ‖z ^ k‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
      _ ≤ 2 := by
        simpa only [norm_pow, Real.norm_eq_abs, abs_one, one_add_one_eq_two, add_comm] using
          add_le_add_right (pow_le_one₀ (n := k) (abs_nonneg z) hz) 1
  simpa [mul_comm] using norm_integral_le_of_norm_le_const
    (μ := ν.restrict (Set.Ici 2)) (C := (2 : ℝ)) (ae_of_all _ hbound)

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
theorem _root_.MeasureTheory.Measure.pgf_conv (μ ν : Measure ℕ)
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

/-- On `[-1, 1]`, the probability-generating function of the `n`-fold convolution power of a finite
measure on `ℕ` is the `n`th power of its generating function. -/
theorem _root_.MeasureTheory.Measure.pgf_convolutionPower_of_abs_le_one (ν : Measure ℕ)
    [IsFiniteMeasure ν] (n : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    pgf id (ν.convolutionPower n) t = pgf id ν t ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Measure.convolutionPower_succ, Measure.pgf_conv_of_abs_le_one _ _ ht, ih, pow_succ]

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
    rw [mul_comm t, Real.exp_natCast_mul]
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
  let _ : IsFiniteMeasure ν := hExp.isFiniteMeasure_of_one_le_norm <|
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

/-- Evaluating at the origin the probability-generating function of a measure on `ℕ` gives
the real-valued mass `ν.real {0}`; if `ν {0} = ∞` both sides are `0`, as `ν.real` sends infinite
mass to zero.  For a finite measure this is the `n = 0` case of `iteratedDeriv_pgf_zero`,
which `simp` normalises away from `iteratedDeriv`. -/
@[simp]
theorem pgf_zero (ν : Measure ℕ) : pgf id ν 0 = ν.real {0} := by
  have h : (fun n : ℕ ↦ (0 : ℝ) ^ n) = Set.indicator {0} 1 := by
    ext n
    cases n <;> simp
  rw [pgf_def]
  simp only [id_eq]
  rw [h, integral_indicator_one (measurableSet_singleton 0)]

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

/-! ### The shape of the generating function on `[0, 1]` -/

section Shape

private theorem abs_le_one_of_mem_Icc {u : ℝ} (hu : u ∈ Set.Icc 0 1) : |u| ≤ 1 := by
  rw [abs_of_nonneg hu.1]; exact hu.2

private theorem abs_lt_one_of_mem_Ico {u : ℝ} (hu : u ∈ Set.Ico 0 1) : |u| < 1 := by
  rw [abs_of_nonneg hu.1]; exact hu.2

/-- Each term `ν {n} t ^ n` of the generating function is convex in `t ∈ [0, 1]`. -/
private theorem measureReal_mul_pow_convex_le (ν : Measure ℕ) (n : ℕ) {x y a b : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ν.real {n} * (a * x + b * y) ^ n ≤ a * (ν.real {n} * x ^ n) + b * (ν.real {n} * y ^ n) := by
  have := (convexOn_pow n).2 (Set.mem_Ici.mpr hx.1) (Set.mem_Ici.mpr hy.1) ha hb hab
  simp only [smul_eq_mul] at this
  calc ν.real {n} * (a * x + b * y) ^ n ≤ ν.real {n} * (a * x ^ n + b * y ^ n) :=
        mul_le_mul_of_nonneg_left this measureReal_nonneg
    _ = a * (ν.real {n} * x ^ n) + b * (ν.real {n} * y ^ n) := by ring

/-- The probability-generating function of a finite measure on `ℕ` is continuous on `[-1, 1]`. -/
theorem continuousOn_pgf (ν : Measure ℕ) [IsFiniteMeasure ν] :
    ContinuousOn (pgf id ν) (Set.Icc (-1) 1) := by
  have h : ContinuousOn (fun t : ℝ => ∫ k : ℕ, t ^ k ∂ν) (Set.Icc (-1) 1) := by
    refine continuousOn_of_dominated (bound := fun _ => 1) (fun _ _ => by fun_prop)
      (fun t ht => Eventually.of_forall fun k => ?_) (integrable_const 1)
      (Eventually.of_forall fun k => (continuous_pow k).continuousOn)
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg t) (abs_le.mpr ht)
  have hpgf : pgf id ν = fun t : ℝ => ∫ k : ℕ, t ^ k ∂ν := funext fun t => pgf_def id ν t
  rwa [hpgf]

/-- The probability-generating function of a finite measure on `ℕ` is nondecreasing on
`[0, 1]`. -/
theorem monotoneOn_pgf (ν : Measure ℕ) [IsFiniteMeasure ν] :
    MonotoneOn (pgf id ν) (Set.Icc 0 1) := by
  intro s hs t ht hst
  refine hasSum_le (fun k => ?_) (hasSum_pgf ν (abs_le_one_of_mem_Icc hs))
    (hasSum_pgf ν (abs_le_one_of_mem_Icc ht))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1 hst k) measureReal_nonneg

/-- The probability-generating function of a probability measure on `ℕ` maps `[0, 1]` into
itself. -/
theorem mapsTo_pgf_Icc (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    Set.MapsTo (pgf id ν) (Set.Icc 0 1) (Set.Icc 0 1) := fun s hs => by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨?_, ?_⟩
  · calc (0 : ℝ) ≤ pgf id ν 0 := by rw [pgf_zero]; exact measureReal_nonneg
      _ ≤ pgf id ν s := monotoneOn_pgf ν h0 hs hs.1
  · calc pgf id ν s ≤ pgf id ν 1 := monotoneOn_pgf ν hs h1 hs.2
      _ = 1 := by simp

/-- The probability-generating function of a finite measure on `ℕ` is convex on `[0, 1]`. -/
theorem convexOn_pgf (ν : Measure ℕ) [IsFiniteMeasure ν] :
    ConvexOn ℝ (Set.Icc 0 1) (pgf id ν) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy := convex_Icc (0 : ℝ) 1 hx hy ha hb hab
  refine hasSum_le (fun k => ?_) (hasSum_pgf ν (abs_le_one_of_mem_Icc hxy))
    (((hasSum_pgf ν (abs_le_one_of_mem_Icc hx)).mul_left a).add
      ((hasSum_pgf ν (abs_le_one_of_mem_Icc hy)).mul_left b))
  simpa only [smul_eq_mul] using measureReal_mul_pow_convex_le ν k hx hy ha hb hab

/-- The probability-generating function of a finite measure on `ℕ` that charges some `k ≥ 2` is
strictly convex on `[0, 1]`. See `strictConvexOn_pgf_of_add_lt_one` for the form
`ν {0} + ν {1} < 1` of the hypothesis for a probability measure. -/
theorem strictConvexOn_pgf (ν : Measure ℕ) [IsFiniteMeasure ν] {k : ℕ} (hk : 2 ≤ k)
    (hνk : ν {k} ≠ 0) : StrictConvexOn ℝ (Set.Icc 0 1) (pgf id ν) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hmem := convex_Icc (0 : ℝ) 1 hx hy ha.le hb.le hab
  have hpos : 0 < ν.real {k} := ENNReal.toReal_pos hνk (measure_ne_top ν _)
  have hstrict : ν.real {k} * (a * x + b * y) ^ k <
      a * (ν.real {k} * x ^ k) + b * (ν.real {k} * y ^ k) := by
    have := (strictConvexOn_pow hk).2 (Set.mem_Ici.mpr hx.1) (Set.mem_Ici.mpr hy.1) hxy ha hb
      hab
    simp only [smul_eq_mul] at this
    calc ν.real {k} * (a * x + b * y) ^ k < ν.real {k} * (a * x ^ k + b * y ^ k) :=
          mul_lt_mul_of_pos_left this hpos
      _ = a * (ν.real {k} * x ^ k) + b * (ν.real {k} * y ^ k) := by ring
  simp only [smul_eq_mul]
  exact hasSum_lt (fun n => measureReal_mul_pow_convex_le ν n hx hy ha.le hb.le hab) hstrict
    (hasSum_pgf ν (abs_le_one_of_mem_Icc hmem))
    (((hasSum_pgf ν (abs_le_one_of_mem_Icc hx)).mul_left a).add
      ((hasSum_pgf ν (abs_le_one_of_mem_Icc hy)).mul_left b))

/-- The probability-generating function of a probability measure on `ℕ` with
`ν {0} + ν {1} < 1` is strictly convex on `[0, 1]`. -/
theorem strictConvexOn_pgf_of_add_lt_one (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (h : ν {0} + ν {1} < 1) : StrictConvexOn ℝ (Set.Icc 0 1) (pgf id ν) := by
  obtain ⟨k, hk, hνk⟩ : ∃ k, 2 ≤ k ∧ ν {k} ≠ 0 := by
    by_contra! h0
    have htail : ∑' n, ν {n + 2} = 0 := tsum_eq_zero_iff.2 fun n => h0 _ (by omega)
    have huniv : ν Set.univ = ∑' n, ν {n} := by
      simpa using lintegral_countable' (μ := ν) (fun _ => (1 : ℝ≥0∞))
    rw [measure_univ, tsum_eq_zero_add' CompleteLattice.summable,
      tsum_eq_zero_add' CompleteLattice.summable] at huniv
    simp only [zero_add, htail, add_zero] at huniv
    exact h.ne huniv.symm
  exact strictConvexOn_pgf ν hk hνk

/-- The probability-generating function of a probability measure on `ℕ` carried by `{0, 1}`,
that is with `ν {0} + ν {1} = 1`, is the affine function `t ↦ ν.real {0} + ν.real {1} * t`. This
is the case left out by `strictConvexOn_pgf_of_add_lt_one`. -/
theorem pgf_eq_of_add_eq_one (ν : Measure ℕ) [IsProbabilityMeasure ν] (h : ν {0} + ν {1} = 1)
    (t : ℝ) : pgf id ν t = ν.real {0} + ν.real {1} * t := by
  have hpair : ν {0, 1} = 1 := by
    rw [Set.insert_eq, measure_union (by simp) (measurableSet_singleton 1), h]
  have hcompl : ν {0, 1}ᶜ = 0 := (prob_compl_eq_zero_iff (by measurability)).2 hpair
  have hae : ∀ᵐ k ∂ν, k = 0 ∨ k = 1 := measure_eq_zero_iff_ae_notMem.1 hcompl |>.mono
    fun k hk => by simpa [or_iff_not_imp_left] using hk
  have hint : Integrable (fun n : ℕ => t ^ n) ν := by
    refine Integrable.mono' (integrable_const (max 1 |t|)) (by fun_prop) ?_
    filter_upwards [hae] with k hk
    rcases hk with rfl | rfl <;> simp
  have hzero : ∀ n ∉ Finset.range 2, ν.real {n} * t ^ n = 0 := fun n hn => by
    have hn : ({n} : Set ℕ) ⊆ {0, 1}ᶜ := by
      simp only [Finset.mem_range, not_lt] at hn
      simp only [Set.singleton_subset_iff, Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      omega
    rw [measureReal_def, measure_mono_null hn hcompl, ENNReal.toReal_zero, zero_mul]
  rw [(hasSum_pgf_of_integrable ν hint).unique (hasSum_sum_of_ne_finset_zero hzero)]
  simp [Finset.sum_range_succ]

/-- On the open unit interval, the derivative of the probability-generating function of a finite
measure on `ℕ` is the sum of the termwise derivatives `(n + 1) ν {n + 1} t ^ n`. -/
theorem hasSum_deriv_pgf (ν : Measure ℕ) [IsFiniteMeasure ν] {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ => (n + 1) * ν.real {n + 1} * t ^ n) (deriv (pgf id ν) t) := by
  refine (hasFPowerSeriesOnBall_pgf ν).deriv_ofScalars.hasSum_ofScalars ?_
  rw [← ofReal_norm, ENNReal.ofReal_lt_one, Real.norm_eq_abs]
  exact ht

/-- The derivative of the probability-generating function of a finite measure on `ℕ` is
nondecreasing on `[0, 1)`. -/
theorem monotoneOn_deriv_pgf (ν : Measure ℕ) [IsFiniteMeasure ν] :
    MonotoneOn (deriv (pgf id ν)) (Set.Ico 0 1) := by
  intro s hs t ht hst
  refine hasSum_le (fun n => ?_) (hasSum_deriv_pgf ν (abs_lt_one_of_mem_Ico hs))
    (hasSum_deriv_pgf ν (abs_lt_one_of_mem_Ico ht))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1 hst n)
    (mul_nonneg (by positivity) measureReal_nonneg)

/-- As the argument increases to `1`, the derivative of the probability-generating function of a
finite measure on `ℕ` tends to the mean `∫⁻ k, k ∂ν`, taken in `[0, ∞]`; in particular it tends
to `∞` when the mean is infinite. -/
theorem tendsto_ofReal_deriv_pgf_nhdsLT_one (ν : Measure ℕ) [IsFiniteMeasure ν] :
    Tendsto (fun t => ENNReal.ofReal (deriv (pgf id ν) t)) (𝓝[<] 1)
      (𝓝 (∫⁻ k, (k : ℝ≥0∞) ∂ν)) := by
  -- the mean is the sum of the masses `c n = (n + 1) ν {n + 1}`, and the derivative at `t` is
  -- the sum of `c n * t ^ n`; the finite partial sums converge, and every term increases to `c n`
  let c : ℕ → ℝ≥0∞ := fun n => ((n : ℝ≥0∞) + 1) * ν {n + 1}
  have hmean : ∫⁻ k, (k : ℝ≥0∞) ∂ν = ∑' n, c n := by
    rw [lintegral_countable', tsum_eq_zero_add' CompleteLattice.summable]
    simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one, c]
  have hderiv {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      ENNReal.ofReal (deriv (pgf id ν) t) = ∑' n, c n * ENNReal.ofReal (t ^ n) := by
    have hsum := hasSum_deriv_pgf ν (abs_lt_one_of_mem_Ico ht)
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by
      have := ht.1; positivity) hsum.summable]
    refine tsum_congr fun n => ?_
    rw [ENNReal.ofReal_mul (by have := ht.1; positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_measureReal (measure_ne_top ν _), ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Set.Ico (0 : ℝ) 1 :=
    Ico_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)
  rw [hmean]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rw [tsum_eq_iSup_sum, lt_iSup_iff] at ha
    obtain ⟨s, hs⟩ := ha
    have hlim : Tendsto (fun t : ℝ => ∑ n ∈ s, c n * ENNReal.ofReal (t ^ n)) (𝓝[<] 1)
        (𝓝 (∑ n ∈ s, c n)) := by
      refine tendsto_finsetSum s fun n _ => ?_
      have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n)) (𝓝[<] 1) (𝓝 1) := by
        have : Tendsto (fun t : ℝ => t ^ n) (𝓝[<] 1) (𝓝 1) := by
          simpa using ((continuous_pow n).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
        simpa using ENNReal.tendsto_ofReal this
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inl one_ne_zero)
    filter_upwards [hlim.eventually (lt_mem_nhds hs), hev] with t ht ht'
    rw [hderiv ht']
    exact ht.trans_le (sum_le_tsum s)
  · filter_upwards [hev] with t ht
    rw [hderiv ht]
    refine lt_of_le_of_lt (tsum_le_tsum fun n => ?_) hb
    calc c n * ENNReal.ofReal (t ^ n) ≤ c n * 1 := by
          gcongr
          exact ENNReal.ofReal_le_one.mpr (pow_le_one₀ ht.1 ht.2.le)
      _ = c n := mul_one _

/-- On `[0, 1)` the derivative of the probability-generating function of a finite measure on `ℕ`
is at most the mean `∫⁻ k, k ∂ν`, taken in `[0, ∞]`. -/
theorem ofReal_deriv_pgf_le (ν : Measure ℕ) [IsFiniteMeasure ν] {t : ℝ}
    (ht : t ∈ Set.Ico 0 1) : ENNReal.ofReal (deriv (pgf id ν) t) ≤ ∫⁻ k, (k : ℝ≥0∞) ∂ν := by
  refine ge_of_tendsto (tendsto_ofReal_deriv_pgf_nhdsLT_one ν) ?_
  filter_upwards [Ioo_mem_nhdsLT ht.2] with u hu
  exact ENNReal.ofReal_le_ofReal
    (monotoneOn_deriv_pgf ν ht ⟨ht.1.trans hu.1.le, hu.2⟩ hu.1.le)

end Shape

/-! ### Fixed points of the generating function on `[0, 1]` -/

section FixedPoint

open Filter Set

variable (ν : Measure ℕ) [IsProbabilityMeasure ν]

/-- The iterates `f^[n] 0` of the generating function of a probability measure on `ℕ` lie in
`[0, 1]`. -/
private theorem iterate_pgf_zero_mem_Icc (n : ℕ) : (pgf id ν)^[n] 0 ∈ Icc (0 : ℝ) 1 :=
  (mapsTo_pgf_Icc ν).iterate n ⟨le_rfl, zero_le_one⟩

/-- The iterates `f^[n] 0` of the generating function `f` of a probability measure on `ℕ` form a
nondecreasing sequence. -/
theorem monotone_iterate_pgf_zero : Monotone fun n => (pgf id ν)^[n] 0 := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero => exact (iterate_pgf_zero_mem_Icc ν 1).1
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply' _ (n + 1)]
    exact monotoneOn_pgf ν (iterate_pgf_zero_mem_Icc ν n) (iterate_pgf_zero_mem_Icc ν (n + 1)) ih

/-- The iterates `f^[n] 0` of the generating function `f` of a probability measure on `ℕ` lie
below every nonnegative fixed point of `f`. -/
theorem iterate_pgf_zero_le {s : ℝ} (hs : 0 ≤ s) (hfs : pgf id ν s = s) (n : ℕ) :
    (pgf id ν)^[n] 0 ≤ s := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rcases le_or_gt s 1 with hs1 | hs1
    · rw [Function.iterate_succ_apply', ← hfs]
      exact monotoneOn_pgf ν (iterate_pgf_zero_mem_Icc ν n) ⟨hs, hs1⟩ ih
    · exact (iterate_pgf_zero_mem_Icc ν (n + 1)).2.trans hs1.le

/-- If the iterates `f^[n] 0` of the generating function `f` of a probability measure on `ℕ`
converge to `q`, then `q` is the least fixed point of `f` in `[0, 1]`. -/
theorem isLeast_of_tendsto_iterate_pgf_zero {q : ℝ}
    (hq : Tendsto (fun n => (pgf id ν)^[n] 0) atTop (𝓝 q)) :
    IsLeast {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ pgf id ν s = s} q := by
  have hmem : q ∈ Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hq (Eventually.of_forall (iterate_pgf_zero_mem_Icc ν))
  have hcont : ContinuousWithinAt (pgf id ν) (Icc 0 1) q :=
    ((continuousOn_pgf ν).mono (Icc_subset_Icc (by norm_num) le_rfl)) q hmem
  have hlim : Tendsto (fun n => pgf id ν ((pgf id ν)^[n] 0)) atTop (𝓝 (pgf id ν q)) :=
    hcont.tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hq, Eventually.of_forall (iterate_pgf_zero_mem_Icc ν)⟩)
  have hshift : Tendsto (fun n => pgf id ν ((pgf id ν)^[n] 0)) atTop (𝓝 q) := by
    simpa only [Function.iterate_succ_apply'] using (tendsto_add_atTop_iff_nat 1).2 hq
  refine ⟨⟨hmem.1, hmem.2, tendsto_nhds_unique hlim hshift⟩, fun s hs => ?_⟩
  exact le_of_tendsto' hq (iterate_pgf_zero_le ν hs.1 hs.2.2)

/-- The iterates `f^[n] 0` of the generating function `f` of a probability measure on `ℕ`
converge to their supremum. -/
theorem tendsto_iterate_pgf_zero :
    Tendsto (fun n => (pgf id ν)^[n] 0) atTop (𝓝 (⨆ n, (pgf id ν)^[n] 0)) :=
  tendsto_atTop_ciSup (monotone_iterate_pgf_zero ν)
    ⟨1, forall_mem_range.2 fun n => (iterate_pgf_zero_mem_Icc ν n).2⟩

/-- The generating function `f` of a probability measure on `ℕ` has a least fixed point in
`[0, 1]`, the supremum of the iterates `f^[n] 0`. -/
theorem isLeast_iSup_iterate_pgf_zero :
    IsLeast {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ pgf id ν s = s} (⨆ n, (pgf id ν)^[n] 0) :=
  isLeast_of_tendsto_iterate_pgf_zero ν (tendsto_iterate_pgf_zero ν)

/-- If `ν {0} + ν {1} < 1`, the generating function `f` of a probability measure on `ℕ` lies
strictly below the diagonal between two fixed points in `[0, 1]`. -/
theorem pgf_lt_self_of_add_lt_one (h : ν {0} + ν {1} < 1) {a b t : ℝ} (ha : 0 ≤ a)
    (hb : b ≤ 1) (hfa : pgf id ν a = a) (hfb : pgf id ν b = b) (hat : a < t) (htb : t < b) :
    pgf id ν t < t := by
  have hab : 0 < b - a := by linarith
  have hl : 0 < (b - t) / (b - a) := div_pos (by linarith) hab
  have hr : 0 < (t - a) / (b - a) := div_pos (by linarith) hab
  have hconv := (strictConvexOn_pgf_of_add_lt_one ν h).2 (⟨ha, by linarith⟩ : a ∈ Icc (0 : ℝ) 1)
    (⟨by linarith, hb⟩ : b ∈ Icc (0 : ℝ) 1) (sub_pos.1 hab).ne hl hr (by field_simp; ring)
  have hcomb : (b - t) / (b - a) * a + (t - a) / (b - a) * b = t := by
    field_simp; ring
  simpa only [smul_eq_mul, hfa, hfb, hcomb] using hconv

/-- If `ν {0} + ν {1} = 1` and `ν {1} ≠ 1`, the only fixed point of the generating function of a
probability measure on `ℕ` is `1`. -/
theorem eq_one_of_pgf_eq_self_of_add_eq_one (h : ν {0} + ν {1} = 1) (h1 : ν {1} ≠ 1)
    {s : ℝ} (hfs : pgf id ν s = s) : s = 1 := by
  have hreal : ν.real {0} + ν.real {1} = 1 := by
    rw [measureReal_def, measureReal_def, ← ENNReal.toReal_add (measure_ne_top ν _)
      (measure_ne_top ν _), h, ENNReal.toReal_one]
  have h1' : 1 - ν.real {1} ≠ 0 :=
    sub_ne_zero.2 fun h' => h1 ((ENNReal.toReal_eq_one_iff _).1 h'.symm)
  rw [pgf_eq_of_add_eq_one ν h] at hfs
  have : (1 - ν.real {1}) * (1 - s) = 0 := by linear_combination hfs - hreal
  linarith [(mul_eq_zero.1 this).resolve_left h1']

/-- Unless every individual has exactly one child, the fixed points in `[0, 1]` of the generating
function of a probability measure on `ℕ` are its least fixed point `q` there and `1`. -/
theorem setOf_pgf_eq_self_eq_pair (h1 : ν {1} ≠ 1) {q : ℝ}
    (hq : IsLeast {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ pgf id ν s = s} q) :
    {s : ℝ | 0 ≤ s ∧ s ≤ 1 ∧ pgf id ν s = s} = {q, 1} := by
  ext s
  refine ⟨fun hs => ?_, ?_⟩
  · rcases hs.2.1.lt_or_eq with hs1 | rfl
    · left
      rcases (ν.measure_singleton_add_measure_singleton_le zero_ne_one).lt_or_eq with h | h
      · refine (hq.2 hs).antisymm' (not_lt.1 fun hqs => ?_)
        exact (pgf_lt_self_of_add_lt_one ν h hq.1.1 le_rfl hq.1.2.2 (by simp) hqs hs1).ne
          hs.2.2
      · exact absurd (eq_one_of_pgf_eq_self_of_add_eq_one ν h h1 hs.2.2) hs1.ne
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact hq.1
    · exact ⟨zero_le_one, le_rfl, by simp⟩

end FixedPoint

end Probability

end TauCeti
