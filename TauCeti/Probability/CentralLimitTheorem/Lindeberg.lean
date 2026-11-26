/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import TauCeti.Analysis.Normed.Ring.ProdSubProd
import TauCeti.Analysis.SpecialFunctions.Exp.ImaginaryTaylor
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound
import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation

/-!
# The Lindeberg–Feller central limit theorem

Let `X n i`, for `n : ℕ` and `i : ι n` with `ι n` finite, be real random variables, the `n`th row
living on a probability space `(Ω n, P n)`, such that

* for each `n`, the row `X n` is independent;
* each `X n i` is centred and square integrable;
* the row variances `∑ i, Var[X n i; P n]` converge to `v : ℝ≥0`;
* the **Lindeberg condition** holds: for every `ε > 0`,
  `∑ i, E[X n i ^ 2; ε ≤ |X n i|] → 0` as `n → ∞`.

Then the row sums `∑ i, X n i` converge in distribution to `gaussianReal 0 v`. Neither
boundedness nor identical distribution is assumed, `v = 0` is allowed, and different rows need not
live on a common space, which is what makes the theorem apply to triangular arrays such as sums of
independent indicators with varying success probabilities or scalar projections of Euclidean
triangular arrays in singular directions.

The main consequence proved here is the central limit theorem for bounded independent summands
whose variance tends to infinity: if every centred summand `X n i - E[X n i]` is bounded by a
fixed constant `C` and `∑ i, Var[X n i] → ∞`, then the centred row sum divided by its standard
deviation converges in distribution to the standard Gaussian law. Sums of independent Bernoulli
variables with diverging variance are the basic example.

## Main results

* `MeasureTheory.MemLp.norm_charFun_sub_one_sub_le`: the truncation estimate
  `‖φ_X t - (1 - t² E[X²] / 2)‖ ≤ |t|³ ε E[X²] / 6 + t² E[X²; ε ≤ |X|]` for a centred `X ∈ L²`.
* `TauCeti.Probability.norm_prod_charFun_sub_exp_le`: the product of the characteristic
  functions of one row with variance sum `V` is close to `exp (-t² V / 2)`, with an explicit error.
* `ProbabilityTheory.HasLaw.tendstoInDistribution_sum_of_lindeberg`: the Lindeberg–Feller theorem
  for any limiting variance `v : ℝ≥0` (sufficiency direction).
* `ProbabilityTheory.HasLaw.tendstoInDistribution_sum_sub_div_sqrt_of_abs_sub_le`: the central
  limit theorem for uniformly bounded independent summands with diverging variance.

## Implementation notes

The proof goes through characteristic functions and Lévy's continuity theorem, as in Mathlib's
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`. Writing `σᵢ² = E[X n i ^ 2]` and
`Vₙ = ∑ i, σᵢ²`, each factor `φ_{X n i} t` is compared with `exp (-t² σᵢ² / 2)` rather than with
`1 - t² σᵢ² / 2`: both have norm at most `1`, and the product of the Gaussian factors is
`exp (-t² Vₙ / 2)`, which converges to `exp (-t² v / 2)` as `Vₙ → v`. The error
`(t² σᵢ² / 2) ^ 2 / 2` from `exp (-u) ≈ 1 - u` is summed using
`σᵢ² ≤ ε² + E[X n i ^ 2; ε ≤ |X n i|]`, so the intermediate statement `maxᵢ σᵢ² → 0` is never
needed separately.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995, Section 27, Theorem 27.2.
* J. W. Lindeberg, Eine neue Herleitung des Exponentialgesetzes in der
  Wahrscheinlichkeitsrechnung, *Mathematische Zeitschrift* 15 (1922), 211–225.
* W. Feller, Über den zentralen Grenzwertsatz der Wahrscheinlichkeitsrechnung,
  *Mathematische Zeitschrift* 40 (1935), 521–559.

## Tags

central limit theorem, Lindeberg condition, triangular array
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ}

/-- The characteristic function of a centred random variable `X` with finite variance agrees
with `1 - t² E[X²] / 2` up to an error controlled by `ε` and the truncated second moment
`E[X²; ε ≤ |X|]`. -/
theorem MemLp.norm_charFun_sub_one_sub_le (hX : MemLp X 2 P) (h0 : P[X] = 0) (t : ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    ‖charFun (P.map X) t - (1 - t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2)‖ ≤
      |t| ^ 3 * ε / 6 * ∫ ω, X ω ^ 2 ∂P +
        t ^ 2 * ∫ ω, ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω ∂P := by
  have hm : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
  have hint1 : Integrable X P := hX.integrable one_le_two
  have hint2 : Integrable (fun ω ↦ X ω ^ 2) P := hX.integrable_sq
  have hind := hX.integrable_indicator_sq ε
  have hexp : Integrable (fun ω ↦ Complex.exp (↑(t * X ω) * Complex.I)) P := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun ω ↦ ?_)
    exact (Complex.norm_exp_ofReal_mul_I _).le
  have ha : Integrable (fun ω ↦ 1 - (t * X ω) ^ 2 / 2) P :=
    ((integrable_const 1).sub ((hint2.const_mul (t ^ 2)).div_const 2)).congr
      (ae_of_all _ fun ω ↦ by simp [mul_pow])
  have hb : Integrable (fun ω ↦ t * X ω) P := hint1.const_mul t
  have hF : Integrable
      (fun ω ↦ ((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ) + ↑(t * X ω) * Complex.I) P :=
    ha.ofReal.add (hb.ofReal.mul_const _)
  -- the characteristic function and the quadratic polynomial as expectations
  have hφ : charFun (P.map X) t = ∫ ω, Complex.exp (↑(t * X ω) * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map hm (by fun_prop)]
    simp
  have hE : ((1 - t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 : ℝ) : ℂ) =
      ∫ ω, (((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ) + ↑(t * X ω) * Complex.I) ∂P := by
    rw [integral_add ha.ofReal (hb.ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal, integral_const_mul, h0,
      integral_sub (integrable_const _) ((hint2.const_mul (t ^ 2)).div_const 2 |>.congr
        (ae_of_all _ fun ω ↦ by simp [mul_pow]))]
    simp [integral_div, mul_pow, integral_const_mul]
  have hE' : (1 - (t : ℂ) ^ 2 * ((∫ ω, X ω ^ 2 ∂P : ℝ) : ℂ) / 2) =
      ∫ ω, (((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ) + ↑(t * X ω) * Complex.I) ∂P := by
    rw [← hE]
    push_cast
    ring
  have hbd : Integrable (fun ω ↦ |t| ^ 3 * ε / 6 * X ω ^ 2 +
      t ^ 2 * ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω) P :=
    (hint2.const_mul _).add (hind.const_mul _)
  rw [hφ, hE', ← integral_sub hexp hF, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hint2.const_mul _) (hind.const_mul _)]
  refine norm_integral_le_of_norm_le hbd (ae_of_all _ fun ω ↦ ?_)
  -- pointwise: the cubic bound where `|X| < ε`, the quadratic bound where `ε ≤ |X|`
  have hrw : Complex.exp (↑(t * X ω) * Complex.I) -
      (((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ) + ↑(t * X ω) * Complex.I) =
      Complex.exp (↑(t * X ω) * Complex.I) -
        (1 + ↑(t * X ω) * Complex.I - ↑(t * X ω) ^ 2 / 2) := by
    push_cast
    ring
  rw [hrw]
  have h3 : 0 ≤ |t| ^ 3 * ε / 6 * X ω ^ 2 := by positivity
  by_cases hω : ε ≤ |X ω|
  · rw [Set.indicator_of_mem (s := {ω | ε ≤ |X ω|}) hω]
    have := TauCeti.norm_exp_ofReal_mul_I_sub_le_sq (t * X ω)
    rw [mul_pow] at this
    linarith
  · rw [Set.indicator_of_notMem (s := {ω | ε ≤ |X ω|}) hω, mul_zero, add_zero]
    refine (TauCeti.norm_exp_ofReal_mul_I_sub_le_cube (t * X ω)).trans ?_
    have hX3 : |X ω| ^ 3 ≤ ε * X ω ^ 2 := by
      rw [← sq_abs (X ω), pow_succ, mul_comm]
      gcongr
      exact (not_le.mp hω).le
    rw [abs_mul, mul_pow]
    have ht3 : 0 ≤ |t| ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hX3 ht3]

end MeasureTheory

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Nonnegative-threshold case of `norm_prod_charFun_sub_exp_le`. -/
private theorem norm_prod_charFun_sub_exp_le_of_nonneg {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ}
    (hL2 : ∀ i, MemLp (Y i) 2 P) (h0 : ∀ i, P[Y i] = 0) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖∏ i, charFun (P.map (Y i)) t -
        (Real.exp (-(t ^ 2 * (∑ i, ∫ ω, Y i ω ^ 2 ∂P) / 2)) : ℂ)‖ ≤
      (|t| ^ 3 * ε / 6 + t ^ 4 / 8 * ε ^ 2) * (∑ i, ∫ ω, Y i ω ^ 2 ∂P) +
        (t ^ 2 + t ^ 4 / 8 * (∑ i, ∫ ω, Y i ω ^ 2 ∂P)) *
          (∑ i, ∫ ω, ({ω | ε ≤ |Y i ω|}.indicator fun ω ↦ Y i ω ^ 2) ω ∂P) := by
  set σ : ι → ℝ := fun i ↦ ∫ ω, Y i ω ^ 2 ∂P
  set V : ℝ := ∑ i, σ i
  set Li : ι → ℝ := fun i ↦ ∫ ω, ({ω | ε ≤ |Y i ω|}.indicator fun ω ↦ Y i ω ^ 2) ω ∂P
  set L : ℝ := ∑ i, Li i
  have hσ0 (i : ι) : 0 ≤ σ i := integral_nonneg fun _ ↦ sq_nonneg _
  have hLi0 (i : ι) : 0 ≤ Li i :=
    integral_nonneg fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
  have hσL (i : ι) : σ i ≤ ε ^ 2 + L :=
    ((hL2 i).integral_sq_le_sq_add_integral_indicator ε).trans
      (by linarith [Finset.single_le_sum (fun j _ ↦ hLi0 j) (Finset.mem_univ i)])
  have hprod : (Real.exp (-(t ^ 2 * V / 2)) : ℂ) =
      ∏ i, ((Real.exp (-(t ^ 2 * σ i / 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hprod]
  refine (norm_prod_sub_prod_le_sum_norm_sub _ (fun _ _ ↦ norm_charFun_le_one t)
    (fun i _ ↦ ?_)).trans ?_
  · rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    nlinarith [hσ0 i, sq_nonneg t]
  have hterm (i : ι) : ‖charFun (P.map (Y i)) t - ((Real.exp (-(t ^ 2 * σ i / 2)) : ℝ) : ℂ)‖ ≤
      |t| ^ 3 * ε / 6 * σ i + t ^ 2 * Li i + t ^ 4 / 8 * (ε ^ 2 + L) * σ i := by
    have h1 := (hL2 i).norm_charFun_sub_one_sub_le (h0 i) t hε
    have hlo := Real.add_one_le_exp (-(t ^ 2 * σ i / 2))
    have hhi := Real.exp_le_one_add_add_sq_div_two_of_nonpos
      (x := -(t ^ 2 * σ i / 2)) (by nlinarith [hσ0 i, sq_nonneg t])
    have h3 : ‖((1 - t ^ 2 * σ i / 2 : ℝ) : ℂ) - ((Real.exp (-(t ^ 2 * σ i / 2)) : ℝ) : ℂ)‖ ≤
        (t ^ 2 * σ i / 2) ^ 2 / 2 := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
        abs_of_nonneg (by linarith)]
      nlinarith
    have h4 : (t ^ 2 * σ i / 2) ^ 2 / 2 ≤ t ^ 4 / 8 * (ε ^ 2 + L) * σ i := by
      rw [(by ring : (t ^ 2 * σ i / 2) ^ 2 / 2 = t ^ 4 / 8 * σ i * σ i)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hσL i) (by positivity)) (hσ0 i)
    have htri : ‖charFun (P.map (Y i)) t - ((Real.exp (-(t ^ 2 * σ i / 2)) : ℝ) : ℂ)‖ ≤
        ‖charFun (P.map (Y i)) t - (1 - t ^ 2 * σ i / 2)‖ +
          ‖((1 - t ^ 2 * σ i / 2 : ℝ) : ℂ) - ((Real.exp (-(t ^ 2 * σ i / 2)) : ℝ) : ℂ)‖ := by
      have hcast : ((1 - t ^ 2 * σ i / 2 : ℝ) : ℂ) = 1 - (t : ℂ) ^ 2 * (σ i : ℂ) / 2 := by
        simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_mul,
          Complex.ofReal_pow, Complex.ofReal_ofNat]
      rw [← hcast]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    linarith
  refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- Row estimate for the Lindeberg–Feller theorem: for a finite family of centred
square-integrable random variables with variance sum `V = ∑ i, E[Y i ²]`, the product of their
characteristic functions is within
`(|t|³ |ε| / 6 + t⁴ ε² / 8) V + (t² + t⁴ V / 8) Lε` of `exp (-t² V / 2)`, where
`Lε = ∑ i, E[Y i ²; ε ≤ |Y i|]` is the Lindeberg sum. -/
theorem norm_prod_charFun_sub_exp_le {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ}
    (hL2 : ∀ i, MemLp (Y i) 2 P) (h0 : ∀ i, P[Y i] = 0) (t ε : ℝ) :
    ‖∏ i, charFun (P.map (Y i)) t -
        (Real.exp (-(t ^ 2 * (∑ i, ∫ ω, Y i ω ^ 2 ∂P) / 2)) : ℂ)‖ ≤
      (|t| ^ 3 * |ε| / 6 + t ^ 4 / 8 * ε ^ 2) * (∑ i, ∫ ω, Y i ω ^ 2 ∂P) +
        (t ^ 2 + t ^ 4 / 8 * (∑ i, ∫ ω, Y i ω ^ 2 ∂P)) *
          (∑ i, ∫ ω, ({ω | ε ≤ |Y i ω|}.indicator fun ω ↦ Y i ω ^ 2) ω ∂P) := by
  rcases le_or_gt 0 ε with hε | hε
  · simpa only [abs_of_nonneg hε] using norm_prod_charFun_sub_exp_le_of_nonneg hL2 h0 t hε
  · have hset (i : ι) : {ω | ε ≤ |Y i ω|} = {ω | 0 ≤ |Y i ω|} := by
      ext ω; simp [hε.le.trans (abs_nonneg _)]
    have h0_bound := norm_prod_charFun_sub_exp_le_of_nonneg hL2 h0 t (le_refl (0 : ℝ))
    simp_rw [← hset] at h0_bound
    have : 0 ≤ ∑ i, ∫ ω, Y i ω ^ 2 ∂P :=
      Finset.sum_nonneg fun i _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
    have hextra : 0 ≤ (|t| ^ 3 * |ε| / 6 + t ^ 4 / 8 * ε ^ 2) * (∑ i, ∫ ω, Y i ω ^ 2 ∂P) := by
      positivity
    linarith

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)} {P : (n : ℕ) → Measure (Ω n)}
  [∀ n, IsProbabilityMeasure (P n)]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Y : Ω' → ℝ}

/-- Under boundedness of row variance sums `V n → v` and the Lindeberg condition, the difference
between the row characteristic-function product and `exp (-t² V n / 2)` tends to `0`. -/
private theorem tendsto_prod_charFun_sub_exp_zero {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {X : (n : ℕ) → ι n → Ω n → ℝ} {v : ℝ≥0}
    (hL2 : ∀ n i, MemLp (X n i) 2 (P n))
    (h0 : ∀ n i, (P n)[X n i] = 0)
    (hV : Tendsto (fun n ↦ ∑ i, ∫ ω, X n i ω ^ 2 ∂(P n)) atTop (𝓝 (v : ℝ)))
    (hlind : ∀ ε > 0, Tendsto
      (fun n ↦ ∑ i, (P n)[{ω | ε ≤ |X n i ω|}.indicator (fun ω ↦ X n i ω ^ 2)]) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun n ↦ ∏ i, charFun ((P n).map (X n i)) t -
      (Real.exp (-(t ^ 2 * (∑ i, ∫ ω, X n i ω ^ 2 ∂(P n)) / 2)) : ℂ)) atTop (𝓝 0) := by
  set V : ℕ → ℝ := fun n ↦ ∑ i, ∫ ω, X n i ω ^ 2 ∂(P n)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set M : ℝ := (v : ℝ) + 1
  set C : ℝ := (|t| ^ 3 + t ^ 4) * M + t ^ 2 + t ^ 4 * M
  have hC0 : 0 ≤ C := by positivity
  refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
  set ε := min 1 (δ / (2 * (C + 1)))
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hCε : C * ε < δ / 2 := by
    calc C * ε ≤ C * (δ / (2 * (C + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC0
      _ < δ / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]; nlinarith
  have hLC := (hlind ε hε0).const_mul C
  rw [mul_zero] at hLC
  filter_upwards [hLC (Iio_mem_nhds (half_pos hδ)), hV (Iio_mem_nhds (lt_add_one (v : ℝ)))]
    with n hn hVn
  have hn' : C * ∑ i, (P n)[{ω | ε ≤ |X n i ω|}.indicator (fun ω ↦ X n i ω ^ 2)] < δ / 2 := hn
  have hVn' : V n < M := hVn
  have hV0 : 0 ≤ V n := Finset.sum_nonneg fun i _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  have hL0 : 0 ≤ ∑ i, ∫ ω, ({ω | ε ≤ |X n i ω|}.indicator fun ω ↦ X n i ω ^ 2) ω ∂(P n) :=
    Finset.sum_nonneg fun i _ ↦
      integral_nonneg fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
  have hε2 : ε ^ 2 ≤ ε := by nlinarith [min_le_left 1 (δ / (2 * (C + 1)))]
  rw [sub_zero, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hrow := norm_prod_charFun_sub_exp_le (hL2 n) (h0 n) t ε
  rw [abs_of_nonneg hε0.le] at hrow
  refine hrow.trans_lt ?_
  have h1 : (|t| ^ 3 * ε / 6 + t ^ 4 / 8 * ε ^ 2) * V n ≤ (|t| ^ 3 + t ^ 4) * M * ε := by
    have : |t| ^ 3 * ε / 6 + t ^ 4 / 8 * ε ^ 2 ≤ (|t| ^ 3 + t ^ 4) * ε := by
      nlinarith [mul_le_mul_of_nonneg_left hε2 (by positivity : 0 ≤ t ^ 4),
        (by positivity : 0 ≤ |t| ^ 3 * ε), (by positivity : 0 ≤ t ^ 4 * ε)]
    nlinarith [mul_le_mul this hVn'.le hV0 (by positivity)]
  have h2 : (t ^ 2 + t ^ 4 / 8 * V n) *
      (∑ i, ∫ ω, ({ω | ε ≤ |X n i ω|}.indicator fun ω ↦ X n i ω ^ 2) ω ∂(P n)) ≤
      (t ^ 2 + t ^ 4 * M) *
        (∑ i, ∫ ω, ({ω | ε ≤ |X n i ω|}.indicator fun ω ↦ X n i ω ^ 2) ω ∂(P n)) := by
    refine mul_le_mul_of_nonneg_right ?_ hL0
    nlinarith [mul_le_mul_of_nonneg_left hVn'.le (by positivity : 0 ≤ t ^ 4),
      (by positivity : 0 ≤ t ^ 4 * M)]
  nlinarith [mul_nonneg (by positivity : 0 ≤ (|t| ^ 3 + t ^ 4) * M) hL0,
    mul_nonneg (by positivity : 0 ≤ t ^ 2 + t ^ 4 * M) hε0.le]

/-- **Lindeberg–Feller central limit theorem** (sufficiency direction). Let `X n i`, `i : ι n`,
be a triangular array of real random variables, the `n`th row on its own probability space
`(Ω n, P n)`. Suppose the rows are independent, centred and square integrable, with row variances
converging to `v : ℝ≥0`. If the Lindeberg condition `∑ i, E[X n i ^ 2; ε ≤ |X n i|] → 0` holds for
every `ε > 0`, then the row sums converge in distribution to any random variable `Y` with law
`gaussianReal 0 v`. -/
theorem HasLaw.tendstoInDistribution_sum_of_lindeberg {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {X : (n : ℕ) → ι n → Ω n → ℝ} {v : ℝ≥0}
    (hY : HasLaw Y (gaussianReal 0 v) P')
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hL2 : ∀ n i, MemLp (X n i) 2 (P n))
    (h0 : ∀ n i, (P n)[X n i] = 0)
    (hvar : Tendsto (fun n ↦ ∑ i, Var[X n i; P n]) atTop (𝓝 (v : ℝ)))
    (hlind : ∀ ε > 0, Tendsto
      (fun n ↦ ∑ i, (P n)[{ω | ε ≤ |X n i ω|}.indicator (fun ω ↦ X n i ω ^ 2)]) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω ↦ ∑ i, X n i ω) atTop Y P P' where
  forall_aemeasurable n :=
    Finset.aemeasurable_fun_sum _ fun i _ ↦ (hL2 n i).aestronglyMeasurable.aemeasurable
  tendsto := by
    have hm n i : AEMeasurable (X n i) (P n) := (hL2 n i).aestronglyMeasurable.aemeasurable
    set V : ℕ → ℝ := fun n ↦ ∑ i, ∫ ω, X n i ω ^ 2 ∂(P n)
    have hV : Tendsto V atTop (𝓝 (v : ℝ)) := hvar.congr fun n ↦
      Finset.sum_congr rfl fun i _ ↦ variance_of_integral_eq_zero (hm n i) (h0 n i)
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    rw! [hY.map_eq]
    have key n : charFun ((P n).map fun ω ↦ ∑ i, X n i ω) t =
        ∏ i, charFun ((P n).map (X n i)) t := by
      rw [(hindep n).charFun_map_fun_sum_eq_prod (hm n), Finset.prod_apply]
    have hG : charFun (gaussianReal 0 v) t = ((Real.exp (-(t ^ 2 * (v : ℝ) / 2)) : ℝ) : ℂ) := by
      rw [charFun_gaussianReal]; push_cast; ring_nf
    simp only [ProbabilityMeasure.coe_mk, key, hG]
    have hG_lim : Tendsto (fun n ↦ ((Real.exp (-(t ^ 2 * V n / 2)) : ℝ) : ℂ)) atTop
        (𝓝 ((Real.exp (-(t ^ 2 * (v : ℝ) / 2)) : ℝ) : ℂ)) :=
      ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (((continuous_const.mul continuous_id).div_const 2).neg))).tendsto _).comp hV
    simpa only [V, sub_add_cancel, zero_add] using
      (tendsto_prod_charFun_sub_exp_zero hL2 h0 hV hlind t).add hG_lim

/-- **Central limit theorem for bounded summands with diverging variance.** Let the rows of the
triangular array `X n i`, `i : ι n`, be independent, the `n`th row on its own probability space
`(Ω n, P n)`, and suppose every centred summand is bounded: `|X n i - E[X n i]| ≤ C` almost
surely, for one constant `C`. If the row variance `∑ i, Var[X n i]` tends to infinity, then the
centred row sum divided by its standard deviation converges in distribution to a standard Gaussian
random variable `Y`.

For sums of independent indicators of events `A n i` with probabilities `p n i`, the centred
summands are bounded by `1`, so the conclusion holds as soon as `∑ i, p n i (1 - p n i) → ∞`. -/
theorem HasLaw.tendstoInDistribution_sum_sub_div_sqrt_of_abs_sub_le {ι : ℕ → Type*}
    [∀ n, Fintype (ι n)] {X : (n : ℕ) → ι n → Ω n → ℝ}
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hindep : ∀ n, iIndepFun (X n) (P n))
    (hm : ∀ n i, AEMeasurable (X n i) (P n))
    {C : ℝ} (hC : ∀ n i, ∀ᵐ ω ∂(P n), |X n i ω - (P n)[X n i]| ≤ C)
    (hvar : Tendsto (fun n ↦ ∑ i, Var[X n i; P n]) atTop atTop) :
    TendstoInDistribution
      (fun n ω ↦ (∑ i, (X n i ω - (P n)[X n i])) / √(∑ i, Var[X n i; P n])) atTop Y
      P P' := by
  set s : ℕ → ℝ := fun n ↦ √(∑ i, Var[X n i; P n]) with hs
  have hs0 n : 0 ≤ s n := Real.sqrt_nonneg _
  -- the centred summands are bounded, hence square integrable
  have hcL2 n i : MemLp (fun ω ↦ X n i ω - (P n)[X n i]) 2 (P n) :=
    MemLp.of_bound ((hm n i).sub_const _).aestronglyMeasurable C
      ((hC n i).mono fun ω h ↦ by rwa [Real.norm_eq_abs])
  have hL2 n i : MemLp (X n i) 2 (P n) := by
    convert (hcL2 n i).add (memLp_const ((P n)[X n i])) using 1; ext ω; simp
  -- the normalised array
  set Z : (n : ℕ) → ι n → Ω n → ℝ := fun n i ω ↦ (X n i ω - (P n)[X n i]) / s n with hZ
  have hsum : (fun n ω ↦ (∑ i, (X n i ω - (P n)[X n i])) / √(∑ i, Var[X n i; P n])) =
      fun n ω ↦ ∑ i, Z n i ω := by ext n ω; simp only [hZ, hs, Finset.sum_div]
  rw [hsum]
  have hZL2 n i : MemLp (Z n i) 2 (P n) := by
    simpa only [hZ, div_eq_mul_inv] using (hcL2 n i).mul_const (s n)⁻¹
  have hZ0 n i : (P n)[Z n i] = 0 := by
    rw [hZ, integral_div, integral_sub ((hL2 n i).integrable one_le_two) (integrable_const _)]
    simp
  have hs_top : Tendsto s atTop atTop := Real.tendsto_sqrt_atTop.comp hvar
  have hZindep n : iIndepFun (Z n) (P n) := by
    have h := (hindep n).comp (fun (i : ι n) (x : ℝ) ↦ (x - ∫ ω, X n i ω ∂(P n)) / s n)
      fun i ↦ (measurable_id.sub_const _).div_const _
    simpa only [hZ, Function.comp_def] using h
  refine hY.tendstoInDistribution_sum_of_lindeberg hZindep hZL2 hZ0 ?_ fun ε hε ↦ ?_
  · -- the normalised row variances are eventually `1`
    rw [NNReal.coe_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hvar.eventually_gt_atTop 0] with n hn
    symm
    have hVZ i : Var[Z n i; P n] = Var[X n i; P n] / s n ^ 2 := by
      simp only [hZ, div_eq_mul_inv, variance_mul_const,
        variance_sub_const (hm n i).aestronglyMeasurable, inv_pow]
    simp only [hVZ, ← Finset.sum_div, hs, Real.sq_sqrt hn.le]
    exact div_self hn.ne'
  · -- the Lindeberg sum vanishes once `C / s n < ε`
    have hCs : Tendsto (fun n ↦ C / s n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hs_top
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hCs (Iio_mem_nhds hε)] with n hn
    symm
    refine Finset.sum_eq_zero fun i _ ↦ integral_eq_zero_of_ae ?_
    filter_upwards [hC n i] with ω hω
    have hZle : |Z n i ω| < ε := by
      calc |Z n i ω| = |X n i ω - (P n)[X n i]| / s n := by
            simp only [hZ, abs_div, abs_of_nonneg (hs0 n)]
        _ ≤ C / s n := div_le_div_of_nonneg_right hω (hs0 n)
        _ < ε := hn
    rw [Pi.zero_apply, Set.indicator_of_notMem (s := {ω | ε ≤ |Z n i ω|})
      (not_le.mpr hZle)]

end ProbabilityTheory
