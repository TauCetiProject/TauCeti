/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NoncentralBeta.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Moments of noncentral Beta laws

The natural moments are convergent Poisson averages of finite products of shape ratios.
The same formula covers the atom at zero when the first shape is zero: the empty product
is one, whereas every positive-order product for the zero-shape component vanishes.
The first two moments give the mean and variance. Bounded support supplies integrability
of every natural and exponential moment, including for the totalized invalid laws.

The calculation uses `integral_pow_betaMeasure` and `Real.prod_range_add_mul_Gamma`
to evaluate the components of `noncentralBetaMeasure_eq_sum`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {a b : ℝ} {l : ℝ≥0}

/-- Every natural power is integrable under a valid Beta mixture component. -/
theorem integrable_pow_noncentralBetaComponent (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (noncentralBetaComponent a b) := by
  let _ := isProbabilityMeasure_noncentralBetaComponent ha hb
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [ae_mem_Icc_noncentralBetaComponent a b] with x hx
  simpa [abs_of_nonneg hx.1] using pow_le_one₀ hx.1 hx.2 (n := n)

/-- Natural moments of the Beta mixture component, including its zero-shape Dirac boundary. -/
@[simp]
theorem integral_pow_noncentralBetaComponent (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ) :
    ∫ x, x ^ n ∂noncentralBetaComponent a b =
      ∏ i ∈ Finset.range n, (a + i) / (a + b + i) := by
  rcases ha.eq_or_lt' with rfl | ha
  · rw [noncentralBetaComponent_zero, integral_dirac]
    cases n with
    | zero => simp
    | succ n =>
      rw [zero_pow (Nat.succ_ne_zero n)]
      exact (Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos n)) (by simp)).symm
  · rw [noncentralBetaComponent_of_pos ha, integral_pow_betaMeasure ha hb,
      ← Real.prod_range_add_mul_Gamma ha n,
      ← Real.prod_range_add_mul_Gamma (add_pos ha hb) n, Finset.prod_div_distrib]
    have hprod : (∏ i ∈ Finset.range n, (a + b + i)) ≠ 0 :=
      ne_of_gt (Finset.prod_pos fun i _ ↦ by positivity)
    field_simp [(Real.Gamma_pos_of_pos ha).ne',
      (Real.Gamma_pos_of_pos (add_pos ha hb)).ne', hprod]

/-- Every real exponential moment of the totalized noncentral Beta family is integrable. -/
@[simp]
theorem integrableExpSet_id_noncentralBetaMeasure (a b : ℝ) (l : ℝ≥0) :
    integrableExpSet id (noncentralBetaMeasure a b l) = univ := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, id_eq, mem_univ, iff_true]
  exact integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable
    (ae_mem_Icc_noncentralBetaMeasure a b l)

/-- Every natural power is integrable, including for invalid zero-measure parameters. -/
theorem integrable_pow_noncentralBetaMeasure (a b : ℝ) (l : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (noncentralBetaMeasure a b l) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := id) _ n
  simp [integrableExpSet_id_noncentralBetaMeasure]

/-- Every absolute natural moment is finite, including for invalid zero-measure parameters. -/
theorem integrable_pow_abs_noncentralBetaMeasure (a b : ℝ) (l : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ n) (noncentralBetaMeasure a b l) := by
  apply integrable_pow_abs_of_mem_interior_integrableExpSet (X := id) _ n
  simp [integrableExpSet_id_noncentralBetaMeasure]

/-- The Poisson series of finite shape-ratio products converges to the natural moment.
At order zero every product is one, including the component with `a = j = 0`. -/
theorem hasSum_integral_pow_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b)
    (l : ℝ≥0) (n : ℕ) :
    HasSum (fun j : ℕ ↦ (poissonMeasure (l / 2)).real {j} *
      ∏ i ∈ Finset.range n, (a + j + i) / (a + j + b + i))
      (∫ x, x ^ n ∂noncentralBetaMeasure a b l) := by
  have h := integrable_pow_noncentralBetaMeasure a b l n
  rw [noncentralBetaMeasure_eq_sum ha hb] at h ⊢
  convert hasSum_integral_measure h using 1
  ext j
  rw [integral_smul_measure, integral_pow_noncentralBetaComponent (by positivity) hb]
  simp only [measureReal_def, smul_eq_mul]

/-- Natural moments of a noncentral Beta law, as a convergent Poisson-weighted series. -/
@[simp]
theorem integral_pow_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) (n : ℕ) :
    ∫ x, x ^ n ∂noncentralBetaMeasure a b l =
      ∑' j : ℕ, (poissonMeasure (l / 2)).real {j} *
        ∏ i ∈ Finset.range n, (a + j + i) / (a + j + b + i) :=
  (hasSum_integral_pow_noncentralBetaMeasure ha hb l n).tsum_eq.symm

/-- The mean is the Poisson average of the component means `(a + j) / (a + j + b)`. -/
@[simp]
theorem integral_id_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    ∫ x, x ∂noncentralBetaMeasure a b l =
      ∑' j : ℕ, (poissonMeasure (l / 2)).real {j} * ((a + j) / (a + j + b)) := by
  simpa using integral_pow_noncentralBetaMeasure ha hb l 1

/-- The second raw moment is the Poisson average of the component second moments. -/
theorem integral_sq_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    ∫ x, x ^ 2 ∂noncentralBetaMeasure a b l =
      ∑' j : ℕ, (poissonMeasure (l / 2)).real {j} *
        ((a + j) * (a + j + 1) / ((a + j + b) * (a + j + b + 1))) := by
  rw [integral_pow_noncentralBetaMeasure ha hb]
  apply tsum_congr
  intro j
  simp [Finset.prod_range_succ]

/-- The variance is the convergent second-moment series minus the square of the mean series. -/
@[simp]
theorem variance_id_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    variance id (noncentralBetaMeasure a b l) =
      (∑' j : ℕ, (poissonMeasure (l / 2)).real {j} *
        ((a + j) * (a + j + 1) / ((a + j + b) * (a + j + b + 1)))) -
      (∑' j : ℕ, (poissonMeasure (l / 2)).real {j} * ((a + j) / (a + j + b))) ^ 2 := by
  let _ := isProbabilityMeasure_noncentralBetaMeasure ha hb l
  have hmem : MemLp id 2 (noncentralBetaMeasure a b l) :=
    memLp_of_bounded (ae_mem_Icc_noncentralBetaMeasure a b l)
      measurable_id.aestronglyMeasurable 2
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq, integral_sq_noncentralBetaMeasure ha hb,
    integral_id_noncentralBetaMeasure ha hb]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- Every natural moment of a variable with a noncentral Beta law is integrable. -/
theorem integrable_pow_of_hasLaw_noncentralBetaMeasure
    (hX : HasLaw X (noncentralBetaMeasure a b l) P) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) P :=
  hX.integrable_fun_comp (integrable_pow_noncentralBetaMeasure a b l n)

/-- Natural moments of a variable with a noncentral Beta law. -/
theorem integral_pow_of_hasLaw_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b)
    (hX : HasLaw X (noncentralBetaMeasure a b l) P) (n : ℕ) :
    ∫ ω, X ω ^ n ∂P =
      ∑' j : ℕ, (poissonMeasure (l / 2)).real {j} *
        ∏ i ∈ Finset.range n, (a + j + i) / (a + j + b + i) := by
  calc
    ∫ ω, X ω ^ n ∂P = ∫ x, x ^ n ∂noncentralBetaMeasure a b l := by
      simpa only [Function.comp_def] using
        hX.integral_comp (f := fun x : ℝ ↦ x ^ n) (by fun_prop)
    _ = _ := integral_pow_noncentralBetaMeasure ha hb l n

/-- A noncentral Beta variable has the Poisson-series mean, including first shape zero. -/
theorem integral_of_hasLaw_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b)
    (hX : HasLaw X (noncentralBetaMeasure a b l) P) :
    ∫ ω, X ω ∂P =
      ∑' j : ℕ, (poissonMeasure (l / 2)).real {j} * ((a + j) / (a + j + b)) := by
  rw [hX.integral_eq, integral_id_noncentralBetaMeasure ha hb]

/-- The variance formula for a variable with a noncentral Beta law. -/
theorem variance_of_hasLaw_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b)
    (hX : HasLaw X (noncentralBetaMeasure a b l) P) :
    variance X P =
      (∑' j : ℕ, (poissonMeasure (l / 2)).real {j} *
        ((a + j) * (a + j + 1) / ((a + j + b) * (a + j + b + 1)))) -
      (∑' j : ℕ, (poissonMeasure (l / 2)).real {j} * ((a + j) / (a + j + b))) ^ 2 := by
  rw [hX.variance_eq, variance_id_noncentralBetaMeasure ha hb]

end TauCeti.Probability
