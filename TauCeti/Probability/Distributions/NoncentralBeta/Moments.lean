/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralBeta.Basic

/-!
# Moments of noncentral Beta laws

Every natural moment is a convergent Poisson average of finite products of Beta shape ratios.
The empty product gives moment one at order zero. At positive orders the first-shape-zero,
zero-count component contributes zero, so the same formula includes the atom at zero and the
Dirac law at zero noncentrality. The first two series give the mean and variance.
Bounded support gives every real exponential moment, including for invalid zero measures.

The calculation uses `noncentralBetaMeasure_eq_sum` and the central Beta moment formula,
following the mixture integration argument for noncentral chi moments.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

variable {a b : ℝ} {l : ℝ≥0}

/-- The extended Beta component has the usual product moments also at first shape zero:
the empty product is one and every positive-order product vanishes there. -/
theorem integral_pow_noncentralBetaComponent (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ) :
    ∫ x, x ^ n ∂noncentralBetaComponent a b =
      ∏ i ∈ Finset.range n, (a + i) / (a + b + i) := by
  rcases ha.eq_or_lt' with rfl | ha
  · rw [noncentralBetaComponent_zero, integral_dirac]
    cases n with
    | zero => simp
    | succ n => simp [Finset.prod_range_succ']
  · rw [noncentralBetaComponent_of_pos ha, integral_pow_betaMeasure_eq_prod ha hb]

/-- Every real exponential moment exists for the entire totalized noncentral Beta family. -/
@[simp]
theorem integrableExpSet_id_noncentralBetaMeasure (a b : ℝ) (l : ℝ≥0) :
    integrableExpSet id (noncentralBetaMeasure a b l) = univ := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true, id_eq]
  exact integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable
    (ae_mem_Icc_noncentralBetaMeasure a b l)

/-- All natural powers are integrable, including the atomic boundary and invalid parameters. -/
theorem integrable_pow_noncentralBetaMeasure (a b : ℝ) (l : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (noncentralBetaMeasure a b l) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := id) _ n
  simp

/-- The identity is integrable for every choice of shapes and noncentrality. -/
theorem integrable_id_noncentralBetaMeasure (a b : ℝ) (l : ℝ≥0) :
    Integrable id (noncentralBetaMeasure a b l) := by
  simpa only [pow_one, Function.id_def] using integrable_pow_noncentralBetaMeasure a b l 1

/-- The natural-moment Poisson series converges to the moment, also at first shape zero
and at order zero. -/
theorem hasSum_integral_pow_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ) :
    HasSum (fun j : ℕ ↦
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        ∏ i ∈ Finset.range n, (a + j + i) / (a + j + b + i))
      (∫ x, x ^ n ∂noncentralBetaMeasure a b l) := by
  have h := integrable_pow_noncentralBetaMeasure a b l n
  rw [noncentralBetaMeasure_eq_sum ha hb] at h ⊢
  convert hasSum_integral_measure h using 1
  funext j
  rw [integral_smul_measure, smul_eq_mul, ← measureReal_def,
    poissonMeasure_real_singleton,
    integral_pow_noncentralBetaComponent (by positivity) hb]
  simp only [NNReal.coe_div, NNReal.coe_ofNat, neg_div]

/-- Natural moments are the convergent Poisson averages of the Beta product moments. -/
theorem integral_pow_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ) :
    ∫ x, x ^ n ∂noncentralBetaMeasure a b l = ∑' j : ℕ,
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        ∏ i ∈ Finset.range n, (a + j + i) / (a + j + b + i) :=
  (hasSum_integral_pow_noncentralBetaMeasure ha hb n).tsum_eq.symm

/-- The mean is the Poisson average of `(a + j) / (a + b + j)`, including `a = 0`. -/
theorem integral_id_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) :
    ∫ x, x ∂noncentralBetaMeasure a b l = ∑' j : ℕ,
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        ((a + j) / (a + j + b)) := by
  simpa using integral_pow_noncentralBetaMeasure (l := l) ha hb 1

/-- The second raw moment is a convergent Poisson average, with zero contribution from
the atom at zero. -/
theorem integral_sq_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) :
    ∫ x, x ^ 2 ∂noncentralBetaMeasure a b l = ∑' j : ℕ,
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        ((a + j) * (a + j + 1) / ((a + j + b) * (a + j + b + 1))) := by
  rw [integral_pow_noncentralBetaMeasure ha hb]
  congr 1
  funext j
  simp [Finset.prod_range_succ, div_mul_div_comm]

/-- The variance is the second Poisson moment series minus the square of the first. -/
theorem variance_id_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) :
    variance id (noncentralBetaMeasure a b l) =
      (∑' j : ℕ, (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        ((a + j) * (a + j + 1) / ((a + j + b) * (a + j + b + 1)))) -
      (∑' j : ℕ, (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        ((a + j) / (a + j + b))) ^ 2 := by
  let _ := isProbabilityMeasure_noncentralBetaMeasure ha hb l
  have hmem : MemLp id 2 (noncentralBetaMeasure a b l) :=
    memLp_of_bounded (ae_mem_Icc_noncentralBetaMeasure a b l)
      measurable_id.aestronglyMeasurable 2
  simpa only [Pi.pow_apply, id_eq, integral_sq_noncentralBetaMeasure ha hb,
    integral_id_noncentralBetaMeasure ha hb] using variance_eq_sub hmem

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
  {a b : ℝ} {l : ℝ≥0}

/-- A variable with noncentral Beta law has every natural moment integrable. -/
theorem integrable_pow_noncentralBetaMeasure
    (hX : HasLaw X (TauCeti.Probability.noncentralBetaMeasure a b l) P) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_pow_noncentralBetaMeasure a b l n)

/-- Natural moments of a noncentral Beta variable are Poisson averages of Beta products. -/
theorem integral_pow_noncentralBetaMeasure
    (hX : HasLaw X (TauCeti.Probability.noncentralBetaMeasure a b l) P)
    (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ) :
    ∫ ω, X ω ^ n ∂P = ∑' j : ℕ,
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        ∏ i ∈ Finset.range n, (a + j + i) / (a + j + b + i) := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ n), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_pow_noncentralBetaMeasure ha hb]

/-- The mean of a noncentral Beta variable is the Poisson average of the component means. -/
theorem integral_noncentralBetaMeasure
    (hX : HasLaw X (TauCeti.Probability.noncentralBetaMeasure a b l) P)
    (ha : 0 ≤ a) (hb : 0 < b) :
    ∫ ω, X ω ∂P = ∑' j : ℕ,
      (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        ((a + j) / (a + j + b)) := by
  rw [hX.integral_eq, TauCeti.Probability.integral_id_noncentralBetaMeasure ha hb]

/-- The variance formula for a random variable with noncentral Beta law. -/
theorem variance_noncentralBetaMeasure
    (hX : HasLaw X (TauCeti.Probability.noncentralBetaMeasure a b l) P)
    (ha : 0 ≤ a) (hb : 0 < b) :
    variance X P =
      (∑' j : ℕ, (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        ((a + j) * (a + j + 1) / ((a + j + b) * (a + j + b + 1)))) -
      (∑' j : ℕ, (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        ((a + j) / (a + j + b))) ^ 2 := by
  rw [hX.variance_eq, TauCeti.Probability.variance_id_noncentralBetaMeasure ha hb]

/-- Every real exponential moment of a variable with noncentral Beta law is integrable. -/
theorem integrable_exp_mul_noncentralBetaMeasure
    (hX : HasLaw X (TauCeti.Probability.noncentralBetaMeasure a b l) P) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω)) P := by
  refine hX.integrable_fun_comp (f := fun x : ℝ ↦ exp (t * x)) ?_
  have ht : t ∈ integrableExpSet id (TauCeti.Probability.noncentralBetaMeasure a b l) := by
    simp
  exact ht

end ProbabilityTheory.HasLaw
