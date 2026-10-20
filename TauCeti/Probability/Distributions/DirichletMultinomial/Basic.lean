/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.MixedMoments
public import TauCeti.Probability.Distributions.Multinomial.Measurability
public import TauCeti.Probability.Distributions.Dirichlet.Measurability
import TauCeti.MeasureTheory.Integral.Bind
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The Dirichlet-multinomial distribution

The Dirichlet-multinomial law mixes multinomial cell probabilities against a Dirichlet law.
It describes count vectors whose probabilities share a random simplex parameter. The mixing
parameter is read through a measurable extension of the inverse simplex-weight embedding;
the resulting law is independent of the extension away from the simplex.

This file gives the construction, normalization, Gamma-ratio singleton masses, exact support,
zero-trial boundary, finite weighted Dirac sum, integration, and parameter measurability.
The construction and iterated integration follow the existing `betaBinomialMeasure` API.
The mass computation uses `integral_prod_pow_dirichletMeasure`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 40.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The Dirichlet mixture of multinomial count laws with `n` trials and concentration vector `a`.
Nonpositive concentration parameters give zero measure. -/
def dirichletMultinomialMeasure (n : ℕ) (a : ι → ℝ) : Measure (ι → ℕ) :=
  (dirichletMeasure a).bind fun x ↦ multinomialMeasure n
    ((StdSimplex.single (Classical.arbitrary ι) : StdSimplex ℝ≥0 ι).extendWeights
      (fun i ↦ (x i).toNNReal))

private theorem measurable_dirichletMultinomialComponent (n : ℕ) :
    Measurable fun x : EuclideanSpace ℝ ι ↦ multinomialMeasure n
      ((StdSimplex.single (Classical.arbitrary ι) : StdSimplex ℝ≥0 ι).extendWeights
        (fun i ↦ (x i).toNNReal)) := by
  exact measurable_multinomialMeasure.comp (measurable_const.prodMk
    ((StdSimplex.measurable_extendWeights _).comp (by fun_prop)))

/-- Any simplex parameter map whose weights agree almost surely with the Dirichlet
vector gives the same mixture. Thus choices away from the simplex do not affect the law. -/
theorem dirichletMultinomialMeasure_eq_bind {a : ι → ℝ} (n : ℕ)
    (p : EuclideanSpace ℝ ι → StdSimplex ℝ≥0 ι)
    (hp : ∀ᵐ x ∂dirichletMeasure a, ∀ i, ((p x).weights i : ℝ) = x i) :
    dirichletMultinomialMeasure n a =
      (dirichletMeasure a).bind (fun x ↦ multinomialMeasure n (p x)) := by
  rw [dirichletMultinomialMeasure]
  by_cases ha : ∀ i, 0 < a i
  · apply Measure.bind_congr_right
    filter_upwards [ae_extendWeights_dirichletMeasure ha
      (StdSimplex.single (Classical.arbitrary ι)), hp] with x hx hpx
    congr 1
    apply StdSimplex.ext
    ext i
    exact (hx i).trans (hpx i).symm
  · rw [dirichletMeasure_eq_zero_of_invalid (by simpa using ha)]
    simp

/-- Invalid concentration parameters give the zero Dirichlet-multinomial measure. -/
@[simp]
theorem dirichletMultinomialMeasure_eq_zero_of_invalid {a : ι → ℝ}
    (ha : ¬ ∀ i, 0 < a i) (n : ℕ) : dirichletMultinomialMeasure n a = 0 := by
  rw [dirichletMultinomialMeasure, dirichletMeasure_eq_zero_of_invalid (by simpa using ha)]
  simp

/-- Positive concentrations normalize the Dirichlet-multinomial law to a probability measure. -/
theorem isProbabilityMeasure_dirichletMultinomialMeasure {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (n : ℕ) : IsProbabilityMeasure (dirichletMultinomialMeasure n a) := by
  let _ := isProbabilityMeasure_dirichletMeasure ha
  exact isProbabilityMeasure_bind (measurable_dirichletMultinomialComponent n).aemeasurable
    (.of_forall fun _ ↦ isProbabilityMeasure_multinomialMeasure n _)

/-- The classical Dirichlet-multinomial mass: a factorial coefficient times a ratio of
Dirichlet normalizers, and zero outside the count antidiagonal. -/
@[simp]
theorem dirichletMultinomialMeasure_real_singleton {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (n : ℕ) (k : ι → ℕ) :
    (dirichletMultinomialMeasure n a).real {k} =
      if ∑ i, k i = n then
        ((n.factorial : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
          (Real.Gamma (∑ i, a i) / Real.Gamma ((∑ i, a i) + n) *
            ∏ i, Real.Gamma (a i + k i) / Real.Gamma (a i))
      else 0 := by
  classical
  let p : EuclideanSpace ℝ ι → StdSimplex ℝ≥0 ι := fun x ↦
    (StdSimplex.single (Classical.arbitrary ι) : StdSimplex ℝ≥0 ι).extendWeights
      (fun i ↦ (x i).toNNReal)
  have hp := ae_extendWeights_dirichletMeasure ha
    (StdSimplex.single (Classical.arbitrary ι))
  rw [dirichletMultinomialMeasure_eq_bind n p hp, measureReal_def,
    Measure.bind_apply (measurableSet_singleton k)
      (measurable_dirichletMultinomialComponent n).aemeasurable]
  have hm : AEMeasurable (fun x ↦ multinomialMeasure n (p x) {k}) (dirichletMeasure a) :=
    ((Measure.measurable_coe (measurableSet_singleton k)).comp
      (measurable_dirichletMultinomialComponent n)).aemeasurable
  have hfinite : ∀ᵐ x ∂dirichletMeasure a, multinomialMeasure n (p x) {k} < ∞ := by
    filter_upwards with x
    have := isProbabilityMeasure_multinomialMeasure n (p x)
    exact measure_lt_top _ _
  rw [← integral_toReal hm hfinite]
  simp_rw [← measureReal_def, multinomialMeasure_real_singleton]
  split_ifs with hk
  · have heq : (fun x ↦ ((n.factorial : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
        ∏ i, ((p x).weights i : ℝ) ^ k i) =ᵐ[dirichletMeasure a]
        fun x ↦ ((n.factorial : ℝ) / ∏ i, ((k i).factorial : ℝ)) * ∏ i, x i ^ k i := by
      filter_upwards [hp] with x hx
      simp only [p, hx]
    rw [integral_congr_ae heq, integral_const_mul,
      integral_prod_pow_dirichletMeasure ha]
    simp only [← Nat.cast_sum, hk]
  · simp

/-- The extended nonnegative singleton masses of a valid Dirichlet-multinomial law. -/
@[simp]
theorem dirichletMultinomialMeasure_singleton {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (n : ℕ) (k : ι → ℕ) :
    dirichletMultinomialMeasure n a {k} =
      if ∑ i, k i = n then
        ENNReal.ofReal (((n.factorial : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
          (Real.Gamma (∑ i, a i) / Real.Gamma ((∑ i, a i) + n) *
            ∏ i, Real.Gamma (a i + k i) / Real.Gamma (a i)))
      else 0 := by
  let _ := isProbabilityMeasure_dirichletMultinomialMeasure ha n
  rw [← ofReal_measureReal (s := {k}), dirichletMultinomialMeasure_real_singleton ha]
  split_ifs <;> simp

/-- A count vector has positive mass precisely when its total is the number of trials.
Positive Dirichlet concentrations make every count vector on this antidiagonal possible. -/
theorem dirichletMultinomialMeasure_singleton_ne_zero_iff {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (n : ℕ) (k : ι → ℕ) :
    dirichletMultinomialMeasure n a {k} ≠ 0 ↔ ∑ i, k i = n := by
  classical
  rw [dirichletMultinomialMeasure_singleton ha]
  split_ifs with hk
  · have hsum : 0 < ∑ i, a i := Finset.sum_pos (fun i _ ↦ ha i) Finset.univ_nonempty
    have hGamma := Real.Gamma_pos_of_pos hsum
    have hGammaSum := Real.Gamma_pos_of_pos
      (add_pos_of_pos_of_nonneg hsum (Nat.cast_nonneg n))
    have hGammaProd : 0 < ∏ i, Real.Gamma (a i + k i) / Real.Gamma (a i) :=
      Finset.prod_pos fun i _ ↦ div_pos
        (Real.Gamma_pos_of_pos (add_pos_of_pos_of_nonneg (ha i) (Nat.cast_nonneg _)))
        (Real.Gamma_pos_of_pos (ha i))
    have hpos : 0 < ((n.factorial : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
        (Real.Gamma (∑ i, a i) / Real.Gamma ((∑ i, a i) + n) *
          ∏ i, Real.Gamma (a i + k i) / Real.Gamma (a i)) := by positivity
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, hk, iff_true]
    exact hpos
  · simp [hk]

open Classical in
/-- A Dirichlet-multinomial law is a finite weighted sum of Dirac measures on the count
antidiagonal, with the classical Gamma-ratio weights. -/
theorem dirichletMultinomialMeasure_eq_sum_dirac {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (n : ℕ) :
    dirichletMultinomialMeasure n a =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        ENNReal.ofReal (((n.factorial : ℝ) / ∏ i, ((k i).factorial : ℝ)) *
          (Real.Gamma (∑ i, a i) / Real.Gamma ((∑ i, a i) + n) *
            ∏ i, Real.Gamma (a i + k i) / Real.Gamma (a i))) • Measure.dirac k := by
  classical
  apply Measure.ext_of_singleton
  intro k
  simp [dirichletMultinomialMeasure_singleton ha, Measure.finsetSum_apply,
    Pi.single_apply, mul_ite, Finset.mem_piAntidiag]

/-- With no trials, a valid Dirichlet-multinomial law is concentrated at the zero count vector. -/
@[simp]
theorem dirichletMultinomialMeasure_zero_trials {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    dirichletMultinomialMeasure 0 a = Measure.dirac 0 := by
  let _ := isProbabilityMeasure_dirichletMeasure ha
  rw [dirichletMultinomialMeasure]
  simp only [multinomialMeasure_zero]
  simp

/-- With one category, all trials fall in that category. -/
@[simp]
theorem dirichletMultinomialMeasure_eq_dirac_of_subsingleton [Subsingleton ι] {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (n : ℕ) :
    dirichletMultinomialMeasure n a = Measure.dirac (fun _ ↦ n) := by
  let i : ι := Classical.arbitrary ι
  apply Measure.ext_of_singleton
  intro k
  rw [dirichletMultinomialMeasure_singleton ha]
  simp only [Fintype.sum_subsingleton _ i, Fintype.prod_subsingleton _ i]
  by_cases hk : k i = n
  · have hkn : k = fun _ ↦ n := funext fun j ↦ (congrArg k (Subsingleton.elim j i)).trans hk
    subst k
    have hGamma := (Real.Gamma_pos_of_pos (ha i)).ne'
    have hGammaN := (Real.Gamma_pos_of_pos
      (add_pos_of_pos_of_nonneg (ha i) (Nat.cast_nonneg n))).ne'
    simp [hGamma, hGammaN, mul_div, Nat.factorial_ne_zero]
  · have hkn : k ≠ fun _ ↦ n := fun h ↦ hk (congrFun h i)
    simp [hk, Ne.symm hkn]

/-- Every observable of the native count vector is integrable: its law has finite support.
This includes invalid concentrations, where the law is zero. -/
theorem integrable_dirichletMultinomialMeasure {E : Type*} [SeminormedAddGroup E]
    (f : (ι → ℕ) → E) (n : ℕ) (a : ι → ℝ) :
    Integrable f (dirichletMultinomialMeasure n a) := by
  by_cases ha : ∀ i, 0 < a i
  · rw [dirichletMultinomialMeasure_eq_sum_dirac ha]
    exact integrable_finsetSum_measure.mpr fun k _ ↦
      (integrable_dirac (by simp)).smul_measure (by simp)
  · simp [dirichletMultinomialMeasure_eq_zero_of_invalid ha]

open Classical in
/-- Integrate a count observable by a finite sum of its values against the singleton masses.
For valid concentrations, the masses simplify to the Gamma-ratio formula; otherwise both
sides vanish. -/
theorem integral_dirichletMultinomialMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : (ι → ℕ) → E) {a : ι → ℝ}
    (n : ℕ) :
    ∫ k, f k ∂dirichletMultinomialMeasure n a =
      ∑ k ∈ Finset.piAntidiag Finset.univ n,
        (dirichletMultinomialMeasure n a).real {k} • f k := by
  classical
  by_cases ha : ∀ i, 0 < a i
  · conv_lhs => rw [dirichletMultinomialMeasure_eq_sum_dirac ha]
    rw [integral_finsetSum_measure]
    · apply Finset.sum_congr rfl
      intro k hk
      have hsum : ∑ i, k i = n := (Finset.mem_piAntidiag.mp hk).1
      simp only [integral_smul_measure, integral_dirac, measureReal_def,
        dirichletMultinomialMeasure_singleton ha, ite_eq_left hsum]
    · intro k _
      exact (integrable_dirac (by simp)).smul_measure (by simp)
  · simp [dirichletMultinomialMeasure_eq_zero_of_invalid ha]

/-- Integrate a count observable by first taking its multinomial expectation, then its
Dirichlet expectation. Any measurable choice of simplex parameters with the correct
almost-sure weights may be used. -/
theorem integral_dirichletMultinomialMeasure_eq_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (ι → ℕ) → E) {a : ι → ℝ} (n : ℕ)
    (p : EuclideanSpace ℝ ι → StdSimplex ℝ≥0 ι) (hp : Measurable p)
    (hweights : ∀ᵐ x ∂dirichletMeasure a, ∀ i, ((p x).weights i : ℝ) = x i) :
    ∫ k, f k ∂dirichletMultinomialMeasure n a =
      ∫ x, ∫ k, f k ∂multinomialMeasure n (p x) ∂dirichletMeasure a := by
  have hf := integrable_dirichletMultinomialMeasure f n a
  rw [dirichletMultinomialMeasure_eq_bind n p hweights] at hf ⊢
  exact Measure.integral_bind
    (measurable_multinomialMeasure.comp (measurable_const.prodMk hp)).aemeasurable hf

/-- The Dirichlet-multinomial family is jointly measurable in the trial count and every
concentration coordinate, including invalid parameters. -/
@[fun_prop]
theorem measurable_dirichletMultinomialMeasure :
    Measurable fun q : ℕ × (ι → ℝ) ↦ dirichletMultinomialMeasure q.1 q.2 := by
  refine measurable_from_prod_countable_right fun n ↦ ?_
  simp only [dirichletMultinomialMeasure]
  exact (Measure.measurable_bind' (measurable_dirichletMultinomialComponent n)).comp
    measurable_dirichletMeasure

end TauCeti.Probability
