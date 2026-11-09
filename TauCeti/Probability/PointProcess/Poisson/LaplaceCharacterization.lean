/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.Probability.RandomMeasure.LaplaceFunctional
import TauCeti.Probability.Moments.LaplaceDeterminacy.Multivariate
import TauCeti.Probability.Distributions.Poisson.Transforms

/-!
# The Laplace characterization of Poisson random measures

The exponential Laplace formula forces independent Poisson counts on disjoint measurable
sets. No integrality assumption on the random measure is needed. Sets of infinite intensity
have almost surely infinite counts, rather than a Poisson law with a truncated parameter.

This is the converse direction of the Laplace characterization, used to recognize Poisson
random measures constructed through their transforms. Disjoint indicator tests give mixed
moments of negative exponentials. The existing directional Poisson transform
`mgf_sum_mul_natCast_pi_poissonMeasure` computes the comparison law, and
`TauCeti.Measure.ext_of_forall_lintegral_prod_exp_neg_pow_eq` identifies the count vector,
without presupposing that its coordinates are finite or integer-valued.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Theorem 3.9.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X}

private theorem poisson_counts_mixed_moment
    (hL : ∀ f : X → ℝ≥0∞, Measurable f → P.laplaceFunctional N f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞))
    {d : ℕ} (A : Fin d → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Disjoint on A)) (n : Fin d → ℕ) :
    ∫⁻ ω, ∏ i, EReal.exp (-((N ω (A i)) : EReal)) ^ n i ∂P =
      (ENNReal.expNeg (∑ i, Λ (A i) *
        (1 - (ENNReal.expNeg (n i) : ℝ≥0∞))) : ℝ≥0∞) := by
  classical
  let f : X → ℝ≥0∞ := fun x => ∑ i, (A i).indicator (fun _ => (n i : ℝ≥0∞)) x
  have hf : Measurable f := Finset.measurable_sum _ fun i _ =>
    measurable_const.indicator (hA i)
  have he (ω : Ω) : (ENNReal.expNeg (∫⁻ x, f x ∂N ω) : ℝ≥0∞) =
      ∏ i, EReal.exp (-((N ω (A i)) : EReal)) ^ n i := by
    simp only [f, lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hA i)),
      lintegral_indicator_const (hA _), ENNReal.expNeg_sum, ENNReal.ofNNReal_finsetProd]
    apply Finset.prod_congr rfl
    intro i _
    rw [ENNReal.coe_expNeg, EReal.coe_ennreal_mul, ENNReal.toEReal_natCast,
      ← mul_neg, EReal.exp_nmul]
  have hg : (fun x => 1 - (ENNReal.expNeg (f x) : ℝ≥0∞)) =
      fun x => ∑ i, (A i).indicator
        (fun _ => 1 - (ENNReal.expNeg (n i) : ℝ≥0∞)) x := by
    funext x
    by_cases hx : ∃ i, x ∈ A i
    · obtain ⟨i, hi⟩ := hx
      have hnot (j : Fin d) (hji : j ≠ i) : x ∉ A j :=
        fun hj => (hd hji).le_bot ⟨hj, hi⟩
      have hsum (g : Fin d → ℝ≥0∞) :
          ∑ j, (A j).indicator (fun _ => g j) x = g i := by
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro j _ hji
          simp [hnot j hji]
        · simp
      rw [hsum]
      dsimp only [f]
      rw [hsum]
    · have hn : ∀ i, x ∉ A i := by simpa using hx
      simp [f, hn]
  have htest := hL f hf
  simp_rw [Measure.laplaceFunctional_def, he] at htest
  rw [hg, lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hA i))] at htest
  simp only [lintegral_indicator_const (hA _)] at htest
  simpa only [mul_comm] using htest

private theorem poisson_counts_identDistrib [IsProbabilityMeasure P]
    (hN : Measurable N)
    (hL : ∀ f : X → ℝ≥0∞, Measurable f → P.laplaceFunctional N f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞))
    {d : ℕ} (A : Fin d → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, Λ (A i) < ∞) (hd : Pairwise (Disjoint on A)) :
    IdentDistrib (fun ω i => N ω (A i)) (fun y : Fin d → ℕ => fun i => (y i : ℝ≥0∞))
      P (Measure.pi fun i => poissonMeasure (Λ (A i)).toNNReal) := by
  classical
  let r (i : Fin d) := (Λ (A i)).toNNReal
  have hmeas : Measurable (fun ω i => N ω (A i)) :=
    measurable_pi_iff.2 fun i => (Measure.measurable_coe (hA i)).comp hN
  have hymeas : Measurable (fun y : Fin d → ℕ => fun i => (y i : ℝ≥0∞)) :=
    measurable_pi_iff.2 fun i => Measurable.of_discrete.comp (measurable_pi_apply i)
  refine ⟨hmeas.aemeasurable, hymeas.aemeasurable,
    TauCeti.Measure.ext_of_forall_lintegral_prod_exp_neg_pow_eq fun n => ?_⟩
  rw [lintegral_map (by fun_prop) hmeas, lintegral_map (by fun_prop) hymeas,
    poisson_counts_mixed_moment hL A hA hd]
  -- Convert the finite product's mixed moment to the existing directional Poisson mgf.
  have he (y : Fin d → ℕ) : ∏ i, EReal.exp (-((y i : ℝ≥0∞) : EReal)) ^ n i =
      ENNReal.ofReal (Real.exp (1 * ∑ i, -(n i : ℝ) * (y i : ℝ))) := by
    simp only [one_mul, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg
      (fun i _ => (Real.exp_pos _).le)]
    apply Finset.prod_congr rfl
    intro i _
    simp only [ENNReal.toEReal_natCast, ← EReal.coe_natCast, ← EReal.coe_neg,
      EReal.exp_coe, ← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
    congr 2
    ring
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_mul_sum_mul_natCast_pi_poissonMeasure r (fun i => -(n i : ℝ)) 1)
    (ae_of_all _ fun _ => (Real.exp_pos _).le),
    ← mgf, mgf_sum_mul_natCast_pi_poissonMeasure]
  have hb (i : Fin d) : Real.toNNReal (Real.exp (-(n i : ℝ))) ≤ 1 := by simp
  have hcoeff (i : Fin d) : Λ (A i) * (1 - (ENNReal.expNeg (n i) : ℝ≥0∞)) =
      ((r i * (1 - Real.toNNReal (Real.exp (-(n i : ℝ)))) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal (hfin i).ne, ← ENNReal.coe_natCast,
      ENNReal.expNeg_coe, ← ENNReal.coe_one, ← ENNReal.coe_sub, ← ENNReal.coe_mul]
    rfl
  simp_rw [hcoeff]
  rw [← ENNReal.ofNNReal_finsetSum, ENNReal.expNeg_coe, ENNReal.ofNNReal_toNNReal]
  congr 2
  simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_sub (hb _), NNReal.coe_one,
    Real.coe_toNNReal _ (Real.exp_nonneg _), one_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **The converse Poisson Laplace characterization.** The exponential formula for all
nonnegative measurable tests implies independent Poisson counts. Neither integrality of
realizations nor sigma-finiteness of the intensity is required; on a set of infinite
intensity, the count is almost surely infinite. The zero test forces `P` to be a probability
measure. -/
theorem isPoissonRandomMeasure_of_laplaceFunctional (hN : Measurable N)
    (hL : ∀ f : X → ℝ≥0∞, Measurable f → P.laplaceFunctional N f =
      (ENNReal.expNeg (∫⁻ x, 1 - (ENNReal.expNeg (f x) : ℝ≥0∞) ∂Λ) : ℝ≥0∞)) :
    IsPoissonRandomMeasure P N Λ := by
  have hmass := hL 0 measurable_const
  have : IsProbabilityMeasure P := ⟨by simpa using hmass⟩
  refine isPoissonRandomMeasure_iff.2 ⟨hN, ?_, ?_⟩
  · intro d A hA hd
    have hvec := poisson_counts_identDistrib hN hL A (fun i => (hA i).1)
      (fun i => (hA i).2) hd
    have hy (i : Fin d) : HasLaw (fun y : Fin d → ℕ => (y i : ℝ≥0∞))
        ((poissonMeasure (Λ (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞))
        (Measure.pi fun i => poissonMeasure (Λ (A i)).toNNReal) := by
      exact (hasLaw_map (P := poissonMeasure (Λ (A i)).toNNReal)
        (X := (Nat.cast : ℕ → ℝ≥0∞)) Measurable.of_discrete.aemeasurable).comp
        (measurePreserving_eval (fun i => poissonMeasure (Λ (A i)).toNNReal) i).hasLaw
    have hx (i : Fin d) := ((hvec.comp (measurable_pi_apply i)).symm).hasLaw (hy i)
    refine ⟨(iIndepFun_iff_hasLaw_pi_pi hx).2 ?_, hx⟩
    exact hvec.symm.hasLaw ((iIndepFun_pi (fun _ => measurable_id.aemeasurable)).comp
      (fun _ => (Nat.cast : ℕ → ℝ≥0∞)) (fun _ => Measurable.of_discrete) |>.hasLaw_pi hy)
  · intro A hA hinf
    have htest := hL (A.indicator (fun _ => (1 : ℝ≥0∞)))
      (measurable_const.indicator hA)
    rw [Measure.laplaceFunctional_indicator_const P N hA] at htest
    have hg : (fun x => 1 - (ENNReal.expNeg (A.indicator (fun _ => (1 : ℝ≥0∞)) x) : ℝ≥0∞)) =
        A.indicator (fun _ => 1 - (ENNReal.expNeg 1 : ℝ≥0∞)) := by
      ext x
      by_cases hx : x ∈ A <;> simp [hx]
    have hc : (1 - (ENNReal.expNeg 1 : ℝ≥0∞)) ≠ 0 := by
      apply ne_of_gt
      apply tsub_pos_of_lt
      apply ENNReal.coe_lt_one_iff.2
      rw [← ENNReal.coe_one, ENNReal.expNeg_coe,
        Real.toNNReal_lt_iff_lt_coe (Real.exp_nonneg _)]
      norm_num [Real.exp_lt_one_iff]
    rw [hg, lintegral_indicator_const hA, hinf, ENNReal.mul_top hc,
      ENNReal.expNeg_top, ENNReal.coe_zero] at htest
    have hm : Measurable (fun ω => (ENNReal.expNeg (1 * N ω A) : ℝ≥0∞)) :=
      measurable_coe_nnreal_ennreal.comp (ENNReal.measurable_expNeg.comp
        (measurable_const.mul ((Measure.measurable_coe hA).comp hN)))
    have hae := (lintegral_eq_zero_iff' hm.aemeasurable).1 htest
    filter_upwards [hae] with ω hω
    simpa using hω

end TauCeti.Probability
