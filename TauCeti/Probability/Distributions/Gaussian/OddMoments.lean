/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.HasLaw
public import TauCeti.Probability.Distributions.Gaussian.Symmetry

/-!
# Odd Gaussian mixed moments

Every centered Gaussian monomial of odd total degree has expectation zero. The factors can
be correlated, repeated, or have variance zero. We give the result for finite families of
continuous linear observables on a real normed space, then for coordinate products
and multi-index monomials of multivariate Gaussian laws and random vectors with those laws.

Integrability is supplied separately in
`TauCeti.Probability.Distributions.Gaussian.MixedMoments`.

## References

* L. Isserlis, *On a formula for the product-moment coefficient of any order of a normal
  frequency distribution in any number of variables*, Biometrika 12 (1918), 134–139.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A product of centered Gaussian linear observables with odd total degree has integral zero.
The observables need not be independent or distinct. -/
@[simp]
theorem integral_prod_pow_sub_dual_eq_zero_of_odd (μ : Measure E) [IsGaussian μ]
    {ι : Type*} (s : Finset ι) (L : ι → StrongDual ℝ E) (n : ι → ℕ)
    (hn : Odd (∑ i ∈ s, n i)) :
    (∫ x, ∏ i ∈ s, (L i x - μ[L i]) ^ n i ∂μ) = 0 := by
  classical
  let T : E →L[ℝ] (s → ℝ) := ContinuousLinearMap.pi (fun i ↦ L i)
  have hn' : Odd (∑ i : s, n i) := by
    simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hn
  have hodd : Function.Odd (fun y : s → ℝ ↦ ∏ i, y i ^ n i) := by
    intro x
    simp only [Pi.neg_apply]
    calc
      _ = ∏ i : s, (-1 : ℝ) ^ n i * x i ^ n i :=
        Finset.prod_congr rfl (fun i _ ↦ neg_pow _ _)
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hn'.neg_one_pow, neg_one_mul]
  have hmean (i : s) : (∫ y, y ∂μ.map T) i = μ[L i] := by
    calc
      _ = ∫ y, y i ∂μ.map T :=
        (integral_dual (μ := μ.map T) (ContinuousLinearMap.proj i : (s → ℝ) →L[ℝ] ℝ)).symm
      _ = μ[L i] := by
        rw [integral_map (by fun_prop) (by fun_prop : Continuous _).aestronglyMeasurable]
        rfl
  calc
    _ = ∫ y : s → ℝ, ∏ i, (y i - μ[L i]) ^ n i ∂μ.map T := by
      rw [integral_map (by fun_prop) (by fun_prop : Continuous _).aestronglyMeasurable]
      exact integral_congr_ae (ae_of_all _ fun x ↦
        (Finset.prod_coe_sort s (fun i ↦ (L i x - μ[L i]) ^ n i)).symm)
    _ = 0 := by
      simpa only [Pi.sub_apply, id_eq, hmean] using
        integral_comp_sub_eq_zero_of_odd (μ.map T) hodd

/-- Every odd product of centered Gaussian linear observables has integral zero. -/
@[simp]
theorem integral_prod_sub_dual_eq_zero_of_odd (μ : Measure E) [IsGaussian μ]
    {ι : Type*} (s : Finset ι) (L : ι → StrongDual ℝ E) (hs : Odd s.card) :
    (∫ x, ∏ i ∈ s, (L i x - μ[L i]) ∂μ) = 0 := by
  simpa using integral_prod_pow_sub_dual_eq_zero_of_odd μ s L (fun _ ↦ 1) (by simpa using hs)

end ProbabilityTheory.IsGaussian

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every centered coordinate monomial of odd total degree has expectation zero under a
multivariate Gaussian law. This includes singular and invalid covariance parameters. -/
@[simp]
theorem integral_prod_pow_sub_multivariateGaussian_eq_zero_of_odd
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (n : ι → ℕ) (hn : Odd (∑ i, n i)) :
    (∫ x, ∏ i, (x i - m i) ^ n i ∂multivariateGaussian m S) = 0 := by
  have h := IsGaussian.integral_prod_pow_sub_dual_eq_zero_of_odd
    (multivariateGaussian m S) Finset.univ EuclideanSpace.proj n hn
  simp_rw [IsGaussian.integral_dual, integral_id_multivariateGaussian] at h
  simpa using h

/-- Every odd product of centered multivariate Gaussian coordinates has expectation zero.
The index map permits repeated coordinates. No covariance validity assumption is needed. -/
@[simp]
theorem integral_prod_sub_multivariateGaussian_eq_zero_of_odd
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) {κ : Type*} (s : Finset κ)
    (j : κ → ι) (hs : Odd s.card) :
    (∫ x, ∏ k ∈ s, (x (j k) - m (j k)) ∂multivariateGaussian m S) = 0 := by
  have h := IsGaussian.integral_prod_sub_dual_eq_zero_of_odd
    (multivariateGaussian m S) s (fun k ↦ EuclideanSpace.proj (j k)) hs
  simp_rw [IsGaussian.integral_dual, integral_id_multivariateGaussian] at h
  simpa using h

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}
  {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}

/-- A random vector with a multivariate Gaussian law has vanishing centered monomials of
odd total degree, including singular covariance. -/
theorem integral_prod_pow_sub_multivariateGaussian_eq_zero_of_odd
    (hX : HasLaw X (multivariateGaussian m S) P) (n : ι → ℕ) (hn : Odd (∑ i, n i)) :
    (∫ ω, ∏ i, (X ω i - m i) ^ n i ∂P) = 0 := by
  calc
    _ = ∫ x, ∏ i, (x i - m i) ^ n i ∂multivariateGaussian m S :=
      hX.integral_comp (by fun_prop)
    _ = 0 := TauCeti.Probability.integral_prod_pow_sub_multivariateGaussian_eq_zero_of_odd
      m S n hn

end ProbabilityTheory.HasLaw
