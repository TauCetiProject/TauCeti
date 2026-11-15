/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.OddMoments
public import TauCeti.Probability.Distributions.Gaussian.MixedMoments

/-!
# Noncentered Gaussian mixed moments

The integrals of finite products of affine Gaussian observables expand about their means.
Only subsets of even cardinality contribute, since odd centered moments vanish. The
observables may be dependent or repeated, and the empty product is included.

For coordinate monomials, the expansion instead sums over bounded multi-indices, with the
binomial coefficients and powers of the mean made explicit. It reduces noncentered moments
to centered moments without requiring a nonsingular covariance matrix.

Integrability is supplied by `ProbabilityTheory.IsGaussian.integrable_prod_dual` and
`TauCeti.Probability.integrable_prod_pow_sub_multivariateGaussian`, re-exported here.

## References

* L. Isserlis, *On a formula for the product-moment coefficient of any order of a normal
  frequency distribution in any number of variables*, Biometrika 12 (1918), 134–139.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The integral of a product of affine Gaussian observables is a sum of even centered moments,
weighted by the means of the remaining factors. No independence or nondegeneracy is assumed. -/
theorem integral_prod_add_dual_eq_sum_even_of_isGaussian (μ : Measure E) [IsGaussian μ]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (L : ι → StrongDual ℝ E) (c : ι → ℝ) :
    (∫ x, ∏ i ∈ s, (L i x + c i) ∂μ) =
      ∑ t ∈ s.powerset with Even t.card,
        (∏ i ∈ s \ t, (μ[L i] + c i)) *
          ∫ x, ∏ i ∈ t, (L i x - μ[L i]) ∂μ := by
  have hint (t : Finset ι) : Integrable (fun x ↦ ∏ i ∈ t, (L i x - μ[L i])) μ := by
    simpa only [sub_eq_add_neg] using
      IsGaussian.integrable_prod_dual μ t L (fun i ↦ -μ[L i])
  calc
    _ = ∫ x, ∑ t ∈ s.powerset,
        (∏ i ∈ s \ t, (μ[L i] + c i)) * ∏ i ∈ t, (L i x - μ[L i]) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simpa only [← add_assoc, sub_add_cancel, mul_comm] using
        (Finset.prod_add (fun i ↦ L i x - μ[L i]) (fun i ↦ μ[L i] + c i) s)
    _ = ∑ t ∈ s.powerset,
        (∏ i ∈ s \ t, (μ[L i] + c i)) *
          ∫ x, ∏ i ∈ t, (L i x - μ[L i]) ∂μ := by
      rw [integral_finsetSum _ (fun t _ ↦ (hint t).const_mul _)]
      simp only [integral_const_mul]
    _ = _ := by
      symm
      apply Finset.sum_filter_of_ne
      intro t _ ht
      by_contra hodd
      exact ht (by rw [IsGaussian.integral_prod_sub_dual_eq_zero_of_odd μ t L
        (Nat.not_even_iff_odd.mp hodd), mul_zero])

/-- The integral of a monomial in affine Gaussian observables is a sum of even centered
moments weighted by binomial coefficients and powers of the shifted means `μ[L i] + c i`. -/
theorem integral_prod_pow_add_dual_eq_sum_even_of_isGaussian (μ : Measure E) [IsGaussian μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ι → StrongDual ℝ E) (c : ι → ℝ) (n : ι → ℕ) :
    (∫ x, ∏ i, (L i x + c i) ^ n i ∂μ) =
      ∑ k ∈ Fintype.piFinset (fun i ↦ Finset.range (n i + 1)) with Even (∑ i, k i),
        (∏ i, ((n i).choose (k i) : ℝ) * (μ[L i] + c i) ^ (n i - k i)) *
          ∫ x, ∏ i, (L i x - μ[L i]) ^ k i ∂μ := by
  have hint (k : ι → ℕ) : Integrable (fun x ↦ ∏ i, (L i x - μ[L i]) ^ k i) μ := by
    simpa [Fintype.prod_sigma, sub_eq_add_neg] using
      IsGaussian.integrable_prod_dual μ (Finset.univ : Finset (Σ i, Fin (k i)))
        (fun p ↦ L p.1) (fun p ↦ -μ[L p.1])
  -- Expand each affine observable by the binomial theorem, then distribute the finite product.
  have hexpand (x : E) :
      (∏ i, (L i x + c i) ^ n i) =
        ∑ k ∈ Fintype.piFinset (fun i ↦ Finset.range (n i + 1)),
          (∏ i, ((n i).choose (k i) : ℝ) * (μ[L i] + c i) ^ (n i - k i)) *
            ∏ i, (L i x - μ[L i]) ^ k i := by
    calc
      _ = ∏ i, ∑ k ∈ Finset.range (n i + 1),
          (((n i).choose k : ℝ) * (μ[L i] + c i) ^ (n i - k)) * (L i x - μ[L i]) ^ k := by
        apply Finset.prod_congr rfl
        intro i _
        calc
          _ = ((L i x - μ[L i]) + (μ[L i] + c i)) ^ n i := by congr 1; ring
          _ = _ := by
            rw [add_pow]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = _ := by
        rw [Finset.prod_univ_sum]
        simp only [Finset.prod_mul_distrib]
  -- Every centered monomial is integrable, so integration commutes with this finite sum.
  calc
    _ = ∫ x, ∑ k ∈ Fintype.piFinset (fun i ↦ Finset.range (n i + 1)),
        (∏ i, ((n i).choose (k i) : ℝ) * (μ[L i] + c i) ^ (n i - k i)) *
          ∏ i, (L i x - μ[L i]) ^ k i ∂μ := by
      exact integral_congr_ae (ae_of_all _ hexpand)
    _ = ∑ k ∈ Fintype.piFinset (fun i ↦ Finset.range (n i + 1)),
        (∏ i, ((n i).choose (k i) : ℝ) * (μ[L i] + c i) ^ (n i - k i)) *
          ∫ x, ∏ i, (L i x - μ[L i]) ^ k i ∂μ := by
      rw [integral_finsetSum _ (fun k _ ↦
        (hint k).const_mul _)]
      simp only [integral_const_mul]
    _ = _ := by
      symm
      apply Finset.sum_filter_of_ne
      intro k _ hk
      by_contra hodd
      exact hk (by rw [IsGaussian.integral_prod_pow_sub_dual_eq_zero_of_odd μ Finset.univ L k
        (Nat.not_even_iff_odd.mp hodd), mul_zero])

end MeasureTheory.Measure

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integral of a finite product of shifted Gaussian coordinates is a sum of even centered
moments weighted by products of `m (j k) - c (j k)`. The index map allows repeated coordinates.
The formula includes singular and invalid covariance parameters. -/
theorem integral_prod_sub_multivariateGaussian_eq_sum_even
    (m c : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (j : κ → ι) :
    (∫ x, ∏ k ∈ s, (x (j k) - c (j k)) ∂multivariateGaussian m S) =
      ∑ t ∈ s.powerset with Even t.card,
        (∏ k ∈ s \ t, (m (j k) - c (j k))) *
          ∫ x, ∏ k ∈ t, (x (j k) - m (j k)) ∂multivariateGaussian m S := by
  have h := Measure.integral_prod_add_dual_eq_sum_even_of_isGaussian
    (multivariateGaussian m S) s (fun k ↦ EuclideanSpace.proj (j k)) (fun k ↦ -c (j k))
  simp_rw [IsGaussian.integral_dual, integral_id_multivariateGaussian] at h
  simpa only [EuclideanSpace.coe_proj, sub_eq_add_neg] using h

/-- The multivariate binomial expansion of the integral of a shifted Gaussian monomial about
its mean. Only bounded multi-indices of even total degree contribute. This includes every natural
raw moment at `c = 0`, all centered moments at `c = m`, and every covariance parameter. -/
theorem integral_prod_pow_sub_multivariateGaussian_eq_sum_even
    (m c : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (n : ι → ℕ) :
    (∫ x, ∏ i, (x i - c i) ^ n i ∂multivariateGaussian m S) =
      ∑ k ∈ Fintype.piFinset (fun i ↦ Finset.range (n i + 1)) with Even (∑ i, k i),
        (∏ i, ((n i).choose (k i) : ℝ) * (m i - c i) ^ (n i - k i)) *
          ∫ x, ∏ i, (x i - m i) ^ k i ∂multivariateGaussian m S := by
  have h := Measure.integral_prod_pow_add_dual_eq_sum_even_of_isGaussian
    (multivariateGaussian m S) EuclideanSpace.proj (fun i ↦ -c i) n
  simp_rw [IsGaussian.integral_dual, integral_id_multivariateGaussian] at h
  simpa only [EuclideanSpace.coe_proj, sub_eq_add_neg] using h

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}
  {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}

/-- The expectation of a shifted mixed product of a Gaussian random vector is a sum of even
centered moments weighted by products of `m (j k) - c (j k)` over the remaining positions.
Positions may select the same coordinate. -/
theorem integral_prod_sub_multivariateGaussian_eq_sum_even
    (hX : HasLaw X (multivariateGaussian m S) P) (c : EuclideanSpace ℝ ι)
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (j : κ → ι) :
    (∫ ω, ∏ k ∈ s, (X ω (j k) - c (j k)) ∂P) =
      ∑ t ∈ s.powerset with Even t.card,
        (∏ k ∈ s \ t, (m (j k) - c (j k))) *
          ∫ ω, ∏ k ∈ t, (X ω (j k) - m (j k)) ∂P := by
  have hcomp (d : EuclideanSpace ℝ ι) (t : Finset κ) :
      (∫ ω, ∏ k ∈ t, (X ω (j k) - d (j k)) ∂P) =
        ∫ x, ∏ k ∈ t, (x (j k) - d (j k)) ∂multivariateGaussian m S :=
    hX.integral_comp (f := fun x ↦ ∏ k ∈ t, (x (j k) - d (j k))) (by fun_prop)
  simp_rw [hcomp]
  exact TauCeti.Probability.integral_prod_sub_multivariateGaussian_eq_sum_even m c S s j

/-- The expectation of a shifted coordinate monomial of a Gaussian random vector is a sum of
even centered moments weighted by multivariate binomial coefficients and powers of `m i - c i`. -/
theorem integral_prod_pow_sub_multivariateGaussian_eq_sum_even
    (hX : HasLaw X (multivariateGaussian m S) P) (c : EuclideanSpace ℝ ι) (n : ι → ℕ) :
    (∫ ω, ∏ i, (X ω i - c i) ^ n i ∂P) =
      ∑ k ∈ Fintype.piFinset (fun i ↦ Finset.range (n i + 1)) with Even (∑ i, k i),
        (∏ i, ((n i).choose (k i) : ℝ) * (m i - c i) ^ (n i - k i)) *
          ∫ ω, ∏ i, (X ω i - m i) ^ k i ∂P := by
  have hcomp (d : EuclideanSpace ℝ ι) (k : ι → ℕ) :
      (∫ ω, ∏ i, (X ω i - d i) ^ k i ∂P) =
        ∫ x, ∏ i, (x i - d i) ^ k i ∂multivariateGaussian m S :=
    hX.integral_comp (f := fun x ↦ ∏ i, (x i - d i) ^ k i) (by fun_prop)
  simp_rw [hcomp]
  exact TauCeti.Probability.integral_prod_pow_sub_multivariateGaussian_eq_sum_even m c S n

end ProbabilityTheory.HasLaw
