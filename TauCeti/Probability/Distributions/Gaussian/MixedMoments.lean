/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Moments
public import TauCeti.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Fourth mixed moments of Gaussian laws

The fourth centered moment of four linear observables is the sum of the three products of
their pairwise covariances. The formula allows repeated observables and singular covariance.
For a multivariate Gaussian this gives the coordinate identity
`E[Zᵢ Zⱼ Zₖ Zₗ] = Sᵢⱼ Sₖₗ + Sᵢₖ Sⱼₗ + Sᵢₗ Sⱼₖ` for centered coordinates.

The linear-observable result is proved for Gaussian measures on real Banach spaces, then
specialized to the multivariate law. Finite products of affine linear observables are integrable.
Polarizing the existing scalar fourth-moment formula avoids any invertibility requirement.

## References

* L. Isserlis, *On a formula for the product-moment coefficient of any order of a normal
  frequency distribution in any number of variables*, Biometrika 12 (1918), 134–139.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Nat

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Finite products of affine linear observables of a Gaussian measure are integrable,
including the empty product. -/
theorem integrable_prod_dual (μ : Measure E) [IsGaussian μ]
    {ι : Type*} (s : Finset ι) (L : ι → StrongDual ℝ E) (c : ι → ℝ) :
    Integrable (fun x ↦ ∏ i ∈ s, (L i x + c i)) μ := by
  classical
  by_cases hs : s = ∅
  · simp [hs]
  have hcard : (s.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
  have hLp := MemLp.fun_prod (s := s) (p := fun _ ↦ (s.card : ℝ≥0∞))
    (fun i _ ↦ (IsGaussian.memLp_dual μ (L i) _ (by simp)).add (memLp_const (c i)))
  have hexp : (∑ _i ∈ s, (s.card : ℝ≥0∞)⁻¹)⁻¹ = 1 := by
    simp [nsmul_eq_mul, hcard, ENNReal.mul_inv_cancel]
  rw [hexp] at hLp
  exact memLp_one_iff_integrable.mp hLp

variable [CompleteSpace E] [SecondCountableTopology E]

/-- The `2n`th centered moment of a linear observable of a Gaussian measure is
`Varⁿ (2n - 1)‼`, with the variance expressed by the covariance bilinear form. -/
theorem integral_pow_two_mul_sub_dual (μ : Measure E) [IsGaussian μ]
    (L : StrongDual ℝ E) (n : ℕ) :
    (∫ x, L (x - μ[id]) ^ (2 * n) ∂μ) =
      covarianceBilinDual μ L L ^ n * (2 * n - 1 : ℕ)‼ := by
  rw [covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id]
  have hmean : μ[L] = L μ[id] :=
    L.integral_comp_comm (IsGaussian.integrable_id (μ := μ))
  calc
    _ = ∫ x, (x - μ[L]) ^ (2 * n) ∂gaussianReal μ[L] (Var[L; μ].toNNReal) := by
      rw [← IsGaussian.map_eq_gaussianReal L, integral_map (by fun_prop) (by fun_prop)]
      simp only [hmean, map_sub]
    _ = _ := by
      rw [TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal,
        Real.coe_toNNReal _ (variance_nonneg L μ)]

/-- The fourth centered mixed moment of four linear observables of a Gaussian measure
is the sum over their three pairings. No independence or nondegeneracy is assumed. -/
theorem integral_mul_mul_mul_sub_dual (μ : Measure E) [IsGaussian μ]
    (L₁ L₂ L₃ L₄ : StrongDual ℝ E) :
    (∫ x, L₁ (x - μ[id]) * L₂ (x - μ[id]) *
      L₃ (x - μ[id]) * L₄ (x - μ[id]) ∂μ) =
      covarianceBilinDual μ L₁ L₂ * covarianceBilinDual μ L₃ L₄ +
      covarianceBilinDual μ L₁ L₃ * covarianceBilinDual μ L₂ L₄ +
      covarianceBilinDual μ L₁ L₄ * covarianceBilinDual μ L₂ L₃ := by
  -- Eight signed fourth powers polarize the product of the four observables.
  let L : Fin 8 → StrongDual ℝ E :=
    ![L₁ + L₂ + L₃ + L₄, L₁ + L₂ + L₃ - L₄,
      L₁ + L₂ - L₃ + L₄, L₁ + L₂ - L₃ - L₄,
      L₁ - L₂ + L₃ + L₄, L₁ - L₂ + L₃ - L₄,
      L₁ - L₂ - L₃ + L₄, L₁ - L₂ - L₃ - L₄]
  let w : Fin 8 → ℝ := ![1, -1, -1, 1, -1, 1, 1, -1]
  have hint (i : Fin 8) : Integrable (fun x ↦ L i (x - μ[id]) ^ 4) μ := by
    simpa [map_sub, sub_eq_add_neg] using integrable_prod_dual μ
      (Finset.univ : Finset (Fin 4)) (fun _ ↦ L i) (fun _ ↦ -L i μ[id])
  have hpolar :
      192 * (∫ x, L₁ (x - μ[id]) * L₂ (x - μ[id]) *
        L₃ (x - μ[id]) * L₄ (x - μ[id]) ∂μ) =
        ∑ i, w i * (∫ x, L i (x - μ[id]) ^ 4 ∂μ) := by
    calc
      _ = ∫ x, ∑ i, w i * L i (x - μ[id]) ^ 4 ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, L, w, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one, add_zero,
          _root_.add_apply, _root_.sub_apply]
        ring
      _ = _ := by
        rw [integral_finsetSum _ (fun i _ ↦ (hint i).const_mul (w i))]
        simp_rw [integral_const_mul]
  simp_rw [integral_pow_two_mul_sub_dual μ _ 2] at hpolar
  norm_num only [Nat.doubleFactorial] at hpolar
  -- Bilinearity and symmetry reduce the polarized variances to the three pairings.
  conv_rhs at hpolar =>
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, L, w, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, add_zero, map_add, map_sub,
      _root_.add_apply, _root_.sub_apply]
  simp only [covarianceBilinDual_comm (μ := μ) L₂ L₁,
    covarianceBilinDual_comm (μ := μ) L₃ L₁, covarianceBilinDual_comm (μ := μ) L₄ L₁,
    covarianceBilinDual_comm (μ := μ) L₃ L₂, covarianceBilinDual_comm (μ := μ) L₄ L₂,
    covarianceBilinDual_comm (μ := μ) L₄ L₃] at hpolar
  linear_combination hpolar / 192

end ProbabilityTheory.IsGaussian

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every shifted coordinate monomial is integrable under every multivariate Gaussian.
Taking `c = 0` gives raw monomials and taking `c = m` gives centered monomials.
No validity assumption on the covariance parameter is needed. -/
theorem integrable_prod_pow_sub_multivariateGaussian (m c : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (n : ι → ℕ) :
    Integrable (fun x ↦ ∏ i, (x i - c i) ^ n i) (multivariateGaussian m S) := by
  simpa [Fintype.prod_sigma, sub_eq_add_neg] using
    IsGaussian.integrable_prod_dual (multivariateGaussian m S)
      (Finset.univ : Finset (Σ i, Fin (n i)))
      (fun p ↦ EuclideanSpace.proj p.1) (fun p ↦ -c p.1)

/-- The fourth centered coordinate moment of a multivariate Gaussian, including repeated
coordinates and positive-semidefinite singular covariance matrices. -/
@[simp]
theorem integral_mul_mul_mul_sub_multivariateGaussian
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i j k l : ι) :
    (∫ x, (x i - m i) * (x j - m j) * (x k - m k) * (x l - m l)
      ∂multivariateGaussian m S) = S i j * S k l + S i k * S j l + S i l * S j k := by
  have h := IsGaussian.integral_mul_mul_mul_sub_dual (multivariateGaussian m S)
    (EuclideanSpace.proj i) (EuclideanSpace.proj j)
    (EuclideanSpace.proj k) (EuclideanSpace.proj l)
  have hcov (i j : ι) : covarianceBilinDual (multivariateGaussian m S)
      (EuclideanSpace.proj i) (EuclideanSpace.proj j) = S i j := by
    rw [covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id]
    simpa only [EuclideanSpace.coe_proj] using covariance_eval_multivariateGaussian hS i j
  simp only [hcov] at h
  simpa using h

/-- Isserlis' fourth-moment identity for centered multivariate Gaussian coordinates. -/
@[simp]
theorem integral_mul_mul_mul_multivariateGaussian
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i j k l : ι) :
    (∫ x, x i * x j * x k * x l ∂multivariateGaussian 0 S) =
      S i j * S k l + S i k * S j l + S i l * S j k := by
  simpa using integral_mul_mul_mul_sub_multivariateGaussian 0 hS i j k l

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}
  {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}

/-- The fourth centered coordinate moment of a random vector with a multivariate Gaussian law.
Repeated coordinates and singular covariance matrices are allowed. -/
theorem integral_mul_mul_mul_sub_multivariateGaussian
    (hX : HasLaw X (multivariateGaussian m S) P) (hS : S.PosSemidef) (i j k l : ι) :
    (∫ ω, (X ω i - m i) * (X ω j - m j) * (X ω k - m k) * (X ω l - m l) ∂P) =
      S i j * S k l + S i k * S j l + S i l * S j k := by
  calc
    _ = ∫ x, (x i - m i) * (x j - m j) * (x k - m k) * (x l - m l)
        ∂multivariateGaussian m S := hX.integral_comp (by fun_prop)
    _ = _ := TauCeti.Probability.integral_mul_mul_mul_sub_multivariateGaussian m hS i j k l

end ProbabilityTheory.HasLaw
