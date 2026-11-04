/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Gaussian.Barycenter
public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Barycenter
public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Moments
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Uniqueness.Euclidean
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FrechetMean
public import TauCeti.Probability.Moments.Covariance
import TauCeti.Analysis.Matrix.BuresFixedPoint
import TauCeti.Analysis.Matrix.GeometricMean
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.Probability.Moments.FenchelYoung
import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# The fixed-point equation of Gaussian barycenters

Let `μ j` be finitely many probability laws on `ℝⁿ` with finite second moments, means `m j` and
covariance matrices `C j`, and let `w j` be nonnegative weights summing to `1`. Suppose that a
positive-definite matrix `S` solves the fixed-point equation

`S = ∑ j, w j • (S^(1/2) * C j * S^(1/2))^(1/2)`.

Then for every probability law `ν` the quadratic barycentric cost `∑ j, w j * W₂(ν, μ j) ^ 2` is
at least the cost `∑ j, w j * B(mbar, m j, S, C j)` of the Gaussian law with mean
`mbar = ∑ j, w j • m j` and covariance `S` computed as if every `μ j` were Gaussian, where `B` is
the Bures expression `TauCeti.gaussianWassersteinSq`. The input laws need not be Gaussian. When they
are, the bound is attained by that Gaussian law, so the fixed-point equation characterizes a
Gaussian barycenter: the Gaussian law with mean `mbar` and covariance `S` is a quadratic Fréchet
barycenter in `P₂`, and the only one as soon as an input with positive weight has a
positive-definite covariance.

The matrices `A j = geometricMean S⁻¹ʳ (C j)` are the linear parts of the optimal maps out of the
Gaussian law with covariance `S`, and `S` solves the fixed-point equation exactly when they
average to the identity (`Matrix.PosDef.sum_smul_geometricMean_ringInverse_eq_one_iff`).
Averaging the quadratic Fenchel–Young inequalities `⟪u, y⟫ ≤ (⟪A j y, y⟫ + ⟪(A j)⁺ u, u⟫) / 2`,
in mean over a multi-coupling of the laws `μ j` (`TauCeti.integral_inner_sub_integral_le`),
bounds the variance of the weighted mean of the coupling by `tr S`; the weighted variance
decomposition and the multi-marginal formulation of the barycenter problem turn this into the
lower bound. Singular covariances `C j` are allowed: the pseudoinverse `(A j)⁺` is used on the
range of `A j`, which carries the centred `j`th coordinate almost surely.

When an input with positive weight has a positive-definite covariance, the fixed-point equation
does have a positive-definite solution (`Matrix.exists_posDef_eq_sum_smul_sqrt_sqrt_mul_mul_sqrt`),
so the barycenter of the Gaussian laws `N(m j, C j)` exists, is unique, and is the Gaussian law with
mean `mbar` and that covariance. Two positive-definite solutions give the same barycenter, hence
the same covariance, so the solution is unique as well.

## Main statements

* `TauCeti.integral_norm_sum_smul_sub_integral_sq_le`: the centred weighted mean of a
  multi-coupling has second moment at most `tr S`.
* `TauCeti.sum_mul_ofReal_gaussianWassersteinSq_le`: the Gaussian lower bound for the
  barycentric cost of arbitrary laws with finite second moments.
* `TauCeti.Probability.isFrechetBarycenter_sum_smul_dirac_multivariateGaussian`: the Gaussian law
  with mean `mbar` and covariance `S` is a barycenter of Gaussian laws.
* `TauCeti.Probability.frechetBarycenters_sum_smul_dirac_multivariateGaussian`: it is the unique
  barycenter when an input with positive weight is nondegenerate.
* `TauCeti.Probability.exists_posDef_frechetBarycenters_sum_smul_dirac_multivariateGaussian`:
  Gaussian laws, one of them nondegenerate with a positive weight, have a unique barycenter, the
  Gaussian law with mean `mbar` and a positive-definite covariance solving the fixed-point equation.
* `TauCeti.existsUnique_posDef_eq_sum_smul_sqrt_sqrt_mul_mul_sqrt`: under the same hypothesis the
  fixed-point equation has exactly one positive-definite solution.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904–924, Section 6, for the fixed-point characterization of Gaussian barycenters.
* P. C. Álvarez-Esteban, E. del Barrio, J. A. Cuesta-Albertos and C. Matrán, *A fixed-point
  approach to barycenters in Wasserstein space*, J. Math. Anal. Appl. 441 (2016), 744–762, for
  the fixed-point equation of Gaussian and location-scatter barycenters.
* M. Gelbrich, *On a formula for the L² Wasserstein metric between measures on Euclidean and
  Hilbert spaces*, Math. Nachr. 147 (1990), 185–203, for the Gaussian lower bound on `W₂`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Ring
open scoped ENNReal NNReal Matrix MatrixOrder RealInnerProductSpace

namespace TauCeti

variable {ι : Type*} [Fintype ι]

variable {J : Type*} [Fintype J]

variable {w : J → ℝ≥0} {μ : J → Measure (EuclideanSpace ℝ ι)} {S : Matrix ι ι ℝ}
  {γ : Measure (J → EuclideanSpace ℝ ι)}

open scoped Classical in
/-- **The variance of the weighted mean of a multi-coupling.** Let `μ j` be probability laws on
`ℝⁿ` with finite second moments, means `m j` and covariance matrices `C j`, let `w j` be
nonnegative weights, and let the positive-definite matrix `S` solve
`S = ∑ j, w j • (S^(1/2) * C j * S^(1/2))^(1/2)`. Then under every multi-coupling of the laws
`μ j`, the centred weighted mean `∑ j, w j • (x j - m j)` has second moment at most `tr S`. -/
theorem integral_norm_sum_smul_sub_integral_sq_le [∀ j, IsProbabilityMeasure (μ j)]
    (hμ : ∀ j, MemLp id 2 (μ j)) (hS : S.PosDef)
    (hfix : S = ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * covMatrix (μ j) * CFC.sqrt S))
    (hγ : Measure.IsMultiCoupling γ μ) :
    ∫ x, ‖∑ j, (w j : ℝ) • (x j - ∫ y, y ∂μ j)‖ ^ 2 ∂γ ≤ S.trace := by
  -- Writing `W` for the centred weighted mean, `‖W‖ ^ 2 = ∑ j, w j * ⟪x j - m j, W⟫`. Bound each
  -- correlation by the Fenchel–Young inequality with `A j = geometricMean S⁻¹ʳ (C j)`; since the
  -- `A j` average to the identity, the bounds add up to `(𝔼 ‖W‖ ^ 2 + tr S) / 2`.
  rcases isEmpty_or_nonempty J with hJ | ⟨⟨j₀⟩⟩
  · simpa using hS.posSemidef.trace_nonneg
  have := hγ.isProbabilityMeasure j₀
  set m : J → EuclideanSpace ℝ ι := fun j ↦ ∫ y, y ∂μ j
  set W : (J → EuclideanSpace ℝ ι) → EuclideanSpace ℝ ι := fun x ↦ ∑ j, (w j : ℝ) • (x j - m j)
  set A : J → Matrix ι ι ℝ := fun j ↦ geometricMean S⁻¹ʳ (covMatrix (μ j))
  have hA (j : J) : (A j).PosSemidef := Matrix.nonneg_iff_posSemidef.1 (geometricMean_nonneg _ _)
  have hAone : ∑ j, (w j : ℝ) • A j = 1 :=
    (hS.sum_smul_geometricMean_ringInverse_eq_one_iff _ _).2 hfix
  have hcoord (j : J) : MemLp (fun x : J → EuclideanSpace ℝ ι ↦ x j) 2 γ :=
    hγ.memLp_comp_eval j (hμ j)
  have hmean (j : J) : ∫ x, x j ∂γ = m j := hγ.integral_comp_eval j aestronglyMeasurable_id
  have hW : MemLp W 2 γ := hγ.memLp_sum_smul_sub hμ _ m
  -- The quadratic Fenchel–Young inequality for the `j`th coordinate against `W`.
  have hFY (j : J) : ∫ x, ⟪x j - m j, W x⟫ ∂γ ≤
      (∫ x, ⟪(A j).toEuclideanLin (W x), W x⟫ ∂γ + (A j * S).trace) / 2 := by
    have hcov : covMatrix (γ.map (Function.eval j)) = A j * S * A j := by
      rw [hγ.marginal_eq j,
        geometricMean_ringInverse_mul_mul_geometricMean_ringInverse hS.isStrictlyPositive
          (posSemidef_covMatrix _ (hμ j)).nonneg]
    simpa only [Function.eval_apply, hmean] using
      integral_inner_sub_integral_le (X := Function.eval j) (hcoord j) hW (hA j) hcov
  have hint (j : J) : Integrable (fun x ↦ ⟪x j - m j, W x⟫) γ :=
    ((hcoord j).sub (memLp_const _)).integrable_inner hW
  have hAint (j : J) : Integrable (fun x ↦ ⟪(A j).toEuclideanLin (W x), W x⟫) γ :=
    hW.integrable_inner_toEuclideanLin (A j)
  -- Average the inequalities: the matrices `A j` average to the identity.
  have hsq (x : J → EuclideanSpace ℝ ι) : ‖W x‖ ^ 2 = ∑ j, (w j : ℝ) * ⟪x j - m j, W x⟫ := by
    calc ‖W x‖ ^ 2 = ⟪∑ j, (w j : ℝ) • (x j - m j), W x⟫ := (real_inner_self_eq_norm_sq _).symm
      _ = _ := by simp only [sum_inner, real_inner_smul_left]
  have hquad (x : J → EuclideanSpace ℝ ι) :
      ∑ j, (w j : ℝ) * ⟪(A j).toEuclideanLin (W x), W x⟫ = ‖W x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa only [map_sum, map_smul, Matrix.toLpLin_one, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sum_inner, real_inner_smul_left] using
      congrArg (fun M : Matrix ι ι ℝ ↦ ⟪M.toEuclideanLin (W x), W x⟫) hAone
  have htrace : ∑ j, (w j : ℝ) * (A j * S).trace = S.trace := by
    simpa only [Finset.sum_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul] using
      congrArg (fun M : Matrix ι ι ℝ ↦ (M * S).trace) hAone
  have hle : ∫ x, ‖W x‖ ^ 2 ∂γ ≤ (∫ x, ‖W x‖ ^ 2 ∂γ + S.trace) / 2 := by
    calc ∫ x, ‖W x‖ ^ 2 ∂γ = ∑ j, (w j : ℝ) * ∫ x, ⟪x j - m j, W x⟫ ∂γ := by
          simp only [hsq]
          rw [integral_finsetSum _ fun j _ ↦ (hint j).const_mul _]
          simp only [integral_const_mul]
      _ ≤ ∑ j, (w j : ℝ) *
            ((∫ x, ⟪(A j).toEuclideanLin (W x), W x⟫ ∂γ + (A j * S).trace) / 2) :=
          Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hFY j) (w j).coe_nonneg
      _ = (∑ j, ∫ x, (w j : ℝ) * ⟪(A j).toEuclideanLin (W x), W x⟫ ∂γ +
            ∑ j, (w j : ℝ) * (A j * S).trace) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [integral_const_mul]
          ring
      _ = (∫ x, ‖W x‖ ^ 2 ∂γ + S.trace) / 2 := by
          rw [← integral_finsetSum _ fun j _ ↦ (hAint j).const_mul _, htrace]
          simp only [hquad]
  linarith

section Gaussian

variable [DecidableEq ι]

/-- The weighted Bures cost of a solution `S` of the fixed-point equation, measured from the
weighted mean `mbar` of the means: the cross terms add up to `tr S`. -/
private theorem sum_mul_gaussianWassersteinSq_eq (hw : ∑ j, w j = 1)
    (m : J → EuclideanSpace ℝ ι) (C : J → Matrix ι ι ℝ)
    (hfix : S = ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S)) :
    ∑ j, (w j : ℝ) * gaussianWassersteinSq (∑ i, (w i : ℝ) • m i) (m j) S (C j) =
      ∑ j, (w j : ℝ) * (‖m j - ∑ i, (w i : ℝ) • m i‖ ^ 2 + (C j).trace) - S.trace := by
  set mbar := ∑ i, (w i : ℝ) • m i
  have hw' : ∑ j, (w j : ℝ) = 1 := by exact_mod_cast hw
  have htrS : S.trace = ∑ j, (w j : ℝ) * (CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S)).trace := by
    conv_lhs => rw [hfix]
    simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  have h (j : J) : (w j : ℝ) * gaussianWassersteinSq mbar (m j) S (C j) =
      (w j : ℝ) * (‖m j - mbar‖ ^ 2 + (C j).trace) + (w j : ℝ) * S.trace -
        2 * ((w j : ℝ) * (CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S)).trace) := by
    rw [gaussianWassersteinSq_def, norm_sub_rev]
    ring
  rw [Finset.sum_congr rfl fun j _ ↦ h j, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, hw', ← Finset.mul_sum, ← htrS]
  ring

/-- **The Gaussian lower bound for the quadratic barycentric cost.** Let `μ j` be probability laws
on `ℝⁿ` with finite second moments, means `m j` and covariance matrices `C j`, let `w j` be
nonnegative weights summing to `1`, and let the positive-definite matrix `S` solve
`S = ∑ j, w j • (S^(1/2) * C j * S^(1/2))^(1/2)`. Then for every probability law `ν`,
`∑ j, w j * W₂(ν, μ j) ^ 2` is at least `∑ j, w j * B(mbar, m j, S, C j)`, where
`mbar = ∑ j, w j • m j` and `B = gaussianWassersteinSq` is the Bures expression, the squared
`W₂` distance between Gaussian laws with these means and covariances. -/
theorem sum_mul_ofReal_gaussianWassersteinSq_le (hw : ∑ j, w j = 1)
    [∀ j, IsProbabilityMeasure (μ j)] (hμ : ∀ j, MemLp id 2 (μ j)) (hS : S.PosDef)
    (hfix : S = ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * covMatrix (μ j) * CFC.sqrt S))
    (ν : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure ν] :
    ∑ j, (w j : ℝ≥0∞) * ENNReal.ofReal (gaussianWassersteinSq (∑ i, (w i : ℝ) • ∫ y, y ∂μ i)
        (∫ y, y ∂μ j) S (covMatrix (μ j))) ≤
      ∑ j, (w j : ℝ≥0∞) * wassersteinEDist 2 ν (μ j) ^ 2 := by
  -- The cost of `ν` dominates the multi-marginal cost `∫ F dγ` of some multi-coupling `γ`. By the
  -- weighted variance decomposition about `mbar`, that cost is
  -- `∑ i, w i * (‖m i - mbar‖ ^ 2 + tr C i)` minus the second moment of the centred weighted
  -- mean `W`, which is at most `tr S`.
  obtain ⟨γ, hγ, hle⟩ := exists_isMultiCoupling_lintegral_add_wassersteinEDist_sq_le hw μ ν
  refine le_trans ?_ (le_self_add.trans hle)
  set m : J → EuclideanSpace ℝ ι := fun j ↦ ∫ y, y ∂μ j
  set mbar := ∑ i, (w i : ℝ) • m i
  set F : (J → EuclideanSpace ℝ ι) → ℝ :=
    fun x ↦ ∑ i, (w i : ℝ) * ‖∑ j, (w j : ℝ) • x j - x i‖ ^ 2
  have hC (j : J) : (covMatrix (μ j)).PosSemidef := posSemidef_covMatrix _ (hμ j)
  -- The multi-marginal cost of `γ` as a real integral.
  have hlint : ∫⁻ x, ∑ i, (w i : ℝ≥0∞) * edist (∑ j, (w j : ℝ) • x j) (x i) ^ 2 ∂γ =
      ENNReal.ofReal (∫ x, F x ∂γ) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (hγ.integrable_sum_mul_norm_sum_smul_sub_sq hμ (fun i ↦ (w i : ℝ)) fun j ↦ (w j : ℝ))
      (.of_forall fun x ↦ by positivity)]
    refine lintegral_congr fun x ↦ ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [edist_dist, dist_eq_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (w i).coe_nonneg]
  have hIF := hγ.integral_sum_mul_norm_sum_smul_sub_sq hμ (w := fun j ↦ (w j : ℝ))
    (by exact_mod_cast hw)
  have hg := sum_mul_gaussianWassersteinSq_eq hw m (fun j ↦ covMatrix (μ j)) hfix
  have hvar := integral_norm_sum_smul_sub_integral_sq_le hμ hS hfix hγ
  rw [hlint]
  calc ∑ j, (w j : ℝ≥0∞) *
        ENNReal.ofReal (gaussianWassersteinSq mbar (m j) S (covMatrix (μ j)))
      = ENNReal.ofReal
          (∑ j, (w j : ℝ) * gaussianWassersteinSq mbar (m j) S (covMatrix (μ j))) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ ↦
          mul_nonneg (w j).coe_nonneg (gaussianWassersteinSq_nonneg hS (hC j) _ _)]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [ENNReal.ofReal_mul (w j).coe_nonneg, ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal (∫ x, F x ∂γ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hg, hIF]
        linarith

/-- **Gaussian barycenters from the fixed-point equation.** Let `C j` be positive-semidefinite
covariance matrices, `w j` nonnegative weights summing to `1`, and let the positive-definite
matrix `S` solve `S = ∑ j, w j • (S^(1/2) * C j * S^(1/2))^(1/2)`. Then the Gaussian law with mean
`∑ j, w j • m j` and covariance `S` is a quadratic Fréchet barycenter in `P₂` of the Gaussian laws
with means `m j` and covariances `C j`, weighted by `w j`. -/
theorem Probability.isFrechetBarycenter_sum_smul_dirac_multivariateGaussian (hw : ∑ j, w j = 1)
    (m : J → EuclideanSpace ℝ ι) {C : J → Matrix ι ι ℝ} (hC : ∀ j, (C j).PosSemidef)
    (hS : S.PosDef) (hfix : S = ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S)) :
    IsFrechetBarycenter 2 (∑ j, w j • Measure.dirac (gaussianWassersteinLaw (m j) (C j)))
      (gaussianWassersteinLaw (∑ j, (w j : ℝ) • m j) S) := by
  rw [WassersteinSpace.isFrechetBarycenter_sum_smul_dirac_iff_isMinOn (p := 2)
    ENNReal.ofNat_ne_top, isMinOn_univ_iff]
  intro z
  have key := sum_mul_ofReal_gaussianWassersteinSq_le
    (μ := fun j ↦ multivariateGaussian (m j) (C j)) hw (fun j ↦ IsGaussian.memLp_two_id) hS
    (by simpa only [covMatrix_multivariateGaussian _ (hC _)] using hfix)
    ((z : ProbabilityMeasure (EuclideanSpace ℝ ι)) : Measure (EuclideanSpace ℝ ι))
  simp only [integral_id_multivariateGaussian, covMatrix_multivariateGaussian _ (hC _)] at key
  simp only [gaussianWassersteinLaw_coe, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ ↦ ?_) key
  rw [← ENNReal.rpow_two, wassersteinEDist_two_multivariateGaussian_rpow_two hS (hC j)]

/-- **The unique Gaussian barycenter.** Under the hypotheses of
`TauCeti.Probability.isFrechetBarycenter_sum_smul_dirac_multivariateGaussian`, if moreover one
input law with a positive weight has a positive-definite covariance, then the Gaussian law with
mean `∑ j, w j • m j` and covariance `S` is the only quadratic Fréchet barycenter in `P₂`. -/
theorem Probability.frechetBarycenters_sum_smul_dirac_multivariateGaussian (hw : ∑ j, w j = 1)
    (m : J → EuclideanSpace ℝ ι) {C : J → Matrix ι ι ℝ} (hC : ∀ j, (C j).PosSemidef) {j₀ : J}
    (hj₀ : w j₀ ≠ 0) (hCj₀ : (C j₀).PosDef) (hS : S.PosDef)
    (hfix : S = ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S)) :
    frechetBarycenters 2 (∑ j, w j • Measure.dirac (gaussianWassersteinLaw (m j) (C j))) =
      {gaussianWassersteinLaw (∑ j, (w j : ℝ) • m j) S} := by
  refine (WassersteinSpace.subsingleton_frechetBarycenters_two_sum_smul_dirac
    (ρ := (volume : Measure (EuclideanSpace ℝ ι))) hj₀ ?_).eq_singleton_of_mem
      (mem_frechetBarycenters.2
        (isFrechetBarycenter_sum_smul_dirac_multivariateGaussian hw m hC hS hfix))
  rw [gaussianWassersteinLaw_coe, multivariateGaussian_eq_withDensity hCj₀]
  exact withDensity_absolutelyContinuous _ _

/-- **The Gaussian barycenter.** Let `w j` be nonnegative weights summing to `1`, and let one of
the Gaussian laws `N(m j, C j)` with a positive weight be nondegenerate. Then their quadratic
Wasserstein barycenter in `P₂` is unique. It is the Gaussian law with mean `∑ j, w j • m j` and
positive-definite covariance `S`, where `S` solves the fixed-point equation
`S = ∑ j, w j • (S^(1/2) * C j * S^(1/2))^(1/2)`. -/
theorem Probability.exists_posDef_frechetBarycenters_sum_smul_dirac_multivariateGaussian
    (hw : ∑ j, w j = 1) (m : J → EuclideanSpace ℝ ι) {C : J → Matrix ι ι ℝ}
    (hC : ∀ j, (C j).PosSemidef) {j₀ : J} (hj₀ : w j₀ ≠ 0) (hCj₀ : (C j₀).PosDef) :
    ∃ S : Matrix ι ι ℝ, S.PosDef ∧
      S = ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S) ∧
      frechetBarycenters 2 (∑ j, w j • Measure.dirac (gaussianWassersteinLaw (m j) (C j))) =
        {gaussianWassersteinLaw (∑ j, (w j : ℝ) • m j) S} := by
  obtain ⟨S, hS, hfix⟩ := Matrix.exists_posDef_eq_sum_smul_sqrt_sqrt_mul_mul_sqrt w hC hj₀ hCj₀
  exact ⟨S, hS, hfix,
    frechetBarycenters_sum_smul_dirac_multivariateGaussian hw m hC hj₀ hCj₀ hS hfix⟩

end Gaussian

open scoped Classical in
/-- **The fixed-point equation has exactly one positive-definite solution.** Let `C j` be
positive-semidefinite matrices and `w j` nonnegative weights summing to `1`, and suppose that some
`C j₀` with `w j₀ ≠ 0` is positive definite. Then exactly one positive-definite matrix `S` solves
`S = ∑ j, w j • (S^(1/2) * C j * S^(1/2))^(1/2)`: it is the covariance of the unique quadratic
Wasserstein barycenter of the Gaussian laws with covariances `C j`. -/
theorem existsUnique_posDef_eq_sum_smul_sqrt_sqrt_mul_mul_sqrt (hw : ∑ j, w j = 1)
    {C : J → Matrix ι ι ℝ} (hC : ∀ j, (C j).PosSemidef) {j₀ : J} (hj₀ : w j₀ ≠ 0)
    (hCj₀ : (C j₀).PosDef) :
    ∃! S : Matrix ι ι ℝ, S.PosDef ∧
      S = ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S) := by
  classical
  obtain ⟨S, hS, hfix⟩ := Matrix.exists_posDef_eq_sum_smul_sqrt_sqrt_mul_mul_sqrt w hC hj₀ hCj₀
  refine ⟨S, ⟨hS, hfix⟩, fun T ⟨hT, hfixT⟩ ↦ ?_⟩
  -- Both Gaussian laws are the unique barycenter, so their covariances agree.
  have h := Set.singleton_eq_singleton_iff.1
    ((Probability.frechetBarycenters_sum_smul_dirac_multivariateGaussian hw 0 hC hj₀ hCj₀ hT
      hfixT).symm.trans
      (Probability.frechetBarycenters_sum_smul_dirac_multivariateGaussian hw 0 hC hj₀ hCj₀ hS hfix))
  have hcov := congrArg
    (fun ν : WassersteinSpace 2 (EuclideanSpace ℝ ι) ↦
      covMatrix ((ν.toProbabilityMeasure : ProbabilityMeasure (EuclideanSpace ℝ ι)) :
        Measure (EuclideanSpace ℝ ι))) h
  simpa only [Probability.gaussianWassersteinLaw_coe,
    Probability.covMatrix_multivariateGaussian _ hT.posSemidef,
    Probability.covMatrix_multivariateGaussian _ hS.posSemidef] using hcov

end TauCeti
