/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Gaussian.Barycenter
public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Barycenter
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Barycenter.Uniqueness.Euclidean
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.FrechetMean
public import TauCeti.Probability.Moments.Covariance
import TauCeti.Analysis.Matrix.CovariancePseudoInverse
import TauCeti.Analysis.Matrix.GeometricMean
import TauCeti.MeasureTheory.Function.L2Space
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
average to the identity. Averaging the quadratic Fenchel–Young inequalities
`⟪u, y⟫ ≤ (⟪A j y, y⟫ + ⟪(A j)⁺ u, u⟫) / 2`, in mean over a multi-coupling of the laws `μ j`,
bounds the variance of the weighted mean of the coupling by `tr S`; the weighted variance
decomposition and the multi-marginal formulation of the barycenter problem turn this into the
lower bound. Singular covariances `C j` are allowed: the pseudoinverse `(A j)⁺` is used on the
range of `A j`, which carries the centred `j`th coordinate almost surely.

## Main statements

* `TauCeti.integral_inner_sub_integral_le`: the quadratic Fenchel–Young inequality in mean, for a
  random vector whose covariance has the form `A * T * A`.
* `Matrix.PosDef.sum_smul_geometricMean_ringInverse_eq_one_iff`: the fixed-point equation holds
  exactly when the matrices `geometricMean S⁻¹ʳ (C j)` average to the identity.
* `TauCeti.integral_norm_sum_smul_sub_integral_sq_le`: the centred weighted mean of a
  multi-coupling has second moment at most `tr S`.
* `TauCeti.sum_mul_ofReal_gaussianWassersteinSq_le`: the Gaussian lower bound for the
  barycentric cost of arbitrary laws with finite second moments.
* `TauCeti.Probability.isFrechetBarycenter_sum_smul_dirac_multivariateGaussian`: the Gaussian law
  with mean `mbar` and covariance `S` is a barycenter of Gaussian laws.
* `TauCeti.Probability.frechetBarycenters_sum_smul_dirac_multivariateGaussian`: it is the unique
  barycenter when an input with positive weight is nondegenerate.

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

section FenchelYoung

variable [DecidableEq ι]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → EuclideanSpace ℝ ι}

/-- **The quadratic Fenchel–Young inequality in mean.** Let `X` and `Y` be square-integrable
random vectors, where the law of `X` has covariance matrix `A * T * A` for a positive-semidefinite
matrix `A`. Then the correlation of the centred variable `X - 𝔼 X` with `Y` is at most
`(𝔼 ⟪A Y, Y⟫ + tr (A * T)) / 2`. -/
theorem integral_inner_sub_integral_le (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    {A T : Matrix ι ι ℝ} (hA : A.PosSemidef) (hcov : covMatrix (P.map X) = A * T * A) :
    ∫ ω, ⟪X ω - ∫ ω', X ω' ∂P, Y ω⟫ ∂P ≤
      (∫ ω, ⟪A.toEuclideanLin (Y ω), Y ω⟫ ∂P + (A * T).trace) / 2 := by
  set m := ∫ ω', X ω' ∂P
  set D := A.covariancePseudoInverse
  have hXm : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
  have hU : MemLp (fun ω ↦ X ω - m) 2 P := hX.sub (memLp_const m)
  -- Means of quadratic forms of the centred variable are traces against `A * T * A`.
  have htr (B : Matrix ι ι ℝ) :
      ∫ ω, ⟪B.toEuclideanLin (X ω - m), X ω - m⟫ ∂P = (B * (A * T * A)).trace := by
    have hmap : MemLp id 2 (P.map X) :=
      (memLp_map_measure_iff aestronglyMeasurable_id hXm).2 hX
    have hmean : ∫ y, y ∂(P.map X) = m := integral_map hXm aestronglyMeasurable_id
    rw [← hcov, ← integral_inner_toEuclideanLin_sub_integral_eq_trace_mul_covMatrix _ hmap,
      hmean, integral_map hXm (by fun_prop)]
  have hBint (B : Matrix ι ι ℝ) {Z : Ω → EuclideanSpace ℝ ι} (hZ : MemLp Z 2 P) :
      Integrable (fun ω ↦ ⟪B.toEuclideanLin (Z ω), Z ω⟫) P :=
    (hZ.continuousLinearMap_comp
      (LinearMap.toContinuousLinearMap B.toEuclideanLin)).integrable_inner hZ
  have hsa : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.2 hA.isHermitian
  have hsd : D.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.2 (A.posSemidef_covariancePseudoInverse).isHermitian
  have hpos : A.toEuclideanLin.IsPositive := Matrix.isPositive_toEuclideanLin_iff.2 hA
  have hdad (x : EuclideanSpace ℝ ι) :
      D.toEuclideanLin (A.toEuclideanLin (D.toEuclideanLin x)) = D.toEuclideanLin x := by
    simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] using
      congrArg (fun M : Matrix ι ι ℝ ↦ M.toEuclideanLin x) A.covariancePseudoInverse_mul_self_mul
  -- The centred variable lies almost surely in the range of `A`: with `R = 1 - A * D`, the mean
  -- of `‖R (X - m)‖ ^ 2` is the trace of `Rᴴ * R * (A * T * A)`, and `R * A = 0`.
  set R : Matrix ι ι ℝ := 1 - A * D
  have hRA : R * A = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_covariancePseudoInverse_mul hA, sub_self]
  have hR (x : EuclideanSpace ℝ ι) :
      R.toEuclideanLin x = x - A.toEuclideanLin (D.toEuclideanLin x) := by
    simp [R, Matrix.toLpLin_mul_same]
  have hRR (x : EuclideanSpace ℝ ι) :
      ⟪(Rᴴ * R).toEuclideanLin x, x⟫ = ‖R.toEuclideanLin x‖ ^ 2 := by
    rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq]
  have hrange : ∀ᵐ ω ∂P, A.toEuclideanLin (D.toEuclideanLin (X ω - m)) = X ω - m := by
    have hsq : ∫ ω, ‖R.toEuclideanLin (X ω - m)‖ ^ 2 ∂P = 0 := by
      have h := htr (Rᴴ * R)
      rw [show Rᴴ * R * (A * T * A) = Rᴴ * (R * A) * (T * A) by noncomm_ring, hRA,
        Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero] at h
      simpa only [hRR] using h
    have hint : Integrable (fun ω ↦ ‖R.toEuclideanLin (X ω - m)‖ ^ 2) P := by
      simpa only [hRR] using hBint (Rᴴ * R) hU
    have hae := (integral_eq_zero_iff_of_nonneg (fun ω ↦ by positivity) hint).1 hsq
    filter_upwards [hae] with ω hω
    have : R.toEuclideanLin (X ω - m) = 0 := by simpa using hω
    rw [hR] at this
    exact (sub_eq_zero.1 this).symm
  -- On the range of `A`, the pointwise inequality is `0 ≤ ⟪A (D u - y), D u - y⟫`.
  have hpt : ∀ᵐ ω ∂P, ⟪X ω - m, Y ω⟫ ≤
      (⟪A.toEuclideanLin (Y ω), Y ω⟫ + ⟪D.toEuclideanLin (X ω - m), X ω - m⟫) / 2 := by
    filter_upwards [hrange] with ω hω
    set u := X ω - m
    set y := Y ω
    set v := D.toEuclideanLin u
    have h0 : 0 ≤ ⟪A.toEuclideanLin (v - y), v - y⟫ := by
      simpa only [RCLike.re_to_real] using hpos.re_inner_nonneg_left (v - y)
    have hvv : ⟪A.toEuclideanLin v, v⟫ = ⟪v, u⟫ := by
      rw [← hsd, hdad]
    have huy : ⟪u, y⟫ = ⟪A.toEuclideanLin v, y⟫ := by rw [hω]
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hvv, hsa y v,
      real_inner_comm (A.toEuclideanLin v) y] at h0
    linarith
  have htrace : (D * (A * T * A)).trace = (A * T).trace := by
    rw [Matrix.trace_mul_comm D, show A * T * A * D = A * T * (A * D) by noncomm_ring,
      Matrix.trace_mul_comm (A * T), show A * D * (A * T) = A * D * A * T by noncomm_ring,
      Matrix.mul_covariancePseudoInverse_mul hA]
  calc ∫ ω, ⟪X ω - m, Y ω⟫ ∂P
      ≤ ∫ ω, (⟪A.toEuclideanLin (Y ω), Y ω⟫ + ⟪D.toEuclideanLin (X ω - m), X ω - m⟫) / 2 ∂P :=
        integral_mono_ae (hU.integrable_inner hY) (((hBint A hY).add (hBint D hU)).div_const 2)
          hpt
    _ = (∫ ω, ⟪A.toEuclideanLin (Y ω), Y ω⟫ ∂P + (A * T).trace) / 2 := by
        rw [integral_div, integral_add (hBint A hY) (hBint D hU), htr D, htrace]

end FenchelYoung

variable {J : Type*} [Fintype J]

/-- **The fixed-point equation as an averaging condition.** For a positive-definite `S`, the
standard positive matrices `geometricMean S⁻¹ʳ (C j)`, which solve `A * S * A = C j` when `C j` is
positive semidefinite, average to the identity with weights `w j` exactly when `S` solves the
Gaussian barycenter equation `S = ∑ j, w j • (S^(1/2) * C j * S^(1/2))^(1/2)`. -/
theorem _root_.Matrix.PosDef.sum_smul_geometricMean_ringInverse_eq_one_iff [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosDef) (w : J → ℝ) (C : J → Matrix ι ι ℝ) :
    ∑ j, w j • geometricMean S⁻¹ʳ (C j) = 1 ↔
      S = ∑ j, w j • CFC.sqrt (CFC.sqrt S * C j * CFC.sqrt S) := by
  set R := CFC.sqrt S
  set N := ∑ j, w j • CFC.sqrt (R * C j * R)
  let _ : Invertible R := (hS.isStrictlyPositive.isUnit_cfcSqrt S).invertible
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hsum : ∑ j, w j • geometricMean S⁻¹ʳ (C j) = R⁻¹ * N * R⁻¹ := by
    simp only [hS.geometricMean_ringInverse_eq_sqrt_mul_mul_sqrt, N, Finset.mul_sum,
      Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, R]
  rw [hsum, ← hRR]
  constructor
  · intro h
    calc R * R = R * (R⁻¹ * N * R⁻¹) * R := by
          rw [h, Matrix.mul_one]
      _ = N := by
          simp only [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul,
            Matrix.mul_assoc N, Matrix.inv_mul_of_invertible, Matrix.mul_one]
  · intro h
    rw [← h, Matrix.mul_assoc, Matrix.mul_assoc R, Matrix.mul_inv_of_invertible, Matrix.mul_one,
      Matrix.inv_mul_of_invertible]

variable {w : J → ℝ≥0} {μ : J → Measure (EuclideanSpace ℝ ι)} {S : Matrix ι ι ℝ}

open scoped Classical in
/-- **The variance of the weighted mean of a multi-coupling.** Let `μ j` be probability laws on
`ℝⁿ` with finite second moments, means `m j` and covariance matrices `C j`, let `w j` be
nonnegative weights, and let the positive-definite matrix `S` solve
`S = ∑ j, w j • (S^(1/2) * C j * S^(1/2))^(1/2)`. Then under every multi-coupling of the laws
`μ j`, the centred weighted mean `∑ j, w j • (x j - m j)` has second moment at most `tr S`. -/
theorem integral_norm_sum_smul_sub_integral_sq_le [∀ j, IsProbabilityMeasure (μ j)]
    (hμ : ∀ j, MemLp id 2 (μ j)) (hS : S.PosDef)
    (hfix : S = ∑ j, (w j : ℝ) • CFC.sqrt (CFC.sqrt S * covMatrix (μ j) * CFC.sqrt S))
    {γ : Measure (J → EuclideanSpace ℝ ι)} (hγ : Measure.IsMultiCoupling γ μ) :
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
  have hW : MemLp W 2 γ :=
    memLp_finsetSum _ fun j _ ↦ ((hcoord j).sub (memLp_const (m j))).const_smul (w j : ℝ)
  -- The quadratic Fenchel–Young inequality for the `j`th coordinate against `W`.
  have hFY (j : J) : ∫ x, ⟪x j - m j, W x⟫ ∂γ ≤
      (∫ x, ⟪(A j).toEuclideanLin (W x), W x⟫ ∂γ + (A j * S).trace) / 2 := by
    have hcov : covMatrix (γ.map fun x ↦ x j) = A j * S * A j := by
      rw [show (γ.map fun x ↦ x j) = μ j from hγ.marginal_eq j,
        geometricMean_ringInverse_mul_mul_geometricMean_ringInverse hS.isStrictlyPositive
          (posSemidef_covMatrix _ (hμ j)).nonneg]
    simpa only [hmean] using integral_inner_sub_integral_le (hcoord j) hW (hA j) hcov
  have hint (j : J) : Integrable (fun x ↦ ⟪x j - m j, W x⟫) γ :=
    ((hcoord j).sub (memLp_const _)).integrable_inner hW
  have hAint (j : J) : Integrable (fun x ↦ ⟪(A j).toEuclideanLin (W x), W x⟫) γ :=
    (hW.continuousLinearMap_comp
      (LinearMap.toContinuousLinearMap (A j).toEuclideanLin)).integrable_inner hW
  -- Average the inequalities: the matrices `A j` average to the identity.
  have hsq (x : J → EuclideanSpace ℝ ι) : ‖W x‖ ^ 2 = ∑ j, (w j : ℝ) * ⟪x j - m j, W x⟫ := by
    calc ‖W x‖ ^ 2 = ⟪∑ j, (w j : ℝ) • (x j - m j), W x⟫ := (real_inner_self_eq_norm_sq _).symm
      _ = _ := by simp only [sum_inner, real_inner_smul_left]
  have hquad (x : J → EuclideanSpace ℝ ι) :
      ∑ j, (w j : ℝ) * ⟪(A j).toEuclideanLin (W x), W x⟫ = ‖W x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa [map_sum, map_smul, sum_inner, real_inner_smul_left] using
      congrArg (fun M : Matrix ι ι ℝ ↦ ⟪M.toEuclideanLin (W x), W x⟫) hAone
  have htrace : ∑ j, (w j : ℝ) * (A j * S).trace = S.trace := by
    simpa [Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul] using
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
  obtain ⟨j₀, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hw.trans_ne one_ne_zero)
  have := hγ.isProbabilityMeasure j₀
  set m : J → EuclideanSpace ℝ ι := fun j ↦ ∫ y, y ∂μ j
  set mbar := ∑ i, (w i : ℝ) • m i
  set W : (J → EuclideanSpace ℝ ι) → EuclideanSpace ℝ ι := fun x ↦ ∑ j, (w j : ℝ) • (x j - m j)
  set F : (J → EuclideanSpace ℝ ι) → ℝ :=
    fun x ↦ ∑ i, (w i : ℝ) * ‖∑ j, (w j : ℝ) • x j - x i‖ ^ 2
  have hw' : ∑ j, (w j : ℝ) = 1 := by exact_mod_cast hw
  have hcoord (j : J) : MemLp (fun x : J → EuclideanSpace ℝ ι ↦ x j) 2 γ :=
    hγ.memLp_comp_eval j (hμ j)
  have hC (j : J) : (covMatrix (μ j)).PosSemidef := posSemidef_covMatrix _ (hμ j)
  -- The weighted variance decomposition about `mbar`.
  have hF (x : J → EuclideanSpace ℝ ι) :
      F x = ∑ i, (w i : ℝ) * ‖x i - mbar‖ ^ 2 - ‖W x‖ ^ 2 := by
    have h := Finset.univ.sum_mul_norm_sub_sq_eq hw' mbar x
    have hWx : W x = ∑ j, (w j : ℝ) • x j - mbar := by
      simp only [W, mbar, smul_sub, Finset.sum_sub_distrib]
    simp only [norm_sub_rev mbar] at h
    rw [hWx]
    linarith
  have hsq (i : J) : Integrable (fun x : J → EuclideanSpace ℝ ι ↦ ‖x i - mbar‖ ^ 2) γ :=
    have hi := (hcoord i).sub (memLp_const mbar)
    (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).1 hi
  have hW : MemLp W 2 γ :=
    memLp_finsetSum _ fun j _ ↦ ((hcoord j).sub (memLp_const (m j))).const_smul (w j : ℝ)
  have hWsq : Integrable (fun x ↦ ‖W x‖ ^ 2) γ :=
    (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).1 hW
  have hFint : Integrable F γ := by
    rw [show F = fun x ↦ ∑ i, (w i : ℝ) * ‖x i - mbar‖ ^ 2 - ‖W x‖ ^ 2 from funext hF]
    exact (integrable_finsetSum _ fun i _ ↦ (hsq i).const_mul _).sub hWsq
  -- The multi-marginal cost of `γ` as a real integral.
  have hlint : ∫⁻ x, ∑ i, (w i : ℝ≥0∞) * edist (∑ j, (w j : ℝ) • x j) (x i) ^ 2 ∂γ =
      ENNReal.ofReal (∫ x, F x ∂γ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hFint (.of_forall fun x ↦ by positivity)]
    refine lintegral_congr fun x ↦ ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [edist_dist, dist_eq_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (w i).coe_nonneg]
  have hIF : ∫ x, F x ∂γ =
      ∑ i, (w i : ℝ) * (‖m i - mbar‖ ^ 2 + (covMatrix (μ i)).trace) - ∫ x, ‖W x‖ ^ 2 ∂γ := by
    rw [integral_congr_ae (.of_forall hF), integral_sub
      (integrable_finsetSum _ fun i _ ↦ (hsq i).const_mul _) hWsq,
      integral_finsetSum _ fun i _ ↦ (hsq i).const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_const_mul, hγ.integral_comp_eval i (f := fun y ↦ ‖y - mbar‖ ^ 2)
      (by fun_prop), integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix _ (hμ i)]
  have hg := sum_mul_gaussianWassersteinSq_eq hw m (fun j ↦ covMatrix (μ j)) hfix
  have hvar : ∫ x, ‖W x‖ ^ 2 ∂γ ≤ S.trace :=
    integral_norm_sum_smul_sub_integral_sq_le hμ hS hfix hγ
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

end TauCeti
