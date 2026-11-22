/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Constant
public import TauCeti.Probability.Distributions.Gaussian.Isotropic
public import TauCeti.Probability.Distributions.StudentT.ChiSquared

/-!
# Sample mean and residuals of a Gaussian sample

Orthogonally projecting a sample vector onto the constant vectors gives the sample mean in
each coordinate. The projection onto the orthogonal complement is the residual vector.
These projections give the independence of the sample mean and residuals and the chi-squared
law for the residual sum of squares. Normalizing the mean by the estimated standard error
then gives Student's statistic.

## References

* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Theorem 5.3.1 and §5.3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The sum of squared deviations of a real sample from its mean. -/
def residualSumSquares (x : ι → ℝ) : ℝ :=
  ∑ i, (x i - finiteMean ℝ x) ^ 2

theorem residualSumSquares_def (x : ι → ℝ) :
    residualSumSquares x = ∑ i, (x i - finiteMean ℝ x) ^ 2 :=
  (rfl)

/-- The residual sum of squares varies continuously with the sample. -/
@[fun_prop]
theorem continuous_residualSumSquares : Continuous (residualSumSquares : (ι → ℝ) → ℝ) := by
  unfold residualSumSquares
  fun_prop

/-- A sample's residual sum of squares is nonnegative. -/
theorem residualSumSquares_nonneg (x : ι → ℝ) : 0 ≤ residualSumSquares x := by
  unfold residualSumSquares
  positivity

/-- The residual sum of squares vanishes exactly when every entry equals the sample mean. -/
@[simp]
theorem residualSumSquares_eq_zero_iff (x : ι → ℝ) :
    residualSumSquares x = 0 ↔ ∀ i, x i = finiteMean ℝ x := by
  simp [residualSumSquares_def, Finset.sum_sq_eq_zero_iff, sub_eq_zero]

/-- With two observations the residual sum of squares is half the squared difference. -/
theorem residualSumSquares_fin_two (x : Fin 2 → ℝ) :
    residualSumSquares x = (x 0 - x 1) ^ 2 / 2 := by
  norm_num [residualSumSquares_def, finiteMean_eq_inv_smul_sum, Fin.sum_univ_two]
  ring

/-- The Student statistic for a sample mean centered at `m` uses residual degrees of freedom
`card ι - 1` and Lean's totalized division. -/
def studentizedMean (m : ℝ) (x : ι → ℝ) : ℝ :=
  Real.sqrt (Fintype.card ι : ℝ) * (finiteMean ℝ x - m) /
    Real.sqrt (residualSumSquares x / (Fintype.card ι - 1 : ℕ))

theorem studentizedMean_def (m : ℝ) (x : ι → ℝ) :
    studentizedMean m x = Real.sqrt (Fintype.card ι : ℝ) * (finiteMean ℝ x - m) /
      Real.sqrt (residualSumSquares x / (Fintype.card ι - 1 : ℕ)) :=
  (rfl)

/-- Student's statistic is measurable, including on samples with zero residual sum of squares. -/
@[fun_prop]
theorem measurable_studentizedMean (m : ℝ) : Measurable (studentizedMean m : (ι → ℝ) → ℝ) := by
  unfold studentizedMean
  fun_prop

private abbrev ones : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ ↦ 1)

/-- The squared norm of the projection perpendicular to the constants is the residual sum
of squares. -/
theorem _root_.EuclideanSpace.norm_sq_starProjection_orthogonal_span_const
    (x : EuclideanSpace ℝ ι) :
    ‖(ℝ ∙ WithLp.toLp 2 (fun _ ↦ 1)).orthogonal.starProjection x‖ ^ 2 =
      residualSumSquares x.ofLp := by
  rw [Submodule.starProjection_orthogonal_val, EuclideanSpace.starProjection_span_const,
    EuclideanSpace.real_norm_sq_eq]
  simp [residualSumSquares]

end TauCeti

namespace ProbabilityTheory

open TauCeti TauCeti.Probability

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → (ι → ℝ)} {m : ℝ} {v : ℝ≥0}

private theorem hasLaw_toLp_gaussianSample [DecidableEq ι]
    (hX : HasLaw X (Measure.pi fun _ : ι ↦ gaussianReal m v) P) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (X ω))
      (multivariateGaussian (m • (ones : EuclideanSpace ℝ ι))
        ((v : ℝ) • (1 : Matrix ι ι ℝ))) P := by
  refine (HasLaw.mk (X := WithLp.toLp 2) (by fun_prop) ?_).fun_comp hX
  simpa [ones] using
    (m • (ones : EuclideanSpace ℝ ι)).map_pi_gaussianReal_eq_multivariateGaussian v

/-- Standardizing the coordinates of a Gaussian sample gives a standard Gaussian vector. -/
theorem HasLaw.standardize_gaussianSample
    (hX : HasLaw X (Measure.pi fun _ : ι ↦ gaussianReal m v) P) (hv : 0 < v) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (fun i ↦ (X ω i - m) / Real.sqrt v))
      (stdGaussian (EuclideanSpace ℝ ι)) P := by
  classical
  have h := hasLaw_toLp_gaussianSample hX
  rw [← Real.sq_sqrt (NNReal.coe_nonneg (r := v))] at h
  refine (h.standardize_multivariateGaussian_smul_one (by positivity)).congr ?_
  exact Filter.Eventually.of_forall fun ω ↦ by
    ext i
    simp [ones, div_eq_inv_mul]

/-- The sample mean is independent of the residual vector. This holds also for a zero
sampling variance or an empty sample. -/
theorem HasLaw.indepFun_finiteMean_residuals_gaussianSample
    (hX : HasLaw X (Measure.pi fun _ : ι ↦ gaussianReal m v) P) :
    IndepFun (fun ω ↦ finiteMean ℝ (X ω))
      (fun ω i ↦ X ω i - finiteMean ℝ (X ω)) P := by
  classical
  let K : Submodule ℝ (EuclideanSpace ℝ ι) := ℝ ∙ ones
  have h := hasLaw_toLp_gaussianSample hX
  rw [← Real.sq_sqrt (NNReal.coe_nonneg (r := v))] at h
  have hind := h.indepFun_orthogonalProjectionOnto_multivariateGaussian_smul_one
    K.isOrtho_orthogonal_right
  refine (hind.comp (φ := fun x : K ↦ finiteMean ℝ (x : EuclideanSpace ℝ ι).ofLp)
    (ψ := fun y : Kᗮ ↦ (y : EuclideanSpace ℝ ι).ofLp) (by fun_prop) (by fun_prop)).congr ?_ ?_
  · exact Filter.Eventually.of_forall fun ω ↦ by
      simpa only [Function.comp_apply, Submodule.starProjection_apply, WithLp.ofLp_toLp, K] using
        EuclideanSpace.finiteMean_starProjection_span_const (WithLp.toLp 2 (X ω))
  · exact Filter.Eventually.of_forall fun ω ↦ by
      simp only [Function.comp_apply, ← Submodule.starProjection_apply,
        Submodule.starProjection_orthogonal_val, K, EuclideanSpace.starProjection_span_const,
        WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_def, Pi.smul_apply, smul_eq_mul,
        mul_one, ones]

/-- The sample mean is independent of the residual sum of squares. -/
theorem HasLaw.indepFun_finiteMean_residualSumSquares_gaussianSample
    (hX : HasLaw X (Measure.pi fun _ : ι ↦ gaussianReal m v) P) :
    IndepFun (fun ω ↦ finiteMean ℝ (X ω)) (fun ω ↦ residualSumSquares (X ω)) P :=
  hX.indepFun_finiteMean_residuals_gaussianSample.comp (φ := id)
    (ψ := fun r : ι → ℝ ↦ ∑ i, r i ^ 2) measurable_id (by fun_prop)

/-- The residual sum of squares divided by the positive sampling variance has chi-squared
law with one degree of freedom lost to estimating the mean. -/
theorem HasLaw.residualSumSquares_div_gaussianSample
    (hX : HasLaw X (Measure.pi fun _ : ι ↦ gaussianReal m v) P) (hv : 0 < v) :
    HasLaw (fun ω ↦ residualSumSquares (X ω) / v)
      (chiSquaredMeasure (Fintype.card ι - 1 : ℕ)) P := by
  classical
  let K : Submodule ℝ (EuclideanSpace ℝ ι) := ℝ ∙ ones
  have h := hasLaw_toLp_gaussianSample hX
  have hσ := Real.sq_sqrt (NNReal.coe_nonneg (r := v))
  rw [← hσ] at h
  have hSS := h.norm_sq_starProjection_sub_div_multivariateGaussian_smul_one (by positivity) Kᗮ
  rw [EuclideanSpace.finrank_orthogonal_span_const, hσ] at hSS
  refine hSS.congr (Filter.Eventually.of_forall fun ω ↦ ?_)
  have hm : m • (ones : EuclideanSpace ℝ ι) ∈ K :=
    K.smul_mem _ (Submodule.mem_span_singleton_self _)
  simp only [map_sub, Submodule.starProjection_orthogonal_apply_eq_zero hm, sub_zero,
    K, EuclideanSpace.norm_sq_starProjection_orthogonal_span_const]

/-- A Gaussian sample of at least two observations with positive variance has strictly
positive residual sum of squares almost surely. -/
theorem HasLaw.ae_pos_residualSumSquares_gaussianSample
    (hX : HasLaw X (Measure.pi fun _ : ι ↦ gaussianReal m v) P) (hv : 0 < v)
    (hι : 2 ≤ Fintype.card ι) :
    ∀ᵐ ω ∂P, 0 < residualSumSquares (X ω) := by
  have hdf : (0 : ℝ) < (Fintype.card ι - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  have hSS := hX.residualSumSquares_div_gaussianSample hv
  have hpos := (hSS.ae_iff (measurableSet_setOfPred.mp measurableSet_Ioi)).2
    (ae_pos_chiSquaredMeasure hdf)
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  exact hpos.mono fun _ h ↦ (div_pos_iff_of_pos_right hv').mp h

/-- The sampling error of the sample mean in units of its standard deviation is standard
normal. -/
theorem HasLaw.standardized_finiteMean_gaussianSample [Nonempty ι]
    (hX : HasLaw X (Measure.pi fun _ : ι ↦ gaussianReal m v) P) (hv : 0 < v) :
    HasLaw (fun ω ↦ Real.sqrt (Fintype.card ι : ℝ) * (finiteMean ℝ (X ω) - m) / Real.sqrt v)
      (gaussianReal 0 1) P := by
  classical
  let c := Real.sqrt (Fintype.card ι : ℝ)
  have hc : c ≠ 0 := by positivity
  have hc₀ : 0 ≤ c := by positivity
  let u : EuclideanSpace ℝ ι := c⁻¹ • ones
  have hnorm : ‖(ones : EuclideanSpace ℝ ι)‖ = c := by
    simpa [ones, c, Real.sqrt_eq_rpow, ← Function.const_def] using
      (PiLp.norm_toLp_const (ι := ι) (p := 2) (by simp) (1 : ℝ))
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, hnorm, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hc₀)]
    exact inv_mul_cancel₀ hc
  have hZ := hX.standardize_gaussianSample hv |>.strongDual_stdGaussian (innerSL ℝ u)
  rw [innerSL_apply_norm, hu] at hZ
  norm_num at hZ
  refine hZ.congr (Filter.Eventually.of_forall fun ω ↦ ?_)
  have hsum : ∑ i, (X ω i - m) = (Fintype.card ι : ℝ) * (finiteMean ℝ (X ω) - m) := by
    simpa only [finiteMean_sub_const, smul_eq_mul] using
      sum_eq_card_smul_finiteMean (R := ℝ) (fun i ↦ X ω i - m)
  have hcsq : c ^ 2 = (Fintype.card ι : ℝ) := Real.sq_sqrt (by positivity)
  have hcard : c⁻¹ * (Fintype.card ι : ℝ) = c := by
    rw [← hcsq, pow_two, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  simp only [u, ones, real_inner_smul_left, EuclideanSpace.inner_const_one_left, ← Finset.sum_div,
    hsum, ← mul_div_assoc, ← mul_assoc, hcard, c]

/-- Student's statistic from a Gaussian sample of size at least two has the Student law
with one fewer degree of freedom. -/
theorem HasLaw.studentizedMean_gaussianSample
    (hX : HasLaw X (Measure.pi fun _ : ι ↦ gaussianReal m v) P) (hv : 0 < v)
    (hι : 2 ≤ Fintype.card ι) :
    HasLaw (fun ω ↦ studentizedMean m (X ω)) (studentTMeasure (Fintype.card ι - 1 : ℕ)) P := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hdf : (0 : ℝ) < (Fintype.card ι - 1 : ℕ) := Nat.cast_pos.mpr (by omega)
  have hind := hX.indepFun_finiteMean_residualSumSquares_gaussianSample.comp
    (φ := fun x ↦ Real.sqrt (Fintype.card ι : ℝ) * (x - m) / Real.sqrt v)
    (ψ := fun s ↦ s / (v : ℝ)) (by fun_prop) (by fun_prop)
  refine (hasLaw_studentT_of_gaussian_chiSquared hdf hind
    (hX.standardized_finiteMean_gaussianSample hv)
    (hX.residualSumSquares_div_gaussianSample hv)).congr ?_
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  simp only [Function.comp_apply, studentizedMean_def]
  have he : residualSumSquares (X ω) / (v : ℝ) / (Fintype.card ι - 1 : ℕ) =
      residualSumSquares (X ω) / (Fintype.card ι - 1 : ℕ) / (v : ℝ) :=
    div_right_comm _ _ _
  have hs : 0 ≤ residualSumSquares (X ω) / (Fintype.card ι - 1 : ℕ) :=
    div_nonneg (residualSumSquares_nonneg _) (by positivity)
  rw [he, Real.sqrt_div hs, div_div_eq_mul_div]
  have hσ : Real.sqrt (v : ℝ) ≠ 0 := by positivity
  simp only [div_mul_cancel₀ _ hσ]

end ProbabilityTheory
