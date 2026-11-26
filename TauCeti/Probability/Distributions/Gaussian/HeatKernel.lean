/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Basic
public import TauCeti.Probability.Distributions.Gaussian.Density

import TauCeti.Analysis.PDE.HeatKernel.Bounds

/-!
# The isotropic Gaussian density is the heat kernel

For `v > 0` the isotropic Gaussian law `N(m, v • 1)` on `EuclideanSpace ℝ ι` has density
`(2πv)^(-d/2) exp(-‖y - m‖² / (2v))`, which is the heat kernel at time `v / 2` evaluated at
`y - m`. Through this identification the heat-kernel results apply to Gaussian densities: the
density is smooth and all of its derivatives are bounded. Its gradient is `-v⁻¹ φ(y) (y - m)`,
so the score of `N(m, v • 1)` is `-(y - m) / v`.

## Main results

* `TauCeti.Probability.multivariateGaussianPDFReal_smul_one`: the density of `N(m, v • 1)` at `y`
  is `heatKernel (v / 2) (y - m)`.
* `TauCeti.Probability.multivariateGaussianPDFReal_zero_smul_one`: the density of `N(0, v • 1)` is
  `heatKernel (v / 2)`.
* `TauCeti.Probability.multivariateGaussian_smul_one_eq_withDensity_heatKernel`: `N(m, v • 1)` is
  Lebesgue measure weighted by this translated heat kernel.
* `TauCeti.Probability.contDiff_multivariateGaussianPDFReal_smul_one` and
  `TauCeti.Probability.exists_norm_iteratedFDeriv_multivariateGaussianPDFReal_smul_one_le`: the
  density of `N(m, v • 1)` is smooth and all of its derivatives are bounded.
* `TauCeti.Probability.exists_one_add_norm_pow_mul_multivariateGaussianPDFReal_smul_one_le`: the
  density of `N(0, v • 1)` absorbs every polynomial weight `(1 + ‖z‖)^k`.
* `TauCeti.Probability.integrable_multivariateGaussianPDFReal_sub_smul` and
  `TauCeti.Probability.integrable_multivariateGaussianPDFReal_sub_smul_smul`: against a finite
  measure, `x ↦ φ(y - c • x)`, also times any continuous function of at most polynomial growth of
  `y - c • x`, is integrable, for `φ` the density of `N(0, s² • 1)`.
* `TauCeti.Probability.hasGradientAt_multivariateGaussianPDFReal_smul_one`: the density `φ` of
  `N(m, v • 1)` has gradient `-v⁻¹ φ(y) (y - m)`, so its score is `-(y - m) / v`.
* `TauCeti.Probability.hasFDerivAt_multivariateGaussianPDFReal_smul_one_smul_self`: for the density
  `φ` of `N(0, v • 1)`, the derivative of `z ↦ φ(z) z` is `φ(z) (1 - z ⊗ z / v)`.
* `TauCeti.Probability.norm_fderiv_multivariateGaussianPDFReal_smul_one_smul_self_le`: the norm of
  that derivative is at most `(1 + v⁻¹) (1 + ‖z‖)² φ(z)`.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For `v > 0`, the density of the isotropic Gaussian law `N(m, v • 1)` at `y` is the heat kernel
at time `v / 2` evaluated at `y - m`; both equal `(2πv)^(-d/2) exp(-‖y - m‖² / (2v))`. -/
theorem multivariateGaussianPDFReal_smul_one {v : ℝ} (hv : 0 < v) (m y : EuclideanSpace ℝ ι) :
    multivariateGaussianPDFReal m (v • 1) y = heatKernel (v / 2) (y - m) := by
  have hinv : (v • (1 : Matrix ι ι ℝ))⁻¹ = v⁻¹ • 1 := by
    exact Matrix.inv_eq_left_inv (by simp [smul_smul, hv.ne'])
  have hdet : (v • (1 : Matrix ι ι ℝ)).det ^ (-(1 : ℝ) / 2) =
      v ^ (-(Fintype.card ι : ℝ) / 2) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, ← Real.rpow_natCast,
      ← Real.rpow_mul hv.le]
    congr 1
    ring
  have hquad : ⟪y - m, (v⁻¹ • (1 : Matrix ι ι ℝ)).toEuclideanLin (y - m)⟫ = ‖y - m‖ ^ 2 / v := by
    simp [inner_smul_right, div_eq_inv_mul]
  rw [multivariateGaussianPDFReal_def, heatKernel_apply, finrank_euclideanSpace, hinv, hdet]
  dsimp only
  rw [hquad, show 4 * π * (v / 2) = 2 * π * v by ring, Real.mul_rpow (by positivity) hv.le]
  congr 2
  field_simp
  ring

/-- For `v > 0`, the density of the centred isotropic Gaussian law `N(0, v • 1)` is the heat kernel
at time `v / 2`. -/
theorem multivariateGaussianPDFReal_zero_smul_one {v : ℝ} (hv : 0 < v) :
    multivariateGaussianPDFReal (0 : EuclideanSpace ℝ ι) (v • 1) = heatKernel (v / 2) :=
  funext fun y ↦ by rw [multivariateGaussianPDFReal_smul_one hv, sub_zero]

/-- For `v > 0`, the density of the isotropic Gaussian law `N(m, v • 1)` is smooth. -/
theorem contDiff_multivariateGaussianPDFReal_smul_one {v : ℝ} (hv : 0 < v)
    (m : EuclideanSpace ℝ ι) {n : WithTop ℕ∞} :
    ContDiff ℝ n (multivariateGaussianPDFReal m (v • 1)) := by
  rw [funext (multivariateGaussianPDFReal_smul_one hv m)]
  exact (contDiff_heatKernel _).comp (contDiff_id.sub contDiff_const)

/-- For `v > 0`, every derivative of the density of the isotropic Gaussian law `N(m, v • 1)` is
bounded. -/
theorem exists_norm_iteratedFDeriv_multivariateGaussianPDFReal_smul_one_le {v : ℝ} (hv : 0 < v)
    (m : EuclideanSpace ℝ ι) (k : ℕ) :
    ∃ C, ∀ y, ‖iteratedFDeriv ℝ k (multivariateGaussianPDFReal m (v • 1)) y‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedFDeriv_heatKernel_le_const (E := EuclideanSpace ℝ ι) (half_pos hv) k
  refine ⟨C, fun y ↦ ?_⟩
  rw [funext (multivariateGaussianPDFReal_smul_one hv m), iteratedFDeriv_comp_sub]
  exact hC _

/-- For `v > 0`, the density of the centred isotropic Gaussian law `N(0, v • 1)` decays fast enough
to absorb every polynomial weight: `(1 + ‖z‖)^k φ(z)` is bounded. -/
theorem exists_one_add_norm_pow_mul_multivariateGaussianPDFReal_smul_one_le {v : ℝ} (hv : 0 < v)
    (k : ℕ) :
    ∃ C, ∀ z : EuclideanSpace ℝ ι,
      (1 + ‖z‖) ^ k * multivariateGaussianPDFReal 0 (v • 1) z ≤ C := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_one_add_norm_pow_mul_heatKernel_le (E := EuclideanSpace ℝ ι) (half_pos hv) k
  refine ⟨C * (4 * π * (2 * (v / 2))) ^
    (-(Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) / 2), fun z ↦ ?_⟩
  rw [multivariateGaussianPDFReal_zero_smul_one hv]
  exact (hC z).trans (mul_le_mul_of_nonneg_left (heatKernel_le (by positivity) z) hC0.le)

/-- Against a finite measure, `x ↦ φ_{s²}(y - c • x) • g(y - c • x)` is integrable for every
continuous `g` of at most polynomial growth, since `φ_{s²}` absorbs every polynomial weight. -/
theorem integrable_multivariateGaussianPDFReal_sub_smul_smul
    {μ₀ : Measure (EuclideanSpace ℝ ι)} [IsFiniteMeasure μ₀] {c s : ℝ} (hs : s ≠ 0)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : EuclideanSpace ℝ ι → F}
    (hg : Continuous g) {K : ℝ} (k : ℕ) (hgK : ∀ z, ‖g z‖ ≤ K * (1 + ‖z‖) ^ k)
    (y : EuclideanSpace ℝ ι) :
    Integrable (fun x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x) •
      g (y - c • x)) μ₀ := by
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_multivariateGaussianPDFReal_smul_one_le
    (ι := ι) (by positivity : 0 < s ^ 2) k
  have hφ : Continuous (multivariateGaussianPDFReal (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1)) :=
    (contDiff_multivariateGaussianPDFReal_smul_one (n := 0) (by positivity) 0).continuous
  refine Integrable.of_bound (C := K * C)
    ((hφ.smul hg).comp (by fun_prop : Continuous fun x : EuclideanSpace ℝ ι ↦ y - c • x)
      |>.aestronglyMeasurable) (.of_forall fun x ↦ ?_)
  set z := y - c • x
  have hφz := multivariateGaussianPDFReal_nonneg (0 : EuclideanSpace ℝ ι) (s ^ 2 • 1) z
  have hK : 0 ≤ K := by simpa using (norm_nonneg _).trans (hgK 0)
  rw [norm_smul, Real.norm_of_nonneg hφz]
  calc multivariateGaussianPDFReal 0 (s ^ 2 • 1) z * ‖g z‖
      ≤ multivariateGaussianPDFReal 0 (s ^ 2 • 1) z * (K * (1 + ‖z‖) ^ k) :=
        mul_le_mul_of_nonneg_left (hgK z) hφz
    _ = K * ((1 + ‖z‖) ^ k * multivariateGaussianPDFReal 0 (s ^ 2 • 1) z) := by ring
    _ ≤ K * C := mul_le_mul_of_nonneg_left (hC z) hK

/-- Against a finite measure `μ₀`, for `s ≠ 0`, the function `x ↦ φ_{s²}(y - c • x)` is integrable,
where `φ_{s²}` is the density of `N(0, s² • 1)`. -/
theorem integrable_multivariateGaussianPDFReal_sub_smul {μ₀ : Measure (EuclideanSpace ℝ ι)}
    [IsFiniteMeasure μ₀] {c s : ℝ} (hs : s ≠ 0) (y : EuclideanSpace ℝ ι) :
    Integrable (fun x ↦ multivariateGaussianPDFReal 0 (s ^ 2 • 1) (y - c • x)) μ₀ := by
  simpa using integrable_multivariateGaussianPDFReal_sub_smul_smul (μ₀ := μ₀) (c := c) hs
    (g := fun _ ↦ (1 : ℝ)) continuous_const (K := 1) 0 (fun _ ↦ by simp) y

/-- For `v > 0`, the isotropic Gaussian law `N(m, v • 1)` is Lebesgue measure weighted by the
heat kernel at time `v / 2`, translated to `m`. -/
theorem multivariateGaussian_smul_one_eq_withDensity_heatKernel {v : ℝ} (hv : 0 < v)
    (m : EuclideanSpace ℝ ι) :
    multivariateGaussian m (v • 1) =
      volume.withDensity fun y ↦ ENNReal.ofReal (heatKernel (v / 2) (y - m)) := by
  rw [multivariateGaussian_eq_withDensity (Matrix.PosDef.one.smul hv)]
  congr 1
  funext y
  rw [multivariateGaussianPDF_def, ← multivariateGaussianPDFReal_smul_one hv]

/-- For `v > 0`, the density `φ` of the isotropic Gaussian law `N(m, v • 1)` has gradient
`-v⁻¹ φ(y) (y - m)` at `y`; equivalently, the score `∇ log φ` of `N(m, v • 1)` is
`-(y - m) / v`. -/
theorem hasGradientAt_multivariateGaussianPDFReal_smul_one {v : ℝ} (hv : 0 < v)
    (m y : EuclideanSpace ℝ ι) :
    HasGradientAt (multivariateGaussianPDFReal m (v • 1))
      (-v⁻¹ • multivariateGaussianPDFReal m (v • 1) y • (y - m)) y := by
  have h := (hasGradientAt_heatKernel (v / 2) (y - m)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).sub_const m)
  rw [ContinuousLinearMap.comp_id, show 2 * (v / 2) = v by ring] at h
  rw [funext (multivariateGaussianPDFReal_smul_one hv m), hasGradientAt_iff_hasFDerivAt]
  exact h

/-- For `v > 0` and the density `φ` of the centred isotropic Gaussian law `N(0, v • 1)`, the
derivative of `z ↦ φ(z) z` at `z` is `φ(z) (1 - z ⊗ z / v)`, where `z ⊗ z = rankOne ℝ z z` is the
operator `w ↦ ⟪z, w⟫ • z`. -/
theorem hasFDerivAt_multivariateGaussianPDFReal_smul_one_smul_self {v : ℝ} (hv : 0 < v)
    (z : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun z ↦ multivariateGaussianPDFReal 0 (v • 1) z • z)
      (multivariateGaussianPDFReal 0 (v • 1) z • ContinuousLinearMap.id ℝ _ -
        (v⁻¹ * multivariateGaussianPDFReal 0 (v • 1) z) • InnerProductSpace.rankOne ℝ z z) z := by
  have h := (hasGradientAt_multivariateGaussianPDFReal_smul_one hv 0 z).hasFDerivAt
  refine (h.fun_smul (hasFDerivAt_id z)).congr_fderiv ?_
  ext1 w
  simp only [sub_zero, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply_apply, sub_apply,
    InnerProductSpace.rankOne_apply, real_inner_smul_left, mul_smul, id_eq]
  module

/-- For `v > 0` and the density `φ` of the centred isotropic Gaussian law `N(0, v • 1)`, the norm
of the derivative of `z ↦ φ(z) z` at `z` is at most `(1 + v⁻¹) (1 + ‖z‖)² φ(z)`. -/
theorem norm_fderiv_multivariateGaussianPDFReal_smul_one_smul_self_le {v : ℝ} (hv : 0 < v)
    (z : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (fun z ↦ multivariateGaussianPDFReal 0 (v • 1) z • z) z‖ ≤
      (1 + v⁻¹) * ((1 + ‖z‖) ^ 2 * multivariateGaussianPDFReal 0 (v • 1) z) := by
  rw [(hasFDerivAt_multivariateGaussianPDFReal_smul_one_smul_self hv z).fderiv]
  have hφ := multivariateGaussianPDFReal_nonneg (0 : EuclideanSpace ℝ ι) (v • 1) z
  have hid : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, InnerProductSpace.norm_rankOne, Real.norm_of_nonneg hφ,
    Real.norm_of_nonneg (by positivity)]
  have h1 : 1 ≤ (1 + ‖z‖) ^ 2 := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg z))
  have h2 : ‖z‖ * ‖z‖ ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
  calc multivariateGaussianPDFReal 0 (v • 1) z * ‖ContinuousLinearMap.id ℝ _‖ +
        v⁻¹ * multivariateGaussianPDFReal 0 (v • 1) z * (‖z‖ * ‖z‖)
      ≤ multivariateGaussianPDFReal 0 (v • 1) z * (1 + ‖z‖) ^ 2 +
        v⁻¹ * multivariateGaussianPDFReal 0 (v • 1) z * (1 + ‖z‖) ^ 2 := by
        gcongr
        exact hid.trans h1
    _ = _ := by ring

end TauCeti.Probability
