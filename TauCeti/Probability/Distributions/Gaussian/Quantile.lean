/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirac
public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import TauCeti.Probability.Distributions.Gaussian.Smooth
public import TauCeti.Probability.Distributions.Gaussian.Transforms
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The quantile function of a real Gaussian law

This file computes `MeasureTheory.Measure.quantile (gaussianReal m v)` in closed form through the
inverse error function `Real.erfInv`. For a level `0 < u < 1` the quantile is
`m + √(2 * v) * erfInv (2 * u - 1)`, which inverts the cdf `(1 + erf ((x - m) / √(2 * v))) / 2`.
At the singular boundary `v = 0` the law is the Dirac mass at `m` and the same formula gives the
constant quantile `m`.

In particular the standard Gaussian quantile is `z(u) = √2 * erfInv (2 * u - 1)`, and the general
formula reads `m + √v * z(u)`.

For a multivariate Gaussian, every real linear projection is a scalar Gaussian. Its quantile is
therefore the directional mean plus the square root of the directional variance times `z(u)`.
This includes singular covariance matrices and directions with zero variance.

For nonzero variance the quantile is a two-sided inverse of the distribution function on
`(0, 1)`, and for every variance it is smooth on `(0, 1)` with derivative `1 / φ_{m,v}(q(u))`,
where `φ_{m,v}` is the density and `q` the quantile.

The one-sided endpoint limits are stated in `EReal`: a positive-variance Gaussian quantile tends
to `⊥` at level zero and to `⊤` at level one, while the zero-variance law has constant quantile
`m` at both endpoints.

## Main declarations

* `TauCeti.Probability.quantile_gaussianReal` — the quantile of `gaussianReal m v`;
* `TauCeti.Probability.quantile_gaussianReal_zero_one` — the standard Gaussian quantile;
* `TauCeti.Probability.quantile_gaussianReal_eq_add_mul` — the affine form `m + √v * z(u)`;
* `TauCeti.Probability.cdf_quantile_gaussianReal`,
  `TauCeti.Probability.quantile_cdf_gaussianReal` — the two inverse laws;
* `TauCeti.Probability.hasDerivAt_quantile_gaussianReal`,
  `TauCeti.Probability.contDiffOn_quantile_gaussianReal` — the derivative and smoothness of the
  quantile on `(0, 1)`;
* `EuclideanSpace.quantile_map_inner_multivariateGaussian` — the quantile of a real linear
  projection of a multivariate Gaussian;
* `TauCeti.Probability.tendsto_quantile_gaussianReal_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_gaussianReal_nhdsLT_one` — the one-sided endpoint limits.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {u : ℝ}

/-- The quantile function of a real Gaussian law, including the Dirac boundary `v = 0`: at every
level `0 < u < 1` it is `m + √(2 * v) * erfInv (2 * u - 1)`. -/
theorem quantile_gaussianReal (m : ℝ) (v : ℝ≥0) (hu : u ∈ Ioo 0 1) :
    (gaussianReal m v).quantile u = m + √(2 * (v : ℝ)) * Real.erfInv (2 * u - 1) := by
  by_cases hv : v = 0
  · subst hv
    rw [gaussianReal_zero_var, Measure.quantile_dirac m hu.1 hu.2.le]
    simp
  have hc : 0 < √(2 * (v : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hy : 2 * u - 1 ∈ Ioo (-1) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  refine eq_of_forall_ge_iff fun x => ?_
  rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_gaussianReal_eq m hv, ← le_sub_iff_add_le',
    ← le_div_iff₀' hc, Real.erfInv_le_iff hy]
  constructor <;> intro h <;> linarith

/-- The quantile function of the standard Gaussian law: at every level `0 < u < 1` it is
`√2 * erfInv (2 * u - 1)`. -/
theorem quantile_gaussianReal_zero_one (hu : u ∈ Ioo 0 1) :
    (gaussianReal 0 1).quantile u = √2 * Real.erfInv (2 * u - 1) := by
  simpa using quantile_gaussianReal 0 1 hu

/-- Every Gaussian quantile is the affine image `m + √v * z(u)` of the standard Gaussian
quantile `z(u)`, including at the Dirac boundary `v = 0`. -/
theorem quantile_gaussianReal_eq_add_mul (m : ℝ) (v : ℝ≥0) (hu : u ∈ Ioo 0 1) :
    (gaussianReal m v).quantile u = m + √(v : ℝ) * (gaussianReal 0 1).quantile u := by
  rw [quantile_gaussianReal m v hu, quantile_gaussianReal_zero_one hu, Real.sqrt_mul zero_le_two]
  ring

/-- The lower endpoint limit of a Gaussian quantile is minus infinity at positive variance and
the mean at zero variance. -/
theorem tendsto_quantile_gaussianReal_nhdsGT_zero (m : ℝ) (v : ℝ≥0) :
    Tendsto (fun u ↦ ((gaussianReal m v).quantile u : EReal)) (𝓝[>] 0)
      (𝓝 (if v = 0 then (m : EReal) else ⊥)) := by
  by_cases hv : v = 0
  · subst hv
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    simp [gaussianReal_zero_var, Measure.quantile_dirac m hu.1 hu.2.le]
  · rw [ite_eq_right hv]
    apply EReal.tendsto_coe_nhds_bot_iff.2
    refine tendsto_atBot.2 fun b ↦ ?_
    have hb : 0 < cdf (gaussianReal m v) b := by
      rw [cdf_gaussianReal_eq m hv]
      linarith [TauCeti.Real.neg_one_lt_erf ((b - m) / √(2 * (v : ℝ)))]
    filter_upwards [Ioo_mem_nhdsGT hb] with u hu
    exact (Measure.quantile_le_iff _ hu.1
      (hu.2.trans_le (cdf_le_one (gaussianReal m v) b))).2 hu.2.le

/-- The upper endpoint limit of a Gaussian quantile is plus infinity at positive variance and
the mean at zero variance. -/
theorem tendsto_quantile_gaussianReal_nhdsLT_one (m : ℝ) (v : ℝ≥0) :
    Tendsto (fun u ↦ ((gaussianReal m v).quantile u : EReal)) (𝓝[<] 1)
      (𝓝 (if v = 0 then (m : EReal) else ⊤)) := by
  by_cases hv : v = 0
  · subst hv
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    simp [gaussianReal_zero_var, Measure.quantile_dirac m hu.1 hu.2.le]
  · rw [ite_eq_right hv]
    apply EReal.tendsto_coe_nhds_top_iff.2
    refine tendsto_atTop.2 fun b ↦ ?_
    have hb : cdf (gaussianReal m v) b < 1 := by
      rw [cdf_gaussianReal_eq m hv]
      linarith [TauCeti.Real.erf_lt_one ((b - m) / √(2 * (v : ℝ)))]
    filter_upwards [Ioo_mem_nhdsLT hb] with u hu
    exact ((Measure.lt_quantile_iff _
      ((cdf_nonneg (gaussianReal m v) b).trans_lt hu.1) hu.2).2 hu.1).le

section Inverse

variable (m : ℝ) {v : ℝ≥0}

/-- For a Gaussian law with nonzero variance, the distribution function at the quantile of a
level `0 < u < 1` is `u`. -/
theorem cdf_quantile_gaussianReal (hv : v ≠ 0) (hu : u ∈ Ioo 0 1) :
    cdf (gaussianReal m v) ((gaussianReal m v).quantile u) = u :=
  have := nullSingletonClass_gaussianReal (μ := m) hv
  Measure.cdf_quantile_of_noAtoms _ hu.1 hu.2

/-- For a Gaussian law with nonzero variance, the quantile at the value of the distribution
function at `x` is `x`. -/
theorem quantile_cdf_gaussianReal (hv : v ≠ 0) (x : ℝ) :
    (gaussianReal m v).quantile (cdf (gaussianReal m v) x) = x :=
  Measure.quantile_cdf _ ((strictMono_cdf_gaussianReal m hv).strictMonoOn _)
    ⟨cdf_gaussianReal_pos m hv x, cdf_gaussianReal_lt_one m hv x⟩

/-- At zero variance the quantile is the constant `m` on `(0, 1)`. -/
private theorem eqOn_quantile_gaussianReal_zero :
    EqOn (gaussianReal m 0).quantile (fun _ => m) (Ioo 0 1) := fun w hw => by
  rw [quantile_gaussianReal m 0 hw]
  simp

/-- The quantile of a Gaussian law has derivative `1 / φ_{m,v}(q(u))` at every level
`0 < u < 1`, where `φ_{m,v}` is the density and `q` the quantile. At zero variance both sides
vanish, the quantile being constant and the density zero. -/
theorem hasDerivAt_quantile_gaussianReal (v : ℝ≥0) (hu : u ∈ Ioo 0 1) :
    HasDerivAt (gaussianReal m v).quantile
      (gaussianPDFReal m v ((gaussianReal m v).quantile u))⁻¹ u := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianPDFReal_zero_var, Pi.zero_apply, inv_zero]
    exact (hasDerivAt_const u m).congr_of_eventuallyEq <|
      eventually_of_mem (Ioo_mem_nhds hu.1 hu.2) (eqOn_quantile_gaussianReal_zero m)
  have hc : ContinuousAt (gaussianReal m v).quantile u :=
    (Measure.continuousOn_quantile _ ((strictMono_cdf_gaussianReal m hv).strictMonoOn _))
      |>.continuousAt (Ioo_mem_nhds hu.1 hu.2)
  refine (hasDerivAt_cdf_gaussianReal m hv _).of_local_left_inverse hc
    (gaussianPDFReal_pos _ _ _ hv).ne' ?_
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with w hw using cdf_quantile_gaussianReal m hv hw

/-- The quantile of a Gaussian law is smooth on `(0, 1)`. -/
theorem contDiffOn_quantile_gaussianReal (v : ℝ≥0) {n : ℕ∞} :
    ContDiffOn ℝ n (gaussianReal m v).quantile (Ioo 0 1) := by
  rcases eq_or_ne v 0 with rfl | hv
  · exact contDiffOn_const.congr (eqOn_quantile_gaussianReal_zero m)
  refine (contDiffOn_infty.2 fun k => ?_).of_le (mod_cast le_top)
  induction k with
  | zero =>
    exact contDiffOn_zero.2
      (Measure.continuousOn_quantile _ ((strictMono_cdf_gaussianReal m hv).strictMonoOn _))
  | succ k ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun w hw => (hasDerivAt_quantile_gaussianReal m v hw).differentiableAt
      |>.differentiableWithinAt, by simp, ?_⟩
    refine ContDiffOn.congr ?_ fun w hw => (hasDerivAt_quantile_gaussianReal m v hw).deriv
    exact ((contDiff_gaussianPDFReal m v).comp_contDiffOn ih).inv fun w _ =>
      (gaussianPDFReal_pos _ _ _ hv).ne'

end Inverse

end TauCeti.Probability

namespace EuclideanSpace

open TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {u : ℝ}

/-- The quantile of a real linear projection of a multivariate Gaussian is its directional mean
plus its directional standard deviation times the standard Gaussian quantile. This includes
directions with zero variance. -/
theorem quantile_map_inner_multivariateGaussian (m q : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (hu : u ∈ Ioo 0 1) :
    ((multivariateGaussian m S).map (fun x ↦ ⟪q, x⟫)).quantile u =
      ⟪q, m⟫ + √⟪q, S.toEuclideanLin q⟫ * (gaussianReal 0 1).quantile u := by
  rw [map_inner_multivariateGaussian m q hS,
    quantile_gaussianReal_eq_add_mul _ _ hu,
    Real.coe_toNNReal _ ((Matrix.isPositive_toEuclideanLin_iff.mpr hS).inner_nonneg_right q)]

/-- At level zero, a multivariate Gaussian projection tends to its constant value in a
zero-variance direction and to minus infinity otherwise. -/
theorem tendsto_quantile_map_inner_multivariateGaussian_nhdsGT_zero
    (m q : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    Tendsto (fun u ↦
        (((multivariateGaussian m S).map (fun x ↦ ⟪q, x⟫)).quantile u : EReal))
      (𝓝[>] 0)
      (𝓝 (if ⟪q, S.toEuclideanLin q⟫ = 0 then (⟪q, m⟫ : EReal) else ⊥)) := by
  have hnonneg := (Matrix.isPositive_toEuclideanLin_iff.mpr hS).inner_nonneg_right q
  have hzero : (⟪q, S.toEuclideanLin q⟫.toNNReal = 0) ↔
      ⟪q, S.toEuclideanLin q⟫ = 0 := by
    rw [Real.toNNReal_eq_zero]
    exact ⟨fun h ↦ le_antisymm h hnonneg, fun h ↦ h.le⟩
  rw [map_inner_multivariateGaussian m q hS]
  simpa only [hzero] using
    tendsto_quantile_gaussianReal_nhdsGT_zero ⟪q, m⟫
      ⟪q, S.toEuclideanLin q⟫.toNNReal

/-- At level one, a multivariate Gaussian projection tends to its constant value in a
zero-variance direction and to plus infinity otherwise. -/
theorem tendsto_quantile_map_inner_multivariateGaussian_nhdsLT_one
    (m q : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    Tendsto (fun u ↦
        (((multivariateGaussian m S).map (fun x ↦ ⟪q, x⟫)).quantile u : EReal))
      (𝓝[<] 1)
      (𝓝 (if ⟪q, S.toEuclideanLin q⟫ = 0 then (⟪q, m⟫ : EReal) else ⊤)) := by
  have hnonneg := (Matrix.isPositive_toEuclideanLin_iff.mpr hS).inner_nonneg_right q
  have hzero : (⟪q, S.toEuclideanLin q⟫.toNNReal = 0) ↔
      ⟪q, S.toEuclideanLin q⟫ = 0 := by
    rw [Real.toNNReal_eq_zero]
    exact ⟨fun h ↦ le_antisymm h hnonneg, fun h ↦ h.le⟩
  rw [map_inner_multivariateGaussian m q hS]
  simpa only [hzero] using
    tendsto_quantile_gaussianReal_nhdsLT_one ⟪q, m⟫
      ⟪q, S.toEuclideanLin q⟫.toNNReal

end EuclideanSpace
