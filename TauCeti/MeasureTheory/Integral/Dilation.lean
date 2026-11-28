/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Integral.Bochner.Affine

/-!
# Dilation scaling of the lower Lebesgue integral

Dilating the variable of a function on a finite-dimensional real normed space `E` by a nonzero
scalar `r` rescales its integral against an additive Haar measure by `|(r ^ n)⁻¹|`, where `n` is
the dimension of `E`. Mathlib records this for the Bochner integral as
`MeasureTheory.Measure.integral_comp_smul`; this file is the lower-Lebesgue-integral counterpart,
proved the same way from `MeasureTheory.Measure.map_addHaar_smul`, and, like the Bochner version,
needing no measurability hypothesis. Unlike the Bochner version, it needs `r ≠ 0`: for `r = 0`
the left-hand side is `g 0 * μ univ`, which is `∞` in positive dimension unless `g 0 = 0`.

Dilating each coordinate of `ℝ^ι` by its own nonzero factor `cᵢ` rescales an additive Haar
measure by `|∏ᵢ cᵢ|⁻¹` (`MeasureTheory.Measure.map_mul_pi_addHaar_eq_smul`), by Mathlib's
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` for the diagonal matrix of the
factors. The Bochner integral is rescaled by the same factor, for all factors
(`TauCeti.integral_comp_mul_pi`), by the linear change of variables
`MeasureTheory.Measure.integral_comp_linearMap` for the diagonal matrix.

For `ε > 0` the dilation `k_ε(y) = ε⁻ᵈ k(ε⁻¹ • y)` of a kernel `k`, where `d` is the dimension
of `E`, has the same integral as `k`. Substituting `y = ε • z` turns the average of a function `g`
against `k_ε` into the average of `z ↦ g (ε • z)` against `k`. When `g` is bounded and continuous
at `0`, these averages converge to `(∫ k) • g 0` as `ε → 0⁺` by dominated convergence, with no sign,
normalization or support condition on the real or complex kernel `k`. Applied to the translates of
an `Lᵖ` function, this gives the approximate-identity property of dilated kernels in
`TauCeti.MeasureTheory.Function.Lp.Convolution`.

On the plane `ℝ × ℝ`, the Bochner case `MeasureTheory.Measure.setIntegral_comp_smul` of a set
integral is restated with its Jacobian computed: substituting `z = c • z'` contributes the factor
`c * c`.

## Main declarations

* `MeasureTheory.Measure.lintegral_comp_smul`:
  `∫⁻ x, g (r • x) ∂μ = |(r ^ n)⁻¹| * ∫⁻ x, g x ∂μ`.
* `MeasureTheory.Measure.lintegral_comp_inv_smul`: the same law written for `r⁻¹`, with factor
  `|r ^ n|`.
* `MeasureTheory.Measure.lintegral_comp_homothety`: the same law for the homothety of ratio `r`
  about any centre.
* `MeasureTheory.Measure.setLIntegral_comp_add_smul`: the same law for the affine map
  `y ↦ c + r • y`, on the preimage of any set.
* `MeasureTheory.Measure.map_mul_pi_addHaar_eq_smul`: the image of an additive Haar measure on
  `ℝ^ι` under `x ↦ (cᵢ xᵢ)ᵢ` is the measure scaled by `|∏ᵢ cᵢ|⁻¹`.
* `TauCeti.integral_comp_mul_pi`: `∫ x, F (fun i ↦ cᵢ xᵢ) = |∏ᵢ cᵢ|⁻¹ • ∫ y, F y` on `ℝ^ι`.
* `TauCeti.integral_comp_inv_smul_smul`: the average of a function against the dilation
  `k_ε(y) = ε⁻ᵈ k(ε⁻¹ • y)` of a kernel is the average of its rescaling `g (ε • ·)` against `k`.
* `TauCeti.tendsto_integral_comp_inv_smul_smul`: for an integrable real or complex kernel `k` and
  a bounded function `g` continuous at `0`, the averages of `g` against `k_ε` converge to
  `(∫ k) • g 0` as `ε → 0⁺`.
* `MeasureTheory.Measure.setIntegral_prod_eq_mul_smul_setIntegral_comp_smul`:
  `∫ z in s, f z = (c * c) • ∫ z in c⁻¹ • s, f (c • z)` on the plane `ℝ × ℝ`.
-/

public section

namespace MeasureTheory.Measure

open Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Dilation scaling of the lower Lebesgue integral.** This is the counterpart, for `∫⁻`, of
`MeasureTheory.Measure.integral_comp_smul`; as there, `g` need not be measurable. -/
theorem lintegral_comp_smul (g : E → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ x, g (r • x) ∂μ = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ x, g x ∂μ := by
  rw [← (measurableEmbedding_const_smul₀ hr).lintegral_map, map_addHaar_smul μ hr,
    lintegral_smul_measure, smul_eq_mul]

/-- Dilating the variable by `r⁻¹`, for `r ≠ 0`, multiplies a lower Lebesgue integral by
`|r ^ n|`, where `n` is the dimension of the ambient space. -/
theorem lintegral_comp_inv_smul (g : E → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ x, g (r⁻¹ • x) ∂μ = ENNReal.ofReal |r ^ finrank ℝ E| * ∫⁻ x, g x ∂μ := by
  rw [lintegral_comp_smul μ g (inv_ne_zero hr), inv_pow, inv_inv]

/-- **Homothety scaling of the lower Lebesgue integral.** Precomposing with the homothety of
ratio `r ≠ 0` about any centre `x` rescales a lower Lebesgue integral against an additive Haar
measure by `|(r ^ n)⁻¹|`, where `n` is the dimension of the ambient space. -/
theorem lintegral_comp_homothety (g : E → ℝ≥0∞) (x : E) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ y, g (AffineMap.homothety x r y) ∂μ =
      ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ y, g y ∂μ := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  rw [lintegral_sub_right_eq_self (fun z => g (r • z + x)) x,
    lintegral_comp_smul μ (fun z => g (z + x)) hr, lintegral_add_right_eq_self]

/-- **Affine scaling of a set lower Lebesgue integral.** Precomposing with `y ↦ c + r • y`,
`r ≠ 0`, and integrating over the preimage of a set `s` gives `|(r ^ n)⁻¹|` times the integral over
`s`, where `n` is the dimension of the ambient space. Neither `g` nor `s` need be measurable. -/
theorem setLIntegral_comp_add_smul (g : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : r ≠ 0) (s : Set E) :
    ∫⁻ y in (fun y ↦ c + r • y) ⁻¹' s, g (c + r • y) ∂μ =
      ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ z in s, g z ∂μ := by
  have he : MeasurableEmbedding fun y : E ↦ c + r • y :=
    (measurableEmbedding_addLeft c).comp (measurableEmbedding_const_smul₀ hr)
  have hmap : μ.map (fun y ↦ c + r • y) = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| • μ := by
    calc μ.map (fun y ↦ c + r • y) = (μ.map (r • ·)).map (c + ·) :=
          (Measure.map_map (measurable_const_add c) (measurable_const_smul r)).symm
      _ = _ := by
          rw [map_addHaar_smul μ hr, Measure.map_smul _ (measurable_const_add c).aemeasurable,
            map_add_left_eq_self]
  rw [← he.lintegral_map, ← he.restrict_map, hmap, Measure.restrict_smul, lintegral_smul_measure,
    smul_eq_mul]

/-- Multiplying the `i`-th coordinate of `ℝ^ι` by `cᵢ` is the linear map of the diagonal matrix
of the `cᵢ`. -/
private theorem mul_pi_eq_toLin'_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) :
    (fun (x : ι → ℝ) i ↦ c i * x i) = Matrix.toLin' (Matrix.diagonal c) := by
  funext x i
  simp [Matrix.mulVec_diagonal]

/-- The determinant of multiplying the `i`-th coordinate of `ℝ^ι` by `cᵢ` is `∏ᵢ cᵢ`. -/
private theorem det_toLin'_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) :
    LinearMap.det (Matrix.toLin' (Matrix.diagonal c)) = ∏ i, c i := by
  rw [LinearMap.det_toLin', Matrix.det_diagonal]

/-- **Rescaling the coordinates of `ℝ^ι`.** The image of an additive Haar measure under the
map multiplying the `i`-th coordinate by `cᵢ ≠ 0` is the measure scaled by `|∏ᵢ cᵢ|⁻¹`. -/
theorem map_mul_pi_addHaar_eq_smul {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ))
    [μ.IsAddHaarMeasure] {c : ι → ℝ} (hc : ∀ i, c i ≠ 0) :
    μ.map (fun x i ↦ c i * x i) = ENNReal.ofReal |∏ i, c i|⁻¹ • μ := by
  classical
  rw [mul_pi_eq_toLin'_diagonal, Measure.map_linearMap_addHaar_eq_smul_addHaar μ
    (det_toLin'_diagonal c ▸ Finset.prod_ne_zero_iff.2 fun i _ ↦ hc i), det_toLin'_diagonal,
    abs_inv]

open scoped Pointwise in
/-- **Dilation of a set integral over the plane.** For `c ≠ 0`, substituting `z = c • z'` in an
integral over a set `s ⊆ ℝ × ℝ` against a product of additive Haar measures contributes the
Jacobian `c * c`. This is `MeasureTheory.Measure.setIntegral_comp_smul` on `ℝ × ℝ`, where
`|(c ^ 2)⁻¹|` cancels against `c * c`. -/
theorem setIntegral_prod_eq_mul_smul_setIntegral_comp_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (μ ν : Measure ℝ) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (f : ℝ × ℝ → F) {c : ℝ} (hc : c ≠ 0) (s : Set (ℝ × ℝ)) :
    ∫ z in s, f z ∂μ.prod ν = (c * c) • ∫ z in c⁻¹ • s, f (c • z) ∂μ.prod ν := by
  rw [setIntegral_comp_smul (μ.prod ν) f _ hc, smul_inv_smul₀ hc, smul_smul]
  -- `finrank ℝ (ℝ × ℝ) = 2`, so the factor is `(c * c) * |(c ^ 2)⁻¹| = 1`.
  simp [finrank_prod, hc, ← sq]

end MeasureTheory.Measure

namespace TauCeti

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- Dilation of the measure by a nonzero scalar rescales the squared derivative energy by the
inverse square of that scalar. -/
theorem integral_sq_norm_fderiv_comp_smul {μ : Measure E} {f : E → ℝ} {a : ℝ} (ha : a ≠ 0) :
    ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ.map (fun x ↦ a • x) =
      (a ^ 2)⁻¹ * ∫ x, ‖fderiv ℝ (fun y ↦ f (a • y)) x‖ ^ 2 ∂μ := by
  rw [(measurableEmbedding_const_smul₀ (α := E) ha).integral_map, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [norm_fderiv_comp_smul a, mul_pow, sq_abs]
  field_simp

/-- Multiplying the `i`-th coordinate by `cᵢ` scales the integral against an additive Haar
measure on `ℝ^ι` by `|∏ᵢ cᵢ|⁻¹`. If some `cᵢ` is `0`, both sides are `0`. -/
theorem integral_comp_mul_pi {ι G : Type*} [Fintype ι] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure (ι → ℝ)} [μ.IsAddHaarMeasure] (c : ι → ℝ) (F : (ι → ℝ) → G) :
    ∫ x, F (fun i ↦ c i * x i) ∂μ = |∏ i, c i|⁻¹ • ∫ y, F y ∂μ := by
  classical
  -- The coordinatewise dilation is the linear map of the diagonal matrix of the `cᵢ`.
  have h := Measure.integral_comp_linearMap μ F (Matrix.toLin' (Matrix.diagonal c))
  rwa [← Measure.mul_pi_eq_toLin'_diagonal, Measure.det_toLin'_diagonal] at h


section Dilation

open Filter Module
open scoped Topology

variable [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V]
  [IsScalarTower ℝ 𝕜 V]

/-- **Rescaling an average against a dilated kernel.** For `ε > 0`, the average of `g` against
the dilation `ε⁻ᵈ k(ε⁻¹ • y)` of a kernel `k` is the average of `z ↦ g (ε • z)` against `k`. -/
theorem integral_comp_inv_smul_smul {ε : ℝ} (hε : 0 < ε) (k : E → 𝕜) (g : E → V) :
    ∫ y, ((ε ^ finrank ℝ E)⁻¹ • k (ε⁻¹ • y)) • g y ∂μ = ∫ z, k z • g (ε • z) ∂μ := by
  set G : E → V := fun z ↦ k z • g (ε • z)
  have h (y : E) :
      ((ε ^ finrank ℝ E)⁻¹ • k (ε⁻¹ • y)) • g y = (ε ^ finrank ℝ E)⁻¹ • G (ε⁻¹ • y) := by
    simp only [G, smul_assoc, smul_inv_smul₀ hε.ne']
  simp_rw [h]
  rw [integral_smul, Measure.integral_comp_inv_smul_of_nonneg μ G hε.le,
    inv_smul_smul₀ (pow_ne_zero _ hε.ne')]

/-- **Dilations of an integrable kernel concentrate at the origin.** Let `k` be an integrable
real or complex kernel and let `g` be an almost everywhere strongly measurable, essentially
bounded function with values in a Banach space, continuous at `0`. Then the averages of `g`
against the dilations `k_ε(y) = ε⁻ᵈ k(ε⁻¹ • y)` converge to `(∫ k) • g 0` as `ε → 0⁺`. -/
theorem tendsto_integral_comp_inv_smul_smul [CompleteSpace V] {k : E → 𝕜} (hk : Integrable k μ)
    {g : E → V} (hg : AEStronglyMeasurable g μ) {C : ℝ} (hgC : ∀ᵐ y ∂μ, ‖g y‖ ≤ C)
    (hg₀ : ContinuousAt g 0) :
    Tendsto (fun ε : ℝ ↦ ∫ y, ((ε ^ finrank ℝ E)⁻¹ • k (ε⁻¹ • y)) • g y ∂μ)
      (𝓝[>] 0) (𝓝 ((∫ y, k y ∂μ) • g 0)) := by
  rw [← integral_smul_const]
  refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) ↦
    (integral_comp_inv_smul_smul hε k g).symm) ?_
  -- Dominated convergence: `z ↦ g (ε • z)` is bounded by `C` and tends to `g 0` as `ε → 0`.
  have hqmp {ε : ℝ} (hε : 0 < ε) := Measure.quasiMeasurePreserving_smul μ hε.ne'
  refine tendsto_integral_filter_of_dominated_convergence (fun z ↦ ‖k z‖ * C)
    (eventually_nhdsWithin_of_forall fun ε hε ↦
      hk.aestronglyMeasurable.smul (hg.comp_quasiMeasurePreserving (hqmp hε)))
    (eventually_nhdsWithin_of_forall fun ε hε ↦ by
      filter_upwards [(hqmp hε).ae hgC] with z hz
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg _))
    (hk.norm.mul_const _) (ae_of_all _ fun z ↦ ?_)
  have hz : Tendsto (fun ε : ℝ ↦ ε • z) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ ↦ ε • z) (𝓝 0) (𝓝 ((0 : ℝ) • z)) := tendsto_id.smul_const z
    rw [zero_smul] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact (hg₀.tendsto.comp hz).const_smul (k z)

end Dilation

end TauCeti
