/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
public import TauCeti.LinearAlgebra.BilinearForm.DetRatio
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

/-!
# The relative volume density of two Riemannian metrics

Let `g` and `g'` be two Riemannian metrics on the same manifold `M`. At a point `x`, the
*relative volume density* of `g'` with respect to `g` is

`J(x) = √(det G'(x) / det G(x))`,

where `G(x)` and `G'(x)` are the Gram matrices of `g_x` and `g'_x` in a basis of `T_x M`. The
ratio does not depend on the basis, since a change of basis multiplies both determinants by the
square of the same nonzero determinant; in a `g`-orthonormal basis, `J(x)` is the square root of
the Gram determinant of `g'_x`. The density is positive, and it is `C^n` for `C^n` metrics.

The Riemannian volume measures of the two metrics, which live on the copies `TauCeti.WithMetric g`
and `TauCeti.WithMetric g'` of `M`, satisfy

`dV_{g'} = J dV_g`,

so that `∫ φ dV_{g'} = ∫ J φ dV_g` for every function `φ` on `M`. In every chart, the chart
volume density of `g'` is `J` times that of `g`. No orientation is used. For a conformal metric
`g' = f g` in real dimension `N`, `J = f ^ (N / 2)`, recovering
`TauCeti.WithMetric.riemannianVolume_rescale`.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.relativeVolumeDensity`: the relative volume density of
  `g'` with respect to `g`.

## Main results

* `Module.Basis.relativeVolumeDensity_eq_sqrt_det_of_orthonormal`: in a `g`-orthonormal basis,
  `J` is the square root of the Gram determinant of `g'`.
* `Bundle.ContMDiffRiemannianMetric.relativeVolumeDensity_pos`: `J` is positive.
* `Bundle.ContMDiffRiemannianMetric.contMDiff_relativeVolumeDensity`: `J` is `C^n`.
* `Bundle.ContMDiffRiemannianMetric.chartVolumeDensity_toWithMetric_eq_mul`:
  compatibility with chart volume densities.
* `Bundle.ContMDiffRiemannianMetric.riemannianVolume_eq_map_withDensity_relativeVolumeDensity`,
* `integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul`:
  `dV_{g'} = J dV_g`.
* `Bundle.ContMDiffRiemannianMetric.riemannianTotalVolume_eq_integral_relativeVolumeDensity`:
  on a compact manifold,
  `Vol(g') = ∫ J dV_g`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 2.44 and the discussion of Riemannian densities following it.
-/

public section

open Bundle MeasureTheory Set Riemannian.Tensor TauCeti
open scoped ENNReal Manifold ContDiff Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n n' : ℕ∞ω}

/-- The **relative volume density** of a Riemannian metric `g'` with respect to a Riemannian
metric `g` at `x`: the square root of the ratio of the Gram determinants of `g'_x` and `g_x` in
any basis of `T_x M`. -/
def relativeVolumeDensity
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x)) (x : M) : ℝ :=
  √(LinearMap.BilinForm.detRatio (g.inner x).toBilinForm (g'.inner x).toBilinForm)

variable {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x)}

variable (g g') in
/-- The definition of the relative volume density. -/
theorem relativeVolumeDensity_def (x : M) :
    relativeVolumeDensity g g' x =
      √(LinearMap.BilinForm.detRatio (g.inner x).toBilinForm (g'.inner x).toBilinForm) :=
  (rfl)

/-- The relative volume density in a basis `b` of `T_x M`. -/
theorem _root_.Module.Basis.relativeVolumeDensity_eq_sqrt_div {x : M} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I x)) :
    relativeVolumeDensity g g' x =
      √((Matrix.of fun i j ↦ g'.inner x (b i) (b j)).det /
        (Matrix.of fun i j ↦ g.inner x (b i) (b j)).det) := by
  rw [relativeVolumeDensity, b.bilinFormDetRatio_eq]
  congr 3 <;> ext i j <;> simp [LinearMap.BilinForm.toMatrix_apply]

/-- **The relative volume density in an orthonormal basis.** If `b` is a `g`-orthonormal basis of
`T_x M`, the relative volume density of `g'` with respect to `g` at `x` is the square root of the
Gram determinant of `g'_x` in `b`. -/
theorem _root_.Module.Basis.relativeVolumeDensity_eq_sqrt_det_of_orthonormal
    {x : M} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    relativeVolumeDensity g g' x = √(Matrix.of fun i j ↦ g'.inner x (b i) (b j)).det := by
  rw [b.relativeVolumeDensity_eq_sqrt_div]
  congr 1
  have hGram : (Matrix.of fun i j ↦ g.inner x (b i) (b j)) = 1 := by
    ext i j
    simp [hb, Matrix.one_apply]
  rw [hGram, Matrix.det_one, div_one]

variable (g g') in
/-- The relative volume density is nonnegative. -/
@[simp]
theorem relativeVolumeDensity_nonneg (x : M) : 0 ≤ relativeVolumeDensity g g' x :=
  Real.sqrt_nonneg _

variable (g g') in
/-- The relative volume density is positive. -/
@[simp]
theorem relativeVolumeDensity_pos (x : M) : 0 < relativeVolumeDensity g g' x :=
  Real.sqrt_pos.2 <| LinearMap.BilinForm.detRatio_pos _ _
    (g.symm x) (g.pos x) (g'.symm x) (g'.pos x)

variable (g) in
/-- The relative volume density of a metric with respect to itself is one. -/
@[simp]
theorem relativeVolumeDensity_self (x : M) : relativeVolumeDensity g g x = 1 := by
  rw [relativeVolumeDensity, LinearMap.BilinForm.detRatio_self _
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
      (Module.finBasis ℝ (TangentSpace I x))).2
      (Module.Basis.det_toMatrix_pos _ (g.symm x) (g.pos x)).ne'), Real.sqrt_one]

variable (g g') in
/-- The relative volume density never vanishes. -/
@[simp]
theorem relativeVolumeDensity_ne_zero (x : M) : relativeVolumeDensity g g' x ≠ 0 :=
  (relativeVolumeDensity_pos g g' x).ne'

variable (g g') in
/-- Reversing the metrics inverts the relative volume density. -/
@[simp]
theorem relativeVolumeDensity_inv (x : M) :
    (relativeVolumeDensity g g' x)⁻¹ = relativeVolumeDensity g' g x := by
  rw [relativeVolumeDensity_def, relativeVolumeDensity_def, ← Real.sqrt_inv,
    LinearMap.BilinForm.detRatio_inv]

variable (g g') in
/-- The square of the relative volume density is the determinant ratio. -/
@[simp]
theorem relativeVolumeDensity_sq (x : M) :
    relativeVolumeDensity g g' x ^ 2 =
      (g.inner x).toBilinForm.detRatio (g'.inner x).toBilinForm := by
  rw [relativeVolumeDensity_def, Real.sq_sqrt]
  exact (LinearMap.BilinForm.detRatio_pos _ _
    (g.symm x) (g.pos x) (g'.symm x) (g'.pos x)).le

variable (g g') in
/-- The density depends only on the inner products at the given point. -/
theorem relativeVolumeDensity_congr {m m' : ℕ∞ω}
    {g₁ : ContMDiffRiemannianMetric I m E (fun x : M ↦ TangentSpace I x)}
    {g₂ : ContMDiffRiemannianMetric I m' E (fun x : M ↦ TangentSpace I x)}
    {x : M} (h : g.inner x = g₁.inner x) (h' : g'.inner x = g₂.inner x) :
    relativeVolumeDensity g g' x = relativeVolumeDensity g₁ g₂ x := by
  rw [relativeVolumeDensity_def, relativeVolumeDensity_def, h, h']

variable (g g') in
/-- Lowering the regularity of the reference metric leaves the density unchanged. -/
@[simp]
theorem relativeVolumeDensity_ofLE_left {k : ℕ∞ω} (hk : k ≤ n) (x : M) :
    relativeVolumeDensity (g.ofLE hk) g' x = relativeVolumeDensity g g' x := by
  simp only [relativeVolumeDensity_def, ofLE_inner]

variable (g g') in
/-- Lowering the regularity of the compared metric leaves the density unchanged. -/
@[simp]
theorem relativeVolumeDensity_ofLE_right {k : ℕ∞ω} (hk : k ≤ n') (x : M) :
    relativeVolumeDensity g (g'.ofLE hk) x = relativeVolumeDensity g g' x := by
  simp only [relativeVolumeDensity_def, ofLE_inner]

variable (g g') in
/-- On the chart source at `α`, the relative volume density is the square root of the ratio
of the Gram determinants of `g'` and `g`, in that order, in the chart frame. -/
theorem relativeVolumeDensity_eq_sqrt_div_chartGramMatrix {α x : M}
    (hx : x ∈ (chartAt H α).source) :
    relativeVolumeDensity g g' x =
      √((chartGramMatrix (I := I) (WithMetric.toWithMetric g' α)
          (WithMetric.toWithMetric g' x)).det /
        (chartGramMatrix (I := I) (WithMetric.toWithMetric g α)
          (WithMetric.toWithMetric g x)).det) := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  rw [Module.Basis.relativeVolumeDensity_eq_sqrt_div
    ((trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hx'),
    ContMDiffRiemannianMetric.chartGramMatrix_toWithMetric,
    ContMDiffRiemannianMetric.chartGramMatrix_toWithMetric]
  simp only [chartLocalFrame_apply_of_mem_chart_source α hx]

variable (g g') in
/-- **Compatibility with chart volume densities.** On the chart source at `α`, the chart volume
density of `g'` is the relative volume density times the chart volume density of `g`. -/
theorem chartVolumeDensity_toWithMetric_eq_mul {α x : M} (hx : x ∈ (chartAt H α).source) :
    chartVolumeDensity (I := I) (WithMetric.toWithMetric g' α) (WithMetric.toWithMetric g' x) =
      relativeVolumeDensity g g' x * chartVolumeDensity (I := I) (WithMetric.toWithMetric g α)
        (WithMetric.toWithMetric g x) := by
  have hpos : 0 < (chartGramMatrix (I := I) (WithMetric.toWithMetric g α)
      (WithMetric.toWithMetric g x)).det :=
    chartGramMatrix_det_pos _ (by
      rw [TangentBundle.trivializationAt_baseSet]
      exact (WithMetric.mem_chartAt_source_iff _ _).2 hx)
  rw [relativeVolumeDensity_eq_sqrt_div_chartGramMatrix g g' hx, chartVolumeDensity_def,
    chartVolumeDensity_def, ← Real.sqrt_mul (div_nonneg (chartGramMatrix_det_nonneg _ _)
      hpos.le), div_mul_cancel₀ _ hpos.ne']

variable (g g') in
/-- On the chart source at `α`, the relative volume density is the ratio of the chart volume
densities of the two metrics. -/
theorem relativeVolumeDensity_eq_div_chartVolumeDensity {α x : M}
    (hx : x ∈ (chartAt H α).source) :
    relativeVolumeDensity g g' x =
      chartVolumeDensity (I := I) (WithMetric.toWithMetric g' α) (WithMetric.toWithMetric g' x) /
        chartVolumeDensity (I := I) (WithMetric.toWithMetric g α)
          (WithMetric.toWithMetric g x) := by
  have hpos : 0 < chartVolumeDensity (I := I) (WithMetric.toWithMetric g α)
      (WithMetric.toWithMetric g x) :=
    chartVolumeDensity_pos _ (by
      rw [TangentBundle.trivializationAt_baseSet]
      exact (WithMetric.mem_chartAt_source_iff _ _).2 hx)
  rw [chartVolumeDensity_toWithMetric_eq_mul g g' hx, mul_div_cancel_right₀ _ hpos.ne']

variable (g g') in
/-- Changing the reference metric multiplies relative volume densities. -/
theorem relativeVolumeDensity_eq_mul {n'' : ℕ∞ω}
    {g'' : ContMDiffRiemannianMetric I n'' E (fun x : M ↦ TangentSpace I x)} (x : M) :
    relativeVolumeDensity g g'' x =
      relativeVolumeDensity g g' x * relativeVolumeDensity g' g'' x := by
  have hpos := chartVolumeDensity_pos (I := I) (WithMetric.toWithMetric g' x)
    (by simpa only [TangentBundle.trivializationAt_baseSet] using
      mem_chart_source H (WithMetric.toWithMetric g' x))
  rw [relativeVolumeDensity_eq_div_chartVolumeDensity g g'' (mem_chart_source H x),
    relativeVolumeDensity_eq_div_chartVolumeDensity g g' (mem_chart_source H x),
    relativeVolumeDensity_eq_div_chartVolumeDensity g' g'' (mem_chart_source H x), mul_comm,
    div_mul_div_cancel₀ hpos.ne']

variable (g g') in
/-- The relative volume density is `C^k` near every point when both copies of `M` carry `C^k`
metrics. -/
theorem contMDiffAt_relativeVolumeDensity {k : ℕ∞ω} [IsManifold I (k + 1) M]
    [IsContMDiffRiemannianBundle I k E (fun x : WithMetric g ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I k E (fun x : WithMetric g' ↦ TangentSpace I x)] (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ) k (relativeVolumeDensity g g') x₀ := by
  have hsrc : (chartAt H x₀).source ∈ 𝓝 x₀ := chart_source_mem_nhds H x₀
  have hcvd {n'' : ℕ∞ω} (g'' : ContMDiffRiemannianMetric I n'' E (fun x : M ↦ TangentSpace I x))
      [IsContMDiffRiemannianBundle I k E (fun x : WithMetric g'' ↦ TangentSpace I x)] :
      ContMDiffAt I 𝓘(ℝ) k (fun x ↦ chartVolumeDensity (I := I)
        (WithMetric.toWithMetric g'' x₀) (WithMetric.toWithMetric g'' x)) x₀ :=
    ((contMDiffOn_chartVolumeDensity (I := I) (n := k) (WithMetric.toWithMetric g'' x₀)).contMDiffAt
      ((trivializationAt E (TangentSpace I) _).open_baseSet.mem_nhds
        (by simpa only [TangentBundle.trivializationAt_baseSet] using
          mem_chart_source H (WithMetric.toWithMetric g'' x₀)))).comp x₀
      WithMetric.contMDiff_toWithMetric.contMDiffAt
  refine ((hcvd g').div₀ (hcvd g) (chartVolumeDensity_pos _ ?_).ne').congr_of_eventuallyEq ?_
  · simpa only [TangentBundle.trivializationAt_baseSet] using
      mem_chart_source H (WithMetric.toWithMetric g x₀)
  · filter_upwards [hsrc] with x hx
    exact relativeVolumeDensity_eq_div_chartVolumeDensity g g' hx

variable (g g') in
/-- The relative volume density of two continuous metrics is continuous. -/
theorem continuous_relativeVolumeDensity : Continuous (relativeVolumeDensity g g') := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : IsContMDiffRiemannianBundle I 0 E (fun x : WithMetric g ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have : IsContMDiffRiemannianBundle I 0 E (fun x : WithMetric g' ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  exact continuous_iff_continuousAt.2 fun x ↦
    (contMDiffAt_relativeVolumeDensity g g' (k := 0) x).continuousAt

variable (g g') in
/-- The relative volume density is `C^k` whenever both metrics are at least `C^k`. -/
theorem contMDiff_relativeVolumeDensity {k : ℕ∞ω} [IsManifold I (k + 1) M]
    (hk : k ≤ n) (hk' : k ≤ n') :
    ContMDiff I 𝓘(ℝ) k (relativeVolumeDensity g g') := by
  have : IsContMDiffRiemannianBundle I k E (fun x : WithMetric g ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hk
  have : IsContMDiffRiemannianBundle I k E (fun x : WithMetric g' ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hk'
  exact contMDiffAt_relativeVolumeDensity g g'

section Measure

variable [LindelofSpace M]

omit [LindelofSpace M] in
/-- The relative volume density, as a density on the copy of `M` carrying `g`, is measurable. -/
private theorem measurable_ofReal_relativeVolumeDensity :
    Measurable fun x : WithMetric g ↦ ENNReal.ofReal (relativeVolumeDensity g g' x.ofWithMetric) :=
  (((continuous_relativeVolumeDensity g g').comp WithMetric.continuous_ofWithMetric).measurable
    ).ennreal_ofReal

variable (g g') in
/-- **Volume under a change of metric.** The Riemannian volume of `g'` is the image, under the
identity map between the copies of `M`, of the Riemannian volume of `g` weighted by the relative
volume density: `dV_{g'} = J dV_g`. -/
theorem riemannianVolume_eq_map_withDensity_relativeVolumeDensity :
    riemannianVolume I (WithMetric g') =
      ((riemannianVolume I (WithMetric g)).withDensity fun x ↦
          ENNReal.ofReal (relativeVolumeDensity g g' x.ofWithMetric)).map
        fun x ↦ WithMetric.toWithMetric g' x.ofWithMetric := by
  set ι : WithMetric g → WithMetric g' := fun x ↦ WithMetric.toWithMetric g' x.ofWithMetric
  have hι : Measurable ι :=
    (WithMetric.measurableEmbedding_toWithMetric_ofWithMetric g g').measurable
  symm
  refine eq_riemannianVolume_iff.2 fun β ↦ ?_
  obtain ⟨β⟩ := β
  ext s hs
  have hS : MeasurableSet (s ∩ (chartAt H (WithMetric.toWithMetric g' β)).source) :=
    hs.inter (chartAt H _).open_source.measurableSet
  have hsub : ι ⁻¹' (s ∩ (chartAt H (WithMetric.toWithMetric g' β)).source) ⊆
      (chartAt H (WithMetric.toWithMetric g β)).source := fun x hx ↦
    (WithMetric.mem_chartAt_source_iff _ x).2 ((WithMetric.mem_chartAt_source_iff _ (ι x)).1 hx.2)
  rw [Measure.restrict_apply hs, Measure.map_apply hι hS, withDensity_apply _ (hι hS),
    setLIntegral_riemannianVolume_of_subset hsub (hι hS), chartRiemannianVolume_apply _ hs]
  have himage : extChartAt I (WithMetric.toWithMetric g β) ''
      (ι ⁻¹' (s ∩ (chartAt H (WithMetric.toWithMetric g' β)).source)) =
      extChartAt I (WithMetric.toWithMetric g' β) ''
        (s ∩ (extChartAt I (WithMetric.toWithMetric g' β)).source) := by
    rw [extChartAt_source]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ι x, hx, by rw [WithMetric.extChartAt_apply, WithMetric.extChartAt_apply]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨WithMetric.toWithMetric g x.ofWithMetric, hx,
        by rw [WithMetric.extChartAt_apply, WithMetric.extChartAt_apply]⟩
  rw [himage]
  refine setLIntegral_congr_fun
    ((hs.inter (isOpen_extChartAt_source _).measurableSet).image_extChartAt _ inter_subset_right)
    fun y hy ↦ ?_
  obtain ⟨x, ⟨-, hx⟩, rfl⟩ := hy
  have hx' : x.ofWithMetric ∈ (chartAt H β).source :=
    (WithMetric.mem_chartAt_source_iff _ x).1 (by rwa [extChartAt_source] at hx)
  have hsymm : (extChartAt I β).symm (extChartAt I β x.ofWithMetric) = x.ofWithMetric :=
    (extChartAt I β).left_inv (by rwa [extChartAt_source])
  simp only [WithMetric.extChartAt_symm_apply, WithMetric.extChartAt_apply,
    WithMetric.ofWithMetric_toWithMetric, hsymm]
  rw [chartVolumeDensity_toWithMetric_eq_mul g g' hx',
    ENNReal.ofReal_mul (relativeVolumeDensity_nonneg g g' _), mul_comm]

variable (g g') in
/-- Integration of a nonnegative function against the volume of `g'`:
`∫ φ dV_{g'} = ∫ J φ dV_g`. -/
theorem lintegral_riemannianVolume_eq_lintegral_relativeVolumeDensity_mul (φ : M → ℝ≥0∞) :
    ∫⁻ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric g') =
      ∫⁻ x, ENNReal.ofReal (relativeVolumeDensity g g' x.ofWithMetric) * φ x.ofWithMetric
        ∂riemannianVolume I (WithMetric g) := by
  rw [riemannianVolume_eq_map_withDensity_relativeVolumeDensity g g',
    (WithMetric.measurableEmbedding_toWithMetric_ofWithMetric g g').lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      measurable_ofReal_relativeVolumeDensity (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [Pi.mul_apply]

variable (g g') in
/-- Integration against the volume of `g'`: `∫ φ dV_{g'} = ∫ J φ dV_g`. -/
theorem integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : M → F) :
    ∫ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric g') =
      ∫ x, relativeVolumeDensity g g' x.ofWithMetric • φ x.ofWithMetric
        ∂riemannianVolume I (WithMetric g) := by
  rw [riemannianVolume_eq_map_withDensity_relativeVolumeDensity g g',
    (WithMetric.measurableEmbedding_toWithMetric_ofWithMetric g g').integral_map,
    integral_withDensity_eq_integral_toReal_smul measurable_ofReal_relativeVolumeDensity
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (relativeVolumeDensity_nonneg g g' _)]

variable (g g') in
/-- Integrability under a change of metric is integrability after multiplying by its density. -/
theorem integrable_riemannianVolume_iff_integrable_relativeVolumeDensity_smul {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : M → F) :
    Integrable (fun x : WithMetric g' ↦ φ x.ofWithMetric)
        (riemannianVolume I (WithMetric g')) ↔
      Integrable (fun x : WithMetric g ↦ relativeVolumeDensity g g' x.ofWithMetric •
        φ x.ofWithMetric) (riemannianVolume I (WithMetric g)) := by
  rw [riemannianVolume_eq_map_withDensity_relativeVolumeDensity g g',
    (WithMetric.measurableEmbedding_toWithMetric_ofWithMetric g g').integrable_map_iff,
    integrable_withDensity_iff_integrable_smul' measurable_ofReal_relativeVolumeDensity
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (relativeVolumeDensity_nonneg g g' _)]

variable (g g') in
/-- **Total volume under a change of metric.** On a compact manifold, the total volume of `g'` is
`∫ J dV_g`. -/
theorem riemannianTotalVolume_eq_integral_relativeVolumeDensity [CompactSpace M] :
    riemannianTotalVolume I (WithMetric g') =
      ∫ x, relativeVolumeDensity g g' x.ofWithMetric ∂riemannianVolume I (WithMetric g) := by
  simpa only [integral_const, smul_eq_mul, mul_one, ← riemannianTotalVolume_def] using
    integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul g g'
      fun _ ↦ (1 : ℝ)

end Measure

end Bundle.ContMDiffRiemannianMetric
