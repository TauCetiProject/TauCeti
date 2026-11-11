/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Conformal
public import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization

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

* `TauCeti.bilinFormDetRatio`: the basis-independent ratio of the Gram determinants of two
  bilinear forms on a finite-dimensional real vector space.
* `TauCeti.relativeVolumeDensity`: the relative volume density of `g'` with respect to `g`.

## Main results

* `TauCeti.relativeVolumeDensity_eq_sqrt_det_of_orthonormal`: in a `g`-orthonormal basis, `J` is
  the square root of the Gram determinant of `g'`.
* `TauCeti.relativeVolumeDensity_pos`, `TauCeti.contMDiff_relativeVolumeDensity`: `J` is positive
  and `C^n`.
* `TauCeti.chartVolumeDensity_toWithMetric_eq_mul`: compatibility with chart volume densities.
* `TauCeti.riemannianVolume_eq_map_withDensity_relativeVolumeDensity`,
  `TauCeti.integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul`: `dV_{g'} = J dV_g`.
* `TauCeti.riemannianTotalVolume_eq_integral_relativeVolumeDensity`: on a compact manifold,
  `Vol(g') = ∫ J dV_g`.
* `TauCeti.relativeVolumeDensity_rescale`: the conformal case.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 2.44 and the discussion of Riemannian densities following it.
-/

public section

open Bundle MeasureTheory Set Riemannian.Tensor
open scoped ENNReal Manifold ContDiff Topology

noncomputable section

namespace TauCeti

section LinearAlgebra

open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The Gram determinant of a symmetric positive-definite bilinear form is positive in every
basis. -/
theorem det_toMatrix_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V)
    {B : BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    0 < (BilinForm.toMatrix b B).det :=
  ((BilinForm.posDef_toQuadraticMap_iff_matrix b B ⟨hsymm⟩).1 hpos).det_pos

variable [Module.Finite ℝ V]

/-- The ratio `det B' / det B` of the Gram determinants of two bilinear forms on a
finite-dimensional real vector space, computed in the basis `Module.finBasis ℝ V`. It does not
depend on the basis: see `TauCeti.bilinFormDetRatio_eq`. -/
def bilinFormDetRatio (B B' : BilinForm ℝ V) : ℝ :=
  (BilinForm.toMatrix (Module.finBasis ℝ V) B').det /
    (BilinForm.toMatrix (Module.finBasis ℝ V) B).det

/-- **Basis independence of the Gram determinant ratio.** In any basis `b`, `bilinFormDetRatio B B'`
is the ratio of the Gram determinants of `B'` and `B`. -/
theorem bilinFormDetRatio_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ V)
    (B B' : BilinForm ℝ V) :
    bilinFormDetRatio B B' =
      (BilinForm.toMatrix b B').det / (BilinForm.toMatrix b B).det := by
  set b₀ := (Module.finBasis ℝ V).reindex ((Module.finBasis ℝ V).indexEquiv b)
  have hP : (b₀.toMatrix b).det ≠ 0 := by
    rw [← Module.Basis.det_apply]
    exact (b₀.isUnit_det b).ne_zero
  rw [bilinFormDetRatio,
    ← BilinForm.det_toMatrix_reindex _ ((Module.finBasis ℝ V).indexEquiv b) B,
    ← BilinForm.det_toMatrix_reindex _ ((Module.finBasis ℝ V).indexEquiv b) B',
    BilinForm.det_toMatrix_eq_det_sq_mul_det b₀ b, BilinForm.det_toMatrix_eq_det_sq_mul_det b₀ b,
    mul_div_mul_left _ _ (pow_ne_zero 2 hP)]

/-- In a basis in which `B` has the identity Gram matrix, `bilinFormDetRatio B B'` is the Gram
determinant of `B'`. -/
theorem bilinFormDetRatio_eq_det_of_toMatrix_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) {B : BilinForm ℝ V} (hB : BilinForm.toMatrix b B = 1)
    (B' : BilinForm ℝ V) :
    bilinFormDetRatio B B' = (BilinForm.toMatrix b B').det := by
  rw [bilinFormDetRatio_eq b, hB, Matrix.det_one, div_one]

/-- The Gram determinant ratio of two symmetric positive-definite bilinear forms is positive. -/
theorem bilinFormDetRatio_pos {B B' : BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v)
    (hpos : ∀ v, v ≠ 0 → 0 < B v v) (hsymm' : ∀ v w, B' v w = B' w v)
    (hpos' : ∀ v, v ≠ 0 → 0 < B' v v) :
    0 < bilinFormDetRatio B B' :=
  div_pos (det_toMatrix_pos _ hsymm' hpos') (det_toMatrix_pos _ hsymm hpos)

/-- The Gram determinant ratio of a symmetric positive-definite bilinear form with itself is
one. -/
theorem bilinFormDetRatio_self {B : BilinForm ℝ V} (hsymm : ∀ v w, B v w = B w v)
    (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    bilinFormDetRatio B B = 1 :=
  div_self (det_toMatrix_pos _ hsymm hpos).ne'

end LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n n' : ℕ∞ω}

/-- The **relative volume density** of a Riemannian metric `g'` with respect to a Riemannian
metric `g` at `x`: the square root of the ratio of the Gram determinants of `g'_x` and `g_x` in
any basis of `T_x M`. -/
def relativeVolumeDensity (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x)) (x : M) : ℝ :=
  √(bilinFormDetRatio (g.inner x).toBilinForm (g'.inner x).toBilinForm)

variable {g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x)}

/-- The definition of the relative volume density. -/
theorem relativeVolumeDensity_def (x : M) :
    relativeVolumeDensity g g' x =
      √(bilinFormDetRatio (g.inner x).toBilinForm (g'.inner x).toBilinForm) :=
  (rfl)

/-- The relative volume density in a basis `b` of `T_x M`. -/
theorem relativeVolumeDensity_eq_sqrt_div {x : M} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I x)) :
    relativeVolumeDensity g g' x =
      √((Matrix.of fun i j ↦ g'.inner x (b i) (b j)).det /
        (Matrix.of fun i j ↦ g.inner x (b i) (b j)).det) := by
  rw [relativeVolumeDensity, bilinFormDetRatio_eq b]
  congr 3 <;> ext i j <;> simp [LinearMap.BilinForm.toMatrix_apply]

/-- **The relative volume density in an orthonormal basis.** If `b` is a `g`-orthonormal basis of
`T_x M`, the relative volume density of `g'` with respect to `g` at `x` is the square root of the
Gram determinant of `g'_x` in `b`. -/
theorem relativeVolumeDensity_eq_sqrt_det_of_orthonormal {x : M} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    relativeVolumeDensity g g' x = √(Matrix.of fun i j ↦ g'.inner x (b i) (b j)).det := by
  rw [relativeVolumeDensity_eq_sqrt_div b]
  congr 1
  rw [show (Matrix.of fun i j ↦ g.inner x (b i) (b j)) = 1 by
    ext i j; simp [hb, Matrix.one_apply], Matrix.det_one, div_one]

/-- The relative volume density is nonnegative. -/
theorem relativeVolumeDensity_nonneg (x : M) : 0 ≤ relativeVolumeDensity g g' x :=
  Real.sqrt_nonneg _

/-- The relative volume density is positive. -/
theorem relativeVolumeDensity_pos (x : M) : 0 < relativeVolumeDensity g g' x :=
  Real.sqrt_pos.2 <| bilinFormDetRatio_pos (g.symm x) (g.pos x) (g'.symm x) (g'.pos x)

/-- The relative volume density of a metric with respect to itself is one. -/
@[simp]
theorem relativeVolumeDensity_self (x : M) : relativeVolumeDensity g g x = 1 := by
  rw [relativeVolumeDensity, bilinFormDetRatio_self (g.symm x) (g.pos x), Real.sqrt_one]

/-- The chart Gram matrix of the copy of `M` carrying `g` is the Gram matrix of `g` in the chart
frame of `M`. -/
theorem chartGramMatrix_toWithMetric (g : ContMDiffRiemannianMetric I n E
    (fun x : M ↦ TangentSpace I x)) (α x : M) :
    chartGramMatrix (I := I) (WithMetric.toWithMetric g α) (WithMetric.toWithMetric g x) =
      Matrix.of fun i j ↦
        g.inner x (chartLocalFrame (I := I) α i x) (chartLocalFrame (I := I) α j x) := by
  ext i j
  rw [chartGramMatrix_apply, WithMetric.inner_def, WithMetric.mfderiv_ofWithMetric_chartLocalFrame,
    WithMetric.mfderiv_ofWithMetric_chartLocalFrame]
  rfl

/-- On the chart source at `α`, the relative volume density is the ratio of the Gram determinants
of the two metrics in the chart frame. -/
theorem relativeVolumeDensity_eq_sqrt_div_chartGramMatrix {α x : M}
    (hx : x ∈ (chartAt H α).source) :
    relativeVolumeDensity g g' x =
      √((chartGramMatrix (I := I) (WithMetric.toWithMetric g' α)
          (WithMetric.toWithMetric g' x)).det /
        (chartGramMatrix (I := I) (WithMetric.toWithMetric g α)
          (WithMetric.toWithMetric g x)).det) := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  rw [relativeVolumeDensity_eq_sqrt_div
    ((trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E) hx'),
    chartGramMatrix_toWithMetric, chartGramMatrix_toWithMetric]
  simp only [chartLocalFrame_apply_of_mem_chart_source α hx]

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
  rw [relativeVolumeDensity_eq_sqrt_div_chartGramMatrix hx, chartVolumeDensity_def,
    chartVolumeDensity_def, ← Real.sqrt_mul (div_nonneg (chartGramMatrix_det_nonneg _ _)
      hpos.le), div_mul_cancel₀ _ hpos.ne']

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
  rw [chartVolumeDensity_toWithMetric_eq_mul (g := g) hx, mul_div_cancel_right₀ _ hpos.ne']

/-- The relative volume density is `C^k` near every point when both copies of `M` carry `C^k`
metrics. -/
private theorem contMDiffAt_relativeVolumeDensity_aux {k : ℕ∞ω} [IsManifold I (k + 1) M]
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
    exact relativeVolumeDensity_eq_div_chartVolumeDensity hx

/-- The relative volume density of two continuous metrics is continuous. -/
theorem continuous_relativeVolumeDensity : Continuous (relativeVolumeDensity g g') := by
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : IsContMDiffRiemannianBundle I 0 E (fun x : WithMetric g ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have : IsContMDiffRiemannianBundle I 0 E (fun x : WithMetric g' ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  exact continuous_iff_continuousAt.2 fun x ↦
    (contMDiffAt_relativeVolumeDensity_aux (k := 0) x).continuousAt

/-- **Smoothness of the relative volume density.** The relative volume density of two `C^n`
metrics on a `C^(n+1)` manifold is `C^n`. -/
theorem contMDiff_relativeVolumeDensity [IsManifold I (n + 1) M]
    {g g' : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)} :
    ContMDiff I 𝓘(ℝ) n (relativeVolumeDensity g g') :=
  contMDiffAt_relativeVolumeDensity_aux

section Measure

variable [LindelofSpace M]

omit [FiniteDimensional ℝ E] [LindelofSpace M] in
/-- The identity map from the copy of `M` carrying `g` to the copy carrying `g'` is a measurable
embedding. -/
private theorem measurableEmbedding_toWithMetric_ofWithMetric :
    MeasurableEmbedding fun x : WithMetric g ↦ WithMetric.toWithMetric g' x.ofWithMetric :=
  .of_measurable_inverse
    (WithMetric.continuous_toWithMetric.comp WithMetric.continuous_ofWithMetric).measurable
    (by rw [range_eq_univ.2 fun y ↦ ⟨WithMetric.toWithMetric g y.ofWithMetric, rfl⟩]; exact .univ)
    (WithMetric.continuous_toWithMetric.comp WithMetric.continuous_ofWithMetric).measurable
    fun _ ↦ rfl

omit [LindelofSpace M] in
/-- The relative volume density, as a density on the copy of `M` carrying `g`, is measurable. -/
private theorem measurable_ofReal_relativeVolumeDensity :
    Measurable fun x : WithMetric g ↦ ENNReal.ofReal (relativeVolumeDensity g g' x.ofWithMetric) :=
  ((continuous_relativeVolumeDensity.comp WithMetric.continuous_ofWithMetric).measurable
    ).ennreal_ofReal

/-- **Volume under a change of metric.** The Riemannian volume of `g'` is the image, under the
identity map between the copies of `M`, of the Riemannian volume of `g` weighted by the relative
volume density: `dV_{g'} = J dV_g`. -/
theorem riemannianVolume_eq_map_withDensity_relativeVolumeDensity :
    riemannianVolume I (WithMetric g') =
      ((riemannianVolume I (WithMetric g)).withDensity fun x ↦
          ENNReal.ofReal (relativeVolumeDensity g g' x.ofWithMetric)).map
        fun x ↦ WithMetric.toWithMetric g' x.ofWithMetric := by
  set ι : WithMetric g → WithMetric g' := fun x ↦ WithMetric.toWithMetric g' x.ofWithMetric
  have hι : Measurable ι := measurableEmbedding_toWithMetric_ofWithMetric.measurable
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
  rw [chartVolumeDensity_toWithMetric_eq_mul (g := g) (g' := g') hx',
    ENNReal.ofReal_mul (relativeVolumeDensity_nonneg _), mul_comm]

/-- Integration of a nonnegative function against the volume of `g'`:
`∫ φ dV_{g'} = ∫ J φ dV_g`. -/
theorem lintegral_riemannianVolume_eq_lintegral_relativeVolumeDensity_mul (φ : M → ℝ≥0∞) :
    ∫⁻ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric g') =
      ∫⁻ x, ENNReal.ofReal (relativeVolumeDensity g g' x.ofWithMetric) * φ x.ofWithMetric
        ∂riemannianVolume I (WithMetric g) := by
  rw [riemannianVolume_eq_map_withDensity_relativeVolumeDensity (g := g),
    measurableEmbedding_toWithMetric_ofWithMetric.lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      measurable_ofReal_relativeVolumeDensity (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [Pi.mul_apply]

/-- Integration against the volume of `g'`: `∫ φ dV_{g'} = ∫ J φ dV_g`. -/
theorem integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : M → F) :
    ∫ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric g') =
      ∫ x, relativeVolumeDensity g g' x.ofWithMetric • φ x.ofWithMetric
        ∂riemannianVolume I (WithMetric g) := by
  rw [riemannianVolume_eq_map_withDensity_relativeVolumeDensity (g := g),
    measurableEmbedding_toWithMetric_ofWithMetric.integral_map,
    integral_withDensity_eq_integral_toReal_smul measurable_ofReal_relativeVolumeDensity
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (relativeVolumeDensity_nonneg _)]

/-- **Total volume under a change of metric.** On a compact manifold, the total volume of `g'` is
`∫ J dV_g`. -/
theorem riemannianTotalVolume_eq_integral_relativeVolumeDensity [CompactSpace M] :
    riemannianTotalVolume I (WithMetric g') =
      ∫ x, relativeVolumeDensity g g' x.ofWithMetric ∂riemannianVolume I (WithMetric g) := by
  simpa only [integral_const, smul_eq_mul, mul_one, ← riemannianTotalVolume_def] using
    integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul (g := g) (g' := g')
      fun _ ↦ (1 : ℝ)

end Measure

/-- **The conformal case.** In real dimension `N`, the relative volume density of the rescaled
metric `f g` with respect to `g` is `f ^ (N / 2)`. -/
theorem relativeVolumeDensity_rescale {f : M → ℝ} {hf : ContMDiff I 𝓘(ℝ) n f}
    {hf_pos : ∀ x, 0 < f x} (x : M) :
    relativeVolumeDensity g (g.rescale f hf hf_pos) x =
      f x ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  have hpos : 0 < (LinearMap.BilinForm.toMatrix (Module.finBasis ℝ (TangentSpace I x))
      (g.inner x).toBilinForm).det :=
    det_toMatrix_pos _ (g.symm x) (g.pos x)
  have hmat : LinearMap.BilinForm.toMatrix (Module.finBasis ℝ (TangentSpace I x))
      ((g.rescale f hf hf_pos).inner x).toBilinForm =
      f x • LinearMap.BilinForm.toMatrix (Module.finBasis ℝ (TangentSpace I x))
        (g.inner x).toBilinForm := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply]
  rw [relativeVolumeDensity, bilinFormDetRatio, hmat, Matrix.det_smul, Fintype.card_fin,
    mul_div_cancel_right₀ _ hpos.ne', Real.sqrt_pow_eq_rpow (hf_pos x).le]
  rfl

end TauCeti
