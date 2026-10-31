/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# Pullback of metrics is continuous in the chart C² topology

Let `f : M → N` be a smooth immersion. Read in the chart at `x'` of `M` and the chart at `x` of `N`,
the pullback metric `f^* g` is the congruence of the chart metric of `g` by the derivative of the
transition map `τ = (extChartAt x) ∘ f ∘ (extChartAt x').symm`:
`(f^* g)_{x'}(z) (u, w) = g_x(τ z) (Dτ_z u, Dτ_z w)` (`chartMetric_pullback`). The two charts need
not be centred at corresponding points.

The right-hand side is linear in `g` and involves only `τ` and its first derivative. Hence the
coordinate derivatives of `f^* g` of order at most two on a compact set are controlled by those of
`g` on its image under `τ`, with constants independent of `g`. Therefore pulling back along a fixed
smooth immersion is continuous for the chart C² topologies (`continuous_pullback_chartC2`), and
pulling back along a diffeomorphism is a homeomorphism of the spaces of smooth metrics
(`Diffeomorph.pullbackMetricHomeomorph`). This is the metric-family law of pullback: a continuous
family of metrics on `N` pulls back to a continuous family on `M`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.chartMetric_pullback`: the pullback metric in arbitrary charts.
* `Bundle.ContMDiffRiemannianMetric.continuous_pullback_chartC2`: pulling back along a smooth
  immersion is continuous in the chart C² topology.
* `Diffeomorph.pullbackMetricHomeomorph`: a diffeomorphism `M ≃ N` induces a homeomorphism from
  the smooth metrics on `N` to those on `M` by pulling back.
-/

open Bundle Set Filter Topology
open scoped ContDiff Manifold

public section

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- The pullback metric read in the chart at `x'` is the chart metric of `g` at `x`, evaluated at
the image under the transition map `τ = (extChartAt J x) ∘ f ∘ (extChartAt I x').symm` and pulled
back along the derivative of `τ` within the model range.

The metric `g` is smooth because `TauCeti.Manifold.ContMDiffNondegenerateMetric.chartMetric`,
like the chart C² topology built from it, is only defined for smooth metrics; `pullback` then
requires `f` to be smooth as well. The charts are arbitrary and need not be centred at
corresponding points. -/
theorem chartMetric_pullback
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {f : M → N}
    (hf : ContMDiff I J (∞ + 1) f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    {x' : M} {x : N} {z : E} (hz : z ∈ (extChartAt I x').target)
    (hfz : f ((extChartAt I x').symm z) ∈ (extChartAt J x).source) :
    (g.pullback f hf hinj).toNondegenerateMetric.chartMetric x' z =
      (ContinuousLinearMap.precomp ℝ
          (fderivWithin ℝ (extChartAt J x ∘ f ∘ (extChartAt I x').symm) (range I) z)).comp
        ((g.toNondegenerateMetric.chartMetric x
            (extChartAt J x (f ((extChartAt I x').symm z)))).comp
          (fderivWithin ℝ (extChartAt J x ∘ f ∘ (extChartAt I x').symm) (range I) z)) := by
  set y := (extChartAt I x').symm z
  have hy : y ∈ (chartAt H x').source := by
    simpa only [extChartAt_source] using (extChartAt I x').map_target hz
  have hfy : f y ∈ (chartAt H' x).source := by simpa only [extChartAt_source] using hfz
  have hzy : extChartAt I x' y = z := (extChartAt I x').right_inv hz
  -- The derivative of the transition map is the differential of `f` read in the two
  -- trivializations of the tangent bundles.
  have hA : fderivWithin ℝ (extChartAt J x ∘ f ∘ (extChartAt I x').symm) (range I) z =
      (trivializationAt F (TangentSpace J) x).continuousLinearMapAt ℝ (f y) ∘L
        mfderiv I J f y ∘L (trivializationAt E (TangentSpace I) x').symmL ℝ y := by
    have h := ((hf y).mdifferentiableAt (by simp)).hasMFDerivAt.hasFDerivWithinAt_of_mem_source
      hy hfy
    rw [hzy] at h
    rw [h.fderivWithin (I.uniqueDiffOn _ (extChartAt_target_subset_range x' hz)),
      TangentBundle.continuousLinearMapAt_trivializationAt hfy,
      TangentBundle.symmL_trivializationAt hy, hzy]
  have hbase : f y ∈ (trivializationAt F (TangentSpace J) x).baseSet := by simpa using hfy
  have hbase' : y ∈ (trivializationAt E (TangentSpace I) x').baseSet := by simpa using hy
  have key (v : TangentSpace J (f y)) : (trivializationAt F (TangentSpace J) x).symm (f y)
      ((trivializationAt F (TangentSpace J) x).continuousLinearMapAt ℝ (f y) v) = v := by
    rw [← Trivialization.symmL_apply (R := ℝ) _ hbase]
    exact Trivialization.symmL_continuousLinearMapAt _ hbase v
  ext u w
  simp only [ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply,
    g.toNondegenerateMetric.chartMetric_extChartAt_apply hfz, hA, key,
    (g.pullback f hf hinj).toNondegenerateMetric.chartMetric_apply hz,
    toNondegenerateMetric_apply, pullback_inner, Trivialization.symmL_apply _ hbase']
  -- Both sides are now the same expression, with `y` abbreviating its definition.
  rfl

section Topology

variable [I.Boundaryless] [J.Boundaryless]

attribute [local instance] chartC2Topology

-- Cache the canonical operator-space instances, as in the definition of the chart C² topology:
-- searching for the topology on iterated multilinear maps into nested operator spaces otherwise
-- exhausts instance-search heartbeats.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Near each point of a chart target of `M`, the coordinate derivatives of `f^* g` of order at
most two converge uniformly as `g` tends to `g₀` in the chart C² topology. -/
private theorem exists_mem_nhds_tendstoUniformlyOn_iteratedFDeriv_chartMetric_pullback
    {f : M → N} (hf : ContMDiff I J (∞ + 1) f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    (g₀ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) (x' : M) {m : ℕ}
    (hm : m < 3) {z₀ : E} (hz₀ : z₀ ∈ (extChartAt I x').target) :
    ∃ B ∈ 𝓝 z₀, TendstoUniformlyOn
      (fun g z ↦ iteratedFDeriv ℝ m ((g.pullback f hf hinj).toNondegenerateMetric.chartMetric x') z)
      (fun z ↦ iteratedFDeriv ℝ m ((g₀.pullback f hf hinj).toNondegenerateMetric.chartMetric x') z)
      (𝓝 g₀) B := by
  -- Work in the chart of `N` at the image of `z₀`, on the open set `W` where the transition map
  -- `τ` is defined, and on a compact neighbourhood `B ⊆ W` of `z₀`.
  set x := f ((extChartAt I x').symm z₀)
  set τ := extChartAt J x ∘ f ∘ (extChartAt I x').symm
  set W := (extChartAt I x').target ∩ (extChartAt I x').symm ⁻¹' (f ⁻¹' (extChartAt J x).source)
  have hW : IsOpen W := (continuousOn_extChartAt_symm x').isOpen_inter_preimage
    (isOpen_extChartAt_target x') (hf.continuous.isOpen_preimage _ (isOpen_extChartAt_source x))
  obtain ⟨B, hB, hBW, hBc⟩ := local_compact_nhds (hW.mem_nhds ⟨hz₀, mem_extChartAt_source x⟩)
  have hτ : ContDiffOn ℝ ∞ τ W := by
    have h := ((contMDiffOn_iff (s := univ)).mp (hf.of_le le_self_add).contMDiffOn).2 x' x
    rwa [univ_inter] at h
  have hmaps : MapsTo τ W (extChartAt J x).target := fun z hz ↦ (extChartAt J x).map_source hz.2
  -- `L z` pulls bilinear forms back along `Dτ_z`, as a continuous linear map in the form.
  set L : E → (F →L[ℝ] F →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := fun z ↦
    (ContinuousLinearMap.compL ℝ E (F →L[ℝ] ℝ) (E →L[ℝ] ℝ)
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip (fderiv ℝ τ z))).comp
      ((ContinuousLinearMap.compL ℝ E F (F →L[ℝ] ℝ)).flip (fderiv ℝ τ z))
  have hDτ : ContDiffOn ℝ m (fderiv ℝ τ) W := hτ.fderiv_of_isOpen hW (by simp)
  have hL : ContDiffOn ℝ m L W :=
    ((ContinuousLinearMap.compL ℝ E (F →L[ℝ] ℝ) (E →L[ℝ] ℝ)).contDiff.comp_contDiffOn
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip.contDiff.comp_contDiffOn hDτ)).clm_comp
      ((ContinuousLinearMap.compL ℝ E F (F →L[ℝ] ℝ)).flip.contDiff.comp_contDiffOn hDτ)
  -- On `W`, the difference of two pullbacks is `L` applied to the difference `φ g` of the chart
  -- metrics at `x`, along `τ`.
  set φ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y) → F → _ :=
    fun g ↦ g.toNondegenerateMetric.chartMetric x - g₀.toNondegenerateMetric.chartMetric x
  have hpull (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {z : E}
      (hz : z ∈ W) : (g.pullback f hf hinj).toNondegenerateMetric.chartMetric x' z =
        L z (g.toNondegenerateMetric.chartMetric x (τ z)) := by
    rw [chartMetric_pullback g hf hinj hz.1 hz.2, I.range_eq_univ, fderivWithin_univ]
    -- Both sides pair `u` and `w` through `Dτ_z`; `τ z` unfolds to
    -- `extChartAt J x (f ((extChartAt I x').symm z))`.
    ext u w
    rfl
  have hdiff (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {z : E}
      (hz : z ∈ W) :
      iteratedFDeriv ℝ m ((g.pullback f hf hinj).toNondegenerateMetric.chartMetric x') z -
        iteratedFDeriv ℝ m ((g₀.pullback f hf hinj).toNondegenerateMetric.chartMetric x') z =
      iteratedFDerivWithin ℝ m (fun y ↦ L y (φ g (τ y))) W z := by
    have hnhds := (isOpen_extChartAt_target x').mem_nhds hz.1
    have heq : (g.pullback f hf hinj).toNondegenerateMetric.chartMetric x' -
        (g₀.pullback f hf hinj).toNondegenerateMetric.chartMetric x' =ᶠ[𝓝 z]
        fun y ↦ L y (φ g (τ y)) := by
      filter_upwards [hW.mem_nhds hz] with y hy
      simp only [Pi.sub_apply, hpull g hy, hpull g₀ hy, φ, map_sub]
    rw [← iteratedFDeriv_sub_apply
        (contDiffAt_infty.mp (((g.pullback f hf hinj).toNondegenerateMetric.contDiffOn_chartMetric
          x').contDiffAt hnhds) m)
        (contDiffAt_infty.mp (((g₀.pullback f hf hinj).toNondegenerateMetric.contDiffOn_chartMetric
          x').contDiffAt hnhds) m),
      (heq.iteratedFDeriv ℝ m).self_of_nhds, iteratedFDerivWithin_of_isOpen m hW hz]
  -- The chart derivatives of `g` at `x` of order at most two converge to those of `g₀`
  -- uniformly on the compact set `τ '' B`.
  set Kx : Set (extChartAt J x).target := Subtype.val ⁻¹' (τ '' B)
  have hKx : IsCompact Kx := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr ((image_mono hBW).trans hmaps.image_subset)]
    exact hBc.image_of_continuousOn (hτ.continuousOn.mono hBW)
  have hφ₀ (j : ℕ) (hj : j ≤ m) : TendstoUniformlyOn
      (fun g z ↦ iteratedFDerivWithin ℝ j (φ g) (extChartAt J x).target (τ z)) (fun _ ↦ 0)
      (𝓝 g₀) B := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun δ hδ ↦ ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp ((tendsto_chartC2_iff (g := fun g ↦ g)).mp
      tendsto_id x ⟨j, by omega⟩ Kx hKx) δ hδ] with g hg z hz
    have hτz := hmaps (hBW hz)
    have hnhds := (isOpen_extChartAt_target x).mem_nhds hτz
    rw [iteratedFDerivWithin_of_isOpen j (isOpen_extChartAt_target x) hτz,
      iteratedFDeriv_sub_apply
        (contDiffAt_infty.mp ((g.toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt
          hnhds) j)
        (contDiffAt_infty.mp ((g₀.toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt
          hnhds) j),
      dist_zero_left, ← dist_eq_norm, dist_comm]
    exact hg ⟨τ z, hτz⟩ (mem_image_of_mem τ hz)
  have hlim := hL.tendstoUniformlyOn_iteratedFDerivWithin_clm_apply_comp
    (contDiffOn_infty.mp hτ m) hW.uniqueDiffOn (isOpen_extChartAt_target x).uniqueDiffOn hmaps
    hBc hBW (Eventually.of_forall fun g ↦ contDiffOn_infty.mp
      ((g.toNondegenerateMetric.contDiffOn_chartMetric x).sub
        (g₀.toNondegenerateMetric.contDiffOn_chartMetric x)) m) hφ₀
  refine ⟨B, hB, Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim ε hε] with g hg z hz
  rw [dist_comm, dist_eq_norm, hdiff g (hBW hz), ← dist_zero_left]
  exact hg z hz

/-- Pulling back along a fixed smooth immersion is continuous for the chart C² topologies: if
metrics `g` on `N` converge to `g₀` with their coordinate derivatives through order two, uniformly
on compact chart sets, then so do their pullbacks to `M`. -/
theorem continuous_pullback_chartC2 {f : M → N} (hf : ContMDiff I J (∞ + 1) f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    Continuous (fun g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y) ↦
      g.pullback f hf hinj) := by
  refine continuous_iff_continuousAt.mpr fun g₀ ↦ tendsto_chartC2_iff.mpr fun x' m K hK ↦ ?_
  -- Uniform convergence holds near every point of the open chart target, hence on its compact
  -- subsets.
  have hloc : TendstoLocallyUniformlyOn
      (fun g z ↦ iteratedFDeriv ℝ m ((g.pullback f hf hinj).toNondegenerateMetric.chartMetric x') z)
      (fun z ↦ iteratedFDeriv ℝ m ((g₀.pullback f hf hinj).toNondegenerateMetric.chartMetric x') z)
      (𝓝 g₀) (extChartAt I x').target :=
    tendstoLocallyUniformlyOn_of_forall_exists_nhds fun z hz ↦
      let ⟨B, hB, h⟩ := exists_mem_nhds_tendstoUniformlyOn_iteratedFDeriv_chartMetric_pullback
        hf hinj g₀ x' m.isLt hz
      ⟨B, mem_nhdsWithin_of_mem_nhds hB, h⟩
  exact (((tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_extChartAt_target x')).mp hloc
    (Subtype.val '' K) (image_subset_iff.mpr fun z _ ↦ z.2)
    (hK.image continuous_subtype_val)).comp Subtype.val).mono (subset_preimage_image _ _)

end Topology

end Bundle.ContMDiffRiemannianMetric

namespace Diffeomorph

open Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

attribute [local instance] Bundle.ContMDiffRiemannianMetric.chartC2Topology

/-- Pulling smooth metrics back along a diffeomorphism `Φ : M ≃ N` is a homeomorphism from the
metrics on `N` to the metrics on `M`, for the chart C² topologies. Its inverse pulls back along
`Φ.symm`. -/
def pullbackMetricHomeomorph (Φ : M ≃ₘ^∞⟮I, J⟯ N) :
    Bundle.ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y) ≃ₜ
      Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) where
  toFun g := g.pullback Φ (Φ.contMDiff.of_le (by simp))
    fun x ↦ Function.LeftInverse.injective (Φ.mfderiv_symm_apply_mfderiv_apply (by simp) x)
  invFun g := g.pullback Φ.symm (Φ.symm.contMDiff.of_le (by simp))
    fun y ↦ Function.LeftInverse.injective (Φ.symm.mfderiv_symm_apply_mfderiv_apply (by simp) y)
  left_inv g := (pullback_comp g Φ Φ.symm _ _ _ _).symm.trans
    ((pullback_congr g Φ.self_comp_symm _ _ contMDiff_id fun _ ↦ by
      simpa [mfderiv_id] using Function.injective_id).trans (pullback_id g _ _))
  right_inv g := (pullback_comp g Φ.symm Φ _ _ _ _).symm.trans
    ((pullback_congr g Φ.symm_comp_self _ _ contMDiff_id fun _ ↦ by
      simpa [mfderiv_id] using Function.injective_id).trans (pullback_id g _ _))
  continuous_toFun := continuous_pullback_chartC2 _ _
  continuous_invFun := continuous_pullback_chartC2 _ _

/-- The homeomorphism induced by a diffeomorphism `Φ` pulls metrics back along `Φ`. -/
theorem pullbackMetricHomeomorph_apply (Φ : M ≃ₘ^∞⟮I, J⟯ N)
    (g : Bundle.ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (hf : ContMDiff I J (∞ + 1) Φ) (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) :
    Φ.pullbackMetricHomeomorph g = g.pullback Φ hf hinj :=
  (rfl)

/-- The inverse of the homeomorphism induced by a diffeomorphism `Φ` pulls metrics back along
`Φ.symm`. -/
theorem pullbackMetricHomeomorph_symm_apply (Φ : M ≃ₘ^∞⟮I, J⟯ N)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hf : ContMDiff J I (∞ + 1) Φ.symm) (hinj : ∀ y, Function.Injective (mfderiv J I Φ.symm y)) :
    Φ.pullbackMetricHomeomorph.symm g = g.pullback Φ.symm hf hinj :=
  (rfl)

/-- The metric induced by `Φ` pairs two tangent vectors as `g` pairs their images under the
differential of `Φ`. -/
@[simp]
theorem pullbackMetricHomeomorph_apply_inner (Φ : M ≃ₘ^∞⟮I, J⟯ N)
    (g : Bundle.ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) (x : M)
    (v w : TangentSpace I x) :
    (Φ.pullbackMetricHomeomorph g).inner x v w =
      g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) :=
  pullback_inner ..

/-- The metric induced by the inverse of `Φ` pairs two tangent vectors as `g` pairs their images
under the differential of `Φ.symm`. -/
@[simp]
theorem pullbackMetricHomeomorph_symm_apply_inner (Φ : M ≃ₘ^∞⟮I, J⟯ N)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (y : N)
    (v w : TangentSpace J y) :
    (Φ.pullbackMetricHomeomorph.symm g).inner y v w =
      g.inner (Φ.symm y) (mfderiv J I Φ.symm y v) (mfderiv J I Φ.symm y w) :=
  pullback_inner ..

end Diffeomorph
