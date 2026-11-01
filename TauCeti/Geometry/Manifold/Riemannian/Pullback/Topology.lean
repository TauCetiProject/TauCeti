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
# Pullback and change of charts in the chart Cᵏ topologies

Let `f : M → N` be a smooth immersion. Read in the chart at `x'` of `M` and the chart at `x` of `N`,
the pullback metric `f^* g` is the congruence of the chart metric of `g` by the derivative of the
transition map `τ = (extChartAt x) ∘ f ∘ (extChartAt x').symm`:
`(f^* g)_{x'}(z) (u, w) = g_x(τ z) (Dτ_z u, Dτ_z w)` (`chartMetric_pullback`). The two charts need
not be centred at corresponding points.

The right-hand side is linear in `g` and involves only `τ` and its first derivative. Hence the
coordinate derivatives of `f^* g` of order at most `m` near a point are controlled by those of `g`
near its image under `τ`, with constants independent of `g`
(`exists_mem_nhds_tendstoUniformlyOn_iteratedFDeriv_chartMetric_pullback`). Therefore pulling back
along a fixed smooth immersion is continuous for the chart C² topologies
(`continuous_pullback_chartC2`), and pulling back along a diffeomorphism is a homeomorphism of the
spaces of smooth metrics (`Diffeomorph.pullbackMetricHomeomorph`). This is the metric-family law of
pullback: a continuous family of metrics on `N` pulls back to a continuous family on `M`.

For `f` the identity the same estimate compares the coordinate derivatives of one metric in two
charts of `M`. Hence the chart Cᵏ topology, defined through the charts at all points of `M`, is
already determined by any family of compact sets in chart targets whose interiors cover `M`
(`tendsto_chartCk_iff_of_forall_mem_nhds`), and is the topology induced by the charts at the points
of any set whose chart domains cover `M` (`chartCkTopology_eq_induced`). On a compact manifold
finitely many charts suffice: convergence in the chart Cᵏ topology is uniform convergence of the
coordinate derivatives of order at most `k` on finitely many compact chart sets
(`exists_finset_tendsto_chartCk_iff`). For finite `k` these are finitely many sup-seminorms of
coordinate derivatives.

## Main results

* `Bundle.ContMDiffRiemannianMetric.chartMetric_pullback`: the pullback metric in arbitrary charts.
* `Bundle.ContMDiffRiemannianMetric.continuous_pullback_chartC2`: pulling back along a smooth
  immersion is continuous in the chart C² topology.
* `Diffeomorph.pullbackMetricHomeomorph`: a diffeomorphism `M ≃ N` induces a homeomorphism from
  the smooth metrics on `N` to those on `M` by pulling back.
* `Bundle.ContMDiffRiemannianMetric.chartCkTopology_eq_induced`: the chart Cᵏ topology is induced
  by the charts at the points of any set whose chart domains cover `M`.
* `Bundle.ContMDiffRiemannianMetric.exists_finset_tendsto_chartCk_iff`: on a compact manifold the
  chart Cᵏ topology is described by finitely many compact chart sets.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for the weak Cʳ topology defined
  through local charts.
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

-- Public signatures cannot use private cached instances. Insert the canonical instances
-- directly into each signature involving nested operator spaces, avoiding instance-search
-- timeouts without exporting duplicate instances or changing the global search priorities.
local macro "withMetricOperatorNorms " E:term " in " t:term : term =>
  `(letI : NormedAddCommGroup ($E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ ($E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    letI : NormedAddCommGroup ($E →L[ℝ] $E →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ ($E →L[ℝ] $E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    $t)

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

/-- Near each point `z₀` of a chart target of `M`, the order-`m` coordinate derivatives of the
pullbacks `f^* (g i)` converge uniformly to those of `f^* g₀`, provided the coordinate derivatives
of order at most `m` of the metrics `g i`, read in some chart of `N` at `x` containing the image
point, converge uniformly on the compact subsets of a neighbourhood `V` of that image point. -/
theorem exists_mem_nhds_tendstoUniformlyOn_iteratedFDeriv_chartMetric_pullback
    {f : M → N} (hf : ContMDiff I J (∞ + 1) f) (hinj : ∀ x, Function.Injective (mfderiv I J f x))
    {ι : Type*} {l : Filter ι}
    {g : ι → ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}
    {g₀ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)} {x' : M} {x : N} {m : ℕ}
    {z₀ : E} (hz₀ : z₀ ∈ (extChartAt I x').target)
    (hfz₀ : f ((extChartAt I x').symm z₀) ∈ (extChartAt J x).source) {V : Set F}
    (hV : V ∈ 𝓝 (extChartAt J x (f ((extChartAt I x').symm z₀))))
    (hg : withMetricOperatorNorms F in ∀ j ≤ m, ∀ K ⊆ V, IsCompact K → TendstoUniformlyOn
      (fun i y ↦ iteratedFDeriv ℝ j ((g i).toNondegenerateMetric.chartMetric x) y)
      (fun y ↦ iteratedFDeriv ℝ j (g₀.toNondegenerateMetric.chartMetric x) y) l K) :
    withMetricOperatorNorms E in ∃ B ∈ 𝓝 z₀, TendstoUniformlyOn
      (fun i z ↦
        iteratedFDeriv ℝ m (((g i).pullback f hf hinj).toNondegenerateMetric.chartMetric x') z)
      (fun z ↦ iteratedFDeriv ℝ m ((g₀.pullback f hf hinj).toNondegenerateMetric.chartMetric x') z)
      l B := by
  -- Work on the open set `W` where the transition map `τ` is defined, and on a compact
  -- neighbourhood `B` of `z₀` which `τ` maps into `V`.
  set τ := extChartAt J x ∘ f ∘ (extChartAt I x').symm
  set W := (extChartAt I x').target ∩ (extChartAt I x').symm ⁻¹' (f ⁻¹' (extChartAt J x).source)
  have hW : IsOpen W := (continuousOn_extChartAt_symm x').isOpen_inter_preimage
    (isOpen_extChartAt_target x') (hf.continuous.isOpen_preimage _ (isOpen_extChartAt_source x))
  have hτ : ContDiffOn ℝ ∞ τ W := by
    have h := ((contMDiffOn_iff (s := univ)).mp (hf.of_le le_self_add).contMDiffOn).2 x' x
    rwa [univ_inter] at h
  have hWV : W ∩ τ ⁻¹' V ∈ 𝓝 z₀ := inter_mem (hW.mem_nhds ⟨hz₀, hfz₀⟩)
    ((hτ.continuousOn.continuousAt (hW.mem_nhds ⟨hz₀, hfz₀⟩)).preimage_mem_nhds hV)
  obtain ⟨B, hB, hBWV, hBc⟩ := local_compact_nhds hWV
  have hBW : B ⊆ W := hBWV.trans inter_subset_left
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
  -- On `W`, the difference of two pullbacks is `L` applied to the difference `φ h` of the chart
  -- metrics at `x`, along `τ`.
  set φ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y) → F → _ :=
    fun h ↦ h.toNondegenerateMetric.chartMetric x - g₀.toNondegenerateMetric.chartMetric x
  have hpull (h : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {z : E}
      (hz : z ∈ W) : (h.pullback f hf hinj).toNondegenerateMetric.chartMetric x' z =
        L z (h.toNondegenerateMetric.chartMetric x (τ z)) := by
    rw [chartMetric_pullback h hf hinj hz.1 hz.2, I.range_eq_univ, fderivWithin_univ]
    -- Both sides pair `u` and `w` through `Dτ_z`; `τ z` unfolds to
    -- `extChartAt J x (f ((extChartAt I x').symm z))`.
    ext u w
    rfl
  have hdiff (h : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {z : E}
      (hz : z ∈ W) :
      iteratedFDeriv ℝ m ((h.pullback f hf hinj).toNondegenerateMetric.chartMetric x') z -
        iteratedFDeriv ℝ m ((g₀.pullback f hf hinj).toNondegenerateMetric.chartMetric x') z =
      iteratedFDerivWithin ℝ m (fun y ↦ L y (φ h (τ y))) W z := by
    have hnhds := (isOpen_extChartAt_target x').mem_nhds hz.1
    have heq : (h.pullback f hf hinj).toNondegenerateMetric.chartMetric x' -
        (g₀.pullback f hf hinj).toNondegenerateMetric.chartMetric x' =ᶠ[𝓝 z]
        fun y ↦ L y (φ h (τ y)) := by
      filter_upwards [hW.mem_nhds hz] with y hy
      simp only [Pi.sub_apply, hpull h hy, hpull g₀ hy, φ, map_sub]
    rw [← iteratedFDeriv_sub_apply
        (contDiffAt_infty.mp (((h.pullback f hf hinj).toNondegenerateMetric.contDiffOn_chartMetric
          x').contDiffAt hnhds) m)
        (contDiffAt_infty.mp (((g₀.pullback f hf hinj).toNondegenerateMetric.contDiffOn_chartMetric
          x').contDiffAt hnhds) m),
      (heq.iteratedFDeriv ℝ m).self_of_nhds, iteratedFDerivWithin_of_isOpen m hW hz]
  -- The chart derivatives of `g i` at `x` of order at most `m` converge to those of `g₀`
  -- uniformly on `τ '' B ⊆ V`.
  have hφ₀ (j : ℕ) (hj : j ≤ m) : TendstoUniformlyOn
      (fun i z ↦ iteratedFDerivWithin ℝ j (φ (g i)) (extChartAt J x).target (τ z)) (fun _ ↦ 0)
      l B := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun δ hδ ↦ ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hg j hj (τ '' B)
      (image_subset_iff.mpr fun z hz ↦ (hBWV hz).2)
      (hBc.image_of_continuousOn (hτ.continuousOn.mono hBW))) δ hδ] with i hi z hz
    have hτz := hmaps (hBW hz)
    have hnhds := (isOpen_extChartAt_target x).mem_nhds hτz
    rw [iteratedFDerivWithin_of_isOpen j (isOpen_extChartAt_target x) hτz,
      iteratedFDeriv_sub_apply
        (contDiffAt_infty.mp (((g i).toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt
          hnhds) j)
        (contDiffAt_infty.mp ((g₀.toNondegenerateMetric.contDiffOn_chartMetric x).contDiffAt
          hnhds) j),
      dist_zero_left, ← dist_eq_norm, dist_comm]
    exact hi (τ z) (mem_image_of_mem τ hz)
  have hlim := hL.tendstoUniformlyOn_iteratedFDerivWithin_clm_apply_comp
    (contDiffOn_infty.mp hτ m) hW.uniqueDiffOn (isOpen_extChartAt_target x).uniqueDiffOn hmaps
    hBc hBW (Eventually.of_forall fun i ↦ contDiffOn_infty.mp
      (((g i).toNondegenerateMetric.contDiffOn_chartMetric x).sub
        (g₀.toNondegenerateMetric.contDiffOn_chartMetric x)) m) hφ₀
  refine ⟨B, hB, Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim ε hε] with i hi z hz
  rw [dist_comm, dist_eq_norm, hdiff (g i) (hBW hz), ← dist_zero_left]
  exact hi z hz

/-- Pulling back along a fixed smooth immersion is continuous for the chart C² topologies: if
metrics `g` on `N` converge to `g₀` with their coordinate derivatives through order two, uniformly
on compact chart sets, then so do their pullbacks to `M`. -/
theorem continuous_pullback_chartC2 {f : M → N} (hf : ContMDiff I J (∞ + 1) f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    Continuous (fun g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y) ↦
      g.pullback f hf hinj) := by
  refine continuous_iff_continuousAt.mpr fun g₀ ↦
    (tendsto_chartCk_iff 2).mpr fun x' m hm K hKt hK ↦ ?_
  -- Uniform convergence holds near every point of the open chart target, hence on its compact
  -- subsets.
  have hloc : TendstoLocallyUniformlyOn
      (fun g z ↦ iteratedFDeriv ℝ m ((g.pullback f hf hinj).toNondegenerateMetric.chartMetric x') z)
      (fun z ↦ iteratedFDeriv ℝ m ((g₀.pullback f hf hinj).toNondegenerateMetric.chartMetric x') z)
      (𝓝 g₀) (extChartAt I x').target :=
    tendstoLocallyUniformlyOn_of_forall_exists_nhds fun z hz ↦ by
      -- Read `g` in the chart of `N` at the image point.
      set x := f ((extChartAt I x').symm z)
      obtain ⟨B, hB, h⟩ := exists_mem_nhds_tendstoUniformlyOn_iteratedFDeriv_chartMetric_pullback
        hf hinj (g := fun g ↦ g) hz (mem_extChartAt_source (I := J) x)
        ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)) fun j hj ↦
          (tendsto_chartMetricDerivative_iff x j).mp
            ((continuous_chartMetricDerivative 2 x ((Nat.cast_le.2 hj).trans hm)).tendsto g₀)
      exact ⟨B, mem_nhdsWithin_of_mem_nhds hB, h⟩
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_extChartAt_target x')).mp hloc
    K hKt hK

/-! ### Independence of the choice of charts -/

/-- **The chart Cᵏ topology is determined by any cover by compact chart sets.** Let `K i` be
compact sets in the chart targets at points `c i` such that every point of `M` is mapped by one of
these charts into the interior of the corresponding `K i`. Then metrics converge in the chart Cᵏ
topology exactly when their coordinate derivatives of order at most `k` in these charts converge
uniformly on these sets. -/
theorem tendsto_chartCk_iff_of_forall_mem_nhds (k : ℕ∞) {κ : Type*} {c : κ → M} {K : κ → Set E}
    (hKc : ∀ i, IsCompact (K i)) (hKt : ∀ i, K i ⊆ (extChartAt I (c i)).target)
    (hcover : ∀ y : M, ∃ i, y ∈ (extChartAt I (c i)).source ∧ K i ∈ 𝓝 (extChartAt I (c i) y))
    {P : Type*} {l : Filter P}
    {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} :
    withMetricOperatorNorms E in
    letI := chartCkTopology (I := I) (M := M) k
    Tendsto g l (𝓝 g₀) ↔ ∀ i (m : ℕ), (m : ℕ∞) ≤ k →
      TendstoUniformlyOn
        (fun p z ↦ iteratedFDeriv ℝ m ((g p).toNondegenerateMetric.chartMetric (c i)) z)
        (fun z ↦ iteratedFDeriv ℝ m (g₀.toNondegenerateMetric.chartMetric (c i)) z) l (K i) := by
  let _ := chartCkTopology (I := I) (M := M) k
  refine ⟨fun h i m hm ↦ (tendsto_chartMetricDerivative_iff (c i) m).mp
    ((continuous_chartMetricDerivative k (c i) hm).continuousAt.tendsto.comp h) (K i) (hKt i)
    (hKc i), fun h ↦ (tendsto_chartCk_iff k).mpr fun x' m hm K' hK't hK' ↦ ?_⟩
  -- A metric is its own pullback along the identity, so the convergence of the coordinate
  -- derivatives near a point of the chart target at `x'` follows from that in a chart at some
  -- `c i`, by the change of charts estimate.
  have hid : ContMDiff I I (∞ + 1) (id : M → M) := contMDiff_id
  have hinj (y : M) : Function.Injective (mfderiv I I (id : M → M) y) := by
    simpa [mfderiv_id] using Function.injective_id
  have hloc : TendstoLocallyUniformlyOn
      (fun p z ↦ iteratedFDeriv ℝ m ((g p).toNondegenerateMetric.chartMetric x') z)
      (fun z ↦ iteratedFDeriv ℝ m (g₀.toNondegenerateMetric.chartMetric x') z)
      l (extChartAt I x').target := by
    refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun z hz ↦ ?_
    obtain ⟨i, hi, hiK⟩ := hcover ((extChartAt I x').symm z)
    obtain ⟨B, hB, hBu⟩ := exists_mem_nhds_tendstoUniformlyOn_iteratedFDeriv_chartMetric_pullback
      hid hinj (g := g) hz hi hiK fun j hj K'' hK''K _ ↦
        (h i j ((Nat.cast_le.2 hj).trans hm)).mono hK''K
    simp only [pullback_id] at hBu
    exact ⟨B, mem_nhdsWithin_of_mem_nhds hB, hBu⟩
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_extChartAt_target x')).mp hloc
    K' hK't hK'

/-- **Atlas independence of the chart Cᵏ topology.** The chart Cᵏ topology is the topology induced
by the coordinate derivatives of order at most `k` in the charts at the points of any set `S`
whose chart domains cover `M`. -/
theorem chartCkTopology_eq_induced (k : ℕ∞) {S : Set M}
    (hS : ∀ y : M, ∃ x ∈ S, y ∈ (chartAt H x).source) :
    withMetricOperatorNorms E in
    chartCkTopology (I := I) (M := M) k =
      .induced (fun g (x : S) (m : {m : ℕ // (m : ℕ∞) ≤ k}) ↦ g.chartMetricDerivative x m)
        inferInstance := by
  refine le_antisymm (continuous_iff_le_induced.mp ?_) (le_of_nhds_le_nhds fun g₀ ↦ ?_)
  · let _ := chartCkTopology (I := I) (M := M) k
    exact continuous_pi fun x ↦ continuous_pi fun m ↦
      continuous_chartMetricDerivative k (x : M) m.2
  -- Cover `M` by compact neighbourhoods in the charts at the points of `S`.
  let κ := {p : S × Set E // IsCompact p.2 ∧ p.2 ⊆ (extChartAt I (p.1 : M)).target}
  have hcover (y : M) : ∃ i : κ, y ∈ (extChartAt I (i.1.1 : M)).source ∧
      i.1.2 ∈ 𝓝 (extChartAt I (i.1.1 : M) y) := by
    obtain ⟨x, hx, hy⟩ := hS y
    rw [← extChartAt_source (I := I)] at hy
    obtain ⟨V, hV, hVt, hVc⟩ := local_compact_nhds
      ((isOpen_extChartAt_target x).mem_nhds ((extChartAt I x).map_source hy))
    exact ⟨⟨(⟨x, hx⟩, V), hVc, hVt⟩, hy, hV⟩
  let _ := chartCkTopology (I := I) (M := M) k
  rw [nhds_induced]
  refine tendsto_id'.mp ((tendsto_chartCk_iff_of_forall_mem_nhds k (fun i : κ ↦ i.2.1)
    (fun i ↦ i.2.2) hcover).mpr fun i m hm ↦
      (tendsto_chartMetricDerivative_iff (i.1.1 : M) m).mp ?_ _ i.2.2 i.2.1)
  set F := fun (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x : S)
    (m : {m : ℕ // (m : ℕ∞) ≤ k}) ↦ g.chartMetricDerivative x m
  have h : Tendsto F (comap F (𝓝 (F g₀))) (𝓝 (F g₀)) := tendsto_comap
  exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i.1.1) ⟨m, hm⟩

/-- **Finite-atlas description of the chart Cᵏ topology.** On a compact manifold there are
finitely many points `x` and compact sets `K x` in their chart targets such that metrics converge
in the chart Cᵏ topology exactly when their coordinate derivatives of order at most `k` in these
finitely many charts converge uniformly on these sets. For finite `k` this is convergence for
finitely many seminorms, the suprema over `K x` of the norms of these derivatives. -/
theorem exists_finset_tendsto_chartCk_iff [CompactSpace M] (k : ℕ∞) :
    ∃ (s : Finset M) (K : M → Set E),
      (∀ x ∈ s, IsCompact (K x) ∧ K x ⊆ (extChartAt I x).target) ∧
      ∀ {P : Type*} {l : Filter P}
        {g : P → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
        {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)},
        withMetricOperatorNorms E in
        letI := chartCkTopology (I := I) (M := M) k
        Tendsto g l (𝓝 g₀) ↔ ∀ x ∈ s, ∀ m : ℕ, (m : ℕ∞) ≤ k →
          TendstoUniformlyOn
            (fun p z ↦ iteratedFDeriv ℝ m ((g p).toNondegenerateMetric.chartMetric x) z)
            (fun z ↦ iteratedFDeriv ℝ m (g₀.toNondegenerateMetric.chartMetric x) z) l (K x) := by
  choose K hKn hKt hKc using fun y : M ↦ local_compact_nhds
    ((isOpen_extChartAt_target (I := I) y).mem_nhds (mem_extChartAt_target y))
  -- Finitely many of the open sets of points mapped into the interior of `K y` cover `M`.
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun y : M ↦ (extChartAt I y).source ∩ extChartAt I y ⁻¹' interior (K y))
    (fun y ↦ (continuousOn_extChartAt y).isOpen_inter_preimage (isOpen_extChartAt_source y)
      isOpen_interior)
    fun y _ ↦ mem_iUnion.mpr ⟨y, mem_extChartAt_source y, mem_interior_iff_mem_nhds.mpr (hKn y)⟩
  refine ⟨s, K, fun x _ ↦ ⟨hKc x, hKt x⟩, fun {P l g g₀} ↦ ?_⟩
  have hcover (y : M) : ∃ i : s, y ∈ (extChartAt I (i : M)).source ∧
      K i ∈ 𝓝 (extChartAt I (i : M) y) := by
    obtain ⟨x, hx, hy⟩ := mem_iUnion₂.mp (hs (mem_univ y))
    exact ⟨⟨x, hx⟩, hy.1, mem_interior_iff_mem_nhds.mp hy.2⟩
  rw [tendsto_chartCk_iff_of_forall_mem_nhds k (fun i : s ↦ hKc i) (fun i ↦ hKt i) hcover]
  exact ⟨fun h x hx ↦ h ⟨x, hx⟩, fun h i ↦ h i i.2⟩

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
