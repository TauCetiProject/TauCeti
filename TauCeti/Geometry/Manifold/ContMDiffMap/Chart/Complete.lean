/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.FTaylorSeries
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms
public import TauCeti.Topology.ContinuousMap.CompactConvergence

/-!
# Completeness of the weak Whitney topology on a manifold

Let `M` be a manifold without boundary, modelled on a locally compact space over `ℝ` or `ℂ`, and
let `F` be a Banach space. This file proves that the vector-valued `C^r` maps on `M`, for finite or
smooth regularity `r`, form a complete space in the weak Whitney topology, for the uniform
structure of this topological vector space (`ContMDiffMap.completeSpace_manifoldWeakWhitney`).

The proof is local. In each chart, locally uniform limits of the coordinate derivatives of a net
of maps form the Taylor series of a `C^r` function on the open chart target
(`HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn`). These coordinate limits agree on chart
overlaps, since their values are the pointwise limits of the net, so they glue to a `C^r` map on
`M` whose coordinate derivatives are the given limits
(`ContMDiffMap.exists_chartIteratedFDeriv_eq_of_tendstoLocallyUniformlyOn`). A Cauchy net has
such limits, because each coordinate derivative is a continuous additive map into a complete
space of continuous maps with the topology of compact convergence.

On a compact manifold the topology is also normable
(`ContMDiffMap.isNormableSpace_of_compactSpace`), so together these give the Banach spaces of
`C^k` functions on compact manifolds.

The boundaryless hypothesis makes the chart targets open, which is what the derivative-limit
theorem needs. Analytic regularity is excluded.

## Main results

* `ContMDiffMap.exists_chartIteratedFDeriv_eq_of_tendstoLocallyUniformlyOn`: locally uniform
  limits of the coordinate derivatives of a net of `C^r` maps are the coordinate derivatives of a
  `C^r` map.
* `ContMDiffMap.completeSpace_manifoldWeakWhitney`: the weak Whitney space of vector-valued `C^r`
  maps is complete.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1 and §4, for the weak topology and
  the completeness of spaces of `C^r` maps.
-/

public section

open Set Filter Topology IsManifold
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Gluing

variable {r : ℕ∞} [IsManifold I r M]

omit [LocallyCompactSpace E] in
/-- **Gluing coordinate limits.** If, in every chart, the coordinate derivatives of order at most
`r` of a net of `C^r` maps converge locally uniformly on the chart target, then the limits are the
coordinate derivatives of a single `C^r` map. -/
theorem exists_chartIteratedFDeriv_eq_of_tendstoLocallyUniformlyOn
    {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯}
    {q : M → E → FormalMultilinearSeries 𝕜 E F}
    (hq : ∀ (x : M) (m : ℕ), (m : ℕ∞ω) ≤ r → TendstoLocallyUniformlyOn
      (fun i z ↦ iteratedFDerivWithin 𝕜 m (f i ∘ (extChartAt I x).symm) (extChartAt I x).target z)
      (fun z ↦ q x z m) l (extChartAt I x).target) :
    ∃ h : C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯, ∀ (x : M) (m : ℕ) (hm : (m : ℕ∞ω) ≤ r)
      (z : (extChartAt I x).target), chartIteratedFDeriv h x m hm z = q x z m := by
  have hV (x : M) : IsOpen (extChartAt I x).target := isOpen_extChartAt_target x
  have hcd (x : M) (i : ι) :
      ContDiffOn 𝕜 (r : ℕ∞ω) (f i ∘ (extChartAt I x).symm) (extChartAt I x).target :=
    contDiffOn_comp_extend_symm (f i) (chart_mem_maximalAtlas x)
  -- The values of the net converge, in every chart, to the order-zero limit.
  have hval (x : M) (z : E) (hz : z ∈ (extChartAt I x).target) :
      Tendsto (fun i ↦ f i ((extChartAt I x).symm z)) l (𝓝 ((q x z 0).curry0)) := by
    have ht := ((continuousMultilinearCurryFin0 𝕜 E F).continuous.tendsto (q x z 0)).comp
      ((hq x 0 (by simp)).tendsto_at hz)
    simpa only [Function.comp_def, iteratedFDerivWithin_zero_eq_comp,
      continuousMultilinearCurryFin0_apply, ContinuousMultilinearMap.curry0_apply,
      continuousMultilinearCurryFin0_symm_apply_apply] using ht
  -- In every chart the limits are the Taylor series of the order-zero limit.
  have hT (x : M) : HasFTaylorSeriesUpToOn (r : ℕ∞ω) (fun z ↦ (q x z 0).curry0) (q x)
      (extChartAt I x).target :=
    HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn (hV x)
      (fun i ↦ (hcd x i).ftaylorSeriesWithin (hV x).uniqueDiffOn) (hq x) (hval x)
  -- The glued map, read at each point in its own chart.
  let G : M → F := fun y ↦ (q y (extChartAt I y y) 0).curry0
  have hG (x : M) : EqOn (G ∘ (extChartAt I x).symm) (fun z ↦ (q x z 0).curry0)
      (extChartAt I x).target := by
    intro z hz
    have hy := (extChartAt I x).map_target hz
    have h₁ := hval _ _ (mem_extChartAt_target ((extChartAt I x).symm z))
    rw [(extChartAt I _).left_inv (mem_extChartAt_source _)] at h₁
    exact tendsto_nhds_unique h₁ (hval x z hz)
  have hGs : ContMDiff I 𝓘(𝕜, F) (r : ℕ∞ω) G := by
    intro y
    have hon : ContMDiffOn I 𝓘(𝕜, F) (r : ℕ∞ω) ((fun z ↦ (q y z 0).curry0) ∘ extChartAt I y)
        (chartAt H y).source :=
      (ContDiffOn.contMDiffOn (hT y).contDiffOn).comp contMDiffOn_extChartAt fun p hp ↦
        (extChartAt I y).map_source (by rwa [extChartAt_source])
    refine (hon.congr fun p hp ↦ ?_).contMDiffAt
      ((chartAt H y).open_source.mem_nhds (mem_chart_source H y))
    have hp' : p ∈ (extChartAt I y).source := by rwa [extChartAt_source]
    have := hG y ((extChartAt I y).map_source hp')
    rwa [Function.comp_apply, (extChartAt I y).left_inv hp'] at this
  let h : C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯ := ⟨G, hGs⟩
  refine ⟨h, fun x m hm z ↦ (chartIteratedFDeriv_self_target_apply h x m hm z).trans ?_⟩
  exact (iteratedFDerivWithin_congr (hG x) z.2 m).trans
    ((hT x).eq_iteratedFDerivWithin_of_uniqueDiffOn hm (hV x).uniqueDiffOn z.2).symm

end Gluing

/-- **Completeness of the weak Whitney topology.** On a boundaryless manifold modelled on a
locally compact space over `ℝ` or `ℂ`, the vector-valued `C^n` maps with values in a Banach space,
for finite or smooth regularity `n`, form a complete space for the uniform structure of the weak
Whitney topological vector space. -/
theorem completeSpace_manifoldWeakWhitney [CompleteSpace F] {n : ℕ∞ω} [IsManifold I n M]
    [hn : ENat.LEInfty n] :
    @CompleteSpace C^n⟮I, M; 𝓘(𝕜, F), F⟯
      (IsTopologicalAddGroup.rightUniformSpace C^n⟮I, M; 𝓘(𝕜, F), F⟯) := by
  obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1
    (ne_top_of_le_ne_top (by simp : (∞ : ℕ∞ω) ≠ ⊤) hn.out)
  let _ : UniformSpace C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯ :=
    IsTopologicalAddGroup.rightUniformSpace _
  have : IsUniformAddGroup C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯ := isUniformAddGroup_of_addCommGroup
  refine ⟨fun {𝓕} h𝓕 ↦ ?_⟩
  have := h𝓕.1
  -- Each coordinate derivative of the Cauchy filter converges with compact convergence.
  have hconv (x : M) (m : ℕ) (hm : (m : ℕ∞ω) ≤ r) : ∃ g : C((extChartAt I x).target,
      E [×m]→L[𝕜] F), Tendsto (fun f ↦ chartIteratedFDeriv f x m hm) 𝓕 (𝓝 g) := by
    have : LocallyCompactSpace (extChartAt I x).target :=
      (isOpen_extChartAt_target x).locallyCompactSpace
    have hfun : (⇑(chartIteratedFDerivLinearMap (F := F) (n := (r : ℕ∞ω)) (I := I) x m hm)) =
        fun f ↦ chartIteratedFDeriv f x m hm :=
      funext fun f ↦ chartIteratedFDerivLinearMap_apply x m hm f
    have hu := uniformContinuous_addMonoidHom_of_continuous
      (f := chartIteratedFDerivLinearMap (F := F) (n := (r : ℕ∞ω)) (I := I) x m hm)
      (hfun ▸ continuous_chartIteratedFDeriv x m hm)
    rw [hfun] at hu
    exact CompleteSpace.complete (h𝓕.map hu)
  choose g hg using hconv
  classical
  let q : M → E → FormalMultilinearSeries 𝕜 E F := fun x z m ↦
    if hm : (m : ℕ∞ω) ≤ r then Function.extend Subtype.val (g x m hm) (fun _ ↦ 0) z else 0
  have hq (x : M) (m : ℕ) (hm : (m : ℕ∞ω) ≤ r) (z : (extChartAt I x).target) :
      q x z m = g x m hm z := by
    simp only [q, hm, ↓reduceDIte, Subtype.val_injective.extend_apply]
  obtain ⟨h, hh⟩ := exists_chartIteratedFDeriv_eq_of_tendstoLocallyUniformlyOn (l := 𝓕)
    (f := fun f : C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯ ↦ f) (q := q) fun x m hm ↦ by
      have : LocallyCompactSpace (extChartAt I x).target :=
        (isOpen_extChartAt_target x).locallyCompactSpace
      apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
      have ht := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 (hg x m hm)
      convert ht using 1
      · funext f z
        exact (chartIteratedFDeriv_self_target_apply f x m hm z).symm
      · funext z
        exact hq x m hm z
  refine ⟨h, tendsto_id'.mp (tendsto_manifoldWeakWhitney_iff_chartIteratedFDeriv.mpr
    fun x m hm ↦ ?_)⟩
  have hlim : chartIteratedFDeriv h x m hm = g x m hm :=
    ContinuousMap.ext fun z ↦ (hh x m hm z).trans (hq x m hm z)
  rw [hlim]
  exact hg x m hm

end ContMDiffMap
