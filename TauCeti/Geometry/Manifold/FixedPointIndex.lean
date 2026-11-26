/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FixedPointIndex.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The local fixed-point index of a self-map of a manifold

Let `M` be a manifold without boundary modelled on a finite-dimensional real normed space `E`,
and let `f : M → M` be continuous. In a chart `c` of `M`, extended to `E` by the model with
corners, `f` reads as the continuous map `z ↦ c (f (c⁻¹ z))` on the open set of coordinates `z`
whose image under `f` stays in the chart (`TauCeti.chartFixedPointMap`). The fixed points of
`f` in the chart are the fixed points of this map, so a fixed point `x` of `f` has a local
fixed-point index in the chart (`TauCeti.chartLocalFixedPointIndex`): the local fixed-point index
of the coordinate expression at the coordinate of `x`
(`ContinuousMap.localFixedPointIndex`), the local degree of the displacement `z ↦ z - g z`. The
**local fixed-point index** of `f` at `x` (`TauCeti.localFixedPointIndex`) is the index read in
the preferred chart at `x`.

The local index of a map of open subsets of `E` is invariant under every change of coordinates
with an invertible strict derivative, orientation-preserving or not
(`ContinuousMap.localFixedPointIndex_eq_of_hasStrictFDerivAt`). This makes the local index on
the manifold intrinsic:

* **Chart independence.** On a `C¹` manifold the index can be read in any chart of the maximal
  atlas whose source contains `x` (`TauCeti.chartLocalFixedPointIndex_eq_localFixedPointIndex`),
  since the transition maps are `C¹` with invertible derivatives. No orientation of `M` is used,
  so the index is defined on nonorientable manifolds as well.
* **Conjugation invariance.** A local diffeomorphism `Φ : M → N` at a fixed point `x` of `f` which
  conjugates `f` near `x` to a self-map `g` of `N`, `Φ ∘ f = g ∘ Φ` near `x`, carries the index of
  `f` at `x` to that of `g` at `Φ x`
  (`IsLocalDiffeomorphAt.localFixedPointIndex_eq_of_eventually_semiconj`), and so does a
  diffeomorphism (`Diffeomorph.localFixedPointIndex_eq_of_semiconj`).
* **Locality.** The index depends only on the germ of `f` at `x`
  (`TauCeti.localFixedPointIndex_congr`); it vanishes at points which are not fixed
  (`TauCeti.localFixedPointIndex_of_ne`) and at fixed points which are not isolated
  (`TauCeti.localFixedPointIndex_of_frequently_eq`).
* **Normalization.** At a fixed point where `f` is differentiable and `det (1 - df_x) ≠ 0`, the
  index is the Lefschetz sign `sgn det (1 - df_x)`
  (`TauCeti.localFixedPointIndex_eq_fixedPointSign`),
  in particular at every nondegenerate fixed point
  (`TauCeti.IsNondegenerateFixedPt.localFixedPointIndex_eq_fixedPointSign`). In dimension zero
  every fixed point has index `1` (`TauCeti.localFixedPointIndex_of_subsingleton`).
* **The model space.** On `E` itself, with its trivial chart, the index is the local fixed-point
  index of `f` on any open set containing `x` (`TauCeti.localFixedPointIndex_modelSpace`).

These local indices are the terms of the Lefschetz fixed-point formula
`∑ₓ i(f, x) = ∑ₖ (-1) ^ k tr (f_* | Hₖ(M; ℚ))` for a self-map of a compact manifold with isolated
fixed points, which is not proved here. Applied to the iterates of a surface map, that formula
identifies the Lefschetz numbers of the iterates with counts of periodic points weighted by these
indices.

## Main definitions

* `TauCeti.chartFixedPointMap I c f`: the coordinate expression of `f` in the chart `c`, on the
  open set `TauCeti.chartFixedPointDomain I c f`.
* `TauCeti.chartLocalFixedPointIndex I c f x`: the local fixed-point index of `f` at `x` read in
  the chart `c`.
* `TauCeti.localFixedPointIndex I f x`: the local fixed-point index of `f` at `x`.

## Main results

* `TauCeti.chartLocalFixedPointIndex_eq_localFixedPointIndex`: chart independence.
* `IsLocalDiffeomorphAt.localFixedPointIndex_eq_of_eventually_semiconj`,
  `Diffeomorph.localFixedPointIndex_eq_of_semiconj`: invariance under conjugation.
* `TauCeti.localFixedPointIndex_eq_fixedPointSign`: the index at a fixed point with
  `det (1 - df_x) ≠ 0` is `sgn det (1 - df_x)`.

## References

* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII, §5 (the fixed-point
  index and its invariance under commutation and conjugation).
* R. F. Brown, *The Lefschetz Fixed Point Theorem*, Scott, Foresman and Co., 1971, Chapter IV.
-/

public section

noncomputable section

open Filter Function Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M]

/-! ### The coordinate expression in a chart -/

section Chart

variable (I) in
/-- The domain of the coordinate expression of a continuous map `f : M → M` in the chart `c`: the
open set of coordinates `z` of points of the chart whose image under `f` lies in the chart. -/
def chartFixedPointDomain (c : OpenPartialHomeomorph M H) (f : C(M, M)) : Opens E where
  carrier := (c.extend I).target ∩ (c.extend I).symm ⁻¹' (f ⁻¹' c.source)
  is_open' := c.isOpen_extend_target_inter_preimage (c.open_source.preimage f.continuous)

@[simp]
theorem mem_chartFixedPointDomain {c : OpenPartialHomeomorph M H} {f : C(M, M)} {z : E} :
    z ∈ chartFixedPointDomain I c f ↔
      z ∈ (c.extend I).target ∧ f ((c.extend I).symm z) ∈ c.source :=
  (Iff.rfl)

/-- The coordinate of a point `x` of the chart `c` whose image `f x` lies in the chart belongs to
the domain of the coordinate expression of `f`. -/
theorem extend_mem_chartFixedPointDomain {c : OpenPartialHomeomorph M H} {f : C(M, M)} {x : M}
    (hx : x ∈ c.source) (hfx : f x ∈ c.source) : c.extend I x ∈ chartFixedPointDomain I c f :=
  ⟨(c.extend I).map_source (by rwa [c.extend_source]), by
    rwa [mem_preimage, mem_preimage, c.extend_left_inv hx]⟩

variable (I) in
/-- The **coordinate expression** `z ↦ c (f (c⁻¹ z))` of a continuous map `f : M → M` in the chart
`c`, extended to the model space `E`, on the open set `TauCeti.chartFixedPointDomain I c f` where it
is defined. Its fixed points are the coordinates of the fixed points of `f` in the chart. -/
def chartFixedPointMap (c : OpenPartialHomeomorph M H) (f : C(M, M)) :
    C(chartFixedPointDomain I c f, E) where
  toFun z := c.extend I (f ((c.extend I).symm z))
  continuous_toFun := continuousOn_iff_continuous_domRestrict.1 <|
    c.continuousOn_extend_comp_symm (I := I) (I' := I) c f.continuous.continuousOn (s := univ)
      (W := chartFixedPointDomain I c f) fun _ hz ↦ ⟨hz.1, trivial, hz.2⟩

@[simp]
theorem chartFixedPointMap_apply (c : OpenPartialHomeomorph M H) (f : C(M, M))
    (z : chartFixedPointDomain I c f) :
    chartFixedPointMap I c f z = c.extend I (f ((c.extend I).symm z)) :=
  (rfl)

/-- The fixed points of the coordinate expression of `f` in the chart `c` are the coordinates of
the fixed points of `f` in the chart. -/
theorem chartFixedPointMap_apply_eq_self_iff {c : OpenPartialHomeomorph M H} {f : C(M, M)}
    {z : chartFixedPointDomain I c f} :
    chartFixedPointMap I c f z = z ↔ f ((c.extend I).symm z) = (c.extend I).symm z := by
  rw [chartFixedPointMap_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, (c.extend I).right_inv z.property.1]⟩
  rw [← c.extend_left_inv (I := I) z.property.2, h]

variable [FiniteDimensional ℝ E]

variable (I) in
open scoped Classical in
/-- The **local fixed-point index of `f` at `x` read in the chart `c`**: the local fixed-point
index of the coordinate expression `TauCeti.chartFixedPointMap I c f` at the coordinate of `x`,
when `x` and `f x` lie in the chart, and `0` otherwise. On a `C¹` manifold it does not depend on
the chart of the maximal atlas containing `x`
(`TauCeti.chartLocalFixedPointIndex_eq_localFixedPointIndex`). -/
def chartLocalFixedPointIndex (c : OpenPartialHomeomorph M H) (f : C(M, M)) (x : M) : ℤ :=
  if h : x ∈ c.source ∧ f x ∈ c.source then
    (chartFixedPointMap I c f).localFixedPointIndex
      ⟨c.extend I x, extend_mem_chartFixedPointDomain h.1 h.2⟩
  else 0

/-- When `x` and `f x` lie in the chart `c`, the index read in `c` is the local fixed-point index of
the coordinate expression of `f` at the coordinate of `x`. -/
theorem chartLocalFixedPointIndex_of_mem {c : OpenPartialHomeomorph M H} {f : C(M, M)} {x : M}
    (hx : x ∈ c.source) (hfx : f x ∈ c.source) :
    chartLocalFixedPointIndex I c f x =
      (chartFixedPointMap I c f).localFixedPointIndex
        ⟨c.extend I x, extend_mem_chartFixedPointDomain hx hfx⟩ := by
  simp only [chartLocalFixedPointIndex, hx, hfx, and_self, ↓reduceDIte]

/-- The index read in the chart `c` is `0` unless `x` and `f x` lie in the chart. -/
@[simp]
theorem chartLocalFixedPointIndex_of_notMem {c : OpenPartialHomeomorph M H} {f : C(M, M)} {x : M}
    (h : ¬(x ∈ c.source ∧ f x ∈ c.source)) : chartLocalFixedPointIndex I c f x = 0 := by
  simp only [chartLocalFixedPointIndex, h, ↓reduceDIte]

/-- The local fixed-point index read in a chart vanishes at a point which is not fixed. -/
@[simp]
theorem chartLocalFixedPointIndex_of_ne (c : OpenPartialHomeomorph M H) {f : C(M, M)} {x : M}
    (hfx : f x ≠ x) : chartLocalFixedPointIndex I c f x = 0 := by
  by_cases h : x ∈ c.source ∧ f x ∈ c.source
  · rw [chartLocalFixedPointIndex_of_mem h.1 h.2]
    refine ContinuousMap.localFixedPointIndex_of_ne _ fun heq ↦ hfx ?_
    rwa [chartFixedPointMap_apply_eq_self_iff, c.extend_left_inv h.1] at heq
  · exact chartLocalFixedPointIndex_of_notMem h

/-- **Comparison of local indices read in charts.** Let `x` be a fixed point of `f : M → M`, and
let `Φ : M → N`, continuous at `x`, conjugate `f` near `x` to `g : N → N`. If the coordinate
expression of `Φ` in a chart `c` at `x` and a chart `c'` at `Φ x` has an invertible strict
derivative at the coordinate of `x`, then the index of `g` at `Φ x` read in `c'` is the index of
`f` at `x` read in `c`. -/
theorem chartLocalFixedPointIndex_eq_of_hasStrictFDerivAt {H' N : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E H'} [J.Boundaryless] [TopologicalSpace N]
    {c : OpenPartialHomeomorph M H} {c' : OpenPartialHomeomorph N H'} {f : C(M, M)}
    {g : C(N, N)} {Φ : M → N} {x : M} (hfx : f x = x) (hx : x ∈ c.source)
    (hΦx : Φ x ∈ c'.source) (hΦ : ContinuousAt Φ x) (hconj : ∀ᶠ z in 𝓝 x, Φ (f z) = g (Φ z))
    {A : E ≃L[ℝ] E}
    (hA : HasStrictFDerivAt (c'.extend J ∘ Φ ∘ (c.extend I).symm) (A : E →L[ℝ] E)
      (c.extend I x)) :
    chartLocalFixedPointIndex J c' g (Φ x) = chartLocalFixedPointIndex I c f x := by
  have hgx : g (Φ x) = Φ x := by rw [← hconj.self_of_nhds, hfx]
  have hfx' : f x ∈ c.source := by rwa [hfx]
  have hgx' : g (Φ x) ∈ c'.source := by rwa [hgx]
  rw [chartLocalFixedPointIndex_of_mem hx hfx', chartLocalFixedPointIndex_of_mem hΦx hgx']
  -- The coordinate of `Φ x` is the image of the coordinate of `x` under the coordinate change.
  have he' : c'.extend J (Φ x) = (c'.extend J ∘ Φ ∘ (c.extend I).symm) (c.extend I x) := by
    simp only [comp_apply, c.extend_left_inv hx]
  have hx₀ : chartFixedPointMap I c f ⟨c.extend I x, extend_mem_chartFixedPointDomain hx hfx'⟩ =
      c.extend I x := by
    simp only [chartFixedPointMap_apply, c.extend_left_inv hx, hfx]
  have hmem : (c'.extend J ∘ Φ ∘ (c.extend I).symm) (c.extend I x) ∈
      chartFixedPointDomain J c' g :=
    he' ▸ extend_mem_chartFixedPointDomain hΦx hgx'
  convert ContinuousMap.localFixedPointIndex_eq_of_hasStrictFDerivAt hx₀ hA hmem ?_ using 2
  · exact Subtype.ext he'
  -- Near the coordinate of `x`, the points `c⁻¹ z` lie near `x`, where `Φ` maps into `c'` and
  -- conjugates `f` to `g`.
  have hsymm : Tendsto (fun z : chartFixedPointDomain I c f ↦ (c.extend I).symm z)
      (𝓝 ⟨c.extend I x, extend_mem_chartFixedPointDomain hx hfx'⟩) (𝓝 x) := by
    simpa only [comp_def, c.extend_left_inv hx] using
      (c.continuousAt_extend_symm (I := I) hx).tendsto.comp (continuous_subtypeVal.tendsto
        (⟨c.extend I x, extend_mem_chartFixedPointDomain hx hfx'⟩ : chartFixedPointDomain I c f))
  have hΦc : ∀ᶠ z in 𝓝 x, Φ z ∈ c'.source := hΦ.preimage_mem_nhds (c'.open_source.mem_nhds hΦx)
  filter_upwards [hsymm.eventually hΦc, hsymm.eventually hconj] with z hzc hzconj hz
  have hfz : f ((c.extend I).symm z) ∈ c.source := z.property.2
  simp only [chartFixedPointMap_apply, comp_apply, c'.extend_left_inv hzc, c.extend_left_inv hfz,
    hzconj]

end Chart

/-! ### The local fixed-point index -/

variable [FiniteDimensional ℝ E] [ChartedSpace H M]

variable (I) in
/-- The **local fixed-point index** of a continuous self-map `f` of a manifold without boundary at a
point `x`: the local fixed-point index of the coordinate expression of `f` in the preferred chart
at `x`. It vanishes when `x` is not a fixed point or not an isolated one, and on a `C¹` manifold it
can be read in any chart of the maximal atlas containing `x`
(`TauCeti.chartLocalFixedPointIndex_eq_localFixedPointIndex`). -/
def localFixedPointIndex (f : C(M, M)) (x : M) : ℤ :=
  chartLocalFixedPointIndex I (chartAt H x) f x

theorem localFixedPointIndex_def (f : C(M, M)) (x : M) :
    localFixedPointIndex I f x = chartLocalFixedPointIndex I (chartAt H x) f x :=
  (rfl)

/-- The local fixed-point index vanishes at a point which is not fixed. -/
@[simp]
theorem localFixedPointIndex_of_ne {f : C(M, M)} {x : M} (hfx : f x ≠ x) :
    localFixedPointIndex I f x = 0 :=
  chartLocalFixedPointIndex_of_ne _ hfx

/-- At a fixed point, the local fixed-point index is the local fixed-point index of the coordinate
expression of `f` in the preferred chart at `x`, at the coordinate of `x`. -/
theorem localFixedPointIndex_eq_localFixedPointIndex_chartFixedPointMap {f : C(M, M)} {x : M}
    (hfx : f x = x) :
    localFixedPointIndex I f x =
      (chartFixedPointMap I (chartAt H x) f).localFixedPointIndex
        ⟨extChartAt I x x, extend_mem_chartFixedPointDomain (mem_chart_source H x)
          (by rw [hfx]; exact mem_chart_source H x)⟩ :=
  chartLocalFixedPointIndex_of_mem (mem_chart_source H x) (by rw [hfx]; exact mem_chart_source H x)

/-- **The local fixed-point index only depends on the germ of the map**: maps agreeing near `x`
have the same local fixed-point index at `x`. -/
theorem localFixedPointIndex_congr {f g : C(M, M)} {x : M} (hfg : ⇑f =ᶠ[𝓝 x] g) :
    localFixedPointIndex I f x = localFixedPointIndex I g x := by
  by_cases hfx : f x = x
  · have hgx : g x = x := by rw [← hfg.self_of_nhds]; exact hfx
    -- In the preferred chart at `x`, the identity of `M` reads as the identity near `x`.
    have hcoord : ((chartAt H x).extend I ∘ id ∘ ((chartAt H x).extend I).symm)
        =ᶠ[𝓝 (extChartAt I x x)] id :=
      Filter.mem_of_superset (extChartAt_target_mem_nhds (I := I) x) fun z hz ↦
        (extChartAt I x).right_inv hz
    refine chartLocalFixedPointIndex_eq_of_hasStrictFDerivAt (f := g) (g := f) (Φ := id)
      (A := ContinuousLinearEquiv.refl ℝ E) hgx (mem_chart_source H x) (mem_chart_source H x)
      continuousAt_id (hfg.mono fun z hz ↦ hz.symm) ?_
    rw [ContinuousLinearEquiv.coe_refl]
    exact (hasStrictFDerivAt_id _).congr_of_eventuallyEq hcoord.symm
  · rw [localFixedPointIndex_of_ne hfx, localFixedPointIndex_of_ne (hfg.self_of_nhds ▸ hfx)]

/-- The local fixed-point index vanishes at a fixed point which is not isolated. -/
theorem localFixedPointIndex_of_frequently_eq {f : C(M, M)} {x : M}
    (h : ∃ᶠ z in 𝓝[≠] x, f z = z) : localFixedPointIndex I f x = 0 := by
  by_cases hfx : f x = x
  · rw [localFixedPointIndex_eq_localFixedPointIndex_chartFixedPointMap hfx]
    refine ContinuousMap.localFixedPointIndex_of_frequently_eq _ ?_
    set c := chartAt H x
    have hfx' : f x ∈ c.source := by rw [hfx]; exact mem_chart_source H x
    set x₀ : chartFixedPointDomain I c f :=
      ⟨extChartAt I x x, extend_mem_chartFixedPointDomain (mem_chart_source H x) hfx'⟩
    -- Near `x`, the points of the chart whose image stays in the chart.
    have hsrc : ∀ᶠ z in 𝓝 x, z ∈ c.source := c.open_source.mem_nhds (mem_chart_source H x)
    have hV : ∀ᶠ z in 𝓝 x, z ∈ c.source ∧ f z ∈ c.source :=
      hsrc.and (f.continuous.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hfx'))
    -- The coordinates of these points, and `x₀` elsewhere.
    classical
    let ψ : M → chartFixedPointDomain I c f := fun z ↦
      if hz : z ∈ c.source ∧ f z ∈ c.source then
        ⟨c.extend I z, extend_mem_chartFixedPointDomain hz.1 hz.2⟩
      else x₀
    have hψ : ∀ᶠ z in 𝓝 x, (ψ z : E) = c.extend I z :=
      hV.mono fun z hz ↦ by simp only [ψ, hz, and_self, ↓reduceDIte]
    have hψt : Tendsto ψ (𝓝[≠] x) (𝓝[≠] x₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · refine tendsto_subtype_rng.2 (tendsto_nhdsWithin_of_tendsto_nhds ?_)
        refine ((c.continuousAt_extend (I := I) (mem_chart_source H x)).congr
          (hψ.mono fun z hz ↦ hz.symm)).tendsto.trans_eq ?_
        -- `extChartAt I x` is by definition the extension `c.extend I` of the chart `c` at `x`.
        rw [hψ.self_of_nhds]
        rfl
      · filter_upwards [(I.tendsto_extChartAt_nhdsNE x).eventually self_mem_nhdsWithin,
          nhdsWithin_le_nhds hψ] with z hz hzψ heq
        -- `extChartAt I x` is by definition `c.extend I`, and `x₀` is `extChartAt I x x`.
        exact hz (hzψ.symm.trans (congrArg Subtype.val heq))
    refine hψt.frequently ((h.and_eventually (nhdsWithin_le_nhds (hψ.and hV))).mono ?_)
    rintro z ⟨hfz, hzψ, hzV⟩
    rwa [chartFixedPointMap_apply_eq_self_iff, hzψ, c.extend_left_inv hzV.1]
  · exact localFixedPointIndex_of_ne hfx

/-- **The local fixed-point index at a fixed point with `det (1 - df_x) ≠ 0`** is the Lefschetz sign
`sgn det (1 - df_x)`: if `f` is differentiable at the fixed point `x` and
`fixedPointDet I f x = det (1 - df_x)` does not vanish, the local fixed-point index of `f` at `x`
is `fixedPointSign I f x`. -/
theorem localFixedPointIndex_eq_fixedPointSign {f : C(M, M)} {x : M} (hfx : f x = x)
    (hf : MDifferentiableAt I I f x) (hdet : fixedPointDet I f x ≠ 0) :
    localFixedPointIndex I f x = fixedPointSign I f x := by
  rw [localFixedPointIndex_eq_localFixedPointIndex_chartFixedPointMap hfx,
    fixedPointSign_eq_sign hdet]
  -- In the chart at `x`, the coordinate expression of `f` has derivative `df_x` at `x`.
  have hdiff := hf.differentiableAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, hfx] at hdiff
  -- The tangent spaces at `x` and `f x` are the model space `E`.
  let D : E →L[ℝ] E := mfderiv I I f x
  have hd : HasFDerivAt (extChartAt I x ∘ f ∘ (extChartAt I x).symm) D (extChartAt I x x) := by
    have hD : D = fderiv ℝ (extChartAt I x ∘ f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
      hf.mfderiv_eq_fderiv_extChartAt_conj hfx
    rw [hD]
    exact hdiff.hasFDerivAt
  have hdet' : (1 - D).det = fixedPointDet I f x := by
    rw [hf.hasMFDerivAt.fixedPointDet_eq (D := D)]
    -- `ContinuousLinearMap.det` is the determinant of the underlying linear map, and `1` is `id`.
    simp [ContinuousLinearMap.det, Module.End.one_eq_id]
  rw [← hdet']
  -- `extChartAt I x` is by definition `(chartAt H x).extend I`, so the coordinate expression of
  -- `f` is the function `extChartAt I x ∘ f ∘ (extChartAt I x).symm`.
  refine ContinuousMap.localFixedPointIndex_eq_sign_det ?_ (.of_forall fun z ↦ rfl) hd
    (hdet' ▸ hdet)
  simp only [chartFixedPointMap_apply, extChartAt, (chartAt H x).extend_left_inv
    (mem_chart_source H x), hfx]

/-- **The local fixed-point index at a nondegenerate fixed point** is the Lefschetz sign
`sgn det (1 - df_x)`. -/
theorem IsNondegenerateFixedPt.localFixedPointIndex_eq_fixedPointSign {f : C(M, M)} {x : M}
    (h : IsNondegenerateFixedPt I f x) : localFixedPointIndex I f x = fixedPointSign I f x :=
  TauCeti.localFixedPointIndex_eq_fixedPointSign h.isFixedPt h.mdifferentiableAt
    h.fixedPointDet_ne_zero

/-- On a manifold modelled on a zero-dimensional space every fixed point has local fixed-point
index `1`. -/
theorem localFixedPointIndex_of_subsingleton [Subsingleton E] {f : C(M, M)} {x : M}
    (hfx : f x = x) : localFixedPointIndex I f x = 1 := by
  rw [localFixedPointIndex_eq_localFixedPointIndex_chartFixedPointMap hfx]
  exact ContinuousMap.localFixedPointIndex_of_subsingleton _ _

/-- **The local fixed-point index on the model space**: for a continuous self-map `f` of `E`, with
its trivial chart, the local fixed-point index at `x` is the local fixed-point index at `x` of the
restriction of `f` to any open set containing `x`. -/
theorem localFixedPointIndex_modelSpace (f : C(E, E)) {U : Opens E} {x : E} (hx : x ∈ U) :
    localFixedPointIndex 𝓘(ℝ, E) f x = ContinuousMap.localFixedPointIndex (U := U)
      (f.restrict U) ⟨x, hx⟩ := by
  by_cases hfx : f x = x
  · rw [localFixedPointIndex_eq_localFixedPointIndex_chartFixedPointMap hfx]
    refine (ContinuousMap.localFixedPointIndex_eq_of_hasStrictFDerivAt (h := id)
      (A := ContinuousLinearEquiv.refl ℝ E) ?_ (hasStrictFDerivAt_id _) hx
      (.of_forall fun z hz ↦ ?_)).symm
    · simp [chartFixedPointMap_apply, hfx]
    · simpa [chartFixedPointMap_apply] using f.restrict_apply U ⟨_, hz⟩
  · rw [localFixedPointIndex_of_ne hfx, ContinuousMap.localFixedPointIndex_of_ne _ hfx]

/-- **Chart independence of the local fixed-point index.** On a `C¹` manifold without boundary, the
local fixed-point index of `f` at `x` can be read in any chart of the maximal atlas whose source
contains `x`. -/
theorem chartLocalFixedPointIndex_eq_localFixedPointIndex [IsManifold I 1 M]
    {c : OpenPartialHomeomorph M H} (hc : c ∈ IsManifold.maximalAtlas I 1 M) {f : C(M, M)}
    {x : M} (hx : x ∈ c.source) :
    chartLocalFixedPointIndex I c f x = localFixedPointIndex I f x := by
  by_cases hfx : f x = x
  · have hc' := IsManifold.chart_mem_maximalAtlas (I := I) (n := 1) x
    have hmem : c.extend I x ∈ (I.extendCoordChange c (chartAt H x)).source := by
      rw [← c.extend_image_source_inter]
      exact mem_image_of_mem _ ⟨hx, mem_chart_source H x⟩
    have hopen : IsOpen (I.extendCoordChange c (chartAt H x)).source :=
      I.isOpen_extendCoordChange_source
    obtain ⟨A, hA⟩ := I.isInvertible_fderivWithin_extendCoordChange one_ne_zero hc hc' hmem
    rw [fderivWithin_of_isOpen hopen hmem] at hA
    have hcd : ContDiffAt ℝ 1 (I.extendCoordChange c (chartAt H x)) (c.extend I x) :=
      (I.contDiffOn_extendCoordChange hc hc' _ hmem).contDiffAt (hopen.mem_nhds hmem)
    have hs := hcd.hasStrictFDerivAt_fderiv one_ne_zero
    rw [← hA] at hs
    exact (chartLocalFixedPointIndex_eq_of_hasStrictFDerivAt (Φ := id) hfx hx
      (mem_chart_source H x) continuousAt_id (.of_forall fun _ ↦ rfl) hs).symm
  · rw [chartLocalFixedPointIndex_of_ne _ hfx, localFixedPointIndex_of_ne hfx]

/-! ### Invariance under conjugation -/

section Conjugation

variable {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω}

/-- **Invariance of the local fixed-point index under conjugation by a local diffeomorphism.** If a
`C^n` local diffeomorphism `Φ : M → N` at a fixed point `x` of `f`, `n ≠ 0`, conjugates `f` near
`x` to `g`, that is `Φ (f z) = g (Φ z)` for `z` near `x`, then the local fixed-point index of `g`
at `Φ x` is that of `f` at `x`. This holds whether or not `Φ` preserves orientation. -/
theorem _root_.IsLocalDiffeomorphAt.localFixedPointIndex_eq_of_eventually_semiconj {Φ : M → N}
    {x : M} (hΦ : IsLocalDiffeomorphAt I J n Φ x) (hn : n ≠ 0) {f : C(M, M)} {g : C(N, N)}
    (hfx : f x = x) (h : ∀ᶠ z in 𝓝 x, Φ (f z) = g (Φ z)) :
    localFixedPointIndex J g (Φ x) = localFixedPointIndex I f x := by
  have hΦ1 : ContMDiffAt I J 1 Φ x :=
    hΦ.contMDiffAt.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  -- The coordinate expression of `Φ` has the invertible strict derivative `dΦ_x`.
  obtain ⟨A, hA⟩ := hΦ.isInvertible_mfderiv hn
  have hs := hΦ1.hasStrictFDerivAt_extChartAt_conj
  rw [← (hΦ1.mdifferentiableAt one_ne_zero).mfderiv_eq_fderiv_extChartAt_conj rfl, ← hA] at hs
  exact chartLocalFixedPointIndex_eq_of_hasStrictFDerivAt hfx (mem_chart_source H x)
    (mem_chart_source H' (Φ x)) hΦ1.continuousAt h hs

/-- **Invariance of the local fixed-point index under conjugation by a diffeomorphism.** If a `C^n`
diffeomorphism `Φ : M → N`, `n ≠ 0`, conjugates `f` to `g`, then the local fixed-point index of `g`
at `Φ x` is that of `f` at `x`, for every `x`. -/
theorem _root_.Diffeomorph.localFixedPointIndex_eq_of_semiconj (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0)
    {f : C(M, M)} {g : C(N, N)} (h : Semiconj Φ f g) (x : M) :
    localFixedPointIndex J g (Φ x) = localFixedPointIndex I f x := by
  by_cases hfx : f x = x
  · exact (Φ.isLocalDiffeomorph x).localFixedPointIndex_eq_of_eventually_semiconj hn hfx
      (.of_forall h)
  · rw [localFixedPointIndex_of_ne hfx, localFixedPointIndex_of_ne]
    rw [← h x]
    exact Φ.injective.ne hfx

end Conjugation

end TauCeti
