/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Double
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Interior
public import TauCeti.Topology.Constructions.DoubleAlong.Separation

/-!
# The Schottky double of a Riemann surface with boundary

Let `M` be a Riemann surface with boundary: a charted space modelled on the closed upper
half-plane whose chart changes lie in `TauCeti.borderedHolomorphicGroupoid`. Its boundary is the
complement of its manifold interior `TauCeti.borderedInterior M`, a closed set. The *Schottky
double* `TauCeti.SchottkyDouble M` is the topological double `TauCeti.DoubleAlong` of `M` along its
boundary: two copies of `M` glued by the identity along the boundary. The second copy is the
conjugate surface.

Each chart `e` of `M` doubles to a chart `TauCeti.SchottkyDouble.doubleChart e` of the double,
with values in `ℂ`: it is `e` on the first copy and `z ↦ conj (e z)` on the second copy. This is
well defined because a chart of the maximal atlas is real exactly on the boundary. Its inverse
sends a point `w` of the closed upper half-plane to the first copy and a point of the open lower
half-plane to the second copy, through the fold `TauCeti.ClosedUpperHalfPlane.fold`. The chart
change between two doubled charts agrees on its source with the Schwarz reflection
`TauCeti.ClosedUpperHalfPlane.schwarzDouble` of the chart change of `M`, which is holomorphic by the
Schwarz reflection principle. So the double is a Riemann surface without boundary. It is
Hausdorff and second countable when `M` is, and compact when `M` is.

The sheet swap `TauCeti.DoubleAlong.swap` is an involution of the double which reads as
`z ↦ conj z` in every doubled chart, so it is antiholomorphic in the holomorphic charts of the
double; its fixed set is the boundary on the first copy. The first copy of the interior of `M` is
an open subset of the double, on which the complex structure of the double restricts to that of
the interior: the inclusion of the interior in the first copy is a holomorphic open embedding, and
the inclusion in the second copy is an open embedding which reads as `z ↦ conj z` in charts.

The type `TauCeti.SchottkyDouble M` is a reducible abbreviation of the double along the boundary,
so the topological API of `TauCeti.DoubleAlong` applies to it directly. Its complex charts are
attached only to doubles along the complement of `TauCeti.borderedInterior M`.

## Main definitions

* `TauCeti.SchottkyDouble`: the double of a Riemann surface with boundary along its boundary.
* `TauCeti.SchottkyDouble.doubleChart`: the doubled chart of a chart of the maximal atlas.
* `TauCeti.SchottkyDouble.instChartedSpace`: the doubled charts, modelled on `ℂ`.
* `TauCeti.SchottkyDouble.interiorInl` and `TauCeti.SchottkyDouble.interiorInr`: the inclusions
  of the interior in the first and second copies.

## Main results

* `TauCeti.SchottkyDouble.doubleChart_symm_trans_eqOnSource`: a chart change of the double is the
  Schwarz reflection of the chart change of `M`.
* `TauCeti.SchottkyDouble.doubleChart_mem_maximalAtlas`: the doubled chart of a chart of the
  bordered holomorphic maximal atlas of `M` is a holomorphic chart of the double.
* `TauCeti.SchottkyDouble.instHasGroupoid` and `TauCeti.SchottkyDouble.instIsManifold`: the double
  is a Riemann surface without boundary.
* `TauCeti.SchottkyDouble.instT2Space`, `TauCeti.SchottkyDouble.instSecondCountableTopology`: the
  double is Hausdorff and second countable when `M` is. Compactness is inherited from
  `TauCeti.DoubleAlong`.
* `TauCeti.SchottkyDouble.doubleChart_swap` and
  `TauCeti.SchottkyDouble.writtenInExtChartAt_swap_eventuallyEq_conj`: the swap reads as
  `z ↦ conj z` in every doubled chart.
* `TauCeti.DoubleAlong.swap_swap` and `TauCeti.DoubleAlong.fixed_locus` apply directly: the swap
  is an involution whose fixed set is the boundary on the first copy.
* `TauCeti.SchottkyDouble.isOpenEmbedding_interiorInl` and
  `TauCeti.SchottkyDouble.contMDiff_interiorInl`: the first copy of the interior is a holomorphic
  open embedding.
* `TauCeti.SchottkyDouble.isOpenEmbedding_interiorInr` and
  `TauCeti.SchottkyDouble.writtenInExtChartAt_interiorInr_eventuallyEq_conj`: the second copy of
  the interior is an open embedding which reads as `z ↦ conj z` in charts.

## References

* L. V. Ahlfors and L. Sario, *Riemann Surfaces*, Princeton University Press, 1960, Ch. II, for
  the double of a bordered Riemann surface.
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81.
-/

public section

noncomputable section

open Set Complex Filter Topology TopologicalSpace
open scoped Manifold ContDiff ComplexConjugate

namespace TauCeti

variable (M : Type*) [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M]

/-- The *Schottky double* of a Riemann surface with boundary `M`: two copies of `M` glued by the
identity along the boundary of `M`, the complement of its manifold interior. Doubled charts make it
a Riemann surface without boundary (`TauCeti.SchottkyDouble.instIsManifold`). -/
abbrev SchottkyDouble : Type _ :=
  DoubleAlong (borderedInterior M : Set M)ᶜ

namespace SchottkyDouble

variable {M} {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ℂ]

/-! ### The doubled chart -/

section doubleChart

variable {e : OpenPartialHomeomorph M ClosedUpperHalfPlane}

open Classical in
/-- The doubled chart of a chart `e` of `M`, as a function on the double: it is `e` on the first
copy and `z ↦ conj (e z)` on the second copy. -/
private def doubleChartFun (e : OpenPartialHomeomorph M ClosedUpperHalfPlane) :
    SchottkyDouble M → ℂ :=
  (range (DoubleAlong.inl (borderedInterior M : Set M)ᶜ)).piecewise
    (fun z ↦ (e (DoubleAlong.fold _ z) : ℂ)) fun z ↦ conj (e (DoubleAlong.fold _ z) : ℂ)

open Classical in
/-- The inverse of the doubled chart of a chart `e` of `M`: points of the closed upper half-plane
go to the first copy and points of the open lower half-plane to the second copy. -/
private def doubleChartInvFun (e : OpenPartialHomeomorph M ClosedUpperHalfPlane) :
    ℂ → SchottkyDouble M :=
  {w : ℂ | 0 ≤ w.im}.piecewise
    (fun w ↦ DoubleAlong.inl _ (e.symm (ClosedUpperHalfPlane.fold w)))
    fun w ↦ DoubleAlong.inr _ (e.symm (ClosedUpperHalfPlane.fold w))

/-- A point of `M` at which a chart of the maximal atlas is real lies on the boundary, so its two
copies in the double agree. -/
theorem inl_eq_inr_of_im_eq_zero (he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M)
    {x : M} (hx : x ∈ e.source) (h : (e x : ℂ).im = 0) :
    DoubleAlong.inl (borderedInterior M : Set M)ᶜ x = DoubleAlong.inr _ x :=
  DoubleAlong.inl_coe_eq_inr _
    ⟨x, (im_eq_zero_iff_notMem_borderedInterior he hx).1 h⟩

private theorem doubleChartFun_inl (x : M) : doubleChartFun e (DoubleAlong.inl _ x) = e x := by
  simp [doubleChartFun]

private theorem doubleChartFun_inr (he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M)
    {x : M} (hx : x ∈ e.source) : doubleChartFun e (DoubleAlong.inr _ x) = conj (e x : ℂ) := by
  by_cases hA : x ∈ (borderedInterior M : Set M)ᶜ
  · rw [← DoubleAlong.inl_coe_eq_inr _ ⟨x, hA⟩, doubleChartFun_inl,
      (conj_apply_eq_iff_notMem_borderedInterior he hx).2 hA]
  · have : DoubleAlong.inr _ x ∉ range (DoubleAlong.inl (borderedInterior M : Set M)ᶜ) := by
      rintro ⟨y, hy⟩
      have h := (DoubleAlong.inl_eq_inr_iff _).1 hy
      exact hA (h.1 ▸ h.2)
    simp [doubleChartFun, this]

private theorem doubleChartInvFun_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) :
    doubleChartInvFun e w = DoubleAlong.inl _ (e.symm (ClosedUpperHalfPlane.fold w)) := by
  simp [doubleChartInvFun, hw]

private theorem doubleChartInvFun_of_im_neg {w : ℂ} (hw : w.im < 0) :
    doubleChartInvFun e w = DoubleAlong.inr _ (e.symm (ClosedUpperHalfPlane.fold w)) := by
  simp [doubleChartInvFun, not_le.2 hw]

private theorem fold_doubleChartInvFun (w : ℂ) :
    DoubleAlong.fold _ (doubleChartInvFun e w) = e.symm (ClosedUpperHalfPlane.fold w) := by
  rcases le_or_gt 0 w.im with hw | hw
  · rw [doubleChartInvFun_of_im_nonneg hw, DoubleAlong.fold_inl]
  · rw [doubleChartInvFun_of_im_neg hw, DoubleAlong.fold_inr]

private theorem fold_doubleChartFun (z : SchottkyDouble M) :
    ClosedUpperHalfPlane.fold (doubleChartFun e z) = e (DoubleAlong.fold _ z) := by
  by_cases h : z ∈ range (DoubleAlong.inl (borderedInterior M : Set M)ᶜ) <;>
    simp [doubleChartFun, h, ClosedUpperHalfPlane.fold_conj]

open Classical in
/-- The doubled chart is continuous on both copies of the source of `e`: its two pieces agree on
the frontier of the first copy, which lies in the boundary, where `e` is real. -/
private theorem continuousOn_doubleChartFun
    (he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M) :
    ContinuousOn (doubleChartFun e) (DoubleAlong.fold _ ⁻¹' e.source) := by
  have hc : ContinuousOn (fun z : SchottkyDouble M ↦ (e (DoubleAlong.fold _ z) : ℂ))
      (DoubleAlong.fold _ ⁻¹' e.source) :=
    continuous_subtype_val.comp_continuousOn
      (e.continuousOn.comp (DoubleAlong.fold _).continuous.continuousOn fun _ hz ↦ hz)
  refine ContinuousOn.piecewise ?_ (hc.mono inter_subset_left)
    ((continuous_conj.comp_continuousOn hc).mono inter_subset_left)
  rintro z ⟨hz, hfr⟩
  have hcl := (borderedInterior M).isOpen.isClosed_compl
  obtain ⟨x, hA, rfl⟩ := (DoubleAlong.frontier_range_inl _ hcl).subset hfr
  rw [mem_preimage, DoubleAlong.fold_inl] at hz
  simp only [DoubleAlong.fold_inl]
  exact ((conj_apply_eq_iff_notMem_borderedInterior he hz).2 (hcl.frontier_subset hA)).symm

open Classical in
/-- The inverse of the doubled chart is continuous on its target: its two pieces agree on the real
axis, which `e.symm` sends to the boundary, where the two copies are glued. -/
private theorem continuousOn_doubleChartInvFun
    (he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M) :
    ContinuousOn (doubleChartInvFun e) (ClosedUpperHalfPlane.fold ⁻¹' e.target) := by
  have hc : ContinuousOn (fun w ↦ e.symm (ClosedUpperHalfPlane.fold w))
      (ClosedUpperHalfPlane.fold ⁻¹' e.target) :=
    e.continuousOn_symm.comp ClosedUpperHalfPlane.continuous_fold.continuousOn fun _ hw ↦ hw
  refine ContinuousOn.piecewise ?_
    (((DoubleAlong.inl _).continuous.comp_continuousOn hc).mono inter_subset_left)
    (((DoubleAlong.inr _).continuous.comp_continuousOn hc).mono inter_subset_left)
  rintro w ⟨hw, hfr⟩
  have h0 : w.im = 0 := (frontier_le_subset_eq continuous_const continuous_im hfr).symm
  have hsrc := e.map_target hw
  refine inl_eq_inr_of_im_eq_zero he hsrc ?_
  rw [e.right_inv hw, ClosedUpperHalfPlane.im_fold, h0, abs_zero]

/-- The doubled chart of a chart `e` of the maximal atlas of a Riemann surface with boundary `M`:
the chart of the Schottky double that is `e` on the first copy and `z ↦ conj (e z)` on the second
copy. Its source consists of both copies of the source of `e`, and its target is the preimage of
the target of `e` under the fold `TauCeti.ClosedUpperHalfPlane.fold`. -/
def doubleChart (e : OpenPartialHomeomorph M ClosedUpperHalfPlane)
    (he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M) :
    OpenPartialHomeomorph (SchottkyDouble M) ℂ where
  toFun := doubleChartFun e
  invFun := doubleChartInvFun e
  source := DoubleAlong.fold _ ⁻¹' e.source
  target := ClosedUpperHalfPlane.fold ⁻¹' e.target
  map_source' z hz := by
    simpa [mem_preimage, fold_doubleChartFun] using e.map_source hz
  map_target' w hw := by
    simpa [mem_preimage, fold_doubleChartInvFun] using e.map_target hw
  left_inv' z hz := by
    induction z using DoubleAlong.induction_on with
    | hl x =>
      rw [mem_preimage, DoubleAlong.fold_inl] at hz
      rw [doubleChartFun_inl, doubleChartInvFun_of_im_nonneg (e x).property,
        ClosedUpperHalfPlane.fold_coe, e.left_inv hz]
    | hr x =>
      rw [mem_preimage, DoubleAlong.fold_inr] at hz
      rw [doubleChartFun_inr he hz]
      rcases (e x).property.eq_or_lt with h0 | hpos
      · rw [doubleChartInvFun_of_im_nonneg (by simp [← h0]), ClosedUpperHalfPlane.fold_conj,
          ClosedUpperHalfPlane.fold_coe, e.left_inv hz]
        exact inl_eq_inr_of_im_eq_zero he hz h0.symm
      · rw [doubleChartInvFun_of_im_neg (by simpa using hpos), ClosedUpperHalfPlane.fold_conj,
          ClosedUpperHalfPlane.fold_coe, e.left_inv hz]
  right_inv' w hw := by
    rw [mem_preimage] at hw
    have hsrc := e.map_target hw
    rcases le_or_gt 0 w.im with hnn | hneg
    · rw [doubleChartInvFun_of_im_nonneg hnn, doubleChartFun_inl, e.right_inv hw,
        ClosedUpperHalfPlane.coe_fold_of_im_nonneg hnn]
    · rw [doubleChartInvFun_of_im_neg hneg, doubleChartFun_inr he hsrc, e.right_inv hw,
        ClosedUpperHalfPlane.coe_fold_of_im_nonpos hneg.le, conj_conj]
  open_source := e.open_source.preimage (DoubleAlong.fold _).continuous
  open_target := e.open_target.preimage ClosedUpperHalfPlane.continuous_fold
  continuousOn_toFun := continuousOn_doubleChartFun he
  continuousOn_invFun := continuousOn_doubleChartInvFun he

variable (he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M)

@[simp]
theorem doubleChart_source :
    (doubleChart e he).source = DoubleAlong.fold _ ⁻¹' e.source :=
  (rfl)

@[simp]
theorem doubleChart_target :
    (doubleChart e he).target = ClosedUpperHalfPlane.fold ⁻¹' e.target :=
  (rfl)

/-- On the first copy the doubled chart is the chart of `M`. -/
@[simp]
theorem doubleChart_inl (x : M) : doubleChart e he (DoubleAlong.inl _ x) = e x :=
  doubleChartFun_inl x

/-- On the second copy the doubled chart is the conjugate of the chart of `M`. -/
theorem doubleChart_inr {x : M} (hx : x ∈ e.source) :
    doubleChart e he (DoubleAlong.inr _ x) = conj (e x : ℂ) :=
  doubleChartFun_inr he hx

/-- The inverse of the doubled chart sends the closed upper half-plane to the first copy. -/
theorem doubleChart_symm_apply_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) :
    (doubleChart e he).symm w = DoubleAlong.inl _ (e.symm (ClosedUpperHalfPlane.fold w)) :=
  doubleChartInvFun_of_im_nonneg hw

/-- The inverse of the doubled chart sends the open lower half-plane to the second copy. -/
theorem doubleChart_symm_apply_of_im_neg {w : ℂ} (hw : w.im < 0) :
    (doubleChart e he).symm w = DoubleAlong.inr _ (e.symm (ClosedUpperHalfPlane.fold w)) :=
  doubleChartInvFun_of_im_neg hw

@[simp]
theorem fold_doubleChart_symm (w : ℂ) :
    DoubleAlong.fold _ ((doubleChart e he).symm w) = e.symm (ClosedUpperHalfPlane.fold w) :=
  fold_doubleChartInvFun w

@[simp]
theorem fold_doubleChart (z : SchottkyDouble M) :
    ClosedUpperHalfPlane.fold (doubleChart e he z) = e (DoubleAlong.fold _ z) :=
  fold_doubleChartFun z

/-- The doubled chart intertwines the sheet swap with complex conjugation on its source. -/
theorem doubleChart_swap {z : SchottkyDouble M} (hz : z ∈ (doubleChart e he).source) :
    doubleChart e he (DoubleAlong.swap _ z) = conj (doubleChart e he z) := by
  induction z using DoubleAlong.induction_on with
  | hl x =>
    rw [doubleChart_source, mem_preimage, DoubleAlong.fold_inl] at hz
    rw [DoubleAlong.swap_inl, doubleChart_inr he hz, doubleChart_inl]
  | hr x =>
    rw [doubleChart_source, mem_preimage, DoubleAlong.fold_inr] at hz
    rw [DoubleAlong.swap_inr, doubleChart_inl, doubleChart_inr he hz, conj_conj]

/-- The source of a doubled chart is invariant under the sheet swap. -/
theorem swap_mem_doubleChart_source_iff {z : SchottkyDouble M} :
    DoubleAlong.swap _ z ∈ (doubleChart e he).source ↔ z ∈ (doubleChart e he).source := by
  simp

/-- A chart change of the double is the Schwarz reflection of the chart change of `M`. -/
theorem doubleChart_symm_trans_eqOnSource {e' : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (he' : e' ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M)
    (h : ClosedUpperHalfPlane.PreservesRealAxis (e.symm.trans e')) :
    (doubleChart e he).symm.trans (doubleChart e' he') ≈
      ClosedUpperHalfPlane.schwarzDouble (e.symm.trans e') h := by
  refine (OpenPartialHomeomorph.eqOnSource_iff _ _).2 ⟨?_, fun w hw ↦ ?_⟩
  · ext w
    simp
  · have hw' : ClosedUpperHalfPlane.fold w ∈ e.target ∧
        e.symm (ClosedUpperHalfPlane.fold w) ∈ e'.source := by simpa using hw
    simp only [OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.coe_trans,
      Function.comp_apply]
    rcases le_or_gt 0 w.im with hnn | hneg
    · rw [doubleChart_symm_apply_of_im_nonneg he hnn, doubleChart_inl,
        ClosedUpperHalfPlane.schwarzDouble_apply_of_im_nonneg h hnn,
        OpenPartialHomeomorph.trans_apply]
    · rw [doubleChart_symm_apply_of_im_neg he hneg, doubleChart_inr he' hw'.2,
        ClosedUpperHalfPlane.schwarzDouble_apply_of_im_neg h hneg,
        OpenPartialHomeomorph.trans_apply]

end doubleChart

/-! ### The complex structure -/

/-- The Schottky double is a charted space modelled on `ℂ`: the chart at a point is the doubled
chart of the chart of `M` at its image under the fold. -/
instance instChartedSpace : ChartedSpace ℂ (SchottkyDouble M) where
  atlas := {f | ∃ (e : OpenPartialHomeomorph M ClosedUpperHalfPlane)
    (he : e ∈ atlas ClosedUpperHalfPlane M),
      f = doubleChart e (IsManifold.subset_maximalAtlas he)}
  chartAt z := doubleChart (chartAt ClosedUpperHalfPlane (DoubleAlong.fold _ z))
    (IsManifold.chart_mem_maximalAtlas _)
  mem_chart_source z := by
    rw [doubleChart_source]
    exact mem_chart_source ClosedUpperHalfPlane (DoubleAlong.fold _ z)
  chart_mem_atlas z := ⟨_, chart_mem_atlas _ _, rfl⟩

theorem chartAt_eq (z : SchottkyDouble M) :
    chartAt ℂ z = doubleChart (chartAt ClosedUpperHalfPlane (DoubleAlong.fold _ z))
      (IsManifold.chart_mem_maximalAtlas _) :=
  rfl

/-- The chart of the double at a point of the first copy is the doubled chart at that point. -/
@[simp]
theorem chartAt_inl (x : M) :
    chartAt ℂ (DoubleAlong.inl (borderedInterior M : Set M)ᶜ x) =
      doubleChart (chartAt ClosedUpperHalfPlane x) (IsManifold.chart_mem_maximalAtlas _) := by
  rw [chartAt_eq]
  congr 1
  simp

/-- The chart of the double at a point of the second copy is the doubled chart at that point. -/
@[simp]
theorem chartAt_inr (x : M) :
    chartAt ℂ (DoubleAlong.inr (borderedInterior M : Set M)ᶜ x) =
      doubleChart (chartAt ClosedUpperHalfPlane x) (IsManifold.chart_mem_maximalAtlas _) := by
  rw [chartAt_eq]
  congr 1
  simp

theorem mem_atlas_iff {f : OpenPartialHomeomorph (SchottkyDouble M) ℂ} :
    f ∈ atlas ℂ (SchottkyDouble M) ↔ ∃ (e : OpenPartialHomeomorph M ClosedUpperHalfPlane)
      (he : e ∈ atlas ClosedUpperHalfPlane M),
        f = doubleChart e (IsManifold.subset_maximalAtlas he) :=
  Iff.rfl

/-- The doubled chart of a chart of the atlas of `M` is a chart of the atlas of the double. -/
theorem doubleChart_mem_atlas {e : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (he : e ∈ atlas ClosedUpperHalfPlane M) :
    doubleChart e (IsManifold.subset_maximalAtlas he) ∈ atlas ℂ (SchottkyDouble M) :=
  ⟨e, he, rfl⟩

/-- The chart of the double is the same at a point and at its image under the sheet swap. -/
@[simp]
theorem chartAt_swap (z : SchottkyDouble M) :
    chartAt ℂ (DoubleAlong.swap (borderedInterior M : Set M)ᶜ z) = chartAt ℂ z := by
  rw [chartAt_eq, chartAt_eq]
  congr 1
  simp

/-- In the chart of the double at `z` and the chart at its image under the sheet swap, the swap is
`z ↦ conj z` near the image of `z`. -/
theorem writtenInExtChartAt_swap_eventuallyEq_conj (z : SchottkyDouble M) :
    writtenInExtChartAt 𝓘(𝕜, ℂ) 𝓘(𝕜, ℂ) z (DoubleAlong.swap (borderedInterior M : Set M)ᶜ)
      =ᶠ[𝓝 (extChartAt 𝓘(𝕜, ℂ) z z)] fun w ↦ conj w := by
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, chartAt_swap]
  filter_upwards [(chartAt ℂ z).eventually_right_inverse (mem_chart_target ℂ z),
    (chartAt ℂ z).open_target.mem_nhds (mem_chart_target ℂ z)] with w hw hw'
  have hsrc := (chartAt ℂ z).map_target hw'
  rw [chartAt_eq] at hsrc hw ⊢
  simp only [Function.comp_apply]
  rw [doubleChart_swap _ hsrc, hw]

/-- A chart change between the doubled charts of two charts of `M` whose chart change is bordered
holomorphic is holomorphic. -/
private theorem doubleChart_symm_trans_mem_contDiffGroupoid
    {e e' : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M)
    (he' : e' ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M)
    (hmem : e.symm.trans e' ∈ borderedHolomorphicGroupoid) :
    (doubleChart e he).symm.trans (doubleChart e' he') ∈ contDiffGroupoid ω 𝓘(ℂ) :=
  have hpr := ClosedUpperHalfPlane.preservesRealAxis_of_mem_borderedHolomorphicGroupoid hmem
  (contDiffGroupoid ω 𝓘(ℂ)).mem_of_eqOnSource
    (ClosedUpperHalfPlane.schwarzDouble_mem_contDiffGroupoid hpr hmem)
    (doubleChart_symm_trans_eqOnSource he he' hpr)

/-- The doubled chart of a chart of the bordered holomorphic maximal atlas of `M` is a chart of
the `C^n` maximal atlas of the double for every `n`, the holomorphic one included. -/
theorem doubleChart_mem_maximalAtlas {n : ℕ∞ω} {e : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (he : e ∈ borderedHolomorphicGroupoid.maximalAtlas M) :
    doubleChart e (StructureGroupoid.maximalAtlas_mono
        (borderedHolomorphicGroupoid_le_contDiffGroupoid.trans
          (contDiffGroupoid_le ENat.LEInfty.out)) he) ∈
      IsManifold.maximalAtlas 𝓘(ℂ) n (SchottkyDouble M) := by
  refine IsManifold.maximalAtlas_subset_of_le le_top ?_
  rintro _ ⟨e', he', rfl⟩
  exact ⟨doubleChart_symm_trans_mem_contDiffGroupoid _ _ (he e' he').1,
    doubleChart_symm_trans_mem_contDiffGroupoid _ _ (he e' he').2⟩

section holomorphic

variable [HasGroupoid M borderedHolomorphicGroupoid]

/-- **The Schottky double has holomorphic chart changes.** The chart changes of the double are
Schwarz reflections of bordered holomorphic chart changes. -/
instance instHasGroupoid : HasGroupoid (SchottkyDouble M) (contDiffGroupoid ω 𝓘(ℂ)) where
  compatible := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    exact doubleChart_symm_trans_mem_contDiffGroupoid _ _
      (borderedHolomorphicGroupoid.compatible he he')

/-- **The Schottky double is a Riemann surface without boundary.** -/
instance instIsManifold : IsManifold 𝓘(ℂ) ω (SchottkyDouble M) :=
  IsManifold.mk' _ _ _

end holomorphic

/-- The Schottky double of a Hausdorff Riemann surface with boundary is Hausdorff. -/
instance instT2Space [T2Space M] : T2Space (SchottkyDouble M) :=
  DoubleAlong.t2Space _ (borderedInterior M).isOpen.isClosed_compl

/-- The Schottky double of a second-countable Riemann surface with boundary is second countable. -/
instance instSecondCountableTopology [SecondCountableTopology M] :
    SecondCountableTopology (SchottkyDouble M) :=
  DoubleAlong.secondCountableTopology _ (borderedInterior M).isOpen.isClosed_compl

/-! ### The first copy of the interior -/

/-- A map of the interior of `M` to the double which restricts a map `f` of `M` is an open
embedding when the restriction of `f` to the complement of the boundary is: that complement is
`(borderedInterior M)ᶜᶜ`, which equals the interior by `compl_compl`. -/
private theorem isOpenEmbedding_of_eq_domRestrict {f : M → SchottkyDouble M}
    (hf : IsOpenEmbedding ((borderedInterior M : Set M)ᶜᶜ.domRestrict f))
    {g : borderedInterior M → SchottkyDouble M}
    (hg : g = (borderedInterior M : Set M).domRestrict f) : IsOpenEmbedding g := by
  rw [compl_compl] at hf
  rwa [hg]

variable (M) in
/-- The inclusion of the interior of `M` in the first copy of the Schottky double. -/
def interiorInl : borderedInterior M → SchottkyDouble M :=
  fun x ↦ DoubleAlong.inl _ (x : M)

@[simp]
theorem interiorInl_apply (x : borderedInterior M) :
    interiorInl M x = DoubleAlong.inl _ (x : M) :=
  (rfl)

/-- The first copy of the interior is an open embedded subset of the double. -/
theorem isOpenEmbedding_interiorInl : IsOpenEmbedding (interiorInl M) :=
  isOpenEmbedding_of_eq_domRestrict
    (DoubleAlong.isOpenEmbedding_inl_compl _ (borderedInterior M).isOpen.isClosed_compl)
    (funext fun x ↦ by simp)

/-- In the chart of the interior at `x` and the chart of the double at its image, the inclusion of
the interior in the first copy is the identity near the image of `x`. -/
theorem writtenInExtChartAt_interiorInl_eventuallyEq_id (x : borderedInterior M) :
    writtenInExtChartAt 𝓘(𝕜, ℂ) 𝓘(𝕜, ℂ) x (interiorInl M)
      =ᶠ[𝓝 (extChartAt 𝓘(𝕜, ℂ) x x)] id := by
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp]
  filter_upwards [(chartAt ℂ x).eventually_right_inverse (mem_chart_target ℂ x)] with w hw
  simp only [Function.comp_apply, interiorInl_apply, id_eq]
  rw [chartAt_inl, doubleChart_inl, ← chartAt_borderedInterior_apply x, hw]

/-- **The first copy of the interior is holomorphic.** The inclusion of the interior of `M`, with
its complex structure, in the first copy of the Schottky double is `C^n` over every scalar field
`𝕜` acting on `ℂ`: holomorphic for `𝕜 = ℂ` and real smooth for `𝕜 = ℝ`. -/
theorem contMDiff_interiorInl {n : ℕ∞ω} :
    ContMDiff 𝓘(𝕜, ℂ) 𝓘(𝕜, ℂ) n (interiorInl M) := by
  intro x
  refine contMDiffAt_iff.2 ⟨isOpenEmbedding_interiorInl.continuous.continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
  exact contDiffAt_id.congr_of_eventuallyEq (writtenInExtChartAt_interiorInl_eventuallyEq_id x)

/-! ### The second copy of the interior -/

variable (M) in
/-- The inclusion of the interior of `M` in the second copy of the Schottky double. -/
def interiorInr : borderedInterior M → SchottkyDouble M :=
  fun x ↦ DoubleAlong.inr _ (x : M)

@[simp]
theorem interiorInr_apply (x : borderedInterior M) :
    interiorInr M x = DoubleAlong.inr _ (x : M) :=
  (rfl)

/-- The second copy of the interior is an open embedded subset of the double. -/
theorem isOpenEmbedding_interiorInr : IsOpenEmbedding (interiorInr M) :=
  isOpenEmbedding_of_eq_domRestrict
    (DoubleAlong.isOpenEmbedding_inr_compl _ (borderedInterior M).isOpen.isClosed_compl)
    (funext fun x ↦ by simp)

/-- In the chart of the interior at `x` and the chart of the double at the image of `x` on the
second copy, the inclusion of the interior in the second copy is `z ↦ conj z` near the image of
`x`. -/
theorem writtenInExtChartAt_interiorInr_eventuallyEq_conj (x : borderedInterior M) :
    writtenInExtChartAt 𝓘(𝕜, ℂ) 𝓘(𝕜, ℂ) x (interiorInr M)
      =ᶠ[𝓝 (extChartAt 𝓘(𝕜, ℂ) x x)] fun w ↦ conj w := by
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp]
  filter_upwards [(chartAt ℂ x).eventually_right_inverse (mem_chart_target ℂ x),
    (chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with w hw hw'
  have hsrc : (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hw'
  rw [chartAt_borderedInterior_source] at hsrc
  simp only [Function.comp_apply, interiorInr_apply]
  rw [chartAt_inr, doubleChart_inr _ hsrc,
    ← chartAt_borderedInterior_apply x, hw]

end SchottkyDouble

end TauCeti
