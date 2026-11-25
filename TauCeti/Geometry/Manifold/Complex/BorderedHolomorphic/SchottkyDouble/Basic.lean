/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Double
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Interior
public import TauCeti.Topology.Constructions.DoubleAlong.Separation
public import TauCeti.Geometry.Manifold.Boundary.Derivative
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import TauCeti.Geometry.Manifold.VectorField.StrictInward

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

The FULL first and second sheets are real `C^n` embeddings for every `n ≤ ∞`, including
boundary points, with preferred-chart differentials identity and conjugation. The exact native
boundary, using `ClosedUpperHalfPlane.euclideanHalfSpaceChartedSpace` and the canonical boundary
charts, is smoothly embedded by `boundaryInl`; its range is the fixed locus of the swap and its
tangent image is the real axis. At boundary points the first sheet sends strictly inward vectors
to vectors of positive imaginary part, and the second sheet to vectors of negative imaginary
part, in the preferred doubled chart.

The type `TauCeti.SchottkyDouble M` is a reducible abbreviation of the double along the boundary,
so the topological API of `TauCeti.DoubleAlong` applies to it directly. Its complex charts are
attached only to doubles along the complement of `TauCeti.borderedInterior M`.

## Main definitions

* `TauCeti.SchottkyDouble`: the double of a Riemann surface with boundary along its boundary.
* `TauCeti.SchottkyDouble.doubleChart`: the doubled chart of a chart of the maximal atlas.
* `TauCeti.SchottkyDouble.instChartedSpace`: the doubled charts, modelled on `ℂ`.
* `TauCeti.SchottkyDouble.boundaryInl`: inclusion of the actual native real boundary.
* `TauCeti.SchottkyDouble.interiorInl` and `TauCeti.SchottkyDouble.interiorInr`: the inclusions
  of the interior in the first and second copies.

## Main results

* `TauCeti.SchottkyDouble.doubleChart_symm_trans_eqOnSource`: a chart change of the double is the
  Schwarz reflection of the chart change of `M`.
* `TauCeti.SchottkyDouble.doubleChart_mem_maximalAtlas`: the doubled chart of a chart of the
  bordered holomorphic maximal atlas of `M` is a holomorphic chart of the double.
* `TauCeti.SchottkyDouble.instHasGroupoid` and `TauCeti.SchottkyDouble.instIsManifold`: the double
  is a Riemann surface without boundary; `instIsManifoldReal` also gives its real analytic atlas.
* `TauCeti.SchottkyDouble.instT2Space`, `TauCeti.SchottkyDouble.instSecondCountableTopology`: the
  double is Hausdorff and second countable when `M` is. Compactness is inherited from
  `TauCeti.DoubleAlong`.
* `TauCeti.SchottkyDouble.doubleChart_swap` and
  `TauCeti.SchottkyDouble.writtenInExtChartAt_swap_eventuallyEq_conj`: the swap reads as
  `z ↦ conj z` in every doubled chart, so it is real smooth (`contMDiff_swap`).
* `TauCeti.SchottkyDouble.contMDiffAt_fold_inl` and `TauCeti.SchottkyDouble.contMDiffAt_fold_inr`:
  the fold of the double onto `M` is real smooth at both copies of every interior point.
* `TauCeti.DoubleAlong.swap_swap` and `TauCeti.DoubleAlong.fixed_locus` apply directly: the swap
  is an involution whose fixed set is the boundary on the first copy.
* `TauCeti.SchottkyDouble.isOpenEmbedding_interiorInl` and
  `TauCeti.SchottkyDouble.contMDiff_interiorInl`: the first copy of the interior is a holomorphic
  open embedding.
* `TauCeti.SchottkyDouble.isOpenEmbedding_interiorInr` and
  `TauCeti.SchottkyDouble.writtenInExtChartAt_interiorInr_eventuallyEq_conj`: the second copy of
  the interior is an open embedding which reads as `z ↦ conj z` in charts.

* `TauCeti.SchottkyDouble.isSmoothEmbedding_inl` and `isSmoothEmbedding_inr`: both full
  original-model sheets are real smooth embeddings, at every order up to and including `∞`.
* `TauCeti.SchottkyDouble.hasMFDerivAt_inl` and `hasMFDerivAt_inr`: their native real derivatives
  are identity and conjugation; the corresponding `mfderiv` and application laws compute them.
* `TauCeti.SchottkyDouble.isSmoothEmbedding_boundaryInl` and `range_mfderiv_boundaryInl`: the
  native boundary is smoothly embedded, with tangent image `Complex.imCLM.ker`.
* `TauCeti.SchottkyDouble.range_boundaryInl`: the actual native boundary is the fixed locus of
  the sheet swap.
* `TauCeti.SchottkyDouble.mem_strictInwardTangentCone_iff_im_mfderiv_inl_pos` and
  `mem_strictInwardTangentCone_iff_im_mfderiv_inr_neg`: both intrinsic inward signs.

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
    continuous_subtypeVal.comp_continuousOn
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

/-- The sheet swap of the Schottky double is real `C^n` for every `n`: it reads as `z ↦ conj z` in
the doubled charts. -/
theorem contMDiff_swap {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (DoubleAlong.swap (borderedInterior M : Set M)ᶜ) := by
  intro z
  refine contMDiffAt_iff.2 ⟨(DoubleAlong.swap _).continuous.continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
  exact Complex.conjCLE.contDiff.contDiffAt.congr_of_eventuallyEq
    (writtenInExtChartAt_swap_eventuallyEq_conj z)

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
    doubleChart e (borderedHolomorphicGroupoid_maximalAtlas_subset ENat.LEInfty.out he) ∈
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

/-- The holomorphic Schottky atlas is also a real analytic manifold atlas. -/
instance instIsManifoldReal : IsManifold 𝓘(ℝ, ℂ) ω (SchottkyDouble M) :=
  (inferInstance : IsManifold 𝓘(ℂ) ω (SchottkyDouble M)).restrictScalars ℝ

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

/-! ### Interior sheets in doubled charts -/

section ChartSides

local notation "A" => (borderedInterior M : Set M)ᶜ
local notation "D" => SchottkyDouble M

/-- Folding a doubled-chart coordinate gives an interior point exactly off the real axis. -/
private theorem chartAt_symm_fold_mem_borderedInterior_iff {p z : D}
    (hz : z ∈ (chartAt ℂ p).source) :
    (chartAt ClosedUpperHalfPlane (DoubleAlong.fold A p)).symm
      (ClosedUpperHalfPlane.fold (chartAt ℂ p z)) ∈ borderedInterior M ↔
        (chartAt ℂ p z).im ≠ 0 := by
  let e := chartAt ClosedUpperHalfPlane (DoubleAlong.fold A p)
  have ht : ClosedUpperHalfPlane.fold (chartAt ℂ p z) ∈ e.target := by
    simpa only [chartAt_eq, doubleChart_target, mem_preimage] using
      (chartAt ℂ p).map_source hz
  rw [mem_borderedInterior_iff_im_pos
    (IsManifold.chart_mem_maximalAtlas (DoubleAlong.fold A p)) (e.map_target ht),
    e.right_inv ht, ClosedUpperHalfPlane.im_fold, abs_pos]

/-- In a doubled chart, the first interior sheet consists exactly of positive imaginary
coordinates. -/
theorem mem_range_interiorInl_iff_im_chartAt_pos {p z : D}
    (hz : z ∈ (chartAt ℂ p).source) :
    z ∈ range (interiorInl M) ↔ 0 < (chartAt ℂ p z).im := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [interiorInl_apply, chartAt_eq, doubleChart_inl]
    apply (mem_borderedInterior_iff_im_pos
      (IsManifold.chart_mem_maximalAtlas (DoubleAlong.fold A p)) ?_).1 u.property
    simpa only [interiorInl_apply, chartAt_eq, doubleChart_source, mem_preimage,
      DoubleAlong.fold_inl] using hz
  intro hpos
  have hi := (chartAt_symm_fold_mem_borderedInterior_iff hz).2 (ne_of_gt hpos)
  rw [chartAt_eq] at hz hpos hi
  let e := chartAt ClosedUpperHalfPlane (DoubleAlong.fold A p)
  have he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M :=
    IsManifold.chart_mem_maximalAtlas (DoubleAlong.fold A p)
  let c := doubleChart e he
  refine ⟨⟨e.symm (ClosedUpperHalfPlane.fold (c z)), hi⟩, ?_⟩
  rw [SchottkyDouble.interiorInl_apply]
  exact (SchottkyDouble.doubleChart_symm_apply_of_im_nonneg he hpos.le).symm.trans
    (c.left_inv hz)

/-- In a doubled chart, the second interior sheet consists exactly of negative imaginary
coordinates. -/
theorem mem_range_interiorInr_iff_im_chartAt_neg {p z : D}
    (hz : z ∈ (chartAt ℂ p).source) :
    z ∈ range (interiorInr M) ↔ (chartAt ℂ p z).im < 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hu : (u : M) ∈ (chartAt ClosedUpperHalfPlane (DoubleAlong.fold A p)).source := by
      simpa only [interiorInr_apply, chartAt_eq, doubleChart_source, mem_preimage,
        DoubleAlong.fold_inr] using hz
    rw [interiorInr_apply, chartAt_eq,
      doubleChart_inr (IsManifold.chart_mem_maximalAtlas (DoubleAlong.fold A p)) hu,
      Complex.conj_im, neg_lt_zero]
    exact (mem_borderedInterior_iff_im_pos
      (IsManifold.chart_mem_maximalAtlas (DoubleAlong.fold A p)) hu).1 u.property
  intro hneg
  have hi := (chartAt_symm_fold_mem_borderedInterior_iff hz).2 (ne_of_lt hneg)
  rw [chartAt_eq] at hz hneg hi
  let e := chartAt ClosedUpperHalfPlane (DoubleAlong.fold A p)
  have he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M :=
    IsManifold.chart_mem_maximalAtlas (DoubleAlong.fold A p)
  let c := doubleChart e he
  refine ⟨⟨e.symm (ClosedUpperHalfPlane.fold (c z)), hi⟩, ?_⟩
  rw [SchottkyDouble.interiorInr_apply]
  exact (SchottkyDouble.doubleChart_symm_apply_of_im_neg he hneg).symm.trans (c.left_inv hz)

/-- In a doubled-chart domain, the native seam consists exactly of real coordinates. -/
theorem mem_image_inl_compl_iff_im_chartAt_eq_zero {p z : D}
    (hz : z ∈ (chartAt ℂ p).source) :
    z ∈ DoubleAlong.inl A '' A ↔ (chartAt ℂ p z).im = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [chartAt_eq, doubleChart_inl]
    apply (im_eq_zero_iff_notMem_borderedInterior
      (IsManifold.chart_mem_maximalAtlas (DoubleAlong.fold A p)) ?_).2 hy
    simpa only [chartAt_eq, doubleChart_source, mem_preimage, DoubleAlong.fold_inl] using hz
  intro him
  have hboundary : (chartAt ClosedUpperHalfPlane (DoubleAlong.fold A p)).symm
      (ClosedUpperHalfPlane.fold (chartAt ℂ p z)) ∈ A :=
    fun h ↦ (chartAt_symm_fold_mem_borderedInterior_iff hz).1 h him
  refine ⟨_, hboundary, ?_⟩
  rw [chartAt_eq] at hz him ⊢
  exact (doubleChart_symm_apply_of_im_nonneg
    (IsManifold.chart_mem_maximalAtlas (DoubleAlong.fold A p)) him.ge).symm.trans
      ((doubleChart _ _).left_inv hz)

/-- The first interior sheet is disjoint from the gluing set. -/
theorem disjoint_range_interiorInl_image_inl_compl :
    Disjoint (range (interiorInl M)) (DoubleAlong.inl A '' A) := by
  rw [Set.disjoint_left]
  rintro _ ⟨u, rfl⟩ ⟨y, hy, heq⟩
  rw [interiorInl_apply, DoubleAlong.inl_eq_inl_iff] at heq
  exact hy (heq.symm ▸ u.property)

/-- The second interior sheet is disjoint from the gluing set. -/
theorem disjoint_range_interiorInr_image_inl_compl :
    Disjoint (range (interiorInr M)) (DoubleAlong.inl A '' A) := by
  rw [Set.disjoint_left]
  rintro _ ⟨u, rfl⟩ ⟨y, _, heq⟩
  rw [interiorInr_apply, DoubleAlong.inl_eq_inr_iff] at heq
  exact heq.2 (heq.1 ▸ u.property)

/-- Near the first copy of an interior point, the fold of the double onto `M` is real `C^n`: it is
the identity in the doubled chart and the chart of `M`. -/
theorem contMDiffAt_fold_inl {n : ℕ∞ω} {x : M} (hx : x ∈ borderedInterior M) :
    ContMDiffAt 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel n (DoubleAlong.fold A)
      (DoubleAlong.inl A x) := by
  refine contMDiffAt_iff.2 ⟨(DoubleAlong.fold A).continuous.continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
  set e := chartAt ClosedUpperHalfPlane x
  have he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M :=
    IsManifold.chart_mem_maximalAtlas x
  have hxe : x ∈ e.source := mem_chart_source _ x
  have hpos : 0 < (e x : ℂ).im := (mem_borderedInterior_iff_im_pos he hxe).1 hx
  have htarget : (doubleChart e he).target ∈ 𝓝 (e x : ℂ) := by
    refine (doubleChart e he).open_target.mem_nhds ?_
    simpa [ClosedUpperHalfPlane.fold_coe] using e.map_source hxe
  refine contDiffAt_id.congr_of_eventuallyEq ?_
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, chartAt_inl, doubleChart_inl, DoubleAlong.fold_inl,
    Function.comp_id, Function.id_comp]
  filter_upwards [htarget, continuous_im.continuousAt.eventually (lt_mem_nhds hpos)]
    with w hw hw'
  simp only [Function.comp_apply, fold_doubleChart_symm, id_eq]
  rw [doubleChart_target, mem_preimage] at hw
  rw [e.right_inv hw, closedUpperHalfPlaneModel_apply,
    ClosedUpperHalfPlane.coe_fold_of_im_nonneg hw'.le]

/-- Near the second copy of an interior point, the fold of the double onto `M` is real `C^n`: it is
the fold of the first copy composed with the sheet swap. -/
theorem contMDiffAt_fold_inr {n : ℕ∞ω} {x : M} (hx : x ∈ borderedInterior M) :
    ContMDiffAt 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel n (DoubleAlong.fold A)
      (DoubleAlong.inr A x) := by
  have h := (contMDiffAt_fold_inl (n := n) hx).comp_of_eq (contMDiff_swap.contMDiffAt)
    (DoubleAlong.swap_inr A x)
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ (DoubleAlong.fold_swap A z).symm)

end ChartSides

end SchottkyDouble

end TauCeti

/-! ### Full real sheets and the native boundary -/

namespace TauCeti.SchottkyDouble

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]

/-- In the preferred doubled chart, the full first sheet is the identity on the extended
half-plane target, including its boundary. -/
theorem writtenInExtChartAt_inl_eqOn_id [IsManifold closedUpperHalfPlaneModel 1 M]
    (x : M) :
    EqOn (writtenInExtChartAt closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) x
      (DoubleAlong.inl (borderedInterior M : Set M)ᶜ))
      id (extChartAt closedUpperHalfPlaneModel x).target := by
  intro w hw
  rw [extChartAt_target] at hw
  simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, id_eq, SchottkyDouble.chartAt_inl,
    SchottkyDouble.doubleChart_inl]
  rw [(chartAt ClosedUpperHalfPlane x).right_inv hw.1]
  simpa only [closedUpperHalfPlaneModel_apply] using
    closedUpperHalfPlaneModel.right_inv hw.2

/-- The full first sheet, with its original real model with corners, is a smooth embedding. -/
theorem isSmoothEmbedding_inl [HasGroupoid M borderedHolomorphicGroupoid]
    {n : ℕ∞ω} (hn : n ≤ ∞) :
    Manifold.IsSmoothEmbedding closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) n
    (DoubleAlong.inl (borderedInterior M : Set M)ᶜ) := by
  apply (Topology.IsEmbedding.isSmoothEmbedding_of_writtenInExtChartAt_eqOn
    (n := ∞) (DoubleAlong.isEmbedding_inl (borderedInterior M : Set M)ᶜ)
    (ContinuousLinearEquiv.prodUnique ℝ ℂ PUnit.{1}) ?_).of_le hn
  intro x w hw
  simpa only [Function.comp_apply, ContinuousLinearEquiv.prodUnique_apply, id_eq] using
    writtenInExtChartAt_inl_eqOn_id x hw

/-- The real manifold derivative of the full first sheet is the identity in preferred charts. -/
theorem hasMFDerivAt_inl [IsManifold closedUpperHalfPlaneModel 1 M]
    (x : M) : HasMFDerivAt closedUpperHalfPlaneModel 𝓘(ℝ, ℂ)
    (DoubleAlong.inl (borderedInterior M : Set M)ᶜ) x (ContinuousLinearMap.id ℝ ℂ) := by
  apply ContinuousAt.hasMFDerivAt_of_writtenInExtChartAt_eventuallyEq
    (DoubleAlong.inl _).continuous.continuousAt
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := closedUpperHalfPlaneModel) x] with w hw
  exact writtenInExtChartAt_inl_eqOn_id x hw

/-- The first-sheet derivative is the real identity. -/
@[simp]
theorem mfderiv_inl [IsManifold closedUpperHalfPlaneModel 1 M] (x : M) :
    mfderiv closedUpperHalfPlaneModel 𝓘(ℝ, ℂ)
      (DoubleAlong.inl (borderedInterior M : Set M)ᶜ) x = ContinuousLinearMap.id ℝ ℂ :=
  (hasMFDerivAt_inl x).mfderiv

/-- The first-sheet derivative retains the model coordinate of a tangent vector. -/
theorem mfderiv_inl_apply [IsManifold closedUpperHalfPlaneModel 1 M] (x : M)
    (v : TangentSpace closedUpperHalfPlaneModel x) :
    mfderiv closedUpperHalfPlaneModel 𝓘(ℝ, ℂ)
      (DoubleAlong.inl (borderedInterior M : Set M)ᶜ) x v = (v : ℂ) :=
  DFunLike.congr_fun (mfderiv_inl x) v

/-- In the preferred doubled chart, the full second sheet is complex conjugation on the
extended half-plane target. -/
theorem writtenInExtChartAt_inr_eqOn_conj [IsManifold closedUpperHalfPlaneModel 1 M]
    (x : M) :
    EqOn (writtenInExtChartAt closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) x
      (DoubleAlong.inr (borderedInterior M : Set M)ᶜ))
      (fun z ↦ conj z) (extChartAt closedUpperHalfPlaneModel x).target := by
  intro w hw
  rw [extChartAt_target] at hw
  simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, id_eq, SchottkyDouble.chartAt_inr]
  rw [SchottkyDouble.doubleChart_inr _ ((chartAt ClosedUpperHalfPlane x).map_target hw.1),
    (chartAt ClosedUpperHalfPlane x).right_inv hw.1]
  exact congrArg (fun z : ℂ ↦ conj z)
    (by simpa only [closedUpperHalfPlaneModel_apply] using
      closedUpperHalfPlaneModel.right_inv hw.2)

/-- The full second sheet is a real smooth embedding, including its boundary. -/
theorem isSmoothEmbedding_inr [HasGroupoid M borderedHolomorphicGroupoid]
    {n : ℕ∞ω} (hn : n ≤ ∞) :
    Manifold.IsSmoothEmbedding closedUpperHalfPlaneModel
    𝓘(ℝ, ℂ) n (DoubleAlong.inr (borderedInterior M : Set M)ᶜ) := by
  apply (Topology.IsEmbedding.isSmoothEmbedding_of_writtenInExtChartAt_eqOn
    (n := ∞) (DoubleAlong.isEmbedding_inr (borderedInterior M : Set M)ᶜ)
    ((ContinuousLinearEquiv.prodUnique ℝ ℂ PUnit.{1}).trans Complex.conjCLE) ?_).of_le hn
  intro x w hw
  simpa only [Function.comp_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodUnique_apply, Complex.conjCLE_apply] using
    writtenInExtChartAt_inr_eqOn_conj x hw

/-- The real manifold derivative of the full second sheet is complex conjugation. -/
theorem hasMFDerivAt_inr [IsManifold closedUpperHalfPlaneModel 1 M]
    (x : M) : HasMFDerivAt closedUpperHalfPlaneModel 𝓘(ℝ, ℂ)
    (DoubleAlong.inr (borderedInterior M : Set M)ᶜ) x Complex.conjCLE.toContinuousLinearMap := by
  apply ContinuousAt.hasMFDerivAt_of_writtenInExtChartAt_eventuallyEq
    (DoubleAlong.inr _).continuous.continuousAt
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := closedUpperHalfPlaneModel) x] with w hw
  exact writtenInExtChartAt_inr_eqOn_conj x hw

/-- The second-sheet derivative is the real conjugation map. -/
@[simp]
theorem mfderiv_inr [IsManifold closedUpperHalfPlaneModel 1 M] (x : M) :
    mfderiv closedUpperHalfPlaneModel 𝓘(ℝ, ℂ)
      (DoubleAlong.inr (borderedInterior M : Set M)ᶜ) x = Complex.conjCLE.toContinuousLinearMap :=
  (hasMFDerivAt_inr x).mfderiv

/-- The second-sheet derivative conjugates the model coordinate of a tangent vector. -/
theorem mfderiv_inr_apply [IsManifold closedUpperHalfPlaneModel 1 M] (x : M)
    (v : TangentSpace closedUpperHalfPlaneModel x) :
    mfderiv closedUpperHalfPlaneModel 𝓘(ℝ, ℂ)
      (DoubleAlong.inr (borderedInterior M : Set M)ᶜ) x v = (starRingEnd ℂ) (v : ℂ) :=
  DFunLike.congr_fun (mfderiv_inr x) v

/-- At a boundary point, the first-sheet derivative sends strictly inward vectors to
vectors with positive imaginary part in the preferred doubled chart. -/
theorem mem_strictInwardTangentCone_iff_im_mfderiv_inl_pos
    [IsManifold closedUpperHalfPlaneModel 1 M]
    (x : M) (hx : x ∉ borderedInterior M)
    (v : TangentSpace closedUpperHalfPlaneModel x) :
    v ∈ strictInwardTangentCone closedUpperHalfPlaneModel x ↔
      0 < (mfderiv closedUpperHalfPlaneModel 𝓘(ℝ, ℂ)
        (DoubleAlong.inl (borderedInterior M : Set M)ᶜ) x v).im := by
  rw [mfderiv_inl_apply]
  have hxim : (extChartAt closedUpperHalfPlaneModel x x).im = 0 := by
    simpa only [extChartAt_coe, Function.comp_apply, closedUpperHalfPlaneModel_apply] using
      (im_eq_zero_iff_notMem_borderedInterior (IsManifold.chart_mem_maximalAtlas _)
        (mem_chart_source _ _)).2 hx
  rw [mem_strictInwardTangentCone_iff]
  exact mem_strictInwardCone_closedUpperHalfPlaneModel_iff _ _ hxim

/-- At a boundary point, the second-sheet derivative sends strictly inward vectors to
vectors with negative imaginary part in the preferred doubled chart. -/
theorem mem_strictInwardTangentCone_iff_im_mfderiv_inr_neg
    [IsManifold closedUpperHalfPlaneModel 1 M]
    (x : M) (hx : x ∉ borderedInterior M)
    (v : TangentSpace closedUpperHalfPlaneModel x) :
    v ∈ strictInwardTangentCone closedUpperHalfPlaneModel x ↔
      (mfderiv closedUpperHalfPlaneModel 𝓘(ℝ, ℂ)
        (DoubleAlong.inr (borderedInterior M : Set M)ᶜ) x v).im < 0 := by
  simpa only [mfderiv_inl_apply, mfderiv_inr_apply, Complex.conj_im (v : ℂ),
    neg_lt_zero] using
    mem_strictInwardTangentCone_iff_im_mfderiv_inl_pos x hx v

section NativeBoundary
attribute [local instance] ClosedUpperHalfPlane.euclideanHalfSpaceChartedSpace
  ClosedUpperHalfPlane.isManifold_euclideanHalfSpace

/-- The full first sheet in native half-space coordinates is the inverse of the real
coordinate comparison, on the actual extended chart target. -/
theorem writtenInExtChartAt_inl_euclideanHalfSpace_eqOn [IsManifold closedUpperHalfPlaneModel 1 M]
    (x : M) :
    EqOn (writtenInExtChartAt (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) x
      (DoubleAlong.inl (borderedInterior M : Set M)ᶜ))
      closedUpperHalfPlaneCoordinates.symm (extChartAt (𝓡∂ (1 + 1)) x).target := by
  intro v hv
  rw [extChartAt_target] at hv
  have hvt := hv.1
  rw [Set.mem_preimage, ClosedUpperHalfPlane.mem_chartAt_euclideanHalfSpace_target] at hvt
  have hmodel : ((𝓡∂ (1 + 1)).symm v).val = v := by
    exact (𝓡∂ (1 + 1)).right_inv hv.2
  simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe, extChartAt_coe_symm,
    modelWithCornersSelf_coe, Function.id_comp, SchottkyDouble.chartAt_inl,
    ClosedUpperHalfPlane.chartAt_euclideanHalfSpace_symm_apply]
  rw [SchottkyDouble.doubleChart_inl, (chartAt ClosedUpperHalfPlane x).right_inv hvt,
    ClosedUpperHalfPlane.coe_euclideanHalfSpaceHomeomorph_symm, hmodel]

/-- The full first sheet is a smooth embedding also for the native real half-space model. -/
theorem isSmoothEmbedding_inl_euclideanHalfSpace [HasGroupoid M borderedHolomorphicGroupoid]
    {n : ℕ∞ω} (hn : n ≤ ∞) :
    Manifold.IsSmoothEmbedding (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) n
      (DoubleAlong.inl (borderedInterior M : Set M)ᶜ) := by
  have : IsManifold (𝓡∂ (1 + 1)) ∞ M :=
    ClosedUpperHalfPlane.isManifold_euclideanHalfSpace M
  apply (Topology.IsEmbedding.isSmoothEmbedding_of_writtenInExtChartAt_eqOn
    (n := ∞) (DoubleAlong.isEmbedding_inl (borderedInterior M : Set M)ᶜ)
    ((ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin (1 + 1))) PUnit.{1}).trans
      closedUpperHalfPlaneCoordinates.symm) ?_).of_le hn
  intro x w hw
  simpa only [Function.comp_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodUnique_apply] using
    writtenInExtChartAt_inl_euclideanHalfSpace_eqOn x hw

/-- The first-sheet derivative for the native half-space model is the inverse coordinate map. -/
theorem hasMFDerivAt_inl_euclideanHalfSpace [IsManifold closedUpperHalfPlaneModel 1 M]
    (x : M) : HasMFDerivAt (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ)
    (DoubleAlong.inl (borderedInterior M : Set M)ᶜ) x
      closedUpperHalfPlaneCoordinates.symm.toContinuousLinearMap := by
  apply ContinuousAt.hasMFDerivAt_of_writtenInExtChartAt_eventuallyEq
    (DoubleAlong.inl _).continuous.continuousAt
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓡∂ (1 + 1)) x] with w hw
  exact writtenInExtChartAt_inl_euclideanHalfSpace_eqOn x hw

/-- The inclusion of the actual native manifold boundary into the first sheet of the double.
The boundary uses the half-space charts obtained from the original bordered charts by
`ClosedUpperHalfPlane.euclideanHalfSpaceHomeomorph` and the canonical boundary charts.
Its `C¹` hypothesis is needed to state the codomain `SchottkyDouble M`, whose gluing locus
is packaged using the open manifold interior. -/
def boundaryInl [IsManifold closedUpperHalfPlaneModel 1 M]
    (y : (𝓡∂ (1 + 1)).boundary M) : SchottkyDouble M :=
  DoubleAlong.inl (borderedInterior M : Set M)ᶜ (y : M)

/-- Evaluation of the inclusion of the actual native boundary. -/
@[simp]
theorem boundaryInl_apply [IsManifold closedUpperHalfPlaneModel 1 M]
    (p : (𝓡∂ (1 + 1)).boundary M) :
    boundaryInl p = DoubleAlong.inl (borderedInterior M : Set M)ᶜ (p : M) := by
  rfl

/-- The two sheets agree on the actual native boundary. -/
theorem boundaryInl_eq_inr [IsManifold closedUpperHalfPlaneModel 1 M]
    (p : (𝓡∂ (1 + 1)).boundary M) :
    boundaryInl p = DoubleAlong.inr (borderedInterior M : Set M)ᶜ (p : M) := by
  rw [boundaryInl_apply]
  exact DoubleAlong.inl_coe_eq_inr (borderedInterior M : Set M)ᶜ
    ⟨(p : M), (mem_boundary_euclideanHalfSpace_iff_notMem_borderedInterior (p : M)).1 p.property⟩

/-- The embedded native boundary is exactly the fixed locus of the sheet swap. -/
theorem range_boundaryInl [IsManifold closedUpperHalfPlaneModel 1 M] :
    range (boundaryInl (M := M)) =
      {z | DoubleAlong.swap (borderedInterior M : Set M)ᶜ z = z} := by
  rw [DoubleAlong.fixed_locus]
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨(p : M),
      (mem_boundary_euclideanHalfSpace_iff_notMem_borderedInterior (p : M)).1 p.property,
      (boundaryInl_apply p).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, (mem_boundary_euclideanHalfSpace_iff_notMem_borderedInterior x).2 hx⟩, by rfl⟩

/-- The native boundary inclusion is the real-axis parametrization in preferred charts. -/
theorem writtenInExtChartAt_boundaryInl_eqOn [IsManifold closedUpperHalfPlaneModel 1 M]
    (p : (𝓡∂ (1 + 1)).boundary M) :
    EqOn (writtenInExtChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) p
      (boundaryInl (M := M)))
      (closedUpperHalfPlaneCoordinates.symm ∘ euclideanHalfSpaceBoundaryParam 1)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) p).target := by
  intro z hz
  have hparam := (boundaryParam_mem_extChartAt_target_iff p z).2 hz
  have hzt : EuclideanHalfSpace.boundaryParam 1 z ∈
      (chartAt (EuclideanHalfSpace (1 + 1)) (p : M)).target := by
    rw [extChartAt_target] at hparam
    simpa only [mem_preimage, EuclideanHalfSpace.boundaryParam_coe,
      EuclideanHalfSpace.modelWithCornersEuclideanHalfSpace_symm_boundaryParam]
      using hparam.1
  have h := boundaryChartedSpace_chartAt_symm_apply M p hzt
  simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe_symm,
    modelWithCornersSelf_coe_symm, Function.comp_id] at h ⊢
  simp only [boundaryInl_apply]
  rw [h]
  simpa only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe_symm,
    EuclideanHalfSpace.modelWithCornersEuclideanHalfSpace_symm_boundaryParam] using
      writtenInExtChartAt_inl_euclideanHalfSpace_eqOn (p : M) hparam

/-- The derivative of the actual boundary inclusion inserts the zero normal coordinate and
then applies the native half-space-to-complex coordinate comparison. -/
theorem hasMFDerivAt_boundaryInl [IsManifold closedUpperHalfPlaneModel 1 M]
    (p : (𝓡∂ (1 + 1)).boundary M) :
    HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) (boundaryInl (M := M)) p
      (closedUpperHalfPlaneCoordinates.symm.toContinuousLinearMap.comp
        (euclideanHalfSpaceBoundaryParam 1)) := by
  apply ContinuousAt.hasMFDerivAt_of_writtenInExtChartAt_eventuallyEq
    ((DoubleAlong.inl _).continuous.comp continuous_subtypeVal).continuousAt
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) p]
    with w hw
  exact writtenInExtChartAt_boundaryInl_eqOn p hw

/-- The boundary derivative in preferred charts is the native zero-normal-coordinate map. -/
@[simp]
theorem mfderiv_boundaryInl [IsManifold closedUpperHalfPlaneModel 1 M]
    (p : (𝓡∂ (1 + 1)).boundary M) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) (boundaryInl (M := M)) p =
      closedUpperHalfPlaneCoordinates.symm.toContinuousLinearMap.comp
        (euclideanHalfSpaceBoundaryParam 1) :=
  (hasMFDerivAt_boundaryInl p).mfderiv

/-- A native boundary tangent vector has real-axis image in the doubled chart. -/
theorem mfderiv_boundaryInl_apply [IsManifold closedUpperHalfPlaneModel 1 M]
    (p : (𝓡∂ (1 + 1)).boundary M)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) p) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ)
      (boundaryInl (M := M)) p v =
        (((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) p v) 0 : ℝ) : ℂ) := by
  rw [mfderiv_boundaryInl]
  exact closedUpperHalfPlaneCoordinates_symm_boundaryParam
    (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) p v)

/-- The native boundary tangent image is exactly the kernel of the imaginary-part map. -/
theorem range_mfderiv_boundaryInl [IsManifold closedUpperHalfPlaneModel 1 M]
    (p : (𝓡∂ (1 + 1)).boundary M) :
    LinearMap.range (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ)
      (boundaryInl (M := M)) p).toLinearMap = Complex.imCLM.ker := by
  rw [mfderiv_boundaryInl]
  exact range_closedUpperHalfPlaneCoordinates_symm_boundaryParam

/-- The actual native boundary is smoothly embedded in the Schottky double. -/
theorem isSmoothEmbedding_boundaryInl [HasGroupoid M borderedHolomorphicGroupoid]
    {n : ℕ∞ω} (hn : n ≤ ∞) :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) n
    (boundaryInl (M := M)) := by
  have : IsManifold (𝓡∂ (1 + 1)) ∞ M :=
    ClosedUpperHalfPlane.isManifold_euclideanHalfSpace M
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞ ((𝓡∂ (1 + 1)).boundary M) :=
    TauCeti.isManifold_boundary (n := 1) M
  apply (Topology.IsEmbedding.isSmoothEmbedding_of_writtenInExtChartAt_eqOn (n := ∞)
    (f := boundaryInl (M := M))
    ((DoubleAlong.isEmbedding_inl _).comp IsEmbedding.subtypeVal)
    ((euclideanHalfSpaceBoundaryNormalEquiv 1).trans closedUpperHalfPlaneCoordinates.symm)
    ?_).of_le hn
  intro p z hz
  simpa only [Function.comp_apply, ContinuousLinearEquiv.trans_apply,
    euclideanHalfSpaceBoundaryNormalEquiv_apply_zero_eq_boundaryParam] using
    writtenInExtChartAt_boundaryInl_eqOn p hz

end NativeBoundary

end TauCeti.SchottkyDouble
