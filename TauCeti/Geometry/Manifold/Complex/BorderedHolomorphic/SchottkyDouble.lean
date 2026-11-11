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
well defined because a chart of the atlas is real exactly on the boundary. Its inverse sends a
point `w` of the closed upper half-plane to the first copy and a point of the open lower
half-plane to the second copy, through the fold `TauCeti.ClosedUpperHalfPlane.fold`. The chart
change between two doubled charts agrees on its source with the Schwarz reflection
`TauCeti.ClosedUpperHalfPlane.schwarzDouble` of the chart change of `M`, which is holomorphic by the
Schwarz reflection principle. So the double is a Riemann surface without boundary. It is
Hausdorff and second countable when `M` is, and compact when `M` is.

The sheet swap `TauCeti.DoubleAlong.swap` is an involution of the double which reads as
`z ↦ conj z` in every doubled chart, so it is antiholomorphic; its fixed set is the boundary on the
first copy. The first copy of the interior of `M` is an open subset of the double, on which the
complex structure of the double restricts to that of the interior: the inclusion of the interior
in the first copy is a holomorphic open embedding, and the inclusion in the second copy reads as
`z ↦ conj z` in charts.

The type `TauCeti.SchottkyDouble M` is a reducible abbreviation of the double along the boundary,
so the topological API of `TauCeti.DoubleAlong` applies to it directly. Its complex charts are
attached only to doubles along the complement of `TauCeti.borderedInterior M`.

## Main definitions

* `TauCeti.SchottkyDouble`: the double of a Riemann surface with boundary along its boundary.
* `TauCeti.SchottkyDouble.doubleChart`: the doubled chart of a chart of the atlas.
* `TauCeti.SchottkyDouble.instChartedSpace`: the doubled charts, modelled on `ℂ`.
* `TauCeti.SchottkyDouble.interiorInl`: the inclusion of the interior in the first copy.

## Main results

* `TauCeti.SchottkyDouble.doubleChart_symm_trans_eqOnSource`: a chart change of the double is the
  Schwarz reflection of the chart change of `M`.
* `TauCeti.SchottkyDouble.instHasGroupoid` and `TauCeti.SchottkyDouble.instIsManifold`: the double
  is a Riemann surface without boundary.
* `TauCeti.SchottkyDouble.instT2Space`, `TauCeti.SchottkyDouble.instSecondCountableTopology`: the
  double is Hausdorff and second countable when `M` is. Compactness is inherited from
  `TauCeti.DoubleAlong`.
* `TauCeti.SchottkyDouble.doubleChart_swap`: the swap reads as `z ↦ conj z` in every doubled chart.
* `TauCeti.SchottkyDouble.fixedPoints_swap`: the fixed set of the swap is the boundary.
* `TauCeti.SchottkyDouble.isOpenEmbedding_interiorInl` and
  `TauCeti.SchottkyDouble.contMDiff_interiorInl`: the first copy of the interior is a holomorphic
  open embedding.
* `TauCeti.SchottkyDouble.extChartAt_inr_eventuallyEq_conj`: the second copy is antiholomorphic.

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

/-- The boundary of `M`, along which the Schottky double is glued, is closed. -/
theorem isClosed_boundary : IsClosed (borderedInterior M : Set M)ᶜ :=
  (borderedInterior M).isOpen.isClosed_compl

variable {M}

/-- A chart of the atlas is real exactly at the boundary points of its source. -/
theorem im_eq_zero_iff_notMem_borderedInterior {e : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (he : e ∈ atlas ClosedUpperHalfPlane M) {x : M} (hx : x ∈ e.source) :
    (e x : ℂ).im = 0 ↔ x ∉ borderedInterior M := by
  rw [mem_borderedInterior_iff_im_pos he hx, not_lt]
  exact ⟨le_of_eq, fun h ↦ le_antisymm h (e x).property⟩

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

private theorem doubleChartFun_inl (x : M) : doubleChartFun e (DoubleAlong.inl _ x) = e x := by
  simp [doubleChartFun]

private theorem doubleChartFun_inr (he : e ∈ atlas ClosedUpperHalfPlane M) {x : M}
    (hx : x ∈ e.source) : doubleChartFun e (DoubleAlong.inr _ x) = conj (e x : ℂ) := by
  by_cases hA : x ∈ (borderedInterior M : Set M)ᶜ
  · have h0 : (e x : ℂ).im = 0 := (im_eq_zero_iff_notMem_borderedInterior he hx).2 hA
    rw [← DoubleAlong.inl_coe_eq_inr _ ⟨x, hA⟩, doubleChartFun_inl,
      conj_eq_iff_im.2 h0]
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

private theorem fold_doubleChartFun (he : e ∈ atlas ClosedUpperHalfPlane M) {z : SchottkyDouble M}
    (hz : DoubleAlong.fold _ z ∈ e.source) :
    ClosedUpperHalfPlane.fold (doubleChartFun e z) = e (DoubleAlong.fold _ z) := by
  induction z using DoubleAlong.induction_on with
  | hl x => simp [doubleChartFun_inl]
  | hr x =>
    rw [DoubleAlong.fold_inr] at hz ⊢
    rw [doubleChartFun_inr he hz, ClosedUpperHalfPlane.fold_conj, ClosedUpperHalfPlane.fold_coe]

open Classical in
/-- The doubled chart of a chart `e` of the atlas of a Riemann surface with boundary `M`: the
chart of the Schottky double that is `e` on the first copy and `z ↦ conj (e z)` on the second
copy. Its source consists of both copies of the source of `e`, and its target is the preimage of
the target of `e` under the fold `TauCeti.ClosedUpperHalfPlane.fold`. -/
def doubleChart (e : OpenPartialHomeomorph M ClosedUpperHalfPlane)
    (he : e ∈ atlas ClosedUpperHalfPlane M) : OpenPartialHomeomorph (SchottkyDouble M) ℂ where
  toFun := doubleChartFun e
  invFun := doubleChartInvFun e
  source := DoubleAlong.fold _ ⁻¹' e.source
  target := ClosedUpperHalfPlane.fold ⁻¹' e.target
  map_source' z hz := by
    simpa [mem_preimage, fold_doubleChartFun he hz] using e.map_source hz
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
      · have hA : x ∈ (borderedInterior M : Set M)ᶜ :=
          (im_eq_zero_iff_notMem_borderedInterior he hz).1 h0.symm
        rw [doubleChartInvFun_of_im_nonneg (by simp [← h0]), ClosedUpperHalfPlane.fold_conj,
          ClosedUpperHalfPlane.fold_coe, e.left_inv hz]
        exact DoubleAlong.inl_coe_eq_inr _ ⟨x, hA⟩
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
  continuousOn_toFun := by
    have hc : ContinuousOn (fun z : SchottkyDouble M ↦ (e (DoubleAlong.fold _ z) : ℂ))
        (DoubleAlong.fold _ ⁻¹' e.source) :=
      continuous_subtype_val.comp_continuousOn
        (e.continuousOn.comp (DoubleAlong.fold _).continuous.continuousOn fun _ hz ↦ hz)
    refine ContinuousOn.piecewise ?_ (hc.mono inter_subset_left)
      ((continuous_conj.comp_continuousOn hc).mono inter_subset_left)
    rintro z ⟨hz, hfr⟩
    have hcl : IsClosed (range (DoubleAlong.inl (borderedInterior M : Set M)ᶜ)) :=
      (DoubleAlong.isClosedEmbedding_inl _ (isClosed_boundary M)).isClosed_range
    have hcl' : IsClosed (range (DoubleAlong.inr (borderedInterior M : Set M)ᶜ)) :=
      (DoubleAlong.isClosedEmbedding_inr _ (isClosed_boundary M)).isClosed_range
    obtain ⟨x, rfl⟩ := hcl.frontier_subset hfr
    have hr : DoubleAlong.inl _ x ∈ range (DoubleAlong.inr (borderedInterior M : Set M)ᶜ) := by
      have hfr' : DoubleAlong.inl _ x ∈
          frontier (range (DoubleAlong.inl (borderedInterior M : Set M)ᶜ))ᶜ := by
        rwa [frontier_compl]
      refine closure_minimal ?_ hcl' (frontier_subset_closure hfr')
      rw [← DoubleAlong.image_compl_inr]
      exact image_subset_range _ _
    obtain ⟨y, hy⟩ := hr
    have hA := ((DoubleAlong.inl_eq_inr_iff _).1 hy.symm).2
    rw [mem_preimage, DoubleAlong.fold_inl] at hz
    simp only [DoubleAlong.fold_inl]
    have h0 : (e x : ℂ).im = 0 := by
      obtain rfl := ((DoubleAlong.inl_eq_inr_iff _).1 hy.symm).1
      exact (im_eq_zero_iff_notMem_borderedInterior he hz).2 hA
    exact (conj_eq_iff_im.2 h0).symm
  continuousOn_invFun := by
    have hc : ContinuousOn (fun w ↦ e.symm (ClosedUpperHalfPlane.fold w))
        (ClosedUpperHalfPlane.fold ⁻¹' e.target) :=
      e.continuousOn_symm.comp ClosedUpperHalfPlane.continuous_fold.continuousOn fun _ hw ↦ hw
    refine ContinuousOn.piecewise ?_
      (((DoubleAlong.inl _).continuous.comp_continuousOn hc).mono inter_subset_left)
      (((DoubleAlong.inr _).continuous.comp_continuousOn hc).mono inter_subset_left)
    rintro w ⟨hw, hfr⟩
    have h0 : w.im = 0 := (frontier_le_subset_eq continuous_const continuous_im hfr).symm
    have hsrc := e.map_target hw
    refine DoubleAlong.inl_coe_eq_inr _
      ⟨_, (im_eq_zero_iff_notMem_borderedInterior he hsrc).1 ?_⟩
    rw [e.right_inv hw, ClosedUpperHalfPlane.im_fold, h0, abs_zero]

variable (he : e ∈ atlas ClosedUpperHalfPlane M)

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

theorem fold_doubleChart {z : SchottkyDouble M} (hz : z ∈ (doubleChart e he).source) :
    ClosedUpperHalfPlane.fold (doubleChart e he z) = e (DoubleAlong.fold _ z) :=
  fold_doubleChartFun he hz

/-- The doubled chart intertwines the sheet swap with complex conjugation. -/
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
    (he' : e' ∈ atlas ClosedUpperHalfPlane M)
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
        ClosedUpperHalfPlane.schwarzDouble_apply_of_im_nonneg h hnn]
      rfl
    · rw [doubleChart_symm_apply_of_im_neg he hneg, doubleChart_inr he' hw'.2,
        ClosedUpperHalfPlane.schwarzDouble_apply_of_im_neg h hneg]
      rfl

end doubleChart

/-! ### The complex structure -/

/-- The Schottky double is a charted space modelled on `ℂ`: the chart at a point is the doubled
chart of the chart of `M` at its image under the fold. -/
instance instChartedSpace : ChartedSpace ℂ (SchottkyDouble M) where
  atlas := {f | ∃ (e : OpenPartialHomeomorph M ClosedUpperHalfPlane)
    (he : e ∈ atlas ClosedUpperHalfPlane M), f = doubleChart e he}
  chartAt z := doubleChart (chartAt ClosedUpperHalfPlane (DoubleAlong.fold _ z))
    (chart_mem_atlas _ _)
  mem_chart_source z := by
    rw [doubleChart_source]
    exact mem_chart_source ClosedUpperHalfPlane (DoubleAlong.fold _ z)
  chart_mem_atlas z := ⟨_, _, rfl⟩

theorem chartAt_eq (z : SchottkyDouble M) :
    chartAt ℂ z = doubleChart (chartAt ClosedUpperHalfPlane (DoubleAlong.fold _ z))
      (chart_mem_atlas _ _) :=
  rfl

/-- The chart of the double at a point of the first copy is the doubled chart at that point. -/
theorem chartAt_inl (x : M) :
    chartAt ℂ (DoubleAlong.inl (borderedInterior M : Set M)ᶜ x) =
      doubleChart (chartAt ClosedUpperHalfPlane x) (chart_mem_atlas _ _) := by
  rw [chartAt_eq]
  congr 1
  simp

/-- The chart of the double at a point of the second copy is the doubled chart at that point. -/
theorem chartAt_inr (x : M) :
    chartAt ℂ (DoubleAlong.inr (borderedInterior M : Set M)ᶜ x) =
      doubleChart (chartAt ClosedUpperHalfPlane x) (chart_mem_atlas _ _) := by
  rw [chartAt_eq]
  congr 1
  simp

theorem mem_atlas_iff {f : OpenPartialHomeomorph (SchottkyDouble M) ℂ} :
    f ∈ atlas ℂ (SchottkyDouble M) ↔ ∃ (e : OpenPartialHomeomorph M ClosedUpperHalfPlane)
      (he : e ∈ atlas ClosedUpperHalfPlane M), f = doubleChart e he :=
  Iff.rfl

section holomorphic

variable [HasGroupoid M borderedHolomorphicGroupoid]

/-- **The Schottky double has holomorphic chart changes.** The chart changes of the double are
Schwarz reflections of bordered holomorphic chart changes. -/
instance instHasGroupoid : HasGroupoid (SchottkyDouble M) (contDiffGroupoid ω 𝓘(ℂ)) where
  compatible := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    have hmem := (borderedHolomorphicGroupoid).compatible he he'
    have hpr := ClosedUpperHalfPlane.preservesRealAxis_of_mem_borderedHolomorphicGroupoid hmem
    exact (contDiffGroupoid ω 𝓘(ℂ)).mem_of_eqOnSource
      (ClosedUpperHalfPlane.schwarzDouble_mem_contDiffGroupoid hpr hmem)
      (doubleChart_symm_trans_eqOnSource he he' hpr)

/-- **The Schottky double is a Riemann surface without boundary.** -/
instance instIsManifold : IsManifold 𝓘(ℂ) ω (SchottkyDouble M) :=
  IsManifold.mk' _ _ _

/-- The Schottky double of a Hausdorff Riemann surface with boundary is Hausdorff. -/
instance instT2Space [T2Space M] : T2Space (SchottkyDouble M) :=
  DoubleAlong.t2Space _ (isClosed_boundary M)

/-- The Schottky double of a second-countable Riemann surface with boundary is second countable. -/
instance instSecondCountableTopology [SecondCountableTopology M] :
    SecondCountableTopology (SchottkyDouble M) :=
  DoubleAlong.secondCountableTopology _ (isClosed_boundary M)

end holomorphic

/-! ### The antiholomorphic involution -/

/-- The sheet swap reads as `z ↦ conj z` in every pair of doubled charts: in charts it is complex
conjugation after a holomorphic chart change, so it is antiholomorphic. -/
theorem doubleChart_swap_doubleChart_symm {e e' : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (he : e ∈ atlas ClosedUpperHalfPlane M) (he' : e' ∈ atlas ClosedUpperHalfPlane M) {w : ℂ}
    (hw : w ∈ ((doubleChart e he).symm.trans (doubleChart e' he')).source) :
    doubleChart e' he' (DoubleAlong.swap _ ((doubleChart e he).symm w)) =
      conj (doubleChart e' he' ((doubleChart e he).symm w)) :=
  doubleChart_swap he' hw.2

/-- The sheet swap is an involution. -/
theorem swap_involutive :
    Function.Involutive (DoubleAlong.swap (borderedInterior M : Set M)ᶜ) :=
  DoubleAlong.swap_swap _

/-- The fixed set of the sheet swap is the boundary of `M`, on the first copy. -/
theorem fixedPoints_swap :
    Function.fixedPoints (DoubleAlong.swap (borderedInterior M : Set M)ᶜ) =
      DoubleAlong.inl _ '' (borderedInterior M : Set M)ᶜ :=
  DoubleAlong.fixed_locus _

/-! ### The first copy of the interior -/

variable (M) in
/-- The inclusion of the interior of `M` in the first copy of the Schottky double. -/
def interiorInl : borderedInterior M → SchottkyDouble M :=
  fun x ↦ DoubleAlong.inl _ (x : M)

@[simp]
theorem interiorInl_apply (x : borderedInterior M) :
    interiorInl M x = DoubleAlong.inl _ (x : M) :=
  (rfl)

/-- The first copy of the interior is an open embedded subset of the double. -/
theorem isOpenEmbedding_interiorInl : IsOpenEmbedding (interiorInl M) := by
  have h := DoubleAlong.isOpenEmbedding_inl_compl _ (isClosed_boundary M)
  have hc : ((borderedInterior M : Set M)ᶜᶜ) = (borderedInterior M : Set M) := compl_compl _
  exact h.comp (Homeomorph.setCongr hc.symm).isOpenEmbedding

/-- In the chart of the interior at `x` and the chart of the double at its image, the inclusion of
the interior in the first copy is the identity near the image of `x`. -/
theorem extChartAt_interiorInl_eventuallyEq_id (x : borderedInterior M) :
    (extChartAt 𝓘(ℂ) (interiorInl M x) ∘ interiorInl M ∘ (extChartAt 𝓘(ℂ) x).symm) =ᶠ[𝓝
      (extChartAt 𝓘(ℂ) x x)] id := by
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp]
  filter_upwards [(chartAt ℂ x).eventually_right_inverse (mem_chart_target ℂ x),
    (chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with w hw hw'
  have hsrc : (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hw'
  simp only [Function.comp_apply, interiorInl_apply, id_eq]
  rw [chartAt_inl, doubleChart_inl, ← chartAt_borderedInterior_apply x, hw]

/-- **The first copy of the interior is holomorphic.** The inclusion of the interior of `M`, with
its complex structure, in the first copy of the Schottky double is holomorphic. -/
theorem contMDiff_interiorInl : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (interiorInl M) := by
  intro x
  refine contMDiffAt_iff.2 ⟨isOpenEmbedding_interiorInl.continuous.continuousAt, ?_⟩
  rw [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
  exact contDiffAt_id.congr_of_eventuallyEq (extChartAt_interiorInl_eventuallyEq_id x)

/-- **The second copy of the interior is antiholomorphic.** In the chart of the interior at `x`
and the chart of the double at the image of `x` on the second copy, the inclusion of the interior
in the second copy is `z ↦ conj z` near the image of `x`. -/
theorem extChartAt_inr_eventuallyEq_conj (x : borderedInterior M) :
    (extChartAt 𝓘(ℂ) (DoubleAlong.inr (borderedInterior M : Set M)ᶜ (x : M)) ∘
        (fun y : borderedInterior M ↦ DoubleAlong.inr _ (y : M)) ∘ (extChartAt 𝓘(ℂ) x).symm)
      =ᶠ[𝓝 (extChartAt 𝓘(ℂ) x x)] fun w ↦ conj w := by
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp]
  filter_upwards [(chartAt ℂ x).eventually_right_inverse (mem_chart_target ℂ x),
    (chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with w hw hw'
  have hsrc : (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hw'
  rw [chartAt_borderedInterior_source] at hsrc
  simp only [Function.comp_apply]
  rw [chartAt_inr, doubleChart_inr _ hsrc,
    ← chartAt_borderedInterior_apply x, hw]

end SchottkyDouble

end TauCeti
