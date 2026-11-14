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
half-plane whose transition maps lie in `TauCeti.borderedHolomorphicGroupoid`. Its *Schottky
double* `TauCeti.SchottkyDouble M` is the topological double `TauCeti.DoubleAlong` of `M` along
its manifold boundary: two copies of `M` glued by the identity along the boundary. This file makes
it a Riemann surface without boundary, with the sheet exchange as an antiholomorphic involution
whose fixed set is the boundary.

A chart `e` of `M` gives the chart `TauCeti.schottkyDoubleChart e` of the double, defined on both
copies of the source of `e`: it is `e` on the first copy and `conj ∘ e` on the second, so the
first copy lands in the closed upper half-plane and the second in the closed lower half-plane. The
two formulas agree on the boundary, which `e` sends to the real axis. The change between the doubled
charts of `e` and `e'` is the Schwarz reflection `TauCeti.ClosedUpperHalfPlane.schwarzDouble` of
the chart change `e.symm ≫ₕ e'` (`TauCeti.schottkyDoubleChart_symm_trans_eqOnSource`), which is
holomorphic with holomorphic inverse by the Schwarz reflection principle. In each doubled chart
the sheet exchange reads as complex conjugation (`TauCeti.schottkyDoubleChart_swap`), so it is
antiholomorphic; its fixed set is the image of the boundary (`TauCeti.DoubleAlong.fixed_locus`).

The gluing is by `z ↦ conj z` in the boundary charts. With `z ↦ -conj z` in its place the
chart changes would not be holomorphic across the real axis
(`TauCeti.ClosedUpperHalfPlane.not_differentiableAt_negConj_glue`).

## Main definitions

* `TauCeti.SchottkyDouble`: the double of `M` along its manifold boundary.
* `TauCeti.schottkyDoubleChart`: the chart of the double induced by a chart of `M`.
* `TauCeti.instChartedSpaceSchottkyDouble`: the charts of the double, modelled on `ℂ`.

## Main results

* `TauCeti.schottkyDoubleChart_symm_trans_eqOnSource`: the chart changes of the double are the
  Schwarz reflections of the chart changes of `M`.
* `TauCeti.hasGroupoid_schottkyDouble` and `TauCeti.isManifold_schottkyDouble`: the double is an
  analytic manifold modelled on `ℂ`, that is, a Riemann surface.
* `TauCeti.schottkyDoubleChart_mem_maximalAtlas`: every doubled chart is a holomorphic chart of the
  double.
* `TauCeti.eqOn_writtenInExtChartAt_schottkyDouble_swap`: in every chart of the double the sheet
  exchange is complex conjugation, so it is an antiholomorphic involution.
* `TauCeti.t2Space_schottkyDouble` and `TauCeti.secondCountableTopology_schottkyDouble`: the double
  of a Hausdorff, respectively second countable, surface is Hausdorff, respectively second
  countable. The double of a compact surface is compact.
* `TauCeti.chartAt_schottkyDouble_closedUpperHalfPlane_source` and
  `TauCeti.chartAt_schottkyDouble_closedUpperHalfPlane_target`: the double of the closed upper
  half-plane is covered by a single chart onto `ℂ`.

## References

* L. V. Ahlfors and L. Sario, *Riemann Surfaces*, Princeton University Press, 1960, Ch. II, the
  double of a bordered Riemann surface.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.
-/

public section

noncomputable section

open Set Complex
open scoped Manifold ContDiff ComplexConjugate

namespace TauCeti

open ClosedUpperHalfPlane

variable (M : Type*) [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]

/-- The **Schottky double** of a manifold `M` modelled on the closed upper half-plane: two copies
of `M` glued by the identity along its manifold boundary. When `M` is a Riemann surface with
boundary, it is a Riemann surface without boundary (`TauCeti.isManifold_schottkyDouble`). -/
abbrev SchottkyDouble : Type _ :=
  DoubleAlong (closedUpperHalfPlaneModel.boundary M)

variable {M} [HasGroupoid M borderedHolomorphicGroupoid]

omit [HasGroupoid M borderedHolomorphicGroupoid] in
/-- Charts of a Riemann surface with boundary are charts of its underlying `C^1` manifold. -/
private theorem mem_maximalAtlas_one {e : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (he : e ∈ borderedHolomorphicGroupoid.maximalAtlas M) :
    e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M :=
  StructureGroupoid.maximalAtlas_mono
    (borderedHolomorphicGroupoid_le_contDiffGroupoid.trans (contDiffGroupoid_le (by simp))) he

/-! ### The doubled chart -/

section DoubledChart

variable {e : OpenPartialHomeomorph M ClosedUpperHalfPlane}

open scoped Classical in
/-- The doubled chart as a function: `e` on the first copy and `conj ∘ e` on the second. -/
private def doubleChartFun (e : OpenPartialHomeomorph M ClosedUpperHalfPlane) :
    SchottkyDouble M → ℂ := fun z ↦
  if z ∈ range (DoubleAlong.inl (closedUpperHalfPlaneModel.boundary M)) then
    (e (DoubleAlong.fold _ z) : ℂ) else conj (e (DoubleAlong.fold _ z) : ℂ)

/-- The inverse of the doubled chart as a function: the first copy over the closed upper
half-plane and the second copy over the open lower half-plane. -/
private def doubleChartInvFun (e : OpenPartialHomeomorph M ClosedUpperHalfPlane) :
    ℂ → SchottkyDouble M := fun w ↦
  if 0 ≤ w.im then DoubleAlong.inl _ (e.symm (fold w)) else DoubleAlong.inr _ (e.symm (fold w))

omit [HasGroupoid M borderedHolomorphicGroupoid] in
private theorem doubleChartFun_inl (x : M) :
    doubleChartFun e (DoubleAlong.inl _ x) = e x := by
  simp [doubleChartFun]

private theorem doubleChartFun_inr (he : e ∈ borderedHolomorphicGroupoid.maximalAtlas M)
    {x : M} (hx : x ∈ e.source) :
    doubleChartFun e (DoubleAlong.inr _ x) = conj (e x : ℂ) := by
  by_cases h : DoubleAlong.inr (closedUpperHalfPlaneModel.boundary M) x ∈
    range (DoubleAlong.inl (closedUpperHalfPlaneModel.boundary M))
  · obtain ⟨y, hy⟩ := h
    obtain ⟨rfl, hb⟩ := (DoubleAlong.inl_eq_inr_iff _).1 hy
    rw [← hy, doubleChartFun_inl, eq_comm, conj_eq_iff_im]
    exact (mem_boundary_iff_im_eq_zero (mem_maximalAtlas_one he) hx).1 hb
  · simp [doubleChartFun, h]

omit [HasGroupoid M borderedHolomorphicGroupoid] in
private theorem fold_doubleChartInvFun (w : ℂ) :
    DoubleAlong.fold _ (doubleChartInvFun e w) = e.symm (fold w) := by
  unfold doubleChartInvFun
  split_ifs <;> simp

omit [HasGroupoid M borderedHolomorphicGroupoid] in
private theorem doubleChartInvFun_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) :
    doubleChartInvFun e w = DoubleAlong.inl _ (e.symm (fold w)) := by
  simp [doubleChartInvFun, hw]

omit [HasGroupoid M borderedHolomorphicGroupoid] in
private theorem doubleChartInvFun_of_im_neg {w : ℂ} (hw : w.im < 0) :
    doubleChartInvFun e w = DoubleAlong.inr _ (e.symm (fold w)) := by
  simp [doubleChartInvFun, not_le.2 hw]

private theorem mapsTo_doubleChartFun (he : e ∈ borderedHolomorphicGroupoid.maximalAtlas M) :
    MapsTo (doubleChartFun e) (DoubleAlong.fold _ ⁻¹' e.source) (fold ⁻¹' e.target) := by
  intro z hz
  induction z using DoubleAlong.induction_on with
  | hl x =>
    simp only [mem_preimage, DoubleAlong.fold_inl] at hz
    simpa [doubleChartFun_inl] using e.map_source hz
  | hr x =>
    simp only [mem_preimage, DoubleAlong.fold_inr] at hz
    simpa [doubleChartFun_inr he hz] using e.map_source hz

private theorem leftInvOn_doubleChartInvFun
    (he : e ∈ borderedHolomorphicGroupoid.maximalAtlas M) :
    LeftInvOn (doubleChartInvFun e) (doubleChartFun e) (DoubleAlong.fold _ ⁻¹' e.source) := by
  intro z hz
  induction z using DoubleAlong.induction_on with
  | hl x =>
    simp only [mem_preimage, DoubleAlong.fold_inl] at hz
    simp [doubleChartFun_inl, doubleChartInvFun, (e x).property, e.left_inv hz]
  | hr x =>
    simp only [mem_preimage, DoubleAlong.fold_inr] at hz
    rw [doubleChartFun_inr he hz, doubleChartInvFun, fold_conj, fold_coe, e.left_inv hz]
    split_ifs with h
    · have h0 : (e x : ℂ).im = 0 := le_antisymm (by simpa using h) (e x).property
      exact (DoubleAlong.inl_eq_inr_iff _).2
        ⟨rfl, (mem_boundary_iff_im_eq_zero (mem_maximalAtlas_one he) hz).2 h0⟩
    · rfl

private theorem rightInvOn_doubleChartInvFun
    (he : e ∈ borderedHolomorphicGroupoid.maximalAtlas M) :
    RightInvOn (doubleChartInvFun e) (doubleChartFun e) (fold ⁻¹' e.target) := by
  intro w hw
  rw [mem_preimage] at hw
  unfold doubleChartInvFun
  split_ifs with h
  · rw [doubleChartFun_inl, e.right_inv hw, coe_fold_of_im_nonneg h]
  · rw [doubleChartFun_inr he (e.map_target hw), e.right_inv hw,
      coe_fold_of_im_nonpos (not_le.1 h).le, conj_conj]

private theorem continuousOn_doubleChartFun
    (he : e ∈ borderedHolomorphicGroupoid.maximalAtlas M) :
    ContinuousOn (doubleChartFun e) (DoubleAlong.fold _ ⁻¹' e.source) := by
  have hc : ContinuousOn (fun x ↦ (e x : ℂ)) e.source :=
    continuous_subtype_val.comp_continuousOn e.continuousOn
  have hl : DoubleAlong.inl (closedUpperHalfPlaneModel.boundary M) ⁻¹'
      (DoubleAlong.fold _ ⁻¹' e.source) = e.source := by
    ext; simp
  have hr : DoubleAlong.inr (closedUpperHalfPlaneModel.boundary M) ⁻¹'
      (DoubleAlong.fold _ ⁻¹' e.source) = e.source := by
    ext; simp
  rw [DoubleAlong.continuousOn_iff_of_isOpen _
    (e.open_source.preimage (DoubleAlong.fold _).continuous), hl, hr]
  exact ⟨hc.congr fun x _ ↦ doubleChartFun_inl x,
    (continuous_conj.comp_continuousOn hc).congr fun x hx ↦ doubleChartFun_inr he hx⟩

private theorem continuousOn_doubleChartInvFun
    (he : e ∈ borderedHolomorphicGroupoid.maximalAtlas M) :
    ContinuousOn (doubleChartInvFun e) (fold ⁻¹' e.target) := by
  have hc : ContinuousOn (fun w ↦ e.symm (fold w)) (fold ⁻¹' e.target) :=
    e.continuousOn_symm.comp continuous_fold.continuousOn fun _ hw ↦ hw
  refine ContinuousOn.if (fun w hw ↦ ?_) ((DoubleAlong.inl _).continuous.comp_continuousOn
    (hc.mono inter_subset_left)) ((DoubleAlong.inr _).continuous.comp_continuousOn
    (hc.mono inter_subset_left))
  -- on the real axis the two copies are glued, since `e.symm` sends it to the boundary
  rw [frontier_setOfPred_le_im] at hw
  obtain ⟨hw, hw0⟩ := hw
  rw [mem_preimage] at hw
  refine (DoubleAlong.inl_eq_inr_iff _).2 ⟨rfl, ?_⟩
  rw [mem_boundary_iff_im_eq_zero (mem_maximalAtlas_one he) (e.map_target hw), e.right_inv hw,
    im_fold, hw0, abs_zero]

end DoubledChart

variable {e e' : OpenPartialHomeomorph M ClosedUpperHalfPlane}

/-- The chart of the Schottky double induced by a bordered holomorphic chart `e` of `M`. It is
defined on both copies of the source of `e`, and it is `e` on the first copy
(`TauCeti.schottkyDoubleChart_inl`) and `conj ∘ e` on the second
(`TauCeti.schottkyDoubleChart_inr`). -/
def schottkyDoubleChart (e : OpenPartialHomeomorph M ClosedUpperHalfPlane)
    (he : e ∈ borderedHolomorphicGroupoid.maximalAtlas M) :
    OpenPartialHomeomorph (SchottkyDouble M) ℂ where
  toFun := doubleChartFun e
  invFun := doubleChartInvFun e
  source := DoubleAlong.fold _ ⁻¹' e.source
  target := fold ⁻¹' e.target
  map_source' := mapsTo_doubleChartFun he
  map_target' w hw := by
    simpa only [mem_preimage, fold_doubleChartInvFun] using e.map_target hw
  left_inv' := leftInvOn_doubleChartInvFun he
  right_inv' := rightInvOn_doubleChartInvFun he
  open_source := e.open_source.preimage (DoubleAlong.fold _).continuous
  open_target := e.open_target.preimage continuous_fold
  continuousOn_toFun := continuousOn_doubleChartFun he
  continuousOn_invFun := continuousOn_doubleChartInvFun he

variable (he : e ∈ borderedHolomorphicGroupoid.maximalAtlas M)
  (he' : e' ∈ borderedHolomorphicGroupoid.maximalAtlas M)

@[simp]
theorem schottkyDoubleChart_source :
    (schottkyDoubleChart e he).source =
      DoubleAlong.fold (closedUpperHalfPlaneModel.boundary M) ⁻¹' e.source :=
  (rfl)

@[simp]
theorem schottkyDoubleChart_target : (schottkyDoubleChart e he).target = fold ⁻¹' e.target :=
  (rfl)

/-- On the first copy, the doubled chart is the chart of `M`. -/
@[simp]
theorem schottkyDoubleChart_inl (x : M) : schottkyDoubleChart e he (DoubleAlong.inl _ x) = e x :=
  doubleChartFun_inl x

/-- On the second copy, the doubled chart is the complex conjugate of the chart of `M`. -/
@[simp]
theorem schottkyDoubleChart_inr {x : M} (hx : x ∈ e.source) :
    schottkyDoubleChart e he (DoubleAlong.inr _ x) = conj (e x : ℂ) :=
  doubleChartFun_inr he hx

/-- Over the closed upper half-plane, the inverse of the doubled chart lands in the first copy. -/
theorem schottkyDoubleChart_symm_apply_of_im_nonneg {w : ℂ} (hw : 0 ≤ w.im) :
    (schottkyDoubleChart e he).symm w = DoubleAlong.inl _ (e.symm (fold w)) :=
  doubleChartInvFun_of_im_nonneg hw

/-- Over the open lower half-plane, the inverse of the doubled chart lands in the second copy. -/
theorem schottkyDoubleChart_symm_apply_of_im_neg {w : ℂ} (hw : w.im < 0) :
    (schottkyDoubleChart e he).symm w = DoubleAlong.inr _ (e.symm (fold w)) :=
  doubleChartInvFun_of_im_neg hw

/-- Folding the inverse of the doubled chart is the inverse of the chart of `M` after folding. -/
@[simp]
theorem fold_schottkyDoubleChart_symm (w : ℂ) :
    DoubleAlong.fold _ ((schottkyDoubleChart e he).symm w) = e.symm (fold w) :=
  fold_doubleChartInvFun w

/-- **The doubled chart turns the sheet exchange into complex conjugation.** -/
theorem schottkyDoubleChart_swap {z : SchottkyDouble M}
    (hz : z ∈ (schottkyDoubleChart e he).source) :
    schottkyDoubleChart e he (DoubleAlong.swap _ z) = conj (schottkyDoubleChart e he z) := by
  induction z using DoubleAlong.induction_on with
  | hl x =>
    simp only [schottkyDoubleChart_source, mem_preimage, DoubleAlong.fold_inl] at hz
    rw [DoubleAlong.swap_inl, schottkyDoubleChart_inr he hz, schottkyDoubleChart_inl]
  | hr x =>
    simp only [schottkyDoubleChart_source, mem_preimage, DoubleAlong.fold_inr] at hz
    rw [DoubleAlong.swap_inr, schottkyDoubleChart_inl, schottkyDoubleChart_inr he hz, conj_conj]

/-- **Chart changes of the double.** The change between the doubled charts of `e` and `e'` is the
Schwarz reflection of the chart change `e.symm ≫ₕ e'` of `M`, on the same source. -/
theorem schottkyDoubleChart_symm_trans_eqOnSource :
    (schottkyDoubleChart e he).symm ≫ₕ schottkyDoubleChart e' he' ≈
      schwarzDouble (e.symm ≫ₕ e') (preservesRealAxis_of_mem_borderedHolomorphicGroupoid
        (borderedHolomorphicGroupoid.compatible_of_mem_maximalAtlas he he')) := by
  refine ⟨?_, fun w hw ↦ ?_⟩
  · ext w
    simp
  · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      schottkyDoubleChart_target, schottkyDoubleChart_source, mem_inter_iff, mem_preimage,
      fold_schottkyDoubleChart_symm] at hw
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    rcases le_or_gt 0 w.im with h | h
    · rw [schottkyDoubleChart_symm_apply_of_im_nonneg he h, schottkyDoubleChart_inl,
        schwarzDouble_apply_of_im_nonneg _ h, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
    · rw [schottkyDoubleChart_symm_apply_of_im_neg he h, schottkyDoubleChart_inr he' hw.2,
        schwarzDouble_apply_of_im_neg _ h, OpenPartialHomeomorph.coe_trans, Function.comp_apply]

/-- The doubled chart changes are holomorphic with holomorphic inverse. -/
theorem schottkyDoubleChart_symm_trans_mem_contDiffGroupoid :
    (schottkyDoubleChart e he).symm ≫ₕ schottkyDoubleChart e' he' ∈ contDiffGroupoid ω 𝓘(ℂ) :=
  (contDiffGroupoid ω 𝓘(ℂ)).mem_of_eqOnSource
    (schwarzDouble_mem_contDiffGroupoid _
      (borderedHolomorphicGroupoid.compatible_of_mem_maximalAtlas he he'))
    (schottkyDoubleChart_symm_trans_eqOnSource he he')

/-! ### The Schottky double as a Riemann surface -/

/-- The Schottky double of a Riemann surface with boundary is a charted space modelled on `ℂ`:
the chart at `z` is the doubled chart of the chart of `M` at the fold of `z`. -/
instance instChartedSpaceSchottkyDouble : ChartedSpace ℂ (SchottkyDouble M) where
  atlas := range fun z : SchottkyDouble M ↦ schottkyDoubleChart (chartAt ClosedUpperHalfPlane
    (DoubleAlong.fold _ z)) (borderedHolomorphicGroupoid.chart_mem_maximalAtlas _)
  chartAt z := schottkyDoubleChart (chartAt ClosedUpperHalfPlane (DoubleAlong.fold _ z))
    (borderedHolomorphicGroupoid.chart_mem_maximalAtlas _)
  mem_chart_source z := by
    rw [schottkyDoubleChart_source]
    exact mem_chart_source ClosedUpperHalfPlane (DoubleAlong.fold _ z)
  chart_mem_atlas z := mem_range_self z

/-- The chart of the double at `z` is the doubled chart of the chart of `M` at the fold of `z`. -/
theorem chartAt_schottkyDouble (z : SchottkyDouble M) :
    chartAt ℂ z = schottkyDoubleChart (chartAt ClosedUpperHalfPlane (DoubleAlong.fold _ z))
      (borderedHolomorphicGroupoid.chart_mem_maximalAtlas _) :=
  rfl

/-- The sheet exchange of the double does not change the chart. -/
@[simp]
theorem chartAt_schottkyDouble_swap (z : SchottkyDouble M) :
    chartAt ℂ (DoubleAlong.swap _ z) = chartAt ℂ z := by
  simp only [chartAt_schottkyDouble, DoubleAlong.fold_swap]

/-- The Schottky double of a Riemann surface with boundary has holomorphic transition maps. -/
instance hasGroupoid_schottkyDouble :
    HasGroupoid (SchottkyDouble M) (contDiffGroupoid ω 𝓘(ℂ)) where
  compatible := by
    rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
    exact schottkyDoubleChart_symm_trans_mem_contDiffGroupoid _ _

/-- **The Schottky double of a Riemann surface with boundary is a Riemann surface.** -/
instance isManifold_schottkyDouble : IsManifold 𝓘(ℂ) ω (SchottkyDouble M) :=
  IsManifold.mk' _ _ _

/-- The doubled chart of a bordered holomorphic chart of `M` is a holomorphic chart of the
double. -/
theorem schottkyDoubleChart_mem_maximalAtlas :
    schottkyDoubleChart e he ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω (SchottkyDouble M) := by
  refine mem_maximalAtlas_iff.2 ?_
  rintro _ ⟨z, rfl⟩
  exact ⟨schottkyDoubleChart_symm_trans_mem_contDiffGroupoid _ _,
    schottkyDoubleChart_symm_trans_mem_contDiffGroupoid _ _⟩

/-- In the chart of the double at `z`, the sheet exchange is complex conjugation. -/
theorem chartAt_schottkyDouble_swap_apply (z : SchottkyDouble M) {z' : SchottkyDouble M}
    (hz' : z' ∈ (chartAt ℂ z).source) :
    chartAt ℂ z (DoubleAlong.swap _ z') = conj (chartAt ℂ z z') :=
  schottkyDoubleChart_swap _ hz'

/-- **The sheet exchange is antiholomorphic.** In every chart of the double, it is complex
conjugation. -/
theorem eqOn_writtenInExtChartAt_schottkyDouble_swap (z : SchottkyDouble M) :
    EqOn (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) z (DoubleAlong.swap _)) (starRingEnd ℂ)
      (extChartAt 𝓘(ℂ) z).target := by
  intro w hw
  simp only [extChartAt_target, modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe,
    preimage_id_eq, id_eq, range_id, inter_univ] at hw
  simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq, chartAt_schottkyDouble_swap]
  rw [chartAt_schottkyDouble_swap_apply z ((chartAt ℂ z).map_target hw), (chartAt ℂ z).right_inv hw]

/-! ### Separation -/

/-- The Schottky double of a Hausdorff Riemann surface with boundary is Hausdorff. -/
instance t2Space_schottkyDouble [T2Space M] : T2Space (SchottkyDouble M) :=
  DoubleAlong.t2Space _ (closedUpperHalfPlaneModel.isClosed_boundary (M := M) (n := 1) one_ne_zero)

/-- The Schottky double of a second countable Riemann surface with boundary is second
countable. -/
instance secondCountableTopology_schottkyDouble [SecondCountableTopology M] :
    SecondCountableTopology (SchottkyDouble M) :=
  DoubleAlong.secondCountableTopology _
    (closedUpperHalfPlaneModel.isClosed_boundary (M := M) (n := 1) one_ne_zero)

/-! ### Check: the double of the closed upper half-plane -/

/-- The chart of the double of the closed upper half-plane is defined everywhere. -/
theorem chartAt_schottkyDouble_closedUpperHalfPlane_source
    (z : SchottkyDouble ClosedUpperHalfPlane) : (chartAt ℂ z).source = univ := by
  simp [chartAt_schottkyDouble]

/-- The chart of the double of the closed upper half-plane is onto `ℂ`: doubling the closed
upper half-plane along the real axis gives the plane. -/
theorem chartAt_schottkyDouble_closedUpperHalfPlane_target
    (z : SchottkyDouble ClosedUpperHalfPlane) : (chartAt ℂ z).target = univ := by
  simp [chartAt_schottkyDouble]

end TauCeti
