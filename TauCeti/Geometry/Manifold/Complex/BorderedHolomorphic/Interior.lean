/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Basic

/-!
# The interior of a Riemann surface with boundary

Let `M` be a `C^1` manifold modelled on the closed upper half-plane. Its manifold interior
`TauCeti.borderedInterior M` is open. Restricting the charts of `M` to the interior and reading
them in `ℂ` through the open upper half-plane makes the interior a charted space modelled on `ℂ`.
When `M` is a Riemann surface with boundary, that is, its transition maps lie in
`TauCeti.borderedHolomorphicGroupoid`, these charts have holomorphic transition maps, so the
interior is a Riemann surface without boundary.

The chart of the interior at `x` is the restriction of the chart of `M` at `x`, followed by
`TauCeti.ClosedUpperHalfPlane.upperHalfPlaneChart`, the inclusion of the points of positive
imaginary part into `ℂ`. A bordered holomorphic chart change conjugated by this inclusion is
complex differentiable on an open subset of `ℂ`, hence analytic.

The interior also carries the open-subset structure of `M`, modelled on the closed upper
half-plane. The two structures have the same underlying real smooth structure: the identity is a
diffeomorphism between them (`TauCeti.borderedInteriorDiffeomorph`).

## Main definitions

* `TauCeti.borderedInterior`: the manifold interior of a `C^1` manifold modelled on the closed
  upper half-plane, as an open subset.
* `TauCeti.instChartedSpaceBorderedInterior`: its charts modelled on `ℂ`.
* `TauCeti.borderedInteriorDiffeomorph`: the identity, from the complex charts read over `ℝ` to
  the open-subset structure.

## Main results

* `TauCeti.ClosedUpperHalfPlane.upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid`: bordered
  holomorphic chart changes read in `ℂ` are analytic.
* `TauCeti.hasGroupoid_borderedInterior` and `TauCeti.isManifold_borderedInterior`: the interior
  of a Riemann surface with boundary is an analytic manifold modelled on `ℂ`.
* `TauCeti.mem_borderedInterior_iff_im_pos`: a point is in the interior exactly when one, or any,
  chart of the maximal atlas sends it to a point of positive imaginary part.
* `TauCeti.subtypeRestr_trans_upperHalfPlaneChart_mem_maximalAtlas`: a bordered holomorphic chart
  of a Riemann surface with boundary, restricted to the interior and read in `ℂ`, is a holomorphic
  chart of the interior. Its image and inverse are
  `TauCeti.subtypeRestr_trans_upperHalfPlaneChart_target` and
  `TauCeti.subtypeRestr_trans_upperHalfPlaneChart_symm_apply`.
* `TauCeti.chartAt_borderedInterior_source`, `TauCeti.chartAt_borderedInterior_target` and
  `TauCeti.chartAt_borderedInterior_symm_apply`: the domain, image and inverse of the chart of the
  interior, in terms of the chart of `M`.
* `TauCeti.ClosedUpperHalfPlane.chartAt_borderedInterior_source_eq_univ` and
  `TauCeti.ClosedUpperHalfPlane.chartAt_borderedInterior_target_eq`: the interior of the closed
  upper half-plane is the open upper half-plane, with the inclusion into `ℂ` as chart.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 2.4 and Appendix C.
-/

public section

noncomputable section

open Set Complex Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace ClosedUpperHalfPlane

/-- A bordered holomorphic chart change, read in `ℂ` through the open upper half-plane, is
complex differentiable on its source, hence analytic there. -/
private theorem contDiffOn_upperHalfPlaneChart_conj
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (he : e ∈ borderedHolomorphicGroupoid) :
    ContDiffOn ℂ ω (upperHalfPlaneChart.symm ≫ₕ e ≫ₕ upperHalfPlaneChart)
      (upperHalfPlaneChart.symm ≫ₕ e ≫ₕ upperHalfPlaneChart).source := by
  have hd := (mem_borderedHolomorphicGroupoid_iff.1 he).2.1
  refine DifferentiableOn.contDiffOn ?_ (OpenPartialHomeomorph.open_source _)
  refine (hd.mono fun z hz ↦ ?_).congr fun z _ ↦ ?_
  · simp only [mfld_simps] at hz
    exact ⟨hz.2.1, hz.1⟩
  · simp

/-- Bordered holomorphic chart changes, read in `ℂ` through the open upper half-plane, are
analytic. -/
theorem upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (he : e ∈ borderedHolomorphicGroupoid) :
    upperHalfPlaneChart.symm ≫ₕ e ≫ₕ upperHalfPlaneChart ∈ contDiffGroupoid ω 𝓘(ℂ) :=
  upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid_of_contDiffOn
    (contDiffOn_upperHalfPlaneChart_conj he)
    (contDiffOn_upperHalfPlaneChart_conj (borderedHolomorphicGroupoid.symm he))

end ClosedUpperHalfPlane

open ClosedUpperHalfPlane

variable (M : Type*) [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M]

/-- The manifold interior of a `C^1` manifold modelled on the closed upper half-plane, such as a
Riemann surface with boundary, as an open subset. -/
def borderedInterior : Opens M :=
  ⟨closedUpperHalfPlaneModel.interior M, closedUpperHalfPlaneModel.isOpen_interior one_ne_zero⟩

variable {M}

/-- The points of `borderedInterior M` are the manifold interior points of `M`. -/
theorem mem_borderedInterior {x : M} :
    x ∈ borderedInterior M ↔ closedUpperHalfPlaneModel.IsInteriorPoint x :=
  Iff.rfl

/-- A point is in the interior exactly when its preferred chart sends it to a point of positive
imaginary part. -/
theorem mem_borderedInterior_iff_im_chartAt_pos {x : M} :
    x ∈ borderedInterior M ↔ 0 < (chartAt ClosedUpperHalfPlane x x : ℂ).im := by
  rw [mem_borderedInterior, ModelWithCorners.IsInteriorPoint, range_closedUpperHalfPlaneModel,
    Complex.interior_setOfPred_le_im]
  simp [extChartAt]

/-- A point in the source of a chart of the maximal atlas is in the interior exactly when the
chart sends it to a point of positive imaginary part. -/
theorem mem_borderedInterior_iff_im_pos {e : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M) {x : M}
    (hx : x ∈ e.source) :
    x ∈ borderedInterior M ↔ 0 < (e x : ℂ).im := by
  rw [mem_borderedInterior_iff_im_chartAt_pos]
  have hc := (he _ (chart_mem_atlas ClosedUpperHalfPlane x)).2
  simpa [hx] using im_pos_iff_of_mem_contDiffGroupoid hc one_ne_zero
    (z := chartAt ClosedUpperHalfPlane x x) (by simp [hx])

/-- The interior of a `C^1` manifold modelled on the closed upper half-plane is a charted space
modelled on `ℂ`: the chart at `x` restricts the chart of `M` at `x` to the interior and reads it
in `ℂ`. -/
instance instChartedSpaceBorderedInterior : ChartedSpace ℂ (borderedInterior M) where
  atlas := range fun x : borderedInterior M ↦
    (chartAt ClosedUpperHalfPlane x).trans upperHalfPlaneChart
  chartAt x := (chartAt ClosedUpperHalfPlane x).trans upperHalfPlaneChart
  mem_chart_source x := by
    refine ⟨mem_chart_source _ x, ?_⟩
    simpa [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe] using
      mem_borderedInterior_iff_im_chartAt_pos.1 x.2
  chart_mem_atlas x := mem_range_self x

/-- The chart of the interior at `x` is the open-subset chart at `x` read in `ℂ`. -/
theorem chartAt_borderedInterior (x : borderedInterior M) :
    chartAt ℂ x = (chartAt ClosedUpperHalfPlane x).trans upperHalfPlaneChart :=
  rfl

/-- The chart of the interior at `x` evaluates as the chart of `M` at `x`. -/
@[simp]
theorem chartAt_borderedInterior_apply (x y : borderedInterior M) :
    chartAt ℂ x y = (chartAt ClosedUpperHalfPlane (x : M) y : ℂ) := by
  simp [chartAt_borderedInterior, Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe]

/-- The chart of the interior at `x` is defined on the whole intersection of the interior with the
source of the chart of `M` at `x`. -/
@[simp]
theorem chartAt_borderedInterior_source (x : borderedInterior M) :
    (chartAt ℂ x).source = (↑) ⁻¹' (chartAt ClosedUpperHalfPlane (x : M)).source := by
  ext y
  simp only [chartAt_borderedInterior, OpenPartialHomeomorph.trans_source, mem_inter_iff,
    mem_preimage, TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
    upperHalfPlaneChart_source, mem_ofPred_eq]
  refine ⟨And.left, fun hy ↦ ⟨hy, ?_⟩⟩
  exact (mem_borderedInterior_iff_im_pos (IsManifold.chart_mem_maximalAtlas _) hy).1 y.2

/-- The restriction of a chart `e` of the maximal atlas of `M` to the interior, read in `ℂ`, takes
values in the points of positive imaginary part whose model inverse lies in the target of `e`. -/
theorem subtypeRestr_trans_upperHalfPlaneChart_target
    {e : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (he : e ∈ IsManifold.maximalAtlas closedUpperHalfPlaneModel 1 M)
    (hs : Nonempty (borderedInterior M)) :
    (e.subtypeRestr hs ≫ₕ upperHalfPlaneChart).target =
      closedUpperHalfPlaneModel.symm ⁻¹' e.target ∩ {z : ℂ | 0 < z.im} := by
  ext z
  simp only [OpenPartialHomeomorph.subtypeRestr_def, upperHalfPlaneChart_target,
    upperHalfPlaneChart_symm_apply, mfld_simps]
  refine ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, ?_⟩⟩
  refine (mem_borderedInterior_iff_im_pos he (e.map_target h.1)).2 ?_
  rw [e.right_inv h.1, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg h.2.le]
  exact h.2

/-- The inverse of the restriction of a chart `e` of `M` to the interior, read in `ℂ`, is the
inverse of `e` after the model inverse. -/
theorem subtypeRestr_trans_upperHalfPlaneChart_symm_apply
    {e : OpenPartialHomeomorph M ClosedUpperHalfPlane} {hs : Nonempty (borderedInterior M)}
    {z : ℂ} (hz : z ∈ (e.subtypeRestr hs ≫ₕ upperHalfPlaneChart).target) :
    (((e.subtypeRestr hs ≫ₕ upperHalfPlaneChart).symm z : borderedInterior M) : M) =
      e.symm (closedUpperHalfPlaneModel.symm z) := by
  rw [OpenPartialHomeomorph.trans_target, mem_inter_iff, mem_preimage,
    upperHalfPlaneChart_symm_apply] at hz
  rw [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply, upperHalfPlaneChart_symm_apply]
  exact e.subtypeRestr_symm_apply _ hz.2

/-- The chart of the interior at `x` takes values in the points of positive imaginary part whose
model inverse lies in the target of the chart of `M` at `x`. -/
@[simp]
theorem chartAt_borderedInterior_target (x : borderedInterior M) :
    (chartAt ℂ x).target = closedUpperHalfPlaneModel.symm ⁻¹'
      (chartAt ClosedUpperHalfPlane (x : M)).target ∩ {z : ℂ | 0 < z.im} := by
  rw [chartAt_borderedInterior, Opens.chartAt_eq]
  exact subtypeRestr_trans_upperHalfPlaneChart_target (IsManifold.chart_mem_maximalAtlas _) _

/-- The inverse of the chart of the interior at `x` is the inverse of the chart of `M` at `x`
after the model inverse. -/
theorem chartAt_borderedInterior_symm_apply (x : borderedInterior M) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    ((chartAt ℂ x).symm z : M) =
      (chartAt ClosedUpperHalfPlane (x : M)).symm (closedUpperHalfPlaneModel.symm z) := by
  rw [chartAt_borderedInterior, Opens.chartAt_eq] at hz ⊢
  exact subtypeRestr_trans_upperHalfPlaneChart_symm_apply hz

/-- The interior of a Riemann surface with boundary has holomorphic transition maps. -/
instance hasGroupoid_borderedInterior [HasGroupoid M borderedHolomorphicGroupoid] :
    HasGroupoid (borderedInterior M) (contDiffGroupoid ω 𝓘(ℂ)) where
  compatible := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    have h := (borderedHolomorphicGroupoid).compatible
      (chart_mem_atlas ClosedUpperHalfPlane x) (chart_mem_atlas ClosedUpperHalfPlane y)
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid h

/-- The interior of a Riemann surface with boundary is a Riemann surface without boundary. -/
instance isManifold_borderedInterior [HasGroupoid M borderedHolomorphicGroupoid] :
    IsManifold 𝓘(ℂ) ω (borderedInterior M) :=
  IsManifold.mk' _ _ _

/-- The restriction of a bordered holomorphic chart of `M` to the interior, read in `ℂ` through
the open upper half-plane, is a holomorphic chart of the interior. -/
theorem subtypeRestr_trans_upperHalfPlaneChart_mem_maximalAtlas
    {e : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (he : e ∈ borderedHolomorphicGroupoid.maximalAtlas M) (hs : Nonempty (borderedInterior M)) :
    e.subtypeRestr hs ≫ₕ upperHalfPlaneChart ∈
      IsManifold.maximalAtlas 𝓘(ℂ) 1 (borderedInterior M) := by
  have key : ∀ x : borderedInterior M,
      (e.subtypeRestr hs).symm ≫ₕ chartAt ClosedUpperHalfPlane x ∈ borderedHolomorphicGroupoid ∧
        (chartAt ClosedUpperHalfPlane x).symm ≫ₕ e.subtypeRestr hs ∈
          borderedHolomorphicGroupoid := fun x ↦
    ⟨borderedHolomorphicGroupoid.mem_of_eqOnSource (closedUnderRestriction'
        (he _ (chart_mem_atlas _ (x : M))).1
          (e.isOpen_inter_preimage_symm (borderedInterior M).2))
        (e.subtypeRestr_symm_trans_subtypeRestr hs _),
      borderedHolomorphicGroupoid.mem_of_eqOnSource (closedUnderRestriction'
        (he _ (chart_mem_atlas _ (x : M))).2
          ((chartAt ClosedUpperHalfPlane (x : M)).isOpen_inter_preimage_symm
            (borderedInterior M).2))
        ((chartAt ClosedUpperHalfPlane (x : M)).subtypeRestr_symm_trans_subtypeRestr hs e)⟩
  rintro _ ⟨x, rfl⟩
  have h₁ := upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid (key x).1
  have h₂ := upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid (key x).2
  simp only [OpenPartialHomeomorph.trans_assoc] at h₁ h₂
  simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc]
  exact ⟨contDiffGroupoid_le (by exact_mod_cast le_top) h₁,
    contDiffGroupoid_le (by exact_mod_cast le_top) h₂⟩

/-- The extended chart of the open-subset structure of the interior at `y` evaluates as the
chart of the interior at `y`. -/
theorem extChartAt_borderedInterior_apply (x y : borderedInterior M) :
    extChartAt closedUpperHalfPlaneModel y x = chartAt ℂ y x := by
  rw [extChartAt_coe, Function.comp_apply, closedUpperHalfPlaneModel_apply,
    chartAt_borderedInterior_apply]
  simp [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe]

/-- The inverse of the extended chart of the open-subset structure of the interior at `y` is the
inverse of the chart of the interior at `y`. -/
theorem extChartAt_borderedInterior_symm_apply (y : borderedInterior M) (z : ℂ) :
    (extChartAt closedUpperHalfPlaneModel y).symm z = (chartAt ℂ y).symm z := by
  rw [extChartAt_coe_symm, chartAt_borderedInterior, OpenPartialHomeomorph.coe_trans_symm,
    Function.comp_apply, Function.comp_apply, upperHalfPlaneChart_symm_apply]

/-- The identity is a diffeomorphism from the interior with its complex charts, read over `ℝ`, to
the interior with the open-subset structure of `M`. So the complex structure on the interior
induces the real smooth structure of `M`. -/
def borderedInteriorDiffeomorph (n : ℕ∞ω) :
    Diffeomorph 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel (borderedInterior M) (borderedInterior M) n
    where
  toEquiv := Equiv.refl _
  contMDiff_toFun x := by
    refine contMDiffAt_iff.2 ⟨continuousAt_id,
      contDiffWithinAt_id.congr_of_eventuallyEq_of_mem ?_ (mem_range_self _)⟩
    filter_upwards [nhdsWithin_le_nhds
      ((chartAt ℂ x).eventually_right_inverse (mem_chart_target ℂ x))] with z hz
    simpa only [Function.comp_apply, Equiv.coe_refl, id_eq, extChartAt_coe_symm,
      modelWithCornersSelf_coe_symm, extChartAt_borderedInterior_apply] using hz
  contMDiff_invFun x := by
    refine contMDiffAt_iff.2 ⟨continuousAt_id,
      contDiffWithinAt_id.congr_of_eventuallyEq_of_mem ?_ (mem_range_self _)⟩
    rw [extChartAt_borderedInterior_apply]
    filter_upwards [nhdsWithin_le_nhds
      ((chartAt ℂ x).eventually_right_inverse (mem_chart_target ℂ x))] with z hz
    simpa only [Function.comp_apply, Equiv.refl_symm, Equiv.coe_refl, id_eq, extChartAt_coe,
      modelWithCornersSelf_coe, extChartAt_borderedInterior_symm_apply] using hz

/-- `borderedInteriorDiffeomorph` is the identity. -/
@[simp]
theorem coe_borderedInteriorDiffeomorph (n : ℕ∞ω) :
    ⇑(borderedInteriorDiffeomorph (M := M) n) = id := by
  rw [borderedInteriorDiffeomorph]
  rfl

/-- The inverse of `borderedInteriorDiffeomorph` is the identity. -/
@[simp]
theorem coe_borderedInteriorDiffeomorph_symm (n : ℕ∞ω) :
    ⇑(borderedInteriorDiffeomorph (M := M) n).symm = id := by
  rw [borderedInteriorDiffeomorph]
  rfl

/-! ### The closed upper half-plane -/

namespace ClosedUpperHalfPlane

/-- The interior of the closed upper half-plane consists of the points of positive imaginary
part. -/
theorem mem_borderedInterior_iff {z : ClosedUpperHalfPlane} :
    z ∈ borderedInterior ClosedUpperHalfPlane ↔ 0 < (z : ℂ).im :=
  closedUpperHalfPlaneModel_isInteriorPoint_iff z

/-- The chart of the interior of the closed upper half-plane is the inclusion into `ℂ`. -/
theorem chartAt_borderedInterior_eq_coe (x y : borderedInterior ClosedUpperHalfPlane) :
    chartAt ℂ x y = ((y : ClosedUpperHalfPlane) : ℂ) := by
  simp

/-- The chart of the interior of the closed upper half-plane is defined everywhere. -/
theorem chartAt_borderedInterior_source_eq_univ (x : borderedInterior ClosedUpperHalfPlane) :
    (chartAt ℂ x).source = univ := by
  simp

/-- The chart of the interior of the closed upper half-plane takes values in the whole open upper
half-plane. -/
theorem chartAt_borderedInterior_target_eq (x : borderedInterior ClosedUpperHalfPlane) :
    (chartAt ℂ x).target = {z : ℂ | 0 < z.im} := by
  simp

end ClosedUpperHalfPlane

end TauCeti
