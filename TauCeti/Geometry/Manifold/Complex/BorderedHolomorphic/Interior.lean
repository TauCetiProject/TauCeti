/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic

/-!
# The interior of a Riemann surface with boundary

Let `M` be a Riemann surface with boundary: a charted space modelled on the closed upper
half-plane whose transition maps lie in `TauCeti.borderedHolomorphicGroupoid`. Its manifold
interior `TauCeti.borderedInterior M` is open. Restricting the charts of `M` to the interior and
reading them in `ℂ` through the open upper half-plane makes the interior a charted space modelled
on `ℂ` with holomorphic transition maps, that is, a Riemann surface without boundary.

The chart of the interior at `x` is the restriction of the chart of `M` at `x`, followed by
`TauCeti.ClosedUpperHalfPlane.upperHalfPlaneChart`, the inclusion of the points of positive
imaginary part into `ℂ`. A bordered holomorphic chart change conjugated by this inclusion is
complex differentiable on an open subset of `ℂ`, hence analytic.

The interior also carries the open-subset structure of `M`, modelled on the closed upper
half-plane. The two structures have the same underlying real smooth structure: the identity is a
diffeomorphism between them (`TauCeti.borderedInteriorDiffeomorph`).

## Main definitions

* `TauCeti.ClosedUpperHalfPlane.upperHalfPlaneChart`: the inclusion of the open upper half-plane
  into `ℂ`, as an open partial homeomorphism from the closed upper half-plane.
* `TauCeti.borderedInterior`: the manifold interior of a Riemann surface with boundary, as an open
  subset.
* `TauCeti.instChartedSpaceBorderedInterior`: its charts modelled on `ℂ`.
* `TauCeti.borderedInteriorDiffeomorph`: the identity, from the complex charts read over `ℝ` to
  the open-subset structure.

## Main results

* `TauCeti.ClosedUpperHalfPlane.upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid`: bordered
  holomorphic chart changes read in `ℂ` are analytic.
* `TauCeti.hasGroupoid_borderedInterior` and `TauCeti.isManifold_borderedInterior`: the interior
  is an analytic manifold modelled on `ℂ`.
* `TauCeti.mem_borderedInterior_iff_im_pos`: a point is in the interior exactly when one, or any,
  chart of the atlas sends it to a point of positive imaginary part.
* `TauCeti.ClosedUpperHalfPlane.chartAt_borderedInterior_source_eq_univ` and
  `TauCeti.ClosedUpperHalfPlane.chartAt_borderedInterior_target_eq`: the interior of the closed
  upper half-plane is the open upper half-plane with the identity chart.

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

/-- The inclusion of the open upper half-plane into `ℂ`, as an open partial homeomorphism from the
closed upper half-plane. Its source is the set of points of positive imaginary part, and its
inverse is the model inverse `closedUpperHalfPlaneModel.symm`. -/
-- The exported evaluation, source and target equalities require this body under Lean's module
-- system.
@[expose] def upperHalfPlaneChart : OpenPartialHomeomorph ClosedUpperHalfPlane ℂ where
  toFun := Subtype.val
  invFun := closedUpperHalfPlaneModel.symm
  source := {z | 0 < (z : ℂ).im}
  target := {z | 0 < z.im}
  map_source' {_} hz := hz
  map_target' {z} hz := by
    simpa only [mem_ofPred_eq, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (le_of_lt hz)]
      using hz
  left_inv' z _ := closedUpperHalfPlaneModel_symm_coe z
  right_inv' _ hz := coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (le_of_lt hz)
  open_source := isOpen_lt continuous_const (continuous_im.comp continuous_subtype_val)
  open_target := isOpen_lt continuous_const continuous_im
  continuousOn_toFun := continuous_subtype_val.continuousOn
  continuousOn_invFun := closedUpperHalfPlaneModel.continuous_symm.continuousOn

/-- `upperHalfPlaneChart` is the inclusion into `ℂ`. -/
@[simp, mfld_simps]
theorem upperHalfPlaneChart_apply (z : ClosedUpperHalfPlane) : upperHalfPlaneChart z = z :=
  rfl

/-- The inverse of `upperHalfPlaneChart` is the model inverse. -/
@[simp, mfld_simps]
theorem upperHalfPlaneChart_symm_apply (z : ℂ) :
    upperHalfPlaneChart.symm z = closedUpperHalfPlaneModel.symm z :=
  rfl

/-- `upperHalfPlaneChart` is defined at the points of positive imaginary part. -/
@[simp, mfld_simps]
theorem upperHalfPlaneChart_source :
    upperHalfPlaneChart.source = {z : ClosedUpperHalfPlane | 0 < (z : ℂ).im} :=
  rfl

/-- `upperHalfPlaneChart` takes values in the open upper half-plane. -/
@[simp, mfld_simps]
theorem upperHalfPlaneChart_target : upperHalfPlaneChart.target = {z : ℂ | 0 < z.im} :=
  rfl

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
    upperHalfPlaneChart.symm ≫ₕ e ≫ₕ upperHalfPlaneChart ∈ contDiffGroupoid ω 𝓘(ℂ) := by
  have hsymm : (upperHalfPlaneChart.symm ≫ₕ e ≫ₕ upperHalfPlaneChart).symm =
      upperHalfPlaneChart.symm ≫ₕ e.symm ≫ₕ upperHalfPlaneChart := by
    simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, hsymm]
  constructor
  · simpa [contDiffPregroupoid, inter_assoc] using contDiffOn_upperHalfPlaneChart_conj he
  · simpa [contDiffPregroupoid, inter_assoc] using
      contDiffOn_upperHalfPlaneChart_conj (borderedHolomorphicGroupoid.symm he)

end ClosedUpperHalfPlane

open ClosedUpperHalfPlane

/-- The bordered holomorphic groupoid is closed under restriction to open sets, so open subsets of
a Riemann surface with boundary are again Riemann surfaces with boundary. -/
instance closedUnderRestriction_borderedHolomorphicGroupoid :
    ClosedUnderRestriction borderedHolomorphicGroupoid := by
  refine (closedUnderRestriction_iff_id_le _).2 ?_
  rw [StructureGroupoid.le_iff]
  rintro e ⟨s, hs, hes⟩
  refine StructureGroupoid.mem_of_eqOnSource _ ?_ hes
  have hid : ∀ t : Set ClosedUpperHalfPlane, DifferentiableOn ℂ
      (closedUpperHalfPlaneModel ∘ id ∘ closedUpperHalfPlaneModel.symm)
      (closedUpperHalfPlaneModel.symm ⁻¹' t ∩ {z | 0 < z.im}) := fun t ↦
    differentiableOn_id.congr fun z hz ↦ by
      simpa using coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (le_of_lt hz.2)
  refine mem_borderedHolomorphicGroupoid_iff.2 ⟨ofSet_mem_contDiffGroupoid hs, ?_, ?_⟩ <;>
    simpa using hid s

variable (M : Type*) [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid]

/-- The manifold interior of a Riemann surface with boundary, as an open subset. -/
def borderedInterior : Opens M :=
  ⟨closedUpperHalfPlaneModel.interior M,
    closedUpperHalfPlaneModel.isOpen_interior (n := ∞) (by simp)⟩

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

/-- A point in the source of a chart of the atlas is in the interior exactly when the chart sends
it to a point of positive imaginary part. -/
theorem mem_borderedInterior_iff_im_pos {e : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (he : e ∈ atlas ClosedUpperHalfPlane M) {x : M} (hx : x ∈ e.source) :
    x ∈ borderedInterior M ↔ 0 < (e x : ℂ).im := by
  rw [mem_borderedInterior_iff_im_chartAt_pos]
  have hc := borderedHolomorphicGroupoid_le_contDiffGroupoid
    (HasGroupoid.compatible (chart_mem_atlas ClosedUpperHalfPlane x) he)
  simpa [hx] using im_pos_iff_of_mem_contDiffGroupoid hc (by simp)
    (z := chartAt ClosedUpperHalfPlane x x) (by simp [hx])

/-- The interior of a Riemann surface with boundary is a charted space modelled on `ℂ`: the chart
at `x` restricts the chart of `M` at `x` to the interior and reads it in `ℂ`. -/
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
    chartAt ℂ x y = (chartAt ClosedUpperHalfPlane (x : M) y : ℂ) :=
  rfl

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
  exact (mem_borderedInterior_iff_im_pos (chart_mem_atlas _ _) hy).1 y.2

/-- The interior of a Riemann surface with boundary has holomorphic transition maps. -/
instance hasGroupoid_borderedInterior :
    HasGroupoid (borderedInterior M) (contDiffGroupoid ω 𝓘(ℂ)) where
  compatible := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    have h := (borderedHolomorphicGroupoid).compatible
      (chart_mem_atlas ClosedUpperHalfPlane x) (chart_mem_atlas ClosedUpperHalfPlane y)
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid h

/-- The interior of a Riemann surface with boundary is a Riemann surface without boundary. -/
instance isManifold_borderedInterior : IsManifold 𝓘(ℂ) ω (borderedInterior M) :=
  IsManifold.mk' _ _ _

/-- Near the image of `x`, reading the chart of the interior at `x` back through the open-subset
chart of `M` at `x` is the identity. Both comparisons of the two structures reduce to this. -/
private theorem eventually_chartAt_chartAt_symm_eq (x : borderedInterior M) :
    ∀ᶠ z in 𝓝 (chartAt ℂ x x),
      (chartAt ClosedUpperHalfPlane x
        ((chartAt ClosedUpperHalfPlane x).symm (closedUpperHalfPlaneModel.symm z)) : ℂ) = z :=
  Filter.eventually_of_mem ((chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))
    fun _ hz ↦ (chartAt ℂ x).right_inv hz

/-- The identity is a diffeomorphism from the interior with its complex charts, read over `ℝ`, to
the interior with the open-subset structure of `M`. So the complex structure on the interior
induces the real smooth structure of `M`. -/
def borderedInteriorDiffeomorph (n : ℕ∞ω) :
    Diffeomorph 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel (borderedInterior M) (borderedInterior M) n
    where
  toEquiv := Equiv.refl _
  contMDiff_toFun x := by
    refine contMDiffAt_iff.2 ⟨continuousAt_id, contDiffWithinAt_id.congr_of_eventuallyEq ?_ ?_⟩
    · filter_upwards [nhdsWithin_le_nhds (eventually_chartAt_chartAt_symm_eq x)] with z hz
      simpa [mfld_simps, chartAt_borderedInterior] using hz
    · simp [mfld_simps, chartAt_borderedInterior]
  contMDiff_invFun x := by
    have hx : extChartAt closedUpperHalfPlaneModel x x = chartAt ℂ x x := by
      simp [mfld_simps, chartAt_borderedInterior]
    refine contMDiffAt_iff.2 ⟨continuousAt_id, contDiffWithinAt_id.congr_of_eventuallyEq ?_ ?_⟩
    · rw [hx]
      filter_upwards [nhdsWithin_le_nhds (eventually_chartAt_chartAt_symm_eq x)] with z hz
      simpa [mfld_simps, chartAt_borderedInterior] using hz
    · simp [mfld_simps, chartAt_borderedInterior]

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
    chartAt ℂ x y = ((y : ClosedUpperHalfPlane) : ℂ) :=
  rfl

/-- The chart of the interior of the closed upper half-plane is defined everywhere. -/
theorem chartAt_borderedInterior_source_eq_univ (x : borderedInterior ClosedUpperHalfPlane) :
    (chartAt ℂ x).source = univ := by
  simp

/-- The chart of the interior of the closed upper half-plane takes values in the whole open upper
half-plane. -/
theorem chartAt_borderedInterior_target_eq (x : borderedInterior ClosedUpperHalfPlane) :
    (chartAt ℂ x).target = {z : ℂ | 0 < z.im} := by
  rw [← (chartAt ℂ x).image_source_eq_target, chartAt_borderedInterior_source_eq_univ, image_univ]
  ext z
  refine ⟨?_, fun hz ↦ ⟨⟨⟨z, le_of_lt hz⟩, mem_borderedInterior_iff.2 hz⟩, rfl⟩⟩
  rintro ⟨y, rfl⟩
  exact mem_borderedInterior_iff.1 y.2

end ClosedUpperHalfPlane

end TauCeti
