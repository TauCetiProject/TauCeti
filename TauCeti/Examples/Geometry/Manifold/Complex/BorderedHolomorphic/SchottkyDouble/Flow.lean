/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.SchottkyDouble.Flow
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.VectorField.ModelChart
import TauCeti.Geometry.Manifold.Flow.Diffeomorph
import TauCeti.Geometry.Manifold.Flow.NormedSpace
import Mathlib.Tactic.Convert

/-!
# Flat, empty and disconnected Schottky flow examples

On the double of the closed upper half-plane, the preferred-chart constant field with value `I`
has normal derivative one and imaginary flow coordinate equal to time. Its flow enters the first
and second interior sheets at positive and negative times, meeting the seam only at time zero.
The literal empty original and the open upper half-plane have empty seams and admit unit time.
For two disjoint half-planes, a given positive transverse field has one common time interval at
origins in both components.
-/

public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff ComplexConjugate

universe u

namespace TauCeti.Examples.SchottkyDoubleFlow

open SchottkyDouble

local notation "B" => ClosedUpperHalfPlane
local notation "A" => (borderedInterior B : Set B)ᶜ
local notation "D" => SchottkyDouble B
local notation "J" => 𝓘(ℝ, ℂ)

local instance flatRealManifold (n : ℕ∞ω) : IsManifold J n D :=
  IsManifold.restrictScalars_of_ne_zero n (m := ω) (by simp) inferInstance

/-- The preferred chart at the origin of the flat double. -/
def flatChart : OpenPartialHomeomorph D ℂ :=
  chartAt ℂ (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal 0))

/-- The preferred flat chart is defined on the whole native double. -/
@[simp]
theorem flatChart_source : flatChart.source = univ := by
  simp [flatChart, SchottkyDouble.chartAt_inl, SchottkyDouble.doubleChart_source,
    chartAt_self_eq]

/-- The preferred flat chart has all complex numbers as its target. -/
@[simp]
theorem flatChart_target : flatChart.target = univ := by
  simp [flatChart, SchottkyDouble.chartAt_inl, SchottkyDouble.doubleChart_target,
    chartAt_self_eq]

/-- The doubled identity chart is a global real-smooth diffeomorphism. -/
def flatDiffeomorph : D ≃ₘ⟮J, J⟯ ℂ where
  toEquiv := (flatChart.toHomeomorphOfSourceEqUnivTargetEqUniv
    flatChart_source flatChart_target).toEquiv
  contMDiff_toFun := by
    have h : ContMDiffOn J J ∞ flatChart flatChart.source := contMDiffOn_chart
    simpa only [Homeomorph.coe_toEquiv,
      OpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv_apply,
      flatChart_source, contMDiffOn_univ] using h
  contMDiff_invFun := by
    have h : ContMDiffOn J J ∞ flatChart.symm flatChart.target := contMDiffOn_chart_symm
    have hh := contMDiffOn_univ.mp (flatChart_target ▸ h)
    convert hh using 1
    ext z
    exact congrFun (flatChart.toHomeomorphOfSourceEqUnivTargetEqUniv_symm_apply
      flatChart_source flatChart_target) z

/-- The global flat diffeomorphism acts by the preferred chart. -/
@[simp]
theorem flatDiffeomorph_apply (z : D) : flatDiffeomorph z = flatChart z := by
  rw [flatDiffeomorph]
  exact congrFun (flatChart.toHomeomorphOfSourceEqUnivTargetEqUniv_apply
    flatChart_source flatChart_target) z

/-- On the first sheet, the flat chart is the original complex coordinate. -/
@[simp]
theorem flatChart_inl (x : B) : flatChart (DoubleAlong.inl A x) = x := by
  simp [flatChart, SchottkyDouble.chartAt_inl, SchottkyDouble.doubleChart_inl,
    chartAt_self_eq]

/-- The pullback of the constant imaginary-unit field by the global chart. -/
def flatField (z : D) : TangentSpace J z :=
  chartConstField ℂ (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal 0)) Complex.I z

/-- The native flat field is real C¹. -/
theorem contMDiff_flatField :
    ContMDiff J (J).tangent 1 (fun z ↦ (⟨z, flatField z⟩ : TangentBundle J D)) := by
  have h : ContMDiffOn J (J).tangent ∞
      (fun z ↦ (⟨z, flatField z⟩ : TangentBundle J D)) flatChart.source :=
    contMDiffOn_chartConstField _ Complex.I
  exact (contMDiffOn_univ.mp (flatChart_source ▸ h)).of_le (by simp)

/-- The native derivative of the flat chart carries the flat field to `I`. -/
theorem mfderiv_flatDiffeomorph_flatField (z : D) :
    mfderiv J J flatDiffeomorph z (flatField z) = Complex.I := by
  have hchart : (flatDiffeomorph : D → ℂ) = flatChart := funext flatDiffeomorph_apply
  rw [hchart, flatField]
  exact mfderiv_chartConstField_apply Complex.I (show _ ∈ flatChart.source from by
    simp only [flatChart_source, mem_univ])

/-- The flat field is complete on the native double. -/
theorem isComplete_flatField : IsCompleteVectorField flatField := by
  apply isCompleteVectorField_iff_maximalIntegralCurveInterval.mpr
  intro z
  rw [← flatDiffeomorph.maximalIntegralCurveInterval_apply (by simp)
    (Y := fun _ : ℂ ↦ Complex.I) mfderiv_flatDiffeomorph_flatField]
  exact (isCompleteVectorField_const Complex.I).maximalIntegralCurveInterval_eq_univ _

/-- The preferred chart reads the native flow as translation by `t I`. -/
theorem flatChart_globalFlow (t : ℝ) (z : D) :
    flatChart (globalFlow flatField contMDiff_flatField isComplete_flatField t z) =
      flatChart z + t • Complex.I := by
  rw [← flatDiffeomorph_apply, ← flowOf_eq_globalFlow]
  rw [flatDiffeomorph.apply_flowOf (by simp)
    (contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const)
    mfderiv_flatDiffeomorph_flatField, flowOf_const, flatDiffeomorph_apply]

/-- At every real seam point, the flow's native imaginary coordinate equals time. -/
theorem flatChart_globalFlow_im (t s : ℝ) :
    (flatChart (globalFlow flatField contMDiff_flatField isComplete_flatField t
      (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal s)))).im = t := by
  rw [flatChart_globalFlow, flatChart_inl]
  simp

/-- The native positive-conormal value is one, with no nonzero-field assumption. -/
theorem mvfderiv_im_chartAt_flatField_eq_one (s : ℝ) :
    mvfderiv J
      (fun z : D ↦ (chartAt ℂ (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal s)) z).im)
      (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal s))
      (flatField (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal s))) = 1 := by
  have hchart : chartAt ℂ (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal s)) = flatChart := by
    simp [flatChart, SchottkyDouble.chartAt_inl, chartAt_self_eq]
  rw [hchart]
  rw [flatField, mvfderiv_chartConstField_apply Complex.I (show _ ∈ flatChart.source from by
    simp only [flatChart_source, mem_univ])]
  have hcomp : (fun z : D ↦ (flatChart z).im) ∘ flatChart.symm = Complex.im := by
    funext z
    rw [Function.comp_apply, flatChart.right_inv (by simp)]
  have hzerochart : chartAt ℂ (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal 0)) =
      flatChart := by rw [flatChart]
  rw [hzerochart, hcomp]
  have him : (Complex.imCLM : ℂ → ℝ) = Complex.im := funext Complex.imCLM_apply
  have hd (z : ℂ) : fderiv ℝ Complex.im z = Complex.imCLM := by
    simpa only [him] using Complex.imCLM.hasFDerivAt.fderiv (x := z)
  rw [hd]
  simp

/-- The flat field is nonzero at every real seam point. -/
theorem flatField_ne_zero (s : ℝ) :
    flatField (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal s)) ≠ 0 := by
  intro hzero
  have h := mvfderiv_im_chartAt_flatField_eq_one s
  rw [hzero, map_zero] at h
  exact zero_ne_one h

/-- From the flat origin, positive and negative small times enter the respective interior
sheets, and the flow lies in the seam exactly at time zero. -/
theorem flat_origin_flow_sides :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ t ∈ Ioo 0 ε,
        globalFlow flatField contMDiff_flatField isComplete_flatField t
          (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal 0)) ∈
            range (SchottkyDouble.interiorInl B)) ∧
      (∀ t ∈ Ioo (-ε) 0,
        globalFlow flatField contMDiff_flatField isComplete_flatField t
          (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal 0)) ∈
            range (SchottkyDouble.interiorInr B)) ∧
      (∀ t ∈ Ioo (-ε) ε,
        globalFlow flatField contMDiff_flatField isComplete_flatField t
          (DoubleAlong.inl A (ClosedUpperHalfPlane.ofReal 0)) ∈
            DoubleAlong.inl A '' A ↔ t = 0) := by
  have hA : ({ClosedUpperHalfPlane.ofReal 0} : Set B) ⊆ A := by
    rintro x (rfl : x = ClosedUpperHalfPlane.ofReal 0)
    simp [ClosedUpperHalfPlane.mem_borderedInterior_iff]
  obtain ⟨ε, hε, h⟩ := exists_uniform_globalFlow_mem_interiorSheets
    contMDiff_flatField isComplete_flatField isCompact_singleton hA (by
      rintro x (rfl : x = ClosedUpperHalfPlane.ofReal 0)
      rw [mvfderiv_im_chartAt_flatField_eq_one]
      exact one_pos)
  exact ⟨ε, hε, h _ (mem_singleton _)⟩

section EmptyOriginal

/-- The canonical empty charted-space structure on the literal empty original. -/
local instance emptyOriginalChartedSpace : ChartedSpace B PEmpty.{u + 1} :=
  ChartedSpace.empty B PEmpty.{u + 1}

local instance instHasGroupoidEmptyOriginal :
    HasGroupoid PEmpty.{u + 1} borderedHolomorphicGroupoid where
  compatible {e} _ he _ := by
    have : e ∈ (∅ : Set (OpenPartialHomeomorph PEmpty B)) := he
    exact this.elim

local instance emptyRealManifold : IsManifold J 1 (SchottkyDouble PEmpty.{u + 1}) :=
  IsManifold.restrictScalars_of_ne_zero 1 (m := ω) (by simp) inferInstance

/-- The literal empty original has an empty existing gluing seam. -/
theorem compl_borderedInterior_pEmpty_eq_empty :
    (borderedInterior PEmpty.{u + 1} : Set PEmpty.{u + 1})ᶜ = ∅ := by
  ext x
  exact x.elim

/-- On the literal empty original, unit time satisfies the empty-seam conclusion. -/
theorem empty_original_unit_time
    (v : (z : SchottkyDouble PEmpty.{u + 1}) → TangentSpace J z)
    (hv : ContMDiff J (J).tangent 1
      (fun z ↦ (⟨z, v z⟩ : TangentBundle J (SchottkyDouble PEmpty.{u + 1})))) :
    ∃ ε : ℝ, ε = 1 ∧ 0 < ε ∧ ∀ x : PEmpty.{u + 1},
      ∀ t ∈ Ioo (-ε) ε,
        globalFlow v hv (isCompleteVectorField_of_compactSpace hv) t
          (DoubleAlong.inl (borderedInterior PEmpty.{u + 1} : Set PEmpty.{u + 1})ᶜ x) ∈
            DoubleAlong.inl (borderedInterior PEmpty.{u + 1} : Set PEmpty.{u + 1})ᶜ ''
              (borderedInterior PEmpty.{u + 1} : Set PEmpty.{u + 1})ᶜ ↔ t = 0 := by
  exact ⟨1, rfl, one_pos, fun x ↦ x.elim⟩

/-- The whole-compact theorem supplies completeness on an empty original in every universe. -/
theorem empty_original_compact_flow_sides
    (v : (z : SchottkyDouble PEmpty.{u + 1}) → TangentSpace J z)
    (hv : ContMDiff J (J).tangent 1
      (fun z ↦ (⟨z, v z⟩ : TangentBundle J (SchottkyDouble PEmpty.{u + 1})))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : PEmpty.{u + 1}, ∀ t ∈ Ioo 0 ε,
      globalFlow v hv (isCompleteVectorField_of_compactSpace hv) t
        (DoubleAlong.inl (borderedInterior PEmpty.{u + 1} : Set PEmpty.{u + 1})ᶜ x) ∈
          range (SchottkyDouble.interiorInl PEmpty.{u + 1}) := by
  obtain ⟨ε, hε, h⟩ := exists_uniform_globalFlow_mem_interiorSheets_of_compactSpace
    hv (fun x ↦ x.elim)
  exact ⟨ε, hε, fun x ↦ (h x (x.elim : x ∈
    (borderedInterior PEmpty.{u + 1} : Set PEmpty.{u + 1})ᶜ)).1⟩

end EmptyOriginal

section EmptySeamOriginal

local instance instNonemptyHalfPlaneInterior : Nonempty (borderedInterior B) :=
  ⟨⟨⟨Complex.I, by simp⟩, ClosedUpperHalfPlane.mem_borderedInterior_iff.mpr (by simp)⟩⟩

local instance openRealManifold : IsManifold J 1 (SchottkyDouble (borderedInterior B)) :=
  IsManifold.restrictScalars_of_ne_zero 1 (m := ω) (by simp) inferInstance

/-- The native open upper half-plane, as an original bordered manifold, has empty seam. -/
theorem compl_borderedInterior_borderedInterior_eq_empty :
    (borderedInterior (borderedInterior B) : Set (borderedInterior B))ᶜ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  apply hx
  apply (mem_borderedInterior_iff_im_chartAt_pos (M := borderedInterior B)).2
  rw [TopologicalSpace.Opens.chartAt_eq]
  simpa only [OpenPartialHomeomorph.subtypeRestr_coe, Set.domRestrict_apply, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, id_eq] using
      ClosedUpperHalfPlane.mem_borderedInterior_iff.mp x.property

/-- The nonempty open upper half-plane has the literal unit-time empty-seam certificate. -/
theorem upper_half_plane_unit_time
    (v : (z : SchottkyDouble (borderedInterior B)) → TangentSpace J z)
    (hv : ContMDiff J (J).tangent 1
      (fun z ↦ (⟨z, v z⟩ : TangentBundle J (SchottkyDouble (borderedInterior B)))))
    (hc : IsCompleteVectorField v) :
    ∃ ε : ℝ, ε = 1 ∧ 0 < ε ∧
      ∀ x ∈ (borderedInterior (borderedInterior B) : Set (borderedInterior B))ᶜ,
        (∀ t ∈ Ioo 0 ε,
          globalFlow v hv hc t
            (DoubleAlong.inl
              (borderedInterior (borderedInterior B) : Set (borderedInterior B))ᶜ x) ∈
              range (SchottkyDouble.interiorInl (borderedInterior B))) ∧
        (∀ t ∈ Ioo (-ε) 0,
          globalFlow v hv hc t
            (DoubleAlong.inl
              (borderedInterior (borderedInterior B) : Set (borderedInterior B))ᶜ x) ∈
              range (SchottkyDouble.interiorInr (borderedInterior B))) ∧
        (∀ t ∈ Ioo (-ε) ε,
          globalFlow v hv hc t
            (DoubleAlong.inl
              (borderedInterior (borderedInterior B) : Set (borderedInterior B))ᶜ x) ∈
              DoubleAlong.inl
                (borderedInterior (borderedInterior B) : Set (borderedInterior B))ᶜ ''
                  (borderedInterior (borderedInterior B) : Set (borderedInterior B))ᶜ ↔ t = 0) := by
  refine ⟨1, rfl, one_pos, ?_⟩
  intro x hx
  exact (Set.eq_empty_iff_forall_notMem.mp
    compl_borderedInterior_borderedInterior_eq_empty x hx).elim

end EmptySeamOriginal

section DisconnectedOriginal

local instance instNonemptyHalfPlane : Nonempty B := ⟨ClosedUpperHalfPlane.ofReal 0⟩

/-- A chart transition with empty source belongs to the bordered holomorphic groupoid. -/
private theorem mem_borderedHolomorphicGroupoid_of_source_eq_empty
    {e : OpenPartialHomeomorph B B} (h : ∀ x ∈ e.source, False) :
    e ∈ borderedHolomorphicGroupoid :=
  borderedHolomorphicGroupoid.locality fun x hx ↦ (h x hx).elim

local instance sumBorderedHolomorphic : HasGroupoid (B ⊕ B) borderedHolomorphicGroupoid where
  compatible {e} e' he he' := by
    obtain (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩) := ChartedSpace.mem_atlas_sum he
    · obtain (⟨g, hg, rfl⟩ | ⟨g, _hg, rfl⟩) := ChartedSpace.mem_atlas_sum he'
      · rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
        exact borderedHolomorphicGroupoid.compatible hf hg
      · exact mem_borderedHolomorphicGroupoid_of_source_eq_empty
          fun _ ⟨_, _, _, hxy⟩ ↦ by cases hxy
    · obtain (⟨g, _hg, rfl⟩ | ⟨g, hg, rfl⟩) := ChartedSpace.mem_atlas_sum he'
      · exact mem_borderedHolomorphicGroupoid_of_source_eq_empty
          fun _ ⟨_, _, _, hxy⟩ ↦ by cases hxy
      · rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
        exact borderedHolomorphicGroupoid.compatible hf hg

local instance sumRealManifold : IsManifold J 1 (SchottkyDouble (B ⊕ B)) :=
  IsManifold.restrictScalars_of_ne_zero 1 (m := ω) (by simp) inferInstance

/-- Two native seam starts on different components form a compact admissible starting set. -/
theorem isCompact_pair_origins_and_subset_compl_borderedInterior :
    IsCompact ({Sum.inl (ClosedUpperHalfPlane.ofReal 0),
      Sum.inr (ClosedUpperHalfPlane.ofReal 0)} : Set (B ⊕ B)) ∧
    ({Sum.inl (ClosedUpperHalfPlane.ofReal 0),
      Sum.inr (ClosedUpperHalfPlane.ofReal 0)} : Set (B ⊕ B)) ⊆
      (borderedInterior (B ⊕ B) : Set (B ⊕ B))ᶜ := by
  refine ⟨(Set.toFinite _).isCompact, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · simp [mem_borderedInterior_iff_im_chartAt_pos]
  · rcases hx with rfl
    simp [mem_borderedInterior_iff_im_chartAt_pos]

/-- The uniform theorem admits a native disconnected original and samples both components. -/
theorem disconnected_flow_sides
    (v : (z : SchottkyDouble (B ⊕ B)) → TangentSpace J z)
    (hv : ContMDiff J (J).tangent 1
      (fun z ↦ (⟨z, v z⟩ : TangentBundle J (SchottkyDouble (B ⊕ B)))))
    (hc : IsCompleteVectorField v)
    (hpos : ∀ x ∈ ({Sum.inl (ClosedUpperHalfPlane.ofReal 0),
        Sum.inr (ClosedUpperHalfPlane.ofReal 0)} : Set (B ⊕ B)),
      0 < mvfderiv J
        (fun z : SchottkyDouble (B ⊕ B) ↦
          (chartAt ℂ (DoubleAlong.inl (borderedInterior (B ⊕ B) : Set (B ⊕ B))ᶜ x) z).im)
        (DoubleAlong.inl (borderedInterior (B ⊕ B) : Set (B ⊕ B))ᶜ x)
        (v (DoubleAlong.inl (borderedInterior (B ⊕ B) : Set (B ⊕ B))ᶜ x))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ ({Sum.inl (ClosedUpperHalfPlane.ofReal 0),
        Sum.inr (ClosedUpperHalfPlane.ofReal 0)} : Set (B ⊕ B)),
      (∀ t ∈ Ioo 0 ε,
        globalFlow v hv hc t
          (DoubleAlong.inl (borderedInterior (B ⊕ B) : Set (B ⊕ B))ᶜ x) ∈
            range (SchottkyDouble.interiorInl (B ⊕ B))) ∧
      (∀ t ∈ Ioo (-ε) 0,
        globalFlow v hv hc t
          (DoubleAlong.inl (borderedInterior (B ⊕ B) : Set (B ⊕ B))ᶜ x) ∈
            range (SchottkyDouble.interiorInr (B ⊕ B))) ∧
      (∀ t ∈ Ioo (-ε) ε,
        globalFlow v hv hc t
          (DoubleAlong.inl (borderedInterior (B ⊕ B) : Set (B ⊕ B))ᶜ x) ∈
            DoubleAlong.inl (borderedInterior (B ⊕ B) : Set (B ⊕ B))ᶜ ''
              (borderedInterior (B ⊕ B) : Set (B ⊕ B))ᶜ ↔ t = 0) := by
  let h := isCompact_pair_origins_and_subset_compl_borderedInterior
  exact exists_uniform_globalFlow_mem_interiorSheets hv hc h.1 h.2 hpos

end DisconnectedOriginal

end TauCeti.Examples.SchottkyDoubleFlow
