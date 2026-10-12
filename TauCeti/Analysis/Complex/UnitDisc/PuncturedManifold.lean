/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# The punctured unit disc as a complex manifold

The inclusion of the punctured unit disc into the complex plane is an open embedding.
Its single chart gives the complex manifold structure used by punctured-disc coordinates.
-/

public noncomputable section

open scoped Complex.UnitDisc Manifold ContDiff

namespace TauCeti.Complex.UnitDisc

/-- The punctured unit disc is an open subset of the complex plane. -/
theorem isOpenEmbedding_coe_punctured :
    Topology.IsOpenEmbedding (fun q : {q : 𝔻 // q ≠ 0} ↦ ((q : 𝔻) : ℂ)) := by
  let : T1Space 𝔻 := _root_.Complex.UnitDisc.isEmbedding_coe.t1Space
  -- The unit-disc coercion is definitionally the inclusion of the open unit ball.
  have h : Topology.IsOpenEmbedding ((↑) : 𝔻 → ℂ) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  exact h.comp isOpen_compl_singleton.isOpenEmbedding_subtypeVal

/-- Every nonzero point of the open unit disc is a point of the punctured unit disc. -/
theorem exists_coe_punctured_eq {q : ℂ} (hq : q ≠ 0) (hq1 : ‖q‖ < 1) :
    ∃ q' : {q : 𝔻 // q ≠ 0}, ((q' : 𝔻) : ℂ) = q :=
  ⟨⟨_root_.Complex.UnitDisc.mk q hq1, fun h ↦ hq (by
    have := congrArg ((↑) : 𝔻 → ℂ) h
    rwa [_root_.Complex.UnitDisc.coe_mk, _root_.Complex.UnitDisc.coe_zero] at this)⟩,
    _root_.Complex.UnitDisc.coe_mk q hq1⟩

/-- The unit disc has a point other than its origin. -/
instance instNonemptyPunctured : Nonempty {q : 𝔻 // q ≠ 0} :=
  nonempty_subtype.mpr (exists_ne 0)

/-- The complex inclusion is the single chart of the punctured unit disc. -/
noncomputable instance instChartedSpacePunctured : ChartedSpace ℂ {q : 𝔻 // q ≠ 0} :=
  isOpenEmbedding_coe_punctured.singletonChartedSpace

/-- The punctured unit disc is a complex analytic manifold. -/
instance instIsManifoldPunctured : IsManifold 𝓘(ℂ) ω {q : 𝔻 // q ≠ 0} :=
  isOpenEmbedding_coe_punctured.isManifold_singleton

/-- The extended chart of the punctured unit disc is its inclusion into the complex plane. -/
theorem extChartAt_coe_punctured (q : {q : 𝔻 // q ≠ 0}) :
    ⇑(extChartAt 𝓘(ℂ) q) = (fun p : {q : 𝔻 // q ≠ 0} ↦ ((p : 𝔻) : ℂ)) := by
  rw [extChartAt_coe, isOpenEmbedding_coe_punctured.singletonChartedSpace_chartAt_eq]
  rfl

/-- The inclusion of the punctured unit disc into the complex plane is holomorphic. -/
theorem mdifferentiable_coe_punctured :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun q : {q : 𝔻 // q ≠ 0} ↦ ((q : 𝔻) : ℂ)) := by
  intro q
  rw [← extChartAt_coe_punctured q]
  exact mdifferentiableAt_extChartAt (mem_chart_source ℂ q)

end TauCeti.Complex.UnitDisc
