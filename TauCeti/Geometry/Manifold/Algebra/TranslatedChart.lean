/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Charts translated in a topological group

Left translating an open partial homeomorphism whose source contains the identity gives a
charted space on a group with continuous left translations.
-/

public section

namespace OpenPartialHomeomorph

variable {G V : Type*} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
  [TopologicalSpace V] (e : OpenPartialHomeomorph G V)

/-- The chart obtained by left translating the source of `e` by `p`. -/
def translatedChart (p : G) : OpenPartialHomeomorph G V :=
  (Homeomorph.smul p).symm.transOpenPartialHomeomorph e

/-- Translating a chart by `p` precomposes it with the inverse of left multiplication by `p`. -/
theorem translatedChart_def (p : G) :
    e.translatedChart p = (Homeomorph.smul p).symm.transOpenPartialHomeomorph e := (rfl)

/-- The forward map of a translated chart first translates the point by `p⁻¹`. -/
@[simp]
theorem translatedChart_apply (p q : G) :
    e.translatedChart p q = e (p⁻¹ * q) := by
  simp [translatedChart, Homeomorph.smul_symm_apply, smul_eq_mul]

/-- The inverse map of a translated chart left translates the original inverse by `p`. -/
@[simp]
theorem translatedChart_symm_apply (p : G) (z : V) :
    (e.translatedChart p).symm z = p * e.symm z := by
  simp [translatedChart, smul_eq_mul]

/-- A point is in the translated source exactly when its translate back lies in the source. -/
@[simp]
theorem mem_translatedChart_source_iff (p q : G) :
    q ∈ (e.translatedChart p).source ↔ p⁻¹ * q ∈ e.source := by
  simp [translatedChart, Homeomorph.smul_symm_apply, smul_eq_mul]

/-- If the original chart contains the identity, each translate contains its translating point. -/
theorem mem_translatedChart_source_self (h₁ : (1 : G) ∈ e.source) (p : G) :
    p ∈ (e.translatedChart p).source := by
  simpa using h₁

/-- The target of a translated chart is the original target. -/
@[simp]
theorem translatedChart_target (p : G) : (e.translatedChart p).target = e.target := by
  simp [translatedChart]

/-- The charted space obtained by left translating a chart whose source contains the identity. -/
@[instance_reducible]
def chartedSpaceOfOne (h₁ : (1 : G) ∈ e.source) : ChartedSpace V G where
  atlas := Set.range e.translatedChart
  chartAt := e.translatedChart
  mem_chart_source p := e.mem_translatedChart_source_self h₁ p
  chart_mem_atlas p := Set.mem_range_self p

/-- The chart at each point in the translated atlas is the left translate by that point. -/
@[mfld_simps]
theorem chartAt_chartedSpaceOfOne (h₁ : (1 : G) ∈ e.source) (p : G) :
    letI := e.chartedSpaceOfOne h₁
    chartAt V p = e.translatedChart p := (rfl)

/-- The atlas consists of all left translates of the supplied chart. -/
@[simp]
theorem atlas_chartedSpaceOfOne (h₁ : (1 : G) ∈ e.source) : letI := e.chartedSpaceOfOne h₁
    atlas V G = Set.range e.translatedChart := (rfl)

end OpenPartialHomeomorph
