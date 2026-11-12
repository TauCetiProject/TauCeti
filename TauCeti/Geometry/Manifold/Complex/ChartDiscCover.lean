/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Sets.OpenCover
public import TauCeti.Topology.OpenPartialHomeomorph.ChartOpens

/-!
# Finite covers of a compact Riemann surface by coordinate discs

A compact Riemann surface is covered by finitely many coordinate discs
`(e i).chartDisc (c i) (r i)` of holomorphic charts with `closedBall (c i) (3 * r i)` in the chart
target (`TauCeti.exists_finite_chartDisc_cover`). By
`OpenPartialHomeomorph.closure_chartDisc_subset`, the discs of radii `r i`, `2 * r i` and
`3 * r i` form three nested finite covers, each closure compact in the next.
-/

public section

open scoped Manifold

namespace TauCeti

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- **Finite nested coordinate-disc covers.** A compact Riemann surface is covered by finitely many
coordinate discs `(e i).chartDisc (c i) (r i)` of holomorphic charts with
`closedBall (c i) (3 * r i) ⊆ (e i).target`. By `OpenPartialHomeomorph.closure_chartDisc_subset`
the discs of radii `r i`, `2 * r i` and `3 * r i` are nested, each closure compact in the next. -/
theorem exists_finite_chartDisc_cover [CompactSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (e : ι → OpenPartialHomeomorph X ℂ) (c : ι → ℂ) (r : ι → ℝ),
      (∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) ∧ (∀ i, 0 < r i) ∧
        (∀ i, Metric.closedBall (c i) (3 * r i) ⊆ (e i).target) ∧
          ⨆ i, (e i).chartDisc (c i) (r i) = ⊤ := by
  have hε (x : X) : ∃ ε > 0, Metric.ball (chartAt ℂ x x) ε ⊆ (chartAt ℂ x).target :=
    Metric.isOpen_iff.1 (chartAt ℂ x).open_target _ (mem_chart_target ℂ x)
  choose ε hε hεT using hε
  let D : X → TopologicalSpace.Opens X :=
    fun x ↦ (chartAt ℂ x).chartDisc (chartAt ℂ x x) (ε x / 4)
  have hD : TopologicalSpace.IsOpenCover D := .mk <| eq_top_iff.2 fun x _ ↦
    TopologicalSpace.Opens.mem_iSup.2
      ⟨x, mem_chart_source ℂ x, Metric.mem_ball_self (by linarith [hε x])⟩
  obtain ⟨s, hs⟩ := hD.exists_finite_of_compactSpace
  exact ⟨s, inferInstance, fun i ↦ chartAt ℂ i.1, fun i ↦ chartAt ℂ i.1 i.1, fun i ↦ ε i.1 / 4,
    fun i ↦ IsManifold.chart_mem_maximalAtlas i.1, fun i ↦ by linarith [hε i.1],
    fun i ↦ (Metric.closedBall_subset_ball (by linarith [hε i.1])).trans (hεT i.1),
    hs.iSup_eq_top⟩

end TauCeti
