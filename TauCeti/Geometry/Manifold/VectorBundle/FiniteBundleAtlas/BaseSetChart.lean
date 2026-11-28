/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization

/-!
# Chart domains of a finite bundle atlas and the dual-density bundle

Let `A` be a finite bundle atlas of a vector bundle `V → M` over a manifold modelled on a real
normed space `E` without boundary. The distributional sections of `V` are read in the charts
`TauCeti.baseSetChart` of the dual-density bundle `V →L |Λ|`: the preferred chart restricted to
the base set of the preferred trivialization of `V →L |Λ|`. That base set is the base set of the
preferred trivialization of `V` inside the preferred chart source, so the domain of chart `i` of
`A` lies in the source of `baseSetChart` at the centre of chart `i`
(`TauCeti.FiniteBundleAtlas.dom_subset_baseSetChart_source`).
-/

public section

open Bundle Set
open scoped Manifold

namespace TauCeti.FiniteBundleAtlas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V)

/-- The domain of chart `i` of `A` lies in the source of the chart `baseSetChart` of the
dual-density bundle at the centre of chart `i`. -/
theorem dom_subset_baseSetChart_source (i : Fin A.n) :
    A.dom i ⊆ (baseSetChart (F →L[ℝ] ℝ) 𝓘(ℝ, E)
      (fun x ↦ V x →L[ℝ] DensityBundle 𝓘(ℝ, E) M x) (A.center i)).source := fun x hx ↦ by
  rw [baseSetChart_source, hom_trivializationAt_baseSet, TauCeti.Density.trivializationAt_eq,
    Trivialization.density_baseSet, TangentBundle.trivializationAt_baseSet]
  exact ⟨A.dom_subset_chart_source i hx, A.dom_subset_baseSet i hx,
    A.dom_subset_chart_source i hx⟩

end TauCeti.FiniteBundleAtlas
