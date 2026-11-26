/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Basic
public import TauCeti.Topology.VectorBundle.Pullback.Basic

/-!
# Coordinates of sections of pullback bundles

A section of the pullback bundle `f *ᵖ B` is a section of `B` along `f`. The preferred
trivialization of the pullback bundle at `x` is the pullback of the preferred trivialization of
`B` at `f x`, so the coordinate reading of the total-space section agrees near `x` with the
coordinate reading `sectionCoord` in the trivialization of `B` at `f x`. Hence a section of
`f *ᵖ B` differentiable into the total space has a differentiable coordinate reading
(`TauCeti.Manifold.mdifferentiableAt_sectionCoord_of_mdifferentiableAt_pullback`).
-/

public section

open Bundle Filter
open scoped Manifold Topology

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [TopologicalSpace M]
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀]
  {B : M → Type*} [TopologicalSpace (TotalSpace F₀ B)]
  [∀ x, AddCommGroup (B x)] [∀ x, Module 𝕜 (B x)] [∀ x, TopologicalSpace (B x)]
  [FiberBundle F₀ B] [VectorBundle 𝕜 F₀ B]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} [TopologicalSpace N] [ChartedSpace G N] (f : C(N, M))

/-- A section of the pullback bundle `f *ᵖ B` that is differentiable into the total space at `x`
has a differentiable coordinate reading, as a section of `B` along `f`, in the preferred
trivialization of `B` at `f x`. -/
theorem mdifferentiableAt_sectionCoord_of_mdifferentiableAt_pullback
    {σ : ∀ x, ((f : N → M) *ᵖ B) x} {x : N}
    (hσ : MDifferentiableAt J (J.prod 𝓘(𝕜, F₀))
      (fun y ↦ TotalSpace.mk' F₀ (E := (f : N → M) *ᵖ B) y (σ y)) x) :
    MDifferentiableAt J 𝓘(𝕜, F₀) (sectionCoord 𝕜 (F := F₀) (V := B) f σ (f x)) x := by
  rw [mdifferentiableAt_section] at hσ
  refine hσ.congr_of_eventuallyEq ?_
  filter_upwards [f.continuous.continuousAt.preimage_mem_nhds
    ((trivializationAt F₀ B (f x)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F₀ B (f x)))] with y hy
  -- `σ y : (f *ᵖ B) y` is `B (f y)` only after unfolding, so the lemmas about `B` and its total
  -- space are applied as terms rather than by `rw`.
  refine (sectionCoord_apply (𝕜 := 𝕜) (F := F₀) (V := B) f σ (f x) y).trans
    (((trivializationAt F₀ B (f x)).continuousLinearMapAt_apply_of_mem 𝕜 hy (σ y)).trans ?_)
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
    Trivialization.pullback_apply]
  exact congrArg (fun z ↦ (FiberBundle.trivializationAt' (f x) z).2)
    (Pullback.lift_mk (F := F₀) (E := B) f y (σ y)).symm

end TauCeti.Manifold
