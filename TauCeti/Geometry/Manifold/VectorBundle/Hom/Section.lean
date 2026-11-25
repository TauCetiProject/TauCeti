/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Smooth Hom sections from maps of total spaces

A smooth fibrewise linear map of total spaces with finite source rank over a complete field
bundles as a smooth section of the Hom bundle. Smoothness of the total-space map supplies both
continuity on each fibre and, by `TauCeti.contMDiff_hom_bundle_iff`, smooth dependence on the base.
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V W : M → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
  {n : ℕ∞ω} [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  (ϕ : ∀ x, V x →ₗ[𝕜] W x)
  (hϕ : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, G)) n
    (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.snd⟩ : TotalSpace G W)))

/-- Bundle a smooth map of total spaces that is linear on each fibre into a section of
the Hom bundle, when the source fibre is finite-dimensional over a complete field. -/
def homSectionOfTotalSpaceMap : Cₛ^n⟮I; F →L[𝕜] G, fun x ↦ V x →L[𝕜] W x⟯ := by
  let ϕL (x : M) : V x →L[𝕜] W x :=
    { toLinearMap := ϕ x
      cont := (FiberBundle.totalSpaceMk_isInducing G W x).continuous_iff.2
        (hϕ.continuous.comp (FiberBundle.continuous_totalSpaceMk F V x)) }
  exact ⟨ϕL, (contMDiff_hom_bundle_iff ϕL).2 hϕ⟩

/-- Evaluating the bundled Hom section recovers the original fibrewise linear map. -/
@[simp]
theorem homSectionOfTotalSpaceMap_apply (x : M) :
    ((homSectionOfTotalSpaceMap ϕ hϕ) x).toLinearMap = ϕ x := by
  unfold homSectionOfTotalSpaceMap
  rfl

end TauCeti
