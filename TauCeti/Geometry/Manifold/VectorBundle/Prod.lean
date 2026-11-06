/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Smooth maps into direct-sum bundles

The native atlas of a direct-sum bundle has the pair of the two fibre coordinates. Thus a map
into its total space is smooth exactly when its two component bundle maps are smooth, with the
same base projection. This criterion needs no finite rank, completeness or manifold hypothesis.
-/

public section

open Bundle
open scoped Manifold ContDiff
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₁ E₂ : B → Type*} [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, Zero (E₁ x)] [∀ x, Zero (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {J : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}
/-- A map into a direct-sum bundle is smooth exactly when both component bundle maps are smooth. -/
theorem Bundle.contMDiffAt_totalSpace_prod_iff {f : M → TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)} {x : M} :
    ContMDiffAt J (I.prod 𝓘(𝕜, F₁ × F₂)) n f x ↔
      ContMDiffAt J (I.prod 𝓘(𝕜, F₁)) n
        (fun y ↦ (⟨(f y).proj, (f y).2.1⟩ : TotalSpace F₁ E₁)) x ∧
      ContMDiffAt J (I.prod 𝓘(𝕜, F₂)) n
        (fun y ↦ (⟨(f y).proj, (f y).2.2⟩ : TotalSpace F₂ E₂)) x := by
  rw [Bundle.contMDiffAt_totalSpace, Bundle.contMDiffAt_totalSpace,
    Bundle.contMDiffAt_totalSpace]
  simp only [FiberBundle.prod_trivializationAt',
    contMDiffAt_prod_module_iff]
  constructor
  · rintro ⟨hb, h₁, h₂⟩
    exact ⟨⟨hb, h₁⟩, hb, h₂⟩
  · rintro ⟨⟨hb, h₁⟩, -, h₂⟩
    exact ⟨hb, h₁, h₂⟩
