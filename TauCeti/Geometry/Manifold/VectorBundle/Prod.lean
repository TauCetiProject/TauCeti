/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Smooth maps into direct-sum bundles

The native atlas of a direct-sum bundle has the pair of the two fibre coordinates. Thus a map
into its total space is smooth (or differentiable) exactly when its two component bundle maps are
smooth (or differentiable), with the same base projection. This criterion needs no finite rank,
completeness or manifold hypothesis.
In particular the projections of a direct-sum bundle onto its summands, and the inclusions of the
summands, are smooth maps of total spaces.
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
/-- A map into a direct-sum bundle is smooth within a set exactly when both component bundle maps
are. -/
theorem Bundle.contMDiffWithinAt_totalSpace_prod_iff
    {f : M → TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)} {s : Set M} {x : M} :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ × F₂)) n f s x ↔
      ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁)) n
        (fun y ↦ (⟨(f y).proj, (f y).2.1⟩ : TotalSpace F₁ E₁)) s x ∧
      ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₂)) n
        (fun y ↦ (⟨(f y).proj, (f y).2.2⟩ : TotalSpace F₂ E₂)) s x := by
  rw [Bundle.contMDiffWithinAt_totalSpace_iff, Bundle.contMDiffWithinAt_totalSpace_iff,
    Bundle.contMDiffWithinAt_totalSpace_iff]
  simp only [FiberBundle.prod_trivializationAt', contMDiffWithinAt_prod_module_iff]
  constructor
  · rintro ⟨hb, h₁, h₂⟩
    exact ⟨⟨hb, h₁⟩, hb, h₂⟩
  · rintro ⟨⟨hb, h₁⟩, -, h₂⟩
    exact ⟨hb, h₁, h₂⟩

/-- A map into a direct-sum bundle is smooth exactly when both component bundle maps are smooth. -/
theorem Bundle.contMDiffAt_totalSpace_prod_iff {f : M → TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)} {x : M} :
    ContMDiffAt J (I.prod 𝓘(𝕜, F₁ × F₂)) n f x ↔
      ContMDiffAt J (I.prod 𝓘(𝕜, F₁)) n
        (fun y ↦ (⟨(f y).proj, (f y).2.1⟩ : TotalSpace F₁ E₁)) x ∧
      ContMDiffAt J (I.prod 𝓘(𝕜, F₂)) n
        (fun y ↦ (⟨(f y).proj, (f y).2.2⟩ : TotalSpace F₂ E₂)) x := by
  simp only [← contMDiffWithinAt_univ]
  exact Bundle.contMDiffWithinAt_totalSpace_prod_iff

/-- A section of a direct-sum bundle is smooth within a set at a point exactly when both of its
components are. -/
theorem Bundle.contMDiffWithinAt_section_prod_iff {σ : Π x, E₁ x × E₂ x} {s : Set B} {x : B} :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F₁ × F₂)) n
        (fun y ↦ TotalSpace.mk' (F₁ × F₂) (E := E₁ ×ᵇ E₂) y (σ y)) s x ↔
      ContMDiffWithinAt I (I.prod 𝓘(𝕜, F₁)) n (fun y ↦ TotalSpace.mk' F₁ y (σ y).1) s x ∧
      ContMDiffWithinAt I (I.prod 𝓘(𝕜, F₂)) n (fun y ↦ TotalSpace.mk' F₂ y (σ y).2) s x :=
  Bundle.contMDiffWithinAt_totalSpace_prod_iff

/-- A section of a direct-sum bundle is smooth at a point exactly when both of its components
are. -/
theorem Bundle.contMDiffAt_section_prod_iff {σ : Π x, E₁ x × E₂ x} {x : B} :
    ContMDiffAt I (I.prod 𝓘(𝕜, F₁ × F₂)) n
        (fun y ↦ TotalSpace.mk' (F₁ × F₂) (E := E₁ ×ᵇ E₂) y (σ y)) x ↔
      ContMDiffAt I (I.prod 𝓘(𝕜, F₁)) n (fun y ↦ TotalSpace.mk' F₁ y (σ y).1) x ∧
      ContMDiffAt I (I.prod 𝓘(𝕜, F₂)) n (fun y ↦ TotalSpace.mk' F₂ y (σ y).2) x :=
  Bundle.contMDiffAt_totalSpace_prod_iff

namespace Bundle.Prod

/-- The projection of a direct-sum bundle onto its first summand is smooth on total spaces. -/
theorem contMDiff_fst :
    ContMDiff (I.prod 𝓘(𝕜, F₁ × F₂)) (I.prod 𝓘(𝕜, F₁)) n
      (fun v : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦ TotalSpace.mk' F₁ v.proj v.2.1) :=
  fun _ ↦ (contMDiffAt_totalSpace_prod_iff.1 contMDiffAt_id).1

/-- The projection of a direct-sum bundle onto its second summand is smooth on total spaces. -/
theorem contMDiff_snd :
    ContMDiff (I.prod 𝓘(𝕜, F₁ × F₂)) (I.prod 𝓘(𝕜, F₂)) n
      (fun v : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) ↦ TotalSpace.mk' F₂ v.proj v.2.2) :=
  fun _ ↦ (contMDiffAt_totalSpace_prod_iff.1 contMDiffAt_id).2

end Bundle.Prod

namespace Bundle.Prod

variable {E₁ E₂ : B → Type*} [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]

omit [∀ x, Module 𝕜 (E₁ x)] [VectorBundle 𝕜 F₁ E₁] in
/-- The inclusion of the first summand of a direct-sum bundle is smooth on total spaces. -/
theorem contMDiff_inl :
    ContMDiff (I.prod 𝓘(𝕜, F₁)) (I.prod 𝓘(𝕜, F₁ × F₂)) n
      (fun v : TotalSpace F₁ E₁ ↦
        TotalSpace.mk' (F₁ × F₂) (E := E₁ ×ᵇ E₂) v.proj ((v.2, 0) : E₁ v.proj × E₂ v.proj)) :=
  fun v ↦ contMDiffAt_totalSpace_prod_iff.2
    ⟨contMDiffAt_id, ((contMDiff_zeroSection 𝕜 E₂).comp (contMDiff_proj E₁)) v⟩

omit [∀ x, Module 𝕜 (E₂ x)] [VectorBundle 𝕜 F₂ E₂] in
/-- The inclusion of the second summand of a direct-sum bundle is smooth on total spaces. -/
theorem contMDiff_inr :
    ContMDiff (I.prod 𝓘(𝕜, F₂)) (I.prod 𝓘(𝕜, F₁ × F₂)) n
      (fun v : TotalSpace F₂ E₂ ↦
        TotalSpace.mk' (F₁ × F₂) (E := E₁ ×ᵇ E₂) v.proj ((0, v.2) : E₁ v.proj × E₂ v.proj)) :=
  fun v ↦ contMDiffAt_totalSpace_prod_iff.2
    ⟨((contMDiff_zeroSection 𝕜 E₁).comp (contMDiff_proj E₂)) v, contMDiffAt_id⟩

end Bundle.Prod

/-- A map into a direct-sum bundle is differentiable within a set exactly when both component
bundle maps are. -/
theorem Bundle.mdifferentiableWithinAt_totalSpace_prod_iff
    {f : M → TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)} {s : Set M} {x : M} :
    MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₁ × F₂)) f s x ↔
      MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₁))
        (fun y ↦ (⟨(f y).proj, (f y).2.1⟩ : TotalSpace F₁ E₁)) s x ∧
      MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₂))
        (fun y ↦ (⟨(f y).proj, (f y).2.2⟩ : TotalSpace F₂ E₂)) s x := by
  rw [mdifferentiableWithinAt_totalSpace, mdifferentiableWithinAt_totalSpace,
    mdifferentiableWithinAt_totalSpace]
  simp only [FiberBundle.prod_trivializationAt', mdifferentiableWithinAt_prod_module_iff]
  constructor
  · rintro ⟨hb, h₁, h₂⟩
    exact ⟨⟨hb, h₁⟩, hb, h₂⟩
  · rintro ⟨⟨hb, h₁⟩, -, h₂⟩
    exact ⟨hb, h₁, h₂⟩

/-- A map into a direct-sum bundle is differentiable exactly when both component bundle maps are
differentiable. -/
theorem Bundle.mdifferentiableAt_totalSpace_prod_iff
    {f : M → TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)} {x : M} :
    MDifferentiableAt J (I.prod 𝓘(𝕜, F₁ × F₂)) f x ↔
      MDifferentiableAt J (I.prod 𝓘(𝕜, F₁))
        (fun y ↦ (⟨(f y).proj, (f y).2.1⟩ : TotalSpace F₁ E₁)) x ∧
      MDifferentiableAt J (I.prod 𝓘(𝕜, F₂))
        (fun y ↦ (⟨(f y).proj, (f y).2.2⟩ : TotalSpace F₂ E₂)) x := by
  simp only [← mdifferentiableWithinAt_univ]
  exact Bundle.mdifferentiableWithinAt_totalSpace_prod_iff

/-- A section of a direct-sum bundle is differentiable within a set at a point exactly when both
of its components are. -/
theorem Bundle.mdifferentiableWithinAt_section_prod_iff {σ : Π x, E₁ x × E₂ x} {s : Set B}
    {x : B} :
    MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F₁ × F₂))
        (fun y ↦ TotalSpace.mk' (F₁ × F₂) (E := E₁ ×ᵇ E₂) y (σ y)) s x ↔
      MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F₁)) (fun y ↦ TotalSpace.mk' F₁ y (σ y).1) s x ∧
      MDifferentiableWithinAt I (I.prod 𝓘(𝕜, F₂)) (fun y ↦ TotalSpace.mk' F₂ y (σ y).2) s x :=
  Bundle.mdifferentiableWithinAt_totalSpace_prod_iff

/-- A section of a direct-sum bundle is differentiable at a point exactly when both of its
components are. -/
theorem Bundle.mdifferentiableAt_section_prod_iff {σ : Π x, E₁ x × E₂ x} {x : B} :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F₁ × F₂))
        (fun y ↦ TotalSpace.mk' (F₁ × F₂) (E := E₁ ×ᵇ E₂) y (σ y)) x ↔
      MDifferentiableAt I (I.prod 𝓘(𝕜, F₁)) (fun y ↦ TotalSpace.mk' F₁ y (σ y).1) x ∧
      MDifferentiableAt I (I.prod 𝓘(𝕜, F₂)) (fun y ↦ TotalSpace.mk' F₂ y (σ y).2) x :=
  Bundle.mdifferentiableAt_totalSpace_prod_iff
