/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Transport of supported smooth bundle sections

A smooth family of fibre maps over the identity acts on smooth sections pointwise
(`ContMDiffSection.map`); the fibre maps need not be linear.

A smooth fibrewise linear map over the identity induces a linear map on native
`ContMDiffSection`s. It cannot enlarge closed support and therefore acts on fixed-support
stages and compactly supported sections. If the fibre maps are injective, closed support is
preserved exactly. A smooth fibrewise linear equivalence with smooth inverse consequently
identifies both fixed-support stages and compactly supported sections.

These are algebraic equivalences on the existing section carriers, not assertions about a
section-space topology. In particular, they provide support-preserving transport of tests
when a bundle is replaced by a smoothly isomorphic bundle. Smoothness is stated on total
spaces; no norms on individual fibres, finite-rank assumption, compactness of the base,
or choice of frames is needed. Transport commutes with smooth scalar localization.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace ContMDiffSection

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : ℕ∞ω}
  {V W : M → Type*}
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace G W)] [FiberBundle G W]

section Map

variable (ϕ : ∀ x, V x → W x)
  (hϕ : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, G)) n
    (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.2⟩ : TotalSpace G W)))

/-- Postcomposition of sections with a smooth family of fibre maps over the identity. The fibre
maps need not be linear. -/
protected def map (s : Cₛ^n⟮I; F, V⟯) : Cₛ^n⟮I; G, W⟯ :=
  ⟨fun x ↦ ϕ x (s x), hϕ.comp s.contMDiff⟩

/-- A fibrewise map evaluates by the given fibre map, without a change of base point. -/
@[simp]
theorem map_apply (s : Cₛ^n⟮I; F, V⟯) (x : M) :
    ContMDiffSection.map ϕ hϕ s x = ϕ x (s x) := (rfl)

end Map

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [VectorBundle 𝕜 G W]

variable (ϕ : ∀ x, V x →ₗ[𝕜] W x)
  (hϕ : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, G)) n
    (fun p : TotalSpace F V ↦ (⟨p.proj, ϕ p.proj p.2⟩ : TotalSpace G W)))

/-- Postcomposition of sections with a smooth fibrewise linear map over the identity. -/
def mapLinearMap : Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] Cₛ^n⟮I; G, W⟯ where
  toFun := ContMDiffSection.map (fun x ↦ ϕ x) hϕ
  map_add' s t := by ext x; exact (ϕ x).map_add _ _
  map_smul' c s := by ext x; exact (ϕ x).map_smul c _

/-- Transport evaluates by the given fibre map, without a change of base point. -/
@[simp]
theorem mapLinearMap_apply (s : Cₛ^n⟮I; F, V⟯) (x : M) :
    mapLinearMap ϕ hϕ s x = ϕ x (s x) := (rfl)

/-- A fibrewise linear map cannot enlarge the closed support of a section. -/
theorem tsupport_mapLinearMap_subset (s : Cₛ^n⟮I; F, V⟯) :
    (mapLinearMap ϕ hϕ s).tsupport ⊆ s.tsupport := by
  rw [tsupport_def, tsupport_def]
  apply closure_mono
  intro x hx
  simp only [mem_ofPred_eq, mapLinearMap_apply] at hx ⊢
  exact fun h ↦ hx (by simp [h])

/-- Injective fibre maps preserve the exact closed support, not merely its containment. -/
theorem tsupport_mapLinearMap (s : Cₛ^n⟮I; F, V⟯)
    (h : ∀ x, Function.Injective (ϕ x)) :
    (mapLinearMap ϕ hϕ s).tsupport = s.tsupport := by
  rw [tsupport_def, tsupport_def]
  congr 1
  ext x
  simp [LinearMap.map_eq_zero_iff _ (h x)]

/-- Smooth fibrewise linear transport preserves any prescribed support bound. -/
theorem mapLinearMap_mem_supportedIn {K : Set M} {s : Cₛ^n⟮I; F, V⟯}
    (hs : s ∈ supportedIn I F n V K) :
    mapLinearMap ϕ hϕ s ∈ supportedIn I G n W K :=
  mem_supportedIn.2 <| (tsupport_mapLinearMap_subset ϕ hϕ s).trans (mem_supportedIn.1 hs)

/-- Transport on the submodules of sections supported in a prescribed set. -/
def mapSupportedIn (K : Set M) : supportedIn I F n V K →ₗ[𝕜]
    supportedIn I G n W K :=
  (mapLinearMap ϕ hϕ).restrict fun _ hs ↦ mapLinearMap_mem_supportedIn ϕ hϕ hs

/-- Forgetting the fixed support recovers unrestricted transport. -/
@[simp]
theorem coe_mapSupportedIn (K : Set M) (s : supportedIn I F n V K) :
    (mapSupportedIn ϕ hϕ K s : Cₛ^n⟮I; G, W⟯) = mapLinearMap ϕ hϕ s.val := (rfl)

/-- Smooth fibrewise linear transport preserves compact support. -/
theorem mapLinearMap_mem_compactlySupported {s : Cₛ^n⟮I; F, V⟯}
    (hs : s ∈ compactlySupported I F n V) :
    mapLinearMap ϕ hϕ s ∈ compactlySupported I G n W :=
  mem_compactlySupported.2 <| (mem_compactlySupported.1 hs).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_mapLinearMap_subset ϕ hϕ s)

/-- Transport on the submodules of compactly supported sections. -/
def mapCompactlySupported : compactlySupported I F n V →ₗ[𝕜]
    compactlySupported I G n W :=
  (mapLinearMap ϕ hϕ).restrict fun _ hs ↦ mapLinearMap_mem_compactlySupported ϕ hϕ hs

/-- Forgetting compact support recovers unrestricted transport. -/
@[simp]
theorem coe_mapCompactlySupported (s : compactlySupported I F n V) :
    (mapCompactlySupported ϕ hϕ s : Cₛ^n⟮I; G, W⟯) = mapLinearMap ϕ hϕ s.val := (rfl)

/-- Transport commutes with multiplication by a smooth scalar function. -/
@[simp]
theorem mapLinearMap_smul_function (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) :
    mapLinearMap ϕ hϕ (f • s) = f • mapLinearMap ϕ hϕ s := by
  ext x
  simp

/-- Pointwise injectivity of a bundle map implies injectivity on smooth sections. -/
theorem mapLinearMap_injective (h : ∀ x, Function.Injective (ϕ x)) :
    Function.Injective (mapLinearMap ϕ hϕ) := by
  intro s t hst
  ext x
  exact h x (DFunLike.congr_fun hst x)

/-- The identity bundle map acts identically on sections. -/
@[simp]
theorem mapLinearMap_id :
    mapLinearMap (fun _ ↦ LinearMap.id : ∀ x, V x →ₗ[𝕜] V x) contMDiff_id =
      LinearMap.id (R := 𝕜) (M := Cₛ^n⟮I; F, V⟯) := by
  ext s x
  rfl

section Composition

variable {J : Type*} [NormedAddCommGroup J] [NormedSpace 𝕜 J] {Z : M → Type*}
  [∀ x, AddCommGroup (Z x)] [∀ x, Module 𝕜 (Z x)] [∀ x, TopologicalSpace (Z x)]
  [TopologicalSpace (TotalSpace J Z)] [FiberBundle J Z] [VectorBundle 𝕜 J Z]
  (ψ : ∀ x, W x →ₗ[𝕜] Z x)
  (hψ : ContMDiff (I.prod 𝓘(𝕜, G)) (I.prod 𝓘(𝕜, J)) n
    (fun p : TotalSpace G W ↦ (⟨p.proj, ψ p.proj p.2⟩ : TotalSpace J Z)))

/-- Composition of bundle maps induces composition of the section maps. -/
theorem mapLinearMap_comp :
    mapLinearMap (fun x ↦ (ψ x).comp (ϕ x)) (hψ.comp hϕ) =
      (mapLinearMap ψ hψ).comp (mapLinearMap ϕ hϕ) := by
  ext s x
  rfl

end Composition

section Equivalence

variable (e : ∀ x, V x ≃ₗ[𝕜] W x)
  (he : ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, G)) n
    (fun p : TotalSpace F V ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace G W)))
  (he' : ContMDiff (I.prod 𝓘(𝕜, G)) (I.prod 𝓘(𝕜, F)) n
    (fun p : TotalSpace G W ↦ (⟨p.proj, (e p.proj).symm p.2⟩ : TotalSpace F V)))

/-- Smooth fibrewise linear equivalences with smooth inverse transport smooth sections. -/
def mapEquiv : Cₛ^n⟮I; F, V⟯ ≃ₗ[𝕜] Cₛ^n⟮I; G, W⟯ :=
  { mapLinearMap (fun x ↦ (e x).toLinearMap) he with
    invFun := mapLinearMap (fun x ↦ (e x).symm.toLinearMap) he'
    left_inv := fun s ↦ by ext x; simp
    right_inv := fun s ↦ by ext x; simp }

/-- The linear map underlying section equivalence is fibrewise linear transport. -/
@[simp]
theorem mapEquiv_toLinearMap :
    (mapEquiv e he he').toLinearMap = mapLinearMap (fun x ↦ (e x).toLinearMap) he := (rfl)

/-- The induced section equivalence acts pointwise. -/
@[simp]
theorem mapEquiv_apply (s : Cₛ^n⟮I; F, V⟯) (x : M) :
    mapEquiv e he he' s x = e x (s x) := (rfl)

/-- Inverting the fibre equivalences inverts their section transport. -/
@[simp]
theorem mapEquiv_symm :
    (mapEquiv e he he').symm = mapEquiv (fun x ↦ (e x).symm) he' (by simpa using he) := by
  ext s x
  rfl

/-- Identity fibre equivalences induce the identity section equivalence. -/
@[simp]
theorem mapEquiv_refl :
    mapEquiv (fun x ↦ LinearEquiv.refl 𝕜 (V x)) contMDiff_id contMDiff_id =
      LinearEquiv.refl 𝕜 Cₛ^n⟮I; F, V⟯ := by
  ext s x
  rfl

section Composition

variable {J : Type*} [NormedAddCommGroup J] [NormedSpace 𝕜 J] {Z : M → Type*}
  [∀ x, AddCommGroup (Z x)] [∀ x, Module 𝕜 (Z x)] [∀ x, TopologicalSpace (Z x)]
  [TopologicalSpace (TotalSpace J Z)] [FiberBundle J Z] [VectorBundle 𝕜 J Z]
  (f : ∀ x, W x ≃ₗ[𝕜] Z x)
  (hf : ContMDiff (I.prod 𝓘(𝕜, G)) (I.prod 𝓘(𝕜, J)) n
    (fun p : TotalSpace G W ↦ (⟨p.proj, f p.proj p.2⟩ : TotalSpace J Z)))
  (hf' : ContMDiff (I.prod 𝓘(𝕜, J)) (I.prod 𝓘(𝕜, G)) n
    (fun p : TotalSpace J Z ↦ (⟨p.proj, (f p.proj).symm p.2⟩ : TotalSpace G W)))

/-- Composition of fibre equivalences induces composition of section equivalences. -/
theorem mapEquiv_trans :
    mapEquiv (fun x ↦ (e x).trans (f x)) (hf.comp he) (he'.comp hf') =
      (mapEquiv e he he').trans (mapEquiv f hf hf') := by
  ext s x
  rfl

end Composition

/-- A smooth bundle equivalence preserves closed support exactly. -/
@[simp]
theorem tsupport_mapEquiv (s : Cₛ^n⟮I; F, V⟯) :
    (mapEquiv e he he' s).tsupport = s.tsupport :=
  tsupport_mapLinearMap (fun x ↦ (e x).toLinearMap) he s (fun x ↦ (e x).injective)

/-- Transport identifies the fixed-support submodules for every supporting set. -/
theorem map_supportedIn (K : Set M) :
    (supportedIn I F n V K).map (mapEquiv e he he').toLinearMap =
      supportedIn I G n W K := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact mapLinearMap_mem_supportedIn (fun x ↦ (e x).toLinearMap) he hs
  · intro ht
    refine ⟨(mapEquiv e he he').symm t, ?_, (mapEquiv e he he').apply_symm_apply t⟩
    apply mem_supportedIn.2
    simpa only [mapEquiv_symm, tsupport_mapEquiv] using mem_supportedIn.1 ht

/-- The support-preserving equivalence on any fixed-support stage. -/
def mapSupportedInEquiv (K : Set M) :
    supportedIn I F n V K ≃ₗ[𝕜] supportedIn I G n W K :=
  (mapEquiv e he he').ofSubmodules _ _ (map_supportedIn e he he' K)

/-- Fixed-support equivalence has the same underlying linear map as transport. -/
@[simp]
theorem mapSupportedInEquiv_toLinearMap (K : Set M) :
    (mapSupportedInEquiv e he he' K).toLinearMap =
      mapSupportedIn (fun x ↦ (e x).toLinearMap) he K := (rfl)

/-- Forgetting the fixed support recovers the unrestricted equivalence. -/
@[simp]
theorem coe_mapSupportedInEquiv (K : Set M) (s : supportedIn I F n V K) :
    (mapSupportedInEquiv e he he' K s : Cₛ^n⟮I; G, W⟯) = mapEquiv e he he' s.val := (rfl)

/-- Forgetting the fixed support also commutes with inverse transport. -/
@[simp]
theorem coe_mapSupportedInEquiv_symm (K : Set M) (s : supportedIn I G n W K) :
    ((mapSupportedInEquiv e he he' K).symm s : Cₛ^n⟮I; F, V⟯) =
      (mapEquiv e he he').symm s.val := (rfl)

/-- Transport identifies the compact-support submodules. -/
theorem map_compactlySupported :
    (compactlySupported I F n V).map (mapEquiv e he he').toLinearMap =
      compactlySupported I G n W := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact mapLinearMap_mem_compactlySupported (fun x ↦ (e x).toLinearMap) he hs
  · intro ht
    refine ⟨(mapEquiv e he he').symm t, ?_, (mapEquiv e he he').apply_symm_apply t⟩
    apply mem_compactlySupported.2
    simpa only [mapEquiv_symm, tsupport_mapEquiv] using mem_compactlySupported.1 ht

/-- The induced linear equivalence on compactly supported smooth sections. -/
def mapCompactlySupportedEquiv :
    compactlySupported I F n V ≃ₗ[𝕜] compactlySupported I G n W :=
  (mapEquiv e he he').ofSubmodules _ _ (map_compactlySupported e he he')

/-- Compact-support equivalence has the same underlying linear map as transport. -/
@[simp]
theorem mapCompactlySupportedEquiv_toLinearMap :
    (mapCompactlySupportedEquiv e he he').toLinearMap =
      mapCompactlySupported (fun x ↦ (e x).toLinearMap) he := (rfl)

/-- Forgetting compact support recovers the unrestricted equivalence. -/
@[simp]
theorem coe_mapCompactlySupportedEquiv (s : compactlySupported I F n V) :
    (mapCompactlySupportedEquiv e he he' s : Cₛ^n⟮I; G, W⟯) = mapEquiv e he he' s.val := (rfl)

/-- Forgetting compact support also commutes with inverse transport. -/
@[simp]
theorem coe_mapCompactlySupportedEquiv_symm (s : compactlySupported I G n W) :
    ((mapCompactlySupportedEquiv e he he').symm s : Cₛ^n⟮I; F, V⟯) =
      (mapEquiv e he he').symm s.val := (rfl)

end Equivalence

end ContMDiffSection
