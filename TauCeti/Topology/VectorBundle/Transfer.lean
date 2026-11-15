/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Transporting topological vector bundles along fibrewise continuous linear equivalences

Given `E : B → Type*` with model fibre `F` over `𝕜` and continuous linear equivalences
`e : ∀ b : B, E' b ≃L[𝕜] E b`, any topology on `TotalSpace F E'` making `p ↦ ⟨p.proj, e p.proj p.2⟩`
inducing upgrades to a homeomorphism `TauCeti.totalSpaceHomeomorphOfContinuousLinearEquiv`, pulls
back trivializations via `Bundle.Trivialization.compContinuousLinearEquiv`, and transfers
`FiberBundle.ofContinuousLinearEquiv` and `VectorBundle.ofContinuousLinearEquiv`.
`TauCeti.totalSpaceInduced` supplies the canonical induced total-space topology.
-/

public section

noncomputable section

open Bundle Set Topology

section TotalSpace

variable {B 𝕜 : Type*} [Semiring 𝕜] (F : Type*)
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)] [∀ b, TopologicalSpace (E' b)]

namespace TauCeti

/-- The total-space topology on `TotalSpace F E'` induced from `TotalSpace F E` along `e`. -/
@[expose, instance_reducible]
def totalSpaceInduced (e : ∀ b : B, E' b ≃L[𝕜] E b) : TopologicalSpace (TotalSpace F E') :=
  TopologicalSpace.induced
    (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)) inferInstance

/-- A family of continuous linear equivalences inducing the total-space topology defines a
homeomorphism `TotalSpace F E' ≃ₜ TotalSpace F E` over `B`. -/
def totalSpaceHomeomorphOfContinuousLinearEquiv [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    TotalSpace F E' ≃ₜ TotalSpace F E :=
  ({ toFun := fun p ↦ ⟨p.proj, e p.proj p.2⟩
     invFun := fun p ↦ ⟨p.proj, (e p.proj).symm p.2⟩
     left_inv := fun p ↦ by cases p; simp
     right_inv := fun p ↦ by cases p; simp } :
    TotalSpace F E' ≃ TotalSpace F E).toHomeomorphOfIsInducing h_ind

@[simp] theorem totalSpaceHomeomorphOfContinuousLinearEquiv_apply
    [TopologicalSpace (TotalSpace F E')] (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (p : TotalSpace F E') :
    totalSpaceHomeomorphOfContinuousLinearEquiv F e h_ind p = ⟨p.proj, e p.proj p.2⟩ := (rfl)

@[simp] theorem totalSpaceHomeomorphOfContinuousLinearEquiv_symm_apply
    [TopologicalSpace (TotalSpace F E')] (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (p : TotalSpace F E) :
    (totalSpaceHomeomorphOfContinuousLinearEquiv F e h_ind).symm p =
      ⟨p.proj, (e p.proj).symm p.2⟩ := (rfl)

end TauCeti

end TotalSpace

namespace Bundle.Trivialization

variable {B : Type*} [TopologicalSpace B] {𝕜 : Type*} [Semiring 𝕜] {F : Type*} [TopologicalSpace F]
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
  [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]

/-- Pull back a local trivialization of `E` along `e : ∀ b, E' b ≃L[𝕜] E b` inducing the
total-space topology of `E'`. -/
def compContinuousLinearEquiv (t : Trivialization F (π F E)) (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    Trivialization F (π F E') :=
  let h := TauCeti.totalSpaceHomeomorphOfContinuousLinearEquiv F e h_ind
  { t.compHomeomorph h with
    source_eq := by
      ext p; simp only [Trivialization.compHomeomorph, Homeomorph.transOpenPartialHomeomorph_source,
        mem_preimage, t.mem_source, h, TauCeti.totalSpaceHomeomorphOfContinuousLinearEquiv_apply]
    proj_toFun := fun p hp ↦ by
      simpa only [Function.comp_apply, h,
        TauCeti.totalSpaceHomeomorphOfContinuousLinearEquiv_apply] using
        (t.compHomeomorph h).proj_toFun p hp }

@[simp] theorem compContinuousLinearEquiv_apply (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (p : TotalSpace F E') : t.compContinuousLinearEquiv e h_ind p = t ⟨p.proj, e p.proj p.2⟩ :=
  (rfl)

@[simp] theorem compContinuousLinearEquiv_baseSet (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    (t.compContinuousLinearEquiv e h_ind).baseSet = t.baseSet := (rfl)

@[simp] theorem compContinuousLinearEquiv_symm_apply (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (p : B × F) :
    (t.compContinuousLinearEquiv e h_ind).toOpenPartialHomeomorph.symm p =
      (TauCeti.totalSpaceHomeomorphOfContinuousLinearEquiv F e h_ind).symm
        (t.toOpenPartialHomeomorph.symm p) := (rfl)

instance instIsLinearCompContinuousLinearEquiv [AddCommMonoid F] [Module 𝕜 F]
    (t : Trivialization F (π F E)) [t.IsLinear 𝕜] (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    (t.compContinuousLinearEquiv e h_ind).IsLinear 𝕜 where
  linear b hb := ((t.linear 𝕜 hb).mk'.comp (e b).toLinearMap).isLinear

@[simp] theorem coordChangeL_compContinuousLinearEquiv [AddCommMonoid F] [Module 𝕜 F]
    (t₁ t₂ : Trivialization F (π F E)) [t₁.IsLinear 𝕜] [t₂.IsLinear 𝕜]
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (b : B) :
    (t₁.compContinuousLinearEquiv e h_ind).coordChangeL 𝕜
      (t₂.compContinuousLinearEquiv e h_ind) b = t₁.coordChangeL 𝕜 t₂ b := by
  ext v
  by_cases hb : b ∈ t₁.baseSet ∩ t₂.baseSet
  · rw [Trivialization.coordChangeL_apply' _ _ (by simpa using hb),
      Trivialization.coordChangeL_apply' _ _ hb, compContinuousLinearEquiv_symm_apply,
      compContinuousLinearEquiv_apply,
      ← TauCeti.totalSpaceHomeomorphOfContinuousLinearEquiv_apply F e h_ind,
      Homeomorph.apply_symm_apply]
  · simp [Trivialization.coordChangeL, hb]

end Bundle.Trivialization

section Transfer

/-- Transfer a `FiberBundle F E` structure to `E'` along `e : ∀ b, E' b ≃L[𝕜] E b`. -/
@[instance_reducible]
def FiberBundle.ofContinuousLinearEquiv {B : Type*} [TopologicalSpace B] {𝕜 : Type*} [Semiring 𝕜]
    (F : Type*) [TopologicalSpace F] {E : B → Type*} [∀ b, AddCommMonoid (E b)]
    [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    FiberBundle F E' where
  totalSpaceMk_isInducing' b := h_ind.of_comp_iff.mp <|
    (FiberBundle.totalSpaceMk_isInducing F E b).comp (e b).toHomeomorph.isInducing
  trivializationAtlas' :=
    (fun t : Trivialization F (π F E) ↦ t.compContinuousLinearEquiv e h_ind) ''
      trivializationAtlas F E
  trivializationAt' b := (trivializationAt F E b).compContinuousLinearEquiv e h_ind
  mem_baseSet_trivializationAt' := mem_baseSet_trivializationAt F E
  trivialization_mem_atlas' b := ⟨trivializationAt F E b, trivialization_mem_atlas F E b, rfl⟩

/-- Transfer a `VectorBundle 𝕜 F E` structure to `E'` along `e : ∀ b, E' b ≃L[𝕜] E b`. -/
theorem VectorBundle.ofContinuousLinearEquiv {B : Type*} [TopologicalSpace B]
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    letI := FiberBundle.ofContinuousLinearEquiv F e h_ind
    VectorBundle 𝕜 F E' := by
  let := FiberBundle.ofContinuousLinearEquiv F e h_ind
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · rintro _ ⟨t, ht, rfl⟩; have : MemTrivializationAtlas t := ⟨ht⟩; infer_instance
  · rintro _ _ ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, rfl⟩
    have : MemTrivializationAtlas t₁ := ⟨ht₁⟩; have : MemTrivializationAtlas t₂ := ⟨ht₂⟩
    simpa only [Trivialization.coordChangeL_compContinuousLinearEquiv,
      Trivialization.compContinuousLinearEquiv_baseSet] using continuousOn_coordChange 𝕜 t₁ t₂

/-- Any family of topological spaces over an empty base is vacuously a `FiberBundle`. -/
@[instance_reducible]
def FiberBundle.ofIsEmpty {B : Type*} [TopologicalSpace B] [IsEmpty B] (F : Type*)
    [TopologicalSpace F] (E : B → Type*) [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] : FiberBundle F E where
  totalSpaceMk_isInducing' := isEmptyElim
  trivializationAtlas' := ∅
  trivializationAt' := isEmptyElim
  mem_baseSet_trivializationAt' := isEmptyElim
  trivialization_mem_atlas' := isEmptyElim

/-- Any family of topological modules over an empty base is vacuously a `VectorBundle`. -/
theorem VectorBundle.ofIsEmpty {B : Type*} [TopologicalSpace B] [IsEmpty B] (𝕜 : Type*)
    [NontriviallyNormedField 𝕜] (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (E : B → Type*) [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] :
    letI := FiberBundle.ofIsEmpty F E
    VectorBundle 𝕜 F E := by
  let := FiberBundle.ofIsEmpty F E
  exact { trivialization_linear' := fun _ ⟨h⟩ ↦ False.elim h
          continuousOn_coordChange' := fun _ _ ⟨h⟩ _ ↦ False.elim h }

end Transfer

end
