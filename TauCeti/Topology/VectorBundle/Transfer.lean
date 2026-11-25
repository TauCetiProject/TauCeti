/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Topology.FiberBundle.Transfer

/-!
# Transporting vector bundles along fibrewise continuous linear equivalences

To change the fibre family of a topological vector bundle—for instance, when shrinking coordinate
fibres to a smaller universe or lifting fibres across universes on rank strata—this module
specializes the topological fibre-bundle transport in `TauCeti.Topology.FiberBundle.Transfer` to
fibrewise continuous linear equivalences `e : ∀ b : B, E' b ≃L[𝕜] E b`:

* `TauCeti.totalSpaceHomeomorphOfContinuousLinearEquiv` upgrades `e` (assuming the total-space
  topology on `TotalSpace F E'` is induced along `e`) to a total-space homeomorphism;
* `Bundle.Trivialization.compContinuousLinearEquiv` pulls back local trivializations while
  preserving `𝕜`-linearity (`Bundle.Trivialization.instIsLinearCompContinuousLinearEquiv`) and
  leaving transition operators unchanged
  (`Bundle.Trivialization.coordChangeL_compContinuousLinearEquiv`);
* `FiberBundle.ofContinuousLinearEquiv` and `VectorBundle.ofContinuousLinearEquiv` transport
  `[FiberBundle F E]` and `[VectorBundle 𝕜 F E]` structures to `E'`.

This adapts the bundle-transport pattern in
`TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Euclidean` (for empty base
strata see `TauCeti.Topology.FiberBundle.Empty` and `TauCeti.Topology.VectorBundle.IsEmpty`).
-/

public section

noncomputable section

open Bundle Set Topology

section TotalSpace

namespace TauCeti

section ContinuousLinearEquiv

variable {B 𝕜 : Type*} [Semiring 𝕜] (F : Type*)
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
  [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]

/-- A family of continuous linear equivalences inducing the total-space topology defines a
homeomorphism `TotalSpace F E' ≃ₜ TotalSpace F E` over `B`. -/
def totalSpaceHomeomorphOfContinuousLinearEquiv (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    TotalSpace F E' ≃ₜ TotalSpace F E :=
  totalSpaceHomeomorphOfHomeomorph F (fun b ↦ (e b).toHomeomorph) h_ind

@[simp] theorem totalSpaceHomeomorphOfContinuousLinearEquiv_apply (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    (p : TotalSpace F E') :
    totalSpaceHomeomorphOfContinuousLinearEquiv F e h_ind p = ⟨p.proj, e p.proj p.snd⟩ :=
  totalSpaceHomeomorphOfHomeomorph_apply F (fun b ↦ (e b).toHomeomorph) h_ind p

@[simp] theorem totalSpaceHomeomorphOfContinuousLinearEquiv_symm_apply
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    (p : TotalSpace F E) :
    (totalSpaceHomeomorphOfContinuousLinearEquiv F e h_ind).symm p =
      ⟨p.proj, (e p.proj).symm p.snd⟩ :=
  totalSpaceHomeomorphOfHomeomorph_symm_apply F (fun b ↦ (e b).toHomeomorph) h_ind p

end ContinuousLinearEquiv

end TauCeti

end TotalSpace

namespace Bundle.Trivialization

section ContinuousLinearEquiv

variable {B : Type*} [TopologicalSpace B] {𝕜 : Type*} [Semiring 𝕜] {F : Type*} [TopologicalSpace F]
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
  [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]

/-- Pull back a local trivialization of `E` along `e : ∀ b, E' b ≃L[𝕜] E b` inducing the
total-space topology of `E'`. -/
def compContinuousLinearEquiv (t : Trivialization F (π F E)) (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    Trivialization F (π F E') :=
  t.compFiberHomeomorph (fun b ↦ (e b).toHomeomorph) h_ind

@[simp] theorem compContinuousLinearEquiv_apply (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    (p : TotalSpace F E') : t.compContinuousLinearEquiv e h_ind p = t ⟨p.proj, e p.proj p.snd⟩ :=
  t.compFiberHomeomorph_apply (fun b ↦ (e b).toHomeomorph) h_ind p

@[simp] theorem compContinuousLinearEquiv_baseSet (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    (t.compContinuousLinearEquiv e h_ind).baseSet = t.baseSet :=
  t.compFiberHomeomorph_baseSet (fun b ↦ (e b).toHomeomorph) h_ind

@[simp] theorem compContinuousLinearEquiv_symm_apply (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    (p : B × F) :
    (t.compContinuousLinearEquiv e h_ind).toOpenPartialHomeomorph.symm p =
      (TauCeti.totalSpaceHomeomorphOfContinuousLinearEquiv F e h_ind).symm
        (t.toOpenPartialHomeomorph.symm p) :=
  t.compFiberHomeomorph_symm_apply (fun b ↦ (e b).toHomeomorph) h_ind p

/-- On `t.baseSet`, the fibrewise inverse of `t.compContinuousLinearEquiv e h_ind` applies
`(e b).symm` to `t.symm b v`. -/
@[simp] theorem compContinuousLinearEquiv_symm (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    {b : B} (hb : b ∈ t.baseSet) (v : F) :
    (t.compContinuousLinearEquiv e h_ind).symm b v = (e b).symm (t.symm b v) :=
  t.compFiberHomeomorph_symm (fun b ↦ (e b).toHomeomorph) h_ind hb v

/-- Pulling back a `𝕜`-linear trivialization along fibrewise continuous linear equivalences yields
a `𝕜`-linear trivialization. -/
instance instIsLinearCompContinuousLinearEquiv [AddCommMonoid F] [Module 𝕜 F]
    (t : Trivialization F (π F E)) [t.IsLinear 𝕜] (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    (t.compContinuousLinearEquiv e h_ind).IsLinear 𝕜 where
  linear b hb := by
    rw [compContinuousLinearEquiv_baseSet] at hb
    refine ⟨fun x y ↦ ?_, fun c x ↦ ?_⟩
    · simp only [compContinuousLinearEquiv_apply, map_add, (t.linear 𝕜 hb).map_add]
    · simp only [compContinuousLinearEquiv_apply, map_smul, (t.linear 𝕜 hb).map_smul]

/-- Pulling back two linear trivializations along the same family of fibrewise continuous linear
equivalences leaves their coordinate-change operator `coordChangeL` unchanged. -/
@[simp] theorem coordChangeL_compContinuousLinearEquiv [AddCommMonoid F] [Module 𝕜 F]
    (t₁ t₂ : Trivialization F (π F E)) [t₁.IsLinear 𝕜] [t₂.IsLinear 𝕜]
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    (b : B) :
    (t₁.compContinuousLinearEquiv e h_ind).coordChangeL 𝕜
      (t₂.compContinuousLinearEquiv e h_ind) b = t₁.coordChangeL 𝕜 t₂ b := by
  ext v
  by_cases hb : b ∈ t₁.baseSet ∩ t₂.baseSet
  · simp [Trivialization.coordChangeL_apply', hb]
  · simp [Trivialization.coordChangeL, hb]

end ContinuousLinearEquiv

end Bundle.Trivialization

section Transfer

/-- Transfer a `FiberBundle F E` structure to `E'` along `e : ∀ b, E' b ≃L[𝕜] E b` inducing the
total-space topology on `TotalSpace F E'`. -/
@[instance_reducible]
def FiberBundle.ofContinuousLinearEquiv {B : Type*} [TopologicalSpace B] {𝕜 : Type*} [Semiring 𝕜]
    (F : Type*) [TopologicalSpace F] {E : B → Type*} [∀ b, AddCommMonoid (E b)]
    [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    FiberBundle F E' :=
  FiberBundle.ofHomeomorph F (fun b ↦ (e b).toHomeomorph) h_ind

/-- Under `FiberBundle.ofContinuousLinearEquiv`, the preferred trivialization at `b` is pulled back
from `trivializationAt F E b` along `e`. -/
@[simp] theorem FiberBundle.trivializationAt_ofContinuousLinearEquiv {B : Type*}
    [TopologicalSpace B] {𝕜 : Type*} [Semiring 𝕜] (F : Type*) [TopologicalSpace F]
    {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
    {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    (b : B) :
    letI := FiberBundle.ofContinuousLinearEquiv F e h_ind
    trivializationAt F E' b = (trivializationAt F E b).compContinuousLinearEquiv e h_ind :=
  FiberBundle.trivializationAt_ofHomeomorph F (fun b ↦ (e b).toHomeomorph) h_ind b

/-- Under `FiberBundle.ofContinuousLinearEquiv`, the trivialization atlas is the image of
`trivializationAtlas F E` under `Trivialization.compContinuousLinearEquiv`. -/
@[simp] theorem FiberBundle.trivializationAtlas_ofContinuousLinearEquiv {B : Type*}
    [TopologicalSpace B] {𝕜 : Type*} [Semiring 𝕜] (F : Type*) [TopologicalSpace F]
    {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
    {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    letI := FiberBundle.ofContinuousLinearEquiv F e h_ind
    trivializationAtlas F E' =
      (fun t : Trivialization F (π F E) ↦ t.compContinuousLinearEquiv e h_ind) ''
        trivializationAtlas F E :=
  FiberBundle.trivializationAtlas_ofHomeomorph F (fun b ↦ (e b).toHomeomorph) h_ind

/-- Transfer a `VectorBundle 𝕜 F E` structure to `E'` along `e : ∀ b, E' b ≃L[𝕜] E b` inducing the
total-space topology on `TotalSpace F E'`. -/
theorem VectorBundle.ofContinuousLinearEquiv {B : Type*} [TopologicalSpace B]
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    letI := FiberBundle.ofContinuousLinearEquiv F e h_ind
    VectorBundle 𝕜 F E' := by
  let := FiberBundle.ofContinuousLinearEquiv F e h_ind
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · intro t' ht'
    have hmem := ht'.out
    rw [FiberBundle.trivializationAtlas_ofContinuousLinearEquiv] at hmem
    rcases hmem with ⟨t, ht, rfl⟩
    have : MemTrivializationAtlas t := ⟨ht⟩
    exact Trivialization.instIsLinearCompContinuousLinearEquiv t e h_ind
  · intro t₁' t₂' ht₁' ht₂'
    have hmem₁ := ht₁'.out
    have hmem₂ := ht₂'.out
    rw [FiberBundle.trivializationAtlas_ofContinuousLinearEquiv] at hmem₁ hmem₂
    rcases hmem₁ with ⟨t₁, ht₁, rfl⟩; rcases hmem₂ with ⟨t₂, ht₂, rfl⟩
    have : MemTrivializationAtlas t₁ := ⟨ht₁⟩; have : MemTrivializationAtlas t₂ := ⟨ht₂⟩
    rw [Trivialization.compContinuousLinearEquiv_baseSet,
      Trivialization.compContinuousLinearEquiv_baseSet]
    exact (continuousOn_coordChange 𝕜 t₁ t₂).congr fun b _ ↦ congrArg
      ContinuousLinearEquiv.toContinuousLinearMap
      (Trivialization.coordChangeL_compContinuousLinearEquiv t₁ t₂ e h_ind b)

end Transfer

end
