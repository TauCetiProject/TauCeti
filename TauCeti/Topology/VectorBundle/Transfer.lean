/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Transporting fibre and vector bundles along fibrewise equivalences

To change the fibre family of a topological bundle—for instance, when shrinking coordinate fibres to
a smaller universe or lifting fibres across universes on rank strata—one needs to transport
existing `[FiberBundle F E]` and `[VectorBundle 𝕜 F E]` structures to an isomorphic family `E'`.

* On the topological layer, `TauCeti.totalSpaceInduced` equips `TotalSpace F E'` with the topology
  pulled back along any fibrewise map `e : ∀ b : B, E' b → E b`
  (`TauCeti.isInducing_totalSpaceInduced`). When `e : ∀ b : B, E' b ≃ₜ E b` is a family of
  homeomorphisms inducing the topology on `TotalSpace F E'`, it upgrades to a total-space
  homeomorphism `TauCeti.totalSpaceHomeomorphOfHomeomorph`, pulls back local trivializations via
  `Bundle.Trivialization.compFiberHomeomorph`, and transports `[FiberBundle F E]` to
  `FiberBundle.ofHomeomorph`.
* On the linear layer, specializing `e` to fibrewise continuous linear equivalences
  `e : ∀ b : B, E' b ≃L[𝕜] E b` yields `TauCeti.totalSpaceHomeomorphOfContinuousLinearEquiv`,
  `Bundle.Trivialization.compContinuousLinearEquiv` (preserving linearity and transition operators
  via `Bundle.Trivialization.coordChangeL_compContinuousLinearEquiv`),
  `FiberBundle.ofContinuousLinearEquiv`, and `VectorBundle.ofContinuousLinearEquiv`.

The trivialization pullback adapts Mathlib's `Bundle.Trivialization.compHomeomorph` and the prior
bundle-transport pattern in
`TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Euclidean` (for empty base
strata see `TauCeti.Topology.FiberBundle.IsEmpty` and `TauCeti.Topology.VectorBundle.IsEmpty`).
-/

public section

noncomputable section

open Bundle Set Topology

section TotalSpace

namespace TauCeti

/-- The total-space topology on `TotalSpace F E'` induced from `TotalSpace F E` along a fibrewise
map `e : ∀ b : B, E' b → E b`. -/
@[instance_reducible]
def totalSpaceInduced {B : Type*} (F : Type*) {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
    {E' : B → Type*} (e : ∀ b : B, E' b → E b) : TopologicalSpace (TotalSpace F E') :=
  TopologicalSpace.induced
    (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)) inferInstance

/-- Equipping `TotalSpace F E'` with `TauCeti.totalSpaceInduced F e` makes the total-space map
`p ↦ ⟨p.proj, e p.proj p.2⟩` inducing. -/
theorem isInducing_totalSpaceInduced {B : Type*} (F : Type*) {E : B → Type*}
    [TopologicalSpace (TotalSpace F E)] {E' : B → Type*} (e : ∀ b : B, E' b → E b) :
    letI := totalSpaceInduced F e
    IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)) :=
  letI := totalSpaceInduced F e; ⟨rfl⟩

section Homeomorph

variable {B : Type*} (F : Type*) {E : B → Type*} [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace F E)] {E' : B → Type*} [∀ b, TopologicalSpace (E' b)]
  [TopologicalSpace (TotalSpace F E')]

/-- A family of fibrewise homeomorphisms inducing the total-space topology defines a homeomorphism
`TotalSpace F E' ≃ₜ TotalSpace F E` over `B`. -/
def totalSpaceHomeomorphOfHomeomorph (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    TotalSpace F E' ≃ₜ TotalSpace F E :=
  ({ toFun := fun p ↦ ⟨p.proj, e p.proj p.2⟩
     invFun := fun p ↦ ⟨p.proj, (e p.proj).symm p.2⟩
     left_inv := fun p ↦ by cases p; simp
     right_inv := fun p ↦ by cases p; simp } :
    TotalSpace F E' ≃ TotalSpace F E).toHomeomorphOfIsInducing h_ind

@[simp] theorem totalSpaceHomeomorphOfHomeomorph_apply (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (p : TotalSpace F E') :
    totalSpaceHomeomorphOfHomeomorph F e h_ind p = ⟨p.proj, e p.proj p.2⟩ := (rfl)

@[simp] theorem totalSpaceHomeomorphOfHomeomorph_symm_apply (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (p : TotalSpace F E) :
    (totalSpaceHomeomorphOfHomeomorph F e h_ind).symm p = ⟨p.proj, (e p.proj).symm p.2⟩ := (rfl)

end Homeomorph

section ContinuousLinearEquiv

variable {B 𝕜 : Type*} [Semiring 𝕜] (F : Type*)
  {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
  [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]

/-- A family of continuous linear equivalences inducing the total-space topology defines a
homeomorphism `TotalSpace F E' ≃ₜ TotalSpace F E` over `B`. -/
def totalSpaceHomeomorphOfContinuousLinearEquiv (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    TotalSpace F E' ≃ₜ TotalSpace F E :=
  totalSpaceHomeomorphOfHomeomorph F (fun b ↦ (e b).toHomeomorph) h_ind

@[simp] theorem totalSpaceHomeomorphOfContinuousLinearEquiv_apply (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (p : TotalSpace F E') :
    totalSpaceHomeomorphOfContinuousLinearEquiv F e h_ind p = ⟨p.proj, e p.proj p.2⟩ := (rfl)

@[simp] theorem totalSpaceHomeomorphOfContinuousLinearEquiv_symm_apply
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (p : TotalSpace F E) :
    (totalSpaceHomeomorphOfContinuousLinearEquiv F e h_ind).symm p =
      ⟨p.proj, (e p.proj).symm p.2⟩ := (rfl)

end ContinuousLinearEquiv

end TauCeti

end TotalSpace

namespace Bundle.Trivialization

section Homeomorph

variable {B : Type*} [TopologicalSpace B] {F : Type*} [TopologicalSpace F]
  {E : B → Type*} [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  {E' : B → Type*} [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]

/-- Pull back a local trivialization of `E` along fibrewise homeomorphisms `e : ∀ b, E' b ≃ₜ E b`
inducing the total-space topology on `TotalSpace F E'`. -/
def compFiberHomeomorph (t : Trivialization F (π F E)) (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    Trivialization F (π F E') :=
  let h := TauCeti.totalSpaceHomeomorphOfHomeomorph F e h_ind
  { t.compHomeomorph h with
    source_eq := by
      ext p; simp only [Trivialization.compHomeomorph, Homeomorph.transOpenPartialHomeomorph_source,
        mem_preimage, t.mem_source, h, TauCeti.totalSpaceHomeomorphOfHomeomorph_apply]
    proj_toFun := fun p hp ↦ by
      simpa only [Function.comp_apply, h,
        TauCeti.totalSpaceHomeomorphOfHomeomorph_apply] using
        (t.compHomeomorph h).proj_toFun p hp }

@[simp] theorem compFiberHomeomorph_apply (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (p : TotalSpace F E') : t.compFiberHomeomorph e h_ind p = t ⟨p.proj, e p.proj p.2⟩ :=
  (rfl)

@[simp] theorem compFiberHomeomorph_baseSet (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    (t.compFiberHomeomorph e h_ind).baseSet = t.baseSet := (rfl)

@[simp] theorem compFiberHomeomorph_symm_apply (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (p : B × F) :
    (t.compFiberHomeomorph e h_ind).toOpenPartialHomeomorph.symm p =
      (TauCeti.totalSpaceHomeomorphOfHomeomorph F e h_ind).symm
        (t.toOpenPartialHomeomorph.symm p) := (rfl)

/-- On `t.baseSet`, the fibrewise inverse of `t.compFiberHomeomorph e h_ind` applies `(e b).symm`
to `t.symm b v`. -/
@[simp] theorem compFiberHomeomorph_symm [∀ b, Nonempty (E b)] [∀ b, Nonempty (E' b)]
    (t : Trivialization F (π F E)) (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    {b : B} (hb : b ∈ t.baseSet) (v : F) :
    (t.compFiberHomeomorph e h_ind).symm b v = (e b).symm (t.symm b v) :=
  (TotalSpace.mk_inj (F := F)).mp <| ((t.compFiberHomeomorph e h_ind).mk_symm hb v).trans <| by
    rw [compFiberHomeomorph_symm_apply, ← t.mk_symm hb v,
      TauCeti.totalSpaceHomeomorphOfHomeomorph_symm_apply]

end Homeomorph

section ContinuousLinearEquiv

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
  t.compFiberHomeomorph (fun b ↦ (e b).toHomeomorph) h_ind

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

/-- On `t.baseSet`, the fibrewise inverse of `t.compContinuousLinearEquiv e h_ind` applies
`(e b).symm` to `t.symm b v`. -/
@[simp] theorem compContinuousLinearEquiv_symm (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    {b : B} (hb : b ∈ t.baseSet) (v : F) :
    (t.compContinuousLinearEquiv e h_ind).symm b v = (e b).symm (t.symm b v) :=
  t.compFiberHomeomorph_symm (fun b ↦ (e b).toHomeomorph) h_ind hb v

/-- Pulling back a `𝕜`-linear trivialization along fibrewise continuous linear equivalences yields
a `𝕜`-linear trivialization. -/
instance instIsLinearCompContinuousLinearEquiv [AddCommMonoid F] [Module 𝕜 F]
    (t : Trivialization F (π F E)) [t.IsLinear 𝕜] (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    (t.compContinuousLinearEquiv e h_ind).IsLinear 𝕜 where
  linear b hb := ((t.linear 𝕜 hb).mk'.comp (e b).toLinearMap).isLinear

/-- Pulling back two linear trivializations along the same family of fibrewise continuous linear
equivalences leaves their coordinate-change operator `coordChangeL` unchanged. -/
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

end ContinuousLinearEquiv

end Bundle.Trivialization

section Transfer

/-- Transfer a `FiberBundle F E` structure to `E'` along fibrewise homeomorphisms
`e : ∀ b, E' b ≃ₜ E b` inducing the total-space topology on `TotalSpace F E'`. -/
@[instance_reducible]
def FiberBundle.ofHomeomorph {B : Type*} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
    {E : B → Type*} [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] {E' : B → Type*} [∀ b, TopologicalSpace (E' b)]
    [TopologicalSpace (TotalSpace F E')] (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    FiberBundle F E' where
  totalSpaceMk_isInducing' b := h_ind.of_comp_iff.mp <|
    (FiberBundle.totalSpaceMk_isInducing F E b).comp (e b).isInducing
  trivializationAtlas' :=
    (fun t : Trivialization F (π F E) ↦ t.compFiberHomeomorph e h_ind) '' trivializationAtlas F E
  trivializationAt' b := (trivializationAt F E b).compFiberHomeomorph e h_ind
  mem_baseSet_trivializationAt' := mem_baseSet_trivializationAt F E
  trivialization_mem_atlas' b := ⟨trivializationAt F E b, trivialization_mem_atlas F E b, rfl⟩

/-- Under `FiberBundle.ofHomeomorph`, the preferred trivialization at `b` is pulled back from
`trivializationAt F E b` along `e`. -/
@[simp] theorem FiberBundle.trivializationAt_ofHomeomorph {B : Type*} [TopologicalSpace B]
    (F : Type*) [TopologicalSpace F] {E : B → Type*} [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] {E' : B → Type*}
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (b : B) :
    letI := FiberBundle.ofHomeomorph F e h_ind
    trivializationAt F E' b = (trivializationAt F E b).compFiberHomeomorph e h_ind := (rfl)

/-- Under `FiberBundle.ofHomeomorph`, the trivialization atlas is the image of
`trivializationAtlas F E` under `Trivialization.compFiberHomeomorph`. -/
@[simp] theorem FiberBundle.trivializationAtlas_ofHomeomorph {B : Type*} [TopologicalSpace B]
    (F : Type*) [TopologicalSpace F] {E : B → Type*} [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] {E' : B → Type*}
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    letI := FiberBundle.ofHomeomorph F e h_ind
    trivializationAtlas F E' =
      (fun t : Trivialization F (π F E) ↦ t.compFiberHomeomorph e h_ind) ''
        trivializationAtlas F E := (rfl)

/-- Transfer a `FiberBundle F E` structure to `E'` along `e : ∀ b, E' b ≃L[𝕜] E b` inducing the
total-space topology on `TotalSpace F E'`. -/
@[instance_reducible]
def FiberBundle.ofContinuousLinearEquiv {B : Type*} [TopologicalSpace B] {𝕜 : Type*} [Semiring 𝕜]
    (F : Type*) [TopologicalSpace F] {E : B → Type*} [∀ b, AddCommMonoid (E b)]
    [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
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
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E)))
    (b : B) :
    letI := FiberBundle.ofContinuousLinearEquiv F e h_ind
    trivializationAt F E' b = (trivializationAt F E b).compContinuousLinearEquiv e h_ind := (rfl)

/-- Under `FiberBundle.ofContinuousLinearEquiv`, the trivialization atlas is the image of
`trivializationAtlas F E` under `Trivialization.compContinuousLinearEquiv`. -/
@[simp] theorem FiberBundle.trivializationAtlas_ofContinuousLinearEquiv {B : Type*}
    [TopologicalSpace B] {𝕜 : Type*} [Semiring 𝕜] (F : Type*) [TopologicalSpace F]
    {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
    {E' : B → Type*} [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (TotalSpace F E')]
    (e : ∀ b : B, E' b ≃L[𝕜] E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.2⟩ : TotalSpace F E))) :
    letI := FiberBundle.ofContinuousLinearEquiv F e h_ind
    trivializationAtlas F E' =
      (fun t : Trivialization F (π F E) ↦ t.compContinuousLinearEquiv e h_ind) ''
        trivializationAtlas F E := (rfl)

/-- Transfer a `VectorBundle 𝕜 F E` structure to `E'` along `e : ∀ b, E' b ≃L[𝕜] E b` inducing the
total-space topology on `TotalSpace F E'`. -/
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
  · rintro _ ⟨t, ht, rfl⟩
    have : MemTrivializationAtlas t := ⟨ht⟩
    exact Trivialization.instIsLinearCompContinuousLinearEquiv t e h_ind
  · rintro _ _ ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, rfl⟩
    have : MemTrivializationAtlas t₁ := ⟨ht₁⟩; have : MemTrivializationAtlas t₂ := ⟨ht₂⟩
    exact (continuousOn_coordChange 𝕜 t₁ t₂).congr fun b _ ↦ congrArg
      ContinuousLinearEquiv.toContinuousLinearMap
      (Trivialization.coordChangeL_compContinuousLinearEquiv t₁ t₂ e h_ind b)

end Transfer

end
