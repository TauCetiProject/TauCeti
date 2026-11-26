/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Transporting fibre bundles along fibrewise homeomorphisms

To change the fibre family of a topological bundle—for instance, when shrinking or lifting fibres
across universes on rank strata—one needs to transport an existing `[FiberBundle F E]` structure
to a fibrewise homeomorphic family `E'`.

* `TauCeti.totalSpaceInduced` equips `TotalSpace F E'` with the topology pulled back along any
  fibrewise map `e : ∀ b : B, E' b → E b` (`TauCeti.isInducing_totalSpaceInduced`).
* When `e : ∀ b : B, E' b ≃ₜ E b` is a family of fibrewise homeomorphisms inducing the topology on
  `TotalSpace F E'`, it upgrades to a total-space homeomorphism
  `TauCeti.totalSpaceHomeomorphOfHomeomorph`, pulls back local trivializations via
  `Bundle.Trivialization.compFiberHomeomorph`, and transports `[FiberBundle F E]` to
  `FiberBundle.ofHomeomorph` (with preferred trivializations and atlas given by
  `FiberBundle.trivializationAt_ofHomeomorph` and `FiberBundle.trivializationAtlas_ofHomeomorph`).

The trivialization pullback adapts Mathlib's `Bundle.Trivialization.compHomeomorph`. For the linear
specialization to `VectorBundle` see `TauCeti.Topology.VectorBundle.Transfer`, and for empty base
strata see `TauCeti.Topology.FiberBundle.Empty`.
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
    (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)) inferInstance

/-- Equipping `TotalSpace F E'` with `TauCeti.totalSpaceInduced F e` makes the total-space map
`p ↦ ⟨p.proj, e p.proj p.snd⟩` inducing. -/
theorem isInducing_totalSpaceInduced {B : Type*} (F : Type*) {E : B → Type*}
    [TopologicalSpace (TotalSpace F E)] {E' : B → Type*} (e : ∀ b : B, E' b → E b) :
    letI := totalSpaceInduced F e
    IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)) :=
  letI := totalSpaceInduced F e; ⟨rfl⟩

section Homeomorph

variable {B : Type*} (F : Type*) {E : B → Type*} [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace F E)] {E' : B → Type*} [∀ b, TopologicalSpace (E' b)]
  [TopologicalSpace (TotalSpace F E')]

/-- A family of fibrewise homeomorphisms inducing the total-space topology defines a homeomorphism
`TotalSpace F E' ≃ₜ TotalSpace F E` over `B`. -/
def totalSpaceHomeomorphOfHomeomorph (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    TotalSpace F E' ≃ₜ TotalSpace F E :=
  ({ toFun := fun p ↦ ⟨p.proj, e p.proj p.snd⟩
     invFun := fun p ↦ ⟨p.proj, (e p.proj).symm p.snd⟩
     left_inv := fun p ↦ by cases p; simp
     right_inv := fun p ↦ by cases p; simp } :
    TotalSpace F E' ≃ TotalSpace F E).toHomeomorphOfIsInducing h_ind

@[simp] theorem totalSpaceHomeomorphOfHomeomorph_apply (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    (p : TotalSpace F E') :
    totalSpaceHomeomorphOfHomeomorph F e h_ind p = ⟨p.proj, e p.proj p.snd⟩ := (rfl)

@[simp] theorem totalSpaceHomeomorphOfHomeomorph_symm_apply (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    (p : TotalSpace F E) :
    (totalSpaceHomeomorphOfHomeomorph F e h_ind).symm p = ⟨p.proj, (e p.proj).symm p.snd⟩ := (rfl)

end Homeomorph

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
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
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
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    (p : TotalSpace F E') : t.compFiberHomeomorph e h_ind p = t ⟨p.proj, e p.proj p.snd⟩ :=
  (rfl)

@[simp] theorem compFiberHomeomorph_baseSet (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    (t.compFiberHomeomorph e h_ind).baseSet = t.baseSet := (rfl)

@[simp] theorem compFiberHomeomorph_symm_apply (t : Trivialization F (π F E))
    (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    (p : B × F) :
    (t.compFiberHomeomorph e h_ind).toOpenPartialHomeomorph.symm p =
      (TauCeti.totalSpaceHomeomorphOfHomeomorph F e h_ind).symm
        (t.toOpenPartialHomeomorph.symm p) := (rfl)

/-- On `t.baseSet`, the fibrewise inverse of `t.compFiberHomeomorph e h_ind` applies `(e b).symm`
to `t.symm b v`. -/
@[simp] theorem compFiberHomeomorph_symm [∀ b, Nonempty (E b)] [∀ b, Nonempty (E' b)]
    (t : Trivialization F (π F E)) (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
    {b : B} (hb : b ∈ t.baseSet) (v : F) :
    (t.compFiberHomeomorph e h_ind).symm b v = (e b).symm (t.symm b v) :=
  (TotalSpace.mk_inj (F := F)).mp <| ((t.compFiberHomeomorph e h_ind).mk_symm hb v).trans <| by
    rw [compFiberHomeomorph_symm_apply, ← t.mk_symm hb v,
      TauCeti.totalSpaceHomeomorphOfHomeomorph_symm_apply]

end Homeomorph

end Bundle.Trivialization

section Transfer

/-- Transfer a `FiberBundle F E` structure to `E'` along fibrewise homeomorphisms
`e : ∀ b, E' b ≃ₜ E b` inducing the total-space topology on `TotalSpace F E'`. -/
@[instance_reducible]
def FiberBundle.ofHomeomorph {B : Type*} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
    {E : B → Type*} [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] {E' : B → Type*} [∀ b, TopologicalSpace (E' b)]
    [TopologicalSpace (TotalSpace F E')] (e : ∀ b : B, E' b ≃ₜ E b)
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
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
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E)))
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
    (h_ind : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, e p.proj p.snd⟩ : TotalSpace F E))) :
    letI := FiberBundle.ofHomeomorph F e h_ind
    trivializationAtlas F E' =
      (fun t : Trivialization F (π F E) ↦ t.compFiberHomeomorph e h_ind) ''
        trivializationAtlas F E := (rfl)

end Transfer

end
