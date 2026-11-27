/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Changing the model fibre of a fibre bundle

The model fibre `F` of a bundle `E → B` enters only through its local trivializations: for any two
types `F` and `F'`, the total spaces `TotalSpace F E` and `TotalSpace F' E` have the same points
`⟨b, v⟩` with `v : E b`. Give `TotalSpace F' E` the topology induced along the identity of points
`TotalSpace F' E → TotalSpace F E` (`TauCeti.totalSpaceModelFiberInduced`). Then the identity of
points is a homeomorphism over `B` (`TauCeti.totalSpaceModelFiberHomeomorph`), a homeomorphism
`F ≃ₜ F'` turns each local trivialization with model fibre `F` into one with model fibre `F'`
(`Bundle.Trivialization.transModelFiber`), and so it transports a fibre bundle structure with model
fibre `F` to one with model fibre `F'` (`FiberBundle.ofModelFiberHomeomorph`).

The two model fibres may lie in different universes. For the linear version, transporting a vector
bundle structure along a continuous linear equivalence of model fibres, see
`TauCeti.Topology.VectorBundle.ModelFiber`. For transport along fibrewise homeomorphisms with a
fixed model fibre see `TauCeti.Topology.FiberBundle.Transfer`.
-/

public section

noncomputable section

open Bundle Set Topology

namespace TauCeti

/-- The topology on `TotalSpace F' E` induced from `TotalSpace F E` along the identity of points
`⟨b, v⟩`. -/
@[instance_reducible]
def totalSpaceModelFiberInduced {B : Type*} (F F' : Type*) (E : B → Type*)
    [TopologicalSpace (TotalSpace F E)] : TopologicalSpace (TotalSpace F' E) :=
  TopologicalSpace.induced (fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) inferInstance

/-- Equipping `TotalSpace F' E` with `TauCeti.totalSpaceModelFiberInduced F F' E` makes the identity
of points `TotalSpace F' E → TotalSpace F E` inducing. -/
theorem isInducing_totalSpaceModelFiberInduced {B : Type*} (F F' : Type*) (E : B → Type*)
    [TopologicalSpace (TotalSpace F E)] :
    letI := totalSpaceModelFiberInduced F F' E
    IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd :=
  letI := totalSpaceModelFiberInduced F F' E; ⟨rfl⟩

variable {B : Type*} (F : Type*) {F' : Type*} (E : B → Type*) [TopologicalSpace (TotalSpace F E)]
  [TopologicalSpace (TotalSpace F' E)]

/-- The identity of points `⟨b, v⟩`, from the total space of `E` with model fibre `F'` to its total
space with model fibre `F`, is a homeomorphism over `B` when the topology of the first is induced
from the second. -/
def totalSpaceModelFiberHomeomorph
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) :
    TotalSpace F' E ≃ₜ TotalSpace F E :=
  ({ toFun p := TotalSpace.mk' F p.proj p.snd
     invFun p := TotalSpace.mk' F' p.proj p.snd
     left_inv _ := rfl
     right_inv _ := rfl } : TotalSpace F' E ≃ TotalSpace F E).toHomeomorphOfIsInducing h_ind

variable {F E}

@[simp]
theorem totalSpaceModelFiberHomeomorph_apply
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd)
    (p : TotalSpace F' E) :
    totalSpaceModelFiberHomeomorph F E h_ind p = TotalSpace.mk' F p.proj p.snd :=
  (rfl)

@[simp]
theorem totalSpaceModelFiberHomeomorph_symm_apply
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd)
    (p : TotalSpace F E) :
    (totalSpaceModelFiberHomeomorph F E h_ind).symm p = TotalSpace.mk' F' p.proj p.snd :=
  (rfl)

end TauCeti

namespace Bundle.Trivialization

variable {B : Type*} [TopologicalSpace B] {F F' : Type*} [TopologicalSpace F] [TopologicalSpace F']
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E)]

/-- A local trivialization of `E` with model fibre `F`, read as a trivialization with model fibre
`F'` through a homeomorphism `L : F ≃ₜ F'`, for the topology on `TotalSpace F' E` induced along the
identity of points. -/
def transModelFiber (t : Trivialization F (π F E)) (L : F ≃ₜ F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) :
    Trivialization F' (π F' E) :=
  (t.compHomeomorph (TauCeti.totalSpaceModelFiberHomeomorph F E h_ind)).transFiberHomeomorph L

@[simp]
theorem transModelFiber_apply (t : Trivialization F (π F E)) (L : F ≃ₜ F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd)
    (p : TotalSpace F' E) :
    t.transModelFiber L h_ind p =
      ((t (TotalSpace.mk' F p.proj p.snd)).1, L (t (TotalSpace.mk' F p.proj p.snd)).2) :=
  (rfl)

@[simp]
theorem transModelFiber_baseSet (t : Trivialization F (π F E)) (L : F ≃ₜ F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) :
    (t.transModelFiber L h_ind).baseSet = t.baseSet :=
  (rfl)

@[simp]
theorem transModelFiber_symm_apply (t : Trivialization F (π F E)) (L : F ≃ₜ F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) (p : B × F') :
    (t.transModelFiber L h_ind).toOpenPartialHomeomorph.symm p =
      (TauCeti.totalSpaceModelFiberHomeomorph F E h_ind).symm
        (t.toOpenPartialHomeomorph.symm (p.1, L.symm p.2)) :=
  (rfl)

end Bundle.Trivialization

section Transport

variable {B : Type*} [TopologicalSpace B] (F : Type*) {F' : Type*} {E : B → Type*}
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [TopologicalSpace (TotalSpace F' E)] [TopologicalSpace F] [TopologicalSpace F']

/-- Transport a `FiberBundle F E` structure to model fibre `F'` along a homeomorphism `F ≃ₜ F'`, for
the topology on `TotalSpace F' E` induced along the identity of points. Its trivializations are
those of `E` read through `L` (`Bundle.Trivialization.transModelFiber`). -/
@[instance_reducible]
def FiberBundle.ofModelFiberHomeomorph [FiberBundle F E] (L : F ≃ₜ F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) :
    FiberBundle F' E where
  totalSpaceMk_isInducing' b := h_ind.of_comp_iff.mp (FiberBundle.totalSpaceMk_isInducing F E b)
  trivializationAtlas' :=
    (fun t : Trivialization F (π F E) ↦ t.transModelFiber L h_ind) '' trivializationAtlas F E
  trivializationAt' b := (trivializationAt F E b).transModelFiber L h_ind
  mem_baseSet_trivializationAt' := mem_baseSet_trivializationAt F E
  trivialization_mem_atlas' b := ⟨trivializationAt F E b, trivialization_mem_atlas F E b, rfl⟩

/-- Under `FiberBundle.ofModelFiberHomeomorph`, the preferred trivialization at `b` is that of `E`
read through `L`. -/
@[simp]
theorem FiberBundle.trivializationAt_ofModelFiberHomeomorph [FiberBundle F E] (L : F ≃ₜ F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) (b : B) :
    letI := FiberBundle.ofModelFiberHomeomorph F L h_ind
    trivializationAt F' E b = (trivializationAt F E b).transModelFiber L h_ind :=
  (rfl)

/-- Under `FiberBundle.ofModelFiberHomeomorph`, the trivialization atlas is the image of that of
`E` under `Bundle.Trivialization.transModelFiber`. -/
@[simp]
theorem FiberBundle.trivializationAtlas_ofModelFiberHomeomorph [FiberBundle F E] (L : F ≃ₜ F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) :
    letI := FiberBundle.ofModelFiberHomeomorph F L h_ind
    trivializationAtlas F' E =
      (fun t : Trivialization F (π F E) ↦ t.transModelFiber L h_ind) '' trivializationAtlas F E :=
  (rfl)

end Transport
