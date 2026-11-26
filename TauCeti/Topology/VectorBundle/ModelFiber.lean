/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Changing the model fibre of a fibre bundle

The model fibre `F` of a bundle `E → B` enters only through its local trivializations: for any two
types `F` and `F'`, the total spaces `TotalSpace F E` and `TotalSpace F' E` have the same points
`⟨b, v⟩` with `v : E b`. Give `TotalSpace F' E` the topology induced along the identity of points
`TotalSpace F' E → TotalSpace F E`. Then the identity of points is a homeomorphism over `B`
(`TauCeti.totalSpaceModelFiberHomeomorph`), a homeomorphism `F ≃ₜ F'` turns each local
trivialization with model fibre `F` into one with model fibre `F'`
(`Bundle.Trivialization.transModelFiber`), and so it transports a fibre bundle structure with model
fibre `F` to one with model fibre `F'` (`FiberBundle.ofModelFiberHomeomorph`). A continuous linear
equivalence `F ≃L[𝕜] F'` transports a vector bundle structure in the same way
(`VectorBundle.ofModelFiberContinuousLinearEquiv`), with coordinate changes conjugated by it
(`Bundle.Trivialization.coordChangeL_transModelFiber`).

The two model fibres may lie in different universes. A construction that needs the model fibre in
the universe of the base and the fibres, for instance one taking `TopCat.of F` alongside spaces
built from `E`, applies to a bundle with model fibre `Fin r → ℝ : Type` over a base in a higher
universe through a lift of the model fibre to that universe.

For transport along fibrewise equivalences with a fixed model fibre see
`TauCeti.Topology.VectorBundle.Transfer`.
-/

public section

noncomputable section

open Bundle Set Topology

namespace TauCeti

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

section Linear

variable {𝕜 : Type*} [Semiring 𝕜] [AddCommMonoid F] [Module 𝕜 F] [AddCommMonoid F'] [Module 𝕜 F']
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]

/-- Reading a `𝕜`-linear trivialization through a continuous linear equivalence of model fibres
gives a `𝕜`-linear trivialization. -/
instance instIsLinearTransModelFiber (t : Trivialization F (π F E)) [t.IsLinear 𝕜] (L : F ≃L[𝕜] F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) :
    (t.transModelFiber L.toHomeomorph h_ind).IsLinear 𝕜 where
  linear _ hb := ((L : F →ₗ[𝕜] F').comp (IsLinearMap.mk' _ (t.linear 𝕜 hb))).isLinear

/-- The coordinate changes of two linear trivializations read through a continuous linear
equivalence `L` of model fibres are those of the original trivializations conjugated by `L`. -/
theorem coordChangeL_transModelFiber (t₁ t₂ : Trivialization F (π F E)) [t₁.IsLinear 𝕜]
    [t₂.IsLinear 𝕜] (L : F ≃L[𝕜] F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) (b : B) :
    (t₁.transModelFiber L.toHomeomorph h_ind).coordChangeL 𝕜
        (t₂.transModelFiber L.toHomeomorph h_ind) b =
      (L.symm.trans (t₁.coordChangeL 𝕜 t₂ b)).trans L := by
  ext v
  by_cases hb : b ∈ t₁.baseSet ∩ t₂.baseSet
  · rw [coordChangeL_apply' _ _ (by simpa using hb), ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.trans_apply, coordChangeL_apply' _ _ hb]
    rfl
  · simp [coordChangeL, hb]

end Linear

end Bundle.Trivialization

section Transport

variable {B : Type*} [TopologicalSpace B] (F : Type*) {F' : Type*} {E : B → Type*}
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [TopologicalSpace (TotalSpace F' E)]

section Fiber

variable [TopologicalSpace F] [TopologicalSpace F']

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

end Fiber

/-- Transport a `VectorBundle 𝕜 F E` structure to model fibre `F'` along a continuous linear
equivalence `L : F ≃L[𝕜] F'`, for the fibre bundle structure `FiberBundle.ofModelFiberHomeomorph`
on the topology of `TotalSpace F' E` induced along the identity of points. -/
theorem VectorBundle.ofModelFiberContinuousLinearEquiv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (L : F ≃L[𝕜] F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) :
    letI := FiberBundle.ofModelFiberHomeomorph F L.toHomeomorph h_ind
    VectorBundle 𝕜 F' E := by
  let := FiberBundle.ofModelFiberHomeomorph F L.toHomeomorph h_ind
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := ht'.out
    have : MemTrivializationAtlas t := ⟨ht⟩
    infer_instance
  · intro t₁' t₂' ht₁' ht₂'
    obtain ⟨t₁, ht₁, rfl⟩ := ht₁'.out
    obtain ⟨t₂, ht₂, rfl⟩ := ht₂'.out
    have : MemTrivializationAtlas t₁ := ⟨ht₁⟩
    have : MemTrivializationAtlas t₂ := ⟨ht₂⟩
    -- The coordinate changes are those of `E` conjugated by `L`, a continuous operation on
    -- operators.
    refine ((L.arrowCongr L).continuous.comp_continuousOn (continuousOn_coordChange 𝕜 t₁ t₂)).congr
      fun b _ ↦ ?_
    simp only [Function.comp_apply, Trivialization.coordChangeL_transModelFiber]
    ext v
    rfl

end Transport
