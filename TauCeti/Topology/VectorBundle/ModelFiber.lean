/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Topology.FiberBundle.ModelFiber
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Changing the model fibre of a vector bundle

A continuous linear equivalence `L : F ≃L[𝕜] F'` of model fibres transports a vector bundle
structure with model fibre `F` to one with model fibre `F'`
(`VectorBundle.ofModelFiberContinuousLinearEquiv`), for the fibre bundle structure
`FiberBundle.ofModelFiberHomeomorph` of `TauCeti.Topology.FiberBundle.ModelFiber` on the topology
of `TotalSpace F' E` induced along the identity of points. Its trivializations are linear
(`Bundle.Trivialization.instIsLinearTransModelFiber`), with coordinate changes conjugated by `L`
(`Bundle.Trivialization.coordChangeL_transModelFiber`).

The two model fibres may lie in different universes. A construction that needs the model fibre in
the universe of the base and the fibres, for instance one taking `TopCat.of F` alongside spaces
built from `E`, applies to a bundle with model fibre `Fin r → ℝ : Type` over a base in a higher
universe through a lift of the model fibre to that universe
(`VectorBundle.exists_modelFiber_of_continuousLinearEquiv`), for instance
`ULift (Fin r → ℝ)` (`VectorBundle.exists_modelFiber_ulift_fin`).

For transport along fibrewise continuous linear equivalences with a fixed model fibre see
`TauCeti.Topology.VectorBundle.Transfer`.
-/

public section

noncomputable section

open Bundle Set Topology Module

universe w

namespace Bundle.Trivialization

variable {B : Type*} [TopologicalSpace B] {F F' : Type*} [TopologicalSpace F] [TopologicalSpace F']
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F' E)]
  {𝕜 : Type*} [Semiring 𝕜] [AddCommMonoid F] [Module 𝕜 F] [AddCommMonoid F'] [Module 𝕜 F']
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]

/-- Reading a `𝕜`-linear trivialization through a continuous linear equivalence of model fibres
gives a `𝕜`-linear trivialization. -/
instance instIsLinearTransModelFiber (t : Trivialization F (π F E)) [t.IsLinear 𝕜] (L : F ≃L[𝕜] F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) :
    (t.transModelFiber L.toHomeomorph h_ind).IsLinear 𝕜 where
  linear _ hb := by
    simp only [transModelFiber_apply]
    exact ((L : F →ₗ[𝕜] F').comp (IsLinearMap.mk' _ (t.linear 𝕜 (by simpa using hb)))).isLinear

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
    simp
  · simp [coordChangeL, hb]

end Bundle.Trivialization

section Transport

variable {B : Type*} [TopologicalSpace B] (F : Type*) {F' : Type*} {E : B → Type*}
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]

/-- Transport a `VectorBundle 𝕜 F E` structure to model fibre `F'` along a continuous linear
equivalence `L : F ≃L[𝕜] F'`, for the fibre bundle structure `FiberBundle.ofModelFiberHomeomorph`
on the topology of `TotalSpace F' E` induced along the identity of points. -/
theorem VectorBundle.ofModelFiberContinuousLinearEquiv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
    [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    [TopologicalSpace (TotalSpace F' E)] (L : F ≃L[𝕜] F')
    (h_ind : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd) :
    letI := FiberBundle.ofModelFiberHomeomorph F L.toHomeomorph h_ind
    VectorBundle 𝕜 F' E := by
  let := FiberBundle.ofModelFiberHomeomorph F L.toHomeomorph h_ind
  have h_atlas := FiberBundle.trivializationAtlas_ofModelFiberHomeomorph F L.toHomeomorph h_ind
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := h_atlas ▸ ht'.out
    have : MemTrivializationAtlas t := ⟨ht⟩
    infer_instance
  · intro t₁' t₂' ht₁' ht₂'
    obtain ⟨t₁, ht₁, rfl⟩ := h_atlas ▸ ht₁'.out
    obtain ⟨t₂, ht₂, rfl⟩ := h_atlas ▸ ht₂'.out
    have : MemTrivializationAtlas t₁ := ⟨ht₁⟩
    have : MemTrivializationAtlas t₂ := ⟨ht₂⟩
    -- The coordinate changes are those of `E` conjugated by `L`, a continuous operation on
    -- operators.
    simp only [Trivialization.transModelFiber_baseSet]
    refine ((L.arrowCongr L).continuous.comp_continuousOn (continuousOn_coordChange 𝕜 t₁ t₂)).congr
      fun b _ ↦ ?_
    simp only [Function.comp_apply, Trivialization.coordChangeL_transModelFiber]
    ext v
    simp [ContinuousLinearEquiv.arrowCongr_apply]

/-- A vector bundle with model fibre `F` is a vector bundle with any model fibre `F'` continuously
linearly equivalent to `F`, for a topology on `TotalSpace F' E` induced along the identity of
points. This packages `TauCeti.totalSpaceModelFiberInduced F F' E`,
`FiberBundle.ofModelFiberHomeomorph` and `VectorBundle.ofModelFiberContinuousLinearEquiv` for
callers that need none of their trivializations; use those directly to work with the
trivializations. -/
theorem VectorBundle.exists_modelFiber_of_continuousLinearEquiv {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [FiberBundle F E]
    [VectorBundle 𝕜 F E] (L : F ≃L[𝕜] F') :
    ∃ (_ : TopologicalSpace (TotalSpace F' E))
      (_ : IsInducing fun p : TotalSpace F' E ↦ TotalSpace.mk' F p.proj p.snd)
      (_ : FiberBundle F' E), VectorBundle 𝕜 F' E := by
  let := TauCeti.totalSpaceModelFiberInduced F F' E
  have h_ind := TauCeti.isInducing_totalSpaceModelFiberInduced F F' E
  exact ⟨_, h_ind, _, VectorBundle.ofModelFiberContinuousLinearEquiv F L h_ind⟩

/-- A finite-dimensional vector bundle with model fibre `F` is a vector bundle with model fibre
`ULift.{w} (Fin (finrank 𝕜 F) → 𝕜)`, in any universe `w`, for a topology on its total space
induced along the identity of points. For `𝕜 = ℝ` this puts the model fibre in the universe of the
base and of the fibres. Its rank is that of `F`, by `simp`. -/
theorem VectorBundle.exists_modelFiber_ulift_fin {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [FiberBundle F E] [VectorBundle 𝕜 F E] :
    ∃ (_ : TopologicalSpace (TotalSpace (ULift.{w} (Fin (finrank 𝕜 F) → 𝕜)) E))
      (_ : IsInducing fun p : TotalSpace (ULift.{w} (Fin (finrank 𝕜 F) → 𝕜)) E ↦
        TotalSpace.mk' F p.proj p.snd)
      (_ : FiberBundle (ULift.{w} (Fin (finrank 𝕜 F) → 𝕜)) E),
      VectorBundle 𝕜 (ULift.{w} (Fin (finrank 𝕜 F) → 𝕜)) E :=
  VectorBundle.exists_modelFiber_of_continuousLinearEquiv F
    ((ContinuousLinearEquiv.ofFinrankEq (by simp)).trans ContinuousLinearEquiv.ulift.symm)

end Transport
