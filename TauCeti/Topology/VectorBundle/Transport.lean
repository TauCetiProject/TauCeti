/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Transporting vector-bundle structures along fibrewise continuous linear equivalences

Fibrewise continuous linear equivalences `φ : ∀ b, E' b ≃L[𝕜] E b` over a nontrivially normed field
whose induced total-space map is topological-inducing transfer `VectorBundle 𝕜 F E` to `E'`
(`TauCeti.vectorBundleOfContinuousLinearEquiv`), equipping `E'` with
`TauCeti.fiberBundleOfHomeomorph`, without completeness or finite-dimensionality hypotheses.
-/

public section
open Bundle Topology
namespace TauCeti
universe u v w w'
variable {B : Type u} {F : Type v} {E : B → Type w} {E' : B → Type w'}
  [TopologicalSpace B] [NormedAddCommGroup F]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F E')]

/-- Transfer a `VectorBundle` structure along fibrewise continuous linear equivalences whose
total-space map is inducing, equipping `E'` with `fiberBundleOfHomeomorph`. -/
theorem vectorBundleOfContinuousLinearEquiv (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
    [∀ b, TopologicalSpace (E b)] [∀ b, AddCommMonoid (E' b)] [∀ b, Module 𝕜 (E' b)]
    [∀ b, TopologicalSpace (E' b)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (φ : ∀ b, E' b ≃L[𝕜] E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace F E))) :
    let _ : FiberBundle F E' := fiberBundleOfHomeomorph F (fun b ↦ (φ b).toHomeomorph) ht
    VectorBundle 𝕜 F E' := by
  let _ : FiberBundle F E' := fiberBundleOfHomeomorph F (fun b ↦ (φ b).toHomeomorph) ht
  have hmem := fun e' ↦ (mem_trivializationAtlas_fiberBundleOfHomeomorph_iff F
    (fun b ↦ (φ b).toHomeomorph) ht e').1
  refine ⟨fun e' he' ↦ ?_, fun e₁' e₂' he₁' he₂' ↦ ?_⟩
  · obtain ⟨e, he, rfl⟩ := hmem e' he'.out
    have : MemTrivializationAtlas e := he; exact e.compHomeomorph_isLinear φ ht
  · obtain ⟨e₁, he₁, rfl⟩ := hmem e₁' he₁'.out; obtain ⟨e₂, he₂, rfl⟩ := hmem e₂' he₂'.out
    have : MemTrivializationAtlas e₁ := he₁; have : MemTrivializationAtlas e₂ := he₂
    have := e₁.compHomeomorph_isLinear φ ht; have := e₂.compHomeomorph_isLinear φ ht
    exact (continuousOn_coordChange 𝕜 e₁ e₂).congr fun b hb ↦
      congrArg ContinuousLinearEquiv.toContinuousLinearMap
        (e₁.compHomeomorph_coordChangeL_eq e₂ φ ht hb)

end TauCeti
