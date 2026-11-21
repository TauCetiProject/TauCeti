/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Transport
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Transporting vector-bundle structures along fibrewise continuous linear equivalences

Precomposing `R`-linear trivializations with `TauCeti.totalSpaceHomeomorphOfIsInducing` for
fibrewise continuous linear equivalences preserves linearity and overlap coordinate changes
(`Bundle.Trivialization.compHomeomorph_isLinear`,
`Bundle.Trivialization.compHomeomorph_coordChangeL_eq`). Fibrewise continuous linear equivalences
`φ : ∀ b, E' b ≃L[𝕜] E b` over a nontrivially normed field whose induced total-space map is
topological-inducing transfer `VectorBundle 𝕜 F E` to `E'`
(`TauCeti.vectorBundleOfContinuousLinearEquiv`), equipping `E'` with
`TauCeti.fiberBundleOfHomeomorph`, without completeness or finite-dimensionality hypotheses.
-/

public section
open Bundle Topology

namespace Bundle.Trivialization

variable {B : Type*} [TopologicalSpace B] {F : Type*} {E : B → Type*} {E' : B → Type*}
  [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F E')]
  {R : Type*} [Semiring R] [AddCommMonoid F] [Module R F]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module R (E b)] [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module R (E' b)] [∀ b, TopologicalSpace (E' b)]

/-- Precomposing an `R`-linear trivialization with a total-space homeomorphism given fibrewise by
`R`-linear equivalences preserves `Trivialization.IsLinear`. -/
theorem compHomeomorph_isLinear (e : Trivialization F (π F E)) [e.IsLinear R]
    (φ : ∀ b, E' b ≃L[R] E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace F E))) :
    ((e.compHomeomorph (TauCeti.totalSpaceHomeomorphOfIsInducing F
      (fun b ↦ (φ b).toHomeomorph.toEquiv) ht) : Trivialization F (π F E'))).IsLinear R where
  linear b hb :=
    { map_add v w := by
        -- Unfold `e.compHomeomorph` and `toHomeomorph.toEquiv` to `e` and `φ b`.
        change (e ⟨b, φ b (v + w)⟩).2 = (e ⟨b, φ b v⟩).2 + (e ⟨b, φ b w⟩).2
        rw [map_add]; exact (e.linear R hb).map_add (φ b v) (φ b w)
      map_smul c v := by
        -- Unfold `e.compHomeomorph` and `toHomeomorph.toEquiv` to `e` and `φ b`.
        change (e ⟨b, φ b (c • v)⟩).2 = c • (e ⟨b, φ b v⟩).2
        rw [map_smul]; exact (e.linear R hb).map_smul c (φ b v) }

/-- Precomposing two `R`-linear trivializations with the same fibrewise continuous-linear
total-space homeomorphism leaves their overlap coordinate-change operator unchanged. -/
theorem compHomeomorph_coordChangeL_eq (e₁ e₂ : Trivialization F (π F E))
    [e₁.IsLinear R] [e₂.IsLinear R] (φ : ∀ b, E' b ≃L[R] E b)
    (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace F E)))
    {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) :
    let h := TauCeti.totalSpaceHomeomorphOfIsInducing F (fun b ↦ (φ b).toHomeomorph.toEquiv) ht
    let e₁' : Trivialization F (π F E') := e₁.compHomeomorph h
    let e₂' : Trivialization F (π F E') := e₂.compHomeomorph h
    have : e₁'.IsLinear R := e₁.compHomeomorph_isLinear φ ht
    have : e₂'.IsLinear R := e₂.compHomeomorph_isLinear φ ht
    e₁'.coordChangeL R e₂' b = e₁.coordChangeL R e₂ b := by
  intro h e₁' e₂'
  have : e₁'.IsLinear R := e₁.compHomeomorph_isLinear φ ht
  have : e₂'.IsLinear R := e₂.compHomeomorph_isLinear φ ht
  ext v; rw [e₁'.coordChangeL_apply' e₂' hb, e₁.coordChangeL_apply' e₂ hb]
  -- Both `e₁'` and `e₂'` precompose with `h`, so `h` and `h.symm` cancel on the overlap.
  change (e₂ (h (h.symm (e₁.toOpenPartialHomeomorph.symm (b, v))))).2 =
    (e₂ (e₁.toOpenPartialHomeomorph.symm (b, v))).2
  rw [h.apply_symm_apply]

end Bundle.Trivialization

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
