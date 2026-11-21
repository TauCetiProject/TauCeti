/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Transporting fibre-bundle structures along fibrewise homeomorphisms

Fibrewise bijections `φ : ∀ b, E' b ≃ E b` whose induced total-space map is topological-inducing
give a total-space homeomorphism `TauCeti.totalSpaceHomeomorphOfIsInducing`. When each `φ b` is a
homeomorphism `E' b ≃ₜ E b`, precomposing the trivializations of `FiberBundle F E` transfers the
fibre-bundle structure to `E'` (`TauCeti.fiberBundleOfHomeomorph`), characterized by
`trivializationAt_fiberBundleOfHomeomorph` and
`mem_trivializationAtlas_fiberBundleOfHomeomorph_iff`.
-/

public section
open Bundle Topology
namespace TauCeti
universe u v w w'
variable {B : Type u} (F : Type v) {E : B → Type w} {E' : B → Type w'}
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace F E')]

section Homeomorph
variable (φ : ∀ b, E' b ≃ E b)
  (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace F E)))
/-- A family of bijections on fibres induces a homeomorphism on total spaces whenever the forward
total-space map is topological-inducing. -/
-- Expose the base projection so `e.compHomeomorph` has projection `π F E'` definitionally.
@[expose] def totalSpaceHomeomorphOfIsInducing : TotalSpace F E' ≃ₜ TotalSpace F E :=
  ({ toFun p := ⟨p.proj, φ p.proj p.snd⟩, invFun p := ⟨p.proj, (φ p.proj).symm p.snd⟩
     left_inv := fun ⟨_, _⟩ ↦ by simp only [Equiv.symm_apply_apply]
     right_inv := fun ⟨_, _⟩ ↦ by simp only [Equiv.apply_symm_apply] } :
    TotalSpace F E' ≃ TotalSpace F E).toHomeomorphOfIsInducing ht
@[simp] theorem totalSpaceHomeomorphOfIsInducing_apply (p : TotalSpace F E') :
    totalSpaceHomeomorphOfIsInducing F φ ht p = ⟨p.proj, φ p.proj p.snd⟩ := (rfl)
@[simp] theorem totalSpaceHomeomorphOfIsInducing_symm_apply (p : TotalSpace F E) :
    (totalSpaceHomeomorphOfIsInducing F φ ht).symm p = ⟨p.proj, (φ p.proj).symm p.snd⟩ := (rfl)
end Homeomorph

section FiberBundle
variable [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)]
  [∀ b, TopologicalSpace (E' b)] [FiberBundle F E] (φ : ∀ b, E' b ≃ₜ E b)
  (ht : IsInducing (fun p : TotalSpace F E' ↦ (⟨p.proj, φ p.proj p.snd⟩ : TotalSpace F E)))
/-- Transfer a `FiberBundle` structure along fibrewise homeomorphisms whose total-space map is
inducing. -/
@[instance_reducible] noncomputable def fiberBundleOfHomeomorph : FiberBundle F E' :=
  let h := totalSpaceHomeomorphOfIsInducing F (fun b ↦ (φ b).toEquiv) ht
  { trivializationAtlas' := {e' | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
      e' = e.compHomeomorph h}
    trivializationAt' b := (trivializationAt F E b).compHomeomorph h
    mem_baseSet_trivializationAt' b := mem_baseSet_trivializationAt F E b
    trivialization_mem_atlas' b := ⟨trivializationAt F E b, inferInstance, rfl⟩
    totalSpaceMk_isInducing' b := h.isInducing.of_comp_iff.mp
      ((FiberBundle.totalSpaceMk_isInducing F E b).comp (φ b).isInducing) }

/-- The chosen trivialization of `fiberBundleOfHomeomorph` at `b` is obtained by precomposing
`trivializationAt F E b` with `totalSpaceHomeomorphOfIsInducing`. -/
@[simp] theorem trivializationAt_fiberBundleOfHomeomorph (b : B) :
    let _ : FiberBundle F E' := fiberBundleOfHomeomorph F φ ht
    trivializationAt F E' b = (trivializationAt F E b).compHomeomorph
      (totalSpaceHomeomorphOfIsInducing F (fun b ↦ (φ b).toEquiv) ht) := (rfl)

/-- A trivialization belongs to the atlas of `fiberBundleOfHomeomorph` if and only if it is
obtained by precomposing an atlas trivialization of `E` with `totalSpaceHomeomorphOfIsInducing`. -/
@[simp] theorem mem_trivializationAtlas_fiberBundleOfHomeomorph_iff
    (e' : Trivialization F (π F E')) :
    let _ : FiberBundle F E' := fiberBundleOfHomeomorph F φ ht
    e' ∈ trivializationAtlas F E' ↔
      ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e),
        e' = e.compHomeomorph (totalSpaceHomeomorphOfIsInducing F (fun b ↦ (φ b).toEquiv) ht) :=
  (Iff.rfl)
end FiberBundle
end TauCeti
