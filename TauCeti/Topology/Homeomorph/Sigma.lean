/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions

/-!
# Disjoint unions of families of homeomorphisms

Given `e : ∀ i, X i ≃ₜ Y i`, `Homeomorph.sigmaCongrRight e` is the induced homeomorphism
`(Σ i, X i) ≃ₜ Σ i, Y i` on disjoint unions, matching `Equiv.sigmaCongrRight`.
-/

public section

namespace Homeomorph

variable {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]

/-- An indexed family of homeomorphisms induces a homeomorphism on disjoint unions. -/
def sigmaCongrRight (e : ∀ i, X i ≃ₜ Y i) : (Σ i, X i) ≃ₜ Σ i, Y i where
  toEquiv := Equiv.sigmaCongrRight fun i ↦ (e i).toEquiv
  continuous_toFun := continuous_sigma fun i ↦ continuous_sigmaMk.comp (e i).continuous
  continuous_invFun := continuous_sigma fun i ↦ continuous_sigmaMk.comp (e i).symm.continuous

@[simp] theorem sigmaCongrRight_apply (e : ∀ i, X i ≃ₜ Y i) (p : Σ i, X i) :
    sigmaCongrRight e p = ⟨p.1, e p.1 p.2⟩ := by rfl
@[simp] theorem sigmaCongrRight_toEquiv (e : ∀ i, X i ≃ₜ Y i) :
    (sigmaCongrRight e).toEquiv = Equiv.sigmaCongrRight fun i ↦ (e i).toEquiv := by rfl
@[simp] theorem sigmaCongrRight_symm (e : ∀ i, X i ≃ₜ Y i) :
    (sigmaCongrRight e).symm = sigmaCongrRight fun i ↦ (e i).symm := Homeomorph.ext fun ⟨_, _⟩ ↦ rfl
theorem sigmaCongrRight_symm_apply (e : ∀ i, X i ≃ₜ Y i) (p : Σ i, Y i) :
    (sigmaCongrRight e).symm p = ⟨p.1, (e p.1).symm p.2⟩ := by rfl
@[simp] theorem sigmaCongrRight_refl :
    sigmaCongrRight (fun i ↦ Homeomorph.refl (X i)) = Homeomorph.refl (Σ i, X i) :=
  Homeomorph.ext fun ⟨_, _⟩ ↦ rfl
@[simp] theorem sigmaCongrRight_trans {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)]
    (e₁ : ∀ i, X i ≃ₜ Y i) (e₂ : ∀ i, Y i ≃ₜ Z i) :
    (sigmaCongrRight e₁).trans (sigmaCongrRight e₂) =
      sigmaCongrRight fun i ↦ (e₁ i).trans (e₂ i) := Homeomorph.ext fun ⟨_, _⟩ ↦ rfl

end Homeomorph
