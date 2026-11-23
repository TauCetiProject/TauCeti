/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Lift
public import TauCeti.RingTheory.Huber.NoetherianType.Basic

import TauCeti.RingTheory.Huber.NoetherianType.ModuleTopology

/-!
# Universal lift into finite modules

When `B` is a complete Hausdorff Huber ring of noetherian type and `A → B` is adic, every
finite `B`-module `N` carrying its natural `B`-module topology is complete, Hausdorff, and
nonarchimedean (`IsNoetherianType.complete_t2_nonarchimedean_of_isModuleTopology`). Specializing
`TauCeti.Huber.ContinuousKaehlerDifferential.lift` yields
`TauCeti.Huber.ContinuousKaehlerDifferential.liftOfFinite`, lifting any continuous `A`-derivation
`δ : B → N` to a `B`-linear map `Ωᶜ[B⁄A] →ₗ[B] N`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Definition 1.6.1 and (1.6.2)(ii).
-/

public section

namespace TauCeti.Huber.ContinuousKaehlerDifferential

section FiniteTarget

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace A]
  [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T0Space B] [IsAdicHom (algebraMap A B)]
  [IsHuberRing B] [IsNoetherianType B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  [Module.Finite B N] [TopologicalSpace N] [IsModuleTopology B N]

private noncomputable def liftOfFiniteAux (δ : Derivation A B N) (hδ : Continuous δ) :
    {l : ContinuousKaehlerDifferential A B →ₗ[B] N // ∀ b, l (D A B b) = δ b} := by
  letI := IsModuleTopology.isTopologicalAddGroup B N
  letI := IsTopologicalAddGroup.rightUniformSpace N
  obtain ⟨_, _, _, _⟩ :=
    IsNoetherianType.complete_t2_nonarchimedean_of_isModuleTopology (A := B) (M := N)
  exact ⟨(lift δ hδ).toLinearMap, lift_D δ hδ⟩

/-- **Universal lift into a finite `B`-module with its natural topology** (Huber 1996, §1.6,
Definition 1.6.1 and (1.6.2)(ii)): any continuous `A`-derivation `δ : B → N` lifts to
`Ωᶜ[B⁄A] →ₗ[B] N`. -/
noncomputable def liftOfFinite (δ : Derivation A B N) (hδ : Continuous δ) :
    ContinuousKaehlerDifferential A B →ₗ[B] N := (liftOfFiniteAux δ hδ).val

/-- Evaluating `liftOfFinite δ hδ` on `d b` recovers `δ b`. -/
@[simp] theorem liftOfFinite_D (δ : Derivation A B N) (hδ : Continuous δ) (b : B) :
    liftOfFinite δ hδ (D A B b) = δ b := (liftOfFiniteAux δ hδ).property b

/-- Precomposing `liftOfFinite δ hδ` with `D A B` recovers `δ`. -/
@[simp] theorem compDer_liftOfFinite_D (δ : Derivation A B N) (hδ : Continuous δ) :
    (liftOfFinite δ hδ).compDer (D A B) = δ := by ext b; exact liftOfFinite_D δ hδ b

end FiniteTarget

end TauCeti.Huber.ContinuousKaehlerDifferential
