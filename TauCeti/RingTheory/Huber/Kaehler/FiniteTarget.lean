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
`Derivation.liftContinuousKaehlerDifferential` yields
`Derivation.liftContinuousKaehlerDifferentialOfFinite`, lifting any continuous `A`-derivation
`δ : B → N` to a `B`-linear map `Ωᶜ[B⁄A] →ₗ[B] N`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.6, Definition 1.6.1 and (1.6.2)(ii).
-/

public section

namespace Derivation

open TauCeti.Huber ContinuousKaehlerDifferential

section FiniteTarget

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [TopologicalSpace A]
  [IsTopologicalRing A] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T0Space B] [IsAdicHom (algebraMap A B)]
  [IsHuberRing B] [IsNoetherianType B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  [Module.Finite B N] [TopologicalSpace N] [IsModuleTopology B N]

private noncomputable def liftContinuousKaehlerDifferentialOfFiniteAux
    (δ : Derivation A B N) (hδ : Continuous δ) :
    {l : ContinuousKaehlerDifferential A B →ₗ[B] N // ∀ b, l (D A B b) = δ b} := by
  letI := IsModuleTopology.isTopologicalAddGroup B N
  letI := IsTopologicalAddGroup.rightUniformSpace N
  obtain ⟨_, _, _, _⟩ :=
    IsNoetherianType.complete_t2_nonarchimedean_of_isModuleTopology (A := B) (M := N)
  exact ⟨(δ.liftContinuousKaehlerDifferential hδ).toLinearMap,
    δ.liftContinuousKaehlerDifferential_comp_D hδ⟩

/-- **Universal lift into a finite `B`-module with its natural topology** (Huber 1996, §1.6,
Definition 1.6.1 and (1.6.2)(ii)): any continuous `A`-derivation `δ : B → N` lifts to
`Ωᶜ[B⁄A] →ₗ[B] N`. -/
noncomputable def liftContinuousKaehlerDifferentialOfFinite
    (δ : Derivation A B N) (hδ : Continuous δ) :
    ContinuousKaehlerDifferential A B →ₗ[B] N :=
  (liftContinuousKaehlerDifferentialOfFiniteAux δ hδ).val

/-- Evaluating `δ.liftContinuousKaehlerDifferentialOfFinite hδ` on `d b` recovers `δ b`. -/
@[simp] theorem liftContinuousKaehlerDifferentialOfFinite_comp_D
    (δ : Derivation A B N) (hδ : Continuous δ) (b : B) :
    δ.liftContinuousKaehlerDifferentialOfFinite hδ (D A B b) = δ b :=
  (liftContinuousKaehlerDifferentialOfFiniteAux δ hδ).property b

/-- Precomposing `δ.liftContinuousKaehlerDifferentialOfFinite hδ` with `D A B` recovers `δ`. -/
@[simp] theorem liftContinuousKaehlerDifferentialOfFinite_comp
    (δ : Derivation A B N) (hδ : Continuous δ) :
    (δ.liftContinuousKaehlerDifferentialOfFinite hδ).compDer (D A B) = δ := by
  ext b; exact δ.liftContinuousKaehlerDifferentialOfFinite_comp_D hδ b

end FiniteTarget

end Derivation
