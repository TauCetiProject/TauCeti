/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import TauCeti.Algebra.Module.Injective.Envelope.Existence
public import TauCeti.CategoryTheory.Injective.Envelope

/-!
# Injective envelopes in `ModuleCat`

An injective envelope of modules (`TauCeti.IsInjectiveEnvelope`: an embedding into an injective
module with essential range) is an essential monomorphism into an injective object of `ModuleCat`
(`TauCeti.IsInjectiveEnvelope.isEssentialMono`), by
`TauCeti.isInjectiveEnvelope_iff_forall_injective`. Since every module has an injective envelope,
every object of `ModuleCat` has one in the categorical sense
(`TauCeti.ModuleCat.exists_isEssentialMono`), so the categorical theory of minimal injective
coresolutions applies to modules. This is the injective counterpart of
`TauCeti/Algebra/Module/ProjectiveCover/ModuleCat.lean`.

## Main results

* `TauCeti.IsInjectiveEnvelope.isEssentialMono`: an injective envelope of modules is an essential
  monomorphism in `ModuleCat`.
* `TauCeti.ModuleCat.exists_isEssentialMono`: every object of `ModuleCat` has an injective envelope.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

variable {R : Type u} [Ring R]

/-- **An injective envelope of modules is an essential monomorphism.** Injectivity of the map is
`Mono`, and the essential range is the essentiality clause, by
`TauCeti.isInjectiveEnvelope_iff_forall_injective`. -/
theorem IsInjectiveEnvelope.isEssentialMono {M Q : ModuleCat.{v} R} {f : M ⟶ Q}
    (h : IsInjectiveEnvelope f.hom) : IsEssentialMono f where
  mono := (ModuleCat.mono_iff_injective f).2 h.injective
  mono_of_mono_comp g hg := by
    have := h.moduleInjective
    rw [ModuleCat.mono_iff_injective] at hg ⊢
    exact (isInjectiveEnvelope_iff_forall_injective h.injective).1 h g.hom
      (by simpa [ModuleCat.hom_comp] using hg)

/-- The target of an injective envelope of modules is an injective object of `ModuleCat`. -/
theorem IsInjectiveEnvelope.injective_obj {M Q : ModuleCat.{v} R} {f : M ⟶ Q}
    (h : IsInjectiveEnvelope f.hom) : Injective Q :=
  have := h.moduleInjective
  Module.injective_object_of_injective_module R Q

/-- **Every module has an injective envelope in `ModuleCat`**, in the categorical sense of an
essential monomorphism into an injective object. -/
theorem ModuleCat.exists_isEssentialMono [Small.{v} R] (M : ModuleCat.{v} R) :
    ∃ (I : ModuleCat.{v} R) (ι : M ⟶ I), Injective I ∧ IsEssentialMono ι := by
  obtain ⟨Q, _, _, i, hi⟩ := exists_isInjectiveEnvelope (R := R) (M := M)
  let ι : M ⟶ ModuleCat.of R Q := ModuleCat.ofHom i
  exact ⟨ModuleCat.of R Q, ι, IsInjectiveEnvelope.injective_obj (f := ι) hi,
    IsInjectiveEnvelope.isEssentialMono (f := ι) hi⟩

end TauCeti
