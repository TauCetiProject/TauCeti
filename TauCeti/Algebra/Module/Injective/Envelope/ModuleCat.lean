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

A morphism of modules is an essential monomorphism in `ModuleCat` exactly when it is injective
with essential range (`ModuleCat.isEssentialMono_iff`). Hence an injective envelope of modules
(`TauCeti.IsInjectiveEnvelope`: an embedding into an injective module with essential range) is the
same as an essential monomorphism into an injective object of `ModuleCat`
(`TauCeti.isInjectiveEnvelope_iff_injective_and_isEssentialMono`). Since every module has an
injective envelope, every object of `ModuleCat` has one in the categorical sense
(`ModuleCat.exists_injective_and_isEssentialMono`), so the categorical theory of minimal injective
coresolutions applies to modules. This is the injective counterpart of
`TauCeti/Algebra/Module/ProjectiveCover/ModuleCat.lean`.

## Main results

* `ModuleCat.isEssentialMono_iff`: essential monomorphisms of modules are the injective maps with
  essential range.
* `TauCeti.isInjectiveEnvelope_iff_injective_and_isEssentialMono`: injective envelopes of modules
  are the essential monomorphisms into injective objects of `ModuleCat`.
* `ModuleCat.exists_injective_and_isEssentialMono`: every object of `ModuleCat` has an injective
  envelope.
-/

public section

open CategoryTheory TauCeti

universe u v

variable {R : Type u} [Ring R]

/-- **Essential monomorphisms of modules** are the injective maps with essential range. -/
theorem ModuleCat.isEssentialMono_iff {M Q : ModuleCat.{v} R} (f : M ⟶ Q) :
    IsEssentialMono f ↔ Function.Injective f.hom ∧ IsEssential (LinearMap.range f.hom) := by
  constructor
  · intro hf
    refine ⟨(ModuleCat.mono_iff_injective f).1 hf.mono, isEssential_iff.2 fun N hN ↦ ?_⟩
    -- The quotient map by a submodule meeting the range trivially stays injective on `M`.
    have : Mono (ModuleCat.ofHom N.mkQ) := hf.mono_of_mono_comp _ <| by
      rw [ModuleCat.mono_iff_injective]
      intro x y hxy
      have hf' := (ModuleCat.mono_iff_injective f).1 hf.mono
      refine hf' (sub_eq_zero.1 ?_)
      have hmem : f.hom (x - y) ∈ LinearMap.range f.hom ⊓ N :=
        ⟨⟨x - y, rfl⟩, by simpa [sub_eq_zero, Submodule.Quotient.eq] using hxy⟩
      simpa [hN] using hmem
    rw [ModuleCat.mono_iff_injective] at this
    rw [← Submodule.ker_mkQ N]
    exact LinearMap.ker_eq_bot.2 this
  · rintro ⟨hinj, hess⟩
    exact
      { mono := (ModuleCat.mono_iff_injective f).2 hinj
        mono_of_mono_comp g hg := by
          rw [ModuleCat.mono_iff_injective] at hg ⊢
          exact hess.injective_of_injective_comp (h := g.hom) (by simpa using hg) }

namespace TauCeti

/-- **An injective envelope of modules is an essential monomorphism.** -/
theorem IsInjectiveEnvelope.isEssentialMono {M Q : ModuleCat.{v} R} {f : M ⟶ Q}
    (h : IsInjectiveEnvelope f.hom) : IsEssentialMono f :=
  (ModuleCat.isEssentialMono_iff f).2 ⟨h.injective, h.isEssential_range⟩

/-- The target of an injective envelope of modules is an injective object of `ModuleCat`. -/
theorem IsInjectiveEnvelope.injective_obj {M Q : ModuleCat.{v} R} {f : M ⟶ Q}
    (h : IsInjectiveEnvelope f.hom) : Injective Q :=
  have := h.moduleInjective
  Module.injective_object_of_injective_module R Q

/-- **Injective envelopes of modules are the essential monomorphisms into injective objects** of
`ModuleCat`. -/
theorem isInjectiveEnvelope_iff_injective_and_isEssentialMono {M Q : ModuleCat.{v} R}
    (f : M ⟶ Q) : IsInjectiveEnvelope f.hom ↔ Injective Q ∧ IsEssentialMono f := by
  refine ⟨fun h ↦ ⟨h.injective_obj, h.isEssentialMono⟩, fun ⟨hQ, hf⟩ ↦ ?_⟩
  obtain ⟨hinj, hess⟩ := (ModuleCat.isEssentialMono_iff f).1 hf
  exact ⟨Module.injective_module_of_injective_object R Q, hinj, hess⟩

end TauCeti

/-- **Every module has an injective envelope in `ModuleCat`**, in the categorical sense of an
essential monomorphism into an injective object. -/
theorem ModuleCat.exists_injective_and_isEssentialMono [Small.{v} R] (M : ModuleCat.{v} R) :
    ∃ (I : ModuleCat.{v} R) (ι : M ⟶ I), Injective I ∧ IsEssentialMono ι := by
  obtain ⟨Q, _, _, i, hi⟩ := exists_isInjectiveEnvelope (R := R) (M := M)
  let ι : M ⟶ ModuleCat.of R Q := ModuleCat.ofHom i
  exact ⟨ModuleCat.of R Q, ι, IsInjectiveEnvelope.injective_obj (f := ι) hi,
    IsInjectiveEnvelope.isEssentialMono (f := ι) hi⟩
