/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Essential monomorphisms and the uniqueness of an injective envelope

An *injective envelope* of an object `M` is a monomorphism `ι : M ⟶ I` into an injective object
which is minimal, in the sense of being an **essential monomorphism**: a morphism `g` out of `I`
is a monomorphism as soon as `ι ≫ g` is one. This file packages that condition as
`TauCeti.IsEssentialMono` and proves the categorical uniqueness and minimality properties of an
injective envelope.

The definition and results are dual to `TauCeti.IsEssentialEpi` in
`TauCeti/CategoryTheory/Projective/Cover.lean`. They are stated directly in the original category,
so users do not have to move an injective-envelope argument through the opposite category.

For module categories this is the categorical form of `TauCeti.IsInjectiveEnvelope` from
`TauCeti/Algebra/Module/Injective/Envelope/Basic.lean`: the latter asks that the range be an
essential submodule. Its `TauCeti.isInjectiveEnvelope_iff_forall_injective` theorem identifies
that condition with the one used here. The categorical formulation also applies to functor
categories, in particular to representations of a quiver.

## Main definitions

* `TauCeti.IsEssentialMono`: `ι` is a monomorphism, and every morphism out of its target whose
  composite with `ι` is a monomorphism is already one.

## Main results

* `TauCeti.IsEssentialMono.isIso_of_isSplitMono`: a split essential monomorphism is an isomorphism;
  hence `TauCeti.IsEssentialMono.isIso_of_injective_source`, an injective object is its own
  injective envelope.
* `TauCeti.IsEssentialMono.isIso_of_comp_eq`: a comparison morphism between injective envelopes
  which commutes with their structure maps is an isomorphism.
* `TauCeti.IsEssentialMono.exists_iso`: two injective envelopes of the same object are isomorphic
  under that object.
* `TauCeti.IsEssentialMono.exists_comp_eq_and_isSplitMono`: every embedding of the object into an
  injective object receives the envelope by a split monomorphism.
* `TauCeti.IsEssentialMono.comp` and `TauCeti.isEssentialMono_of_isIso`: essential monomorphisms
  are closed under composition and contain the isomorphisms.

## References

See I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
Algebras, Vol. 1*, I.5.
-/

public section

universe v u

namespace TauCeti

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- An **essential monomorphism** is a monomorphism `ι : M ⟶ I` such that a morphism out of
`I` is a monomorphism as soon as its composite with `ι` is one. An essential monomorphism into
an injective object is an **injective envelope**. -/
structure IsEssentialMono {M I : C} (ι : M ⟶ I) : Prop where
  /-- An essential monomorphism is in particular a monomorphism. -/
  mono : Mono ι
  /-- A morphism out of the target is a monomorphism as soon as its composite with `ι` is one. -/
  mono_of_mono_comp {X : C} (g : I ⟶ X) : Mono (ι ≫ g) → Mono g

/-- An isomorphism is an essential monomorphism: composing with it changes nothing. -/
theorem isEssentialMono_of_isIso {M I : C} (f : M ⟶ I) [IsIso f] : IsEssentialMono f where
  mono := inferInstance
  mono_of_mono_comp g hg := (mono_comp_iff_of_isIso f g).1 hg

namespace IsEssentialMono

/-- Essential monomorphisms are closed under composition: if `ι` and `κ` are both essential then a
morphism whose composite with `ι ≫ κ` is a monomorphism is caught first by `ι`, then by `κ`. -/
theorem comp {M I J : C} {ι : M ⟶ I} {κ : I ⟶ J} (hι : IsEssentialMono ι)
    (hκ : IsEssentialMono κ) : IsEssentialMono (ι ≫ κ) where
  mono := mono_comp' hι.mono hκ.mono
  mono_of_mono_comp g hg :=
    hκ.mono_of_mono_comp g (hι.mono_of_mono_comp (κ ≫ g) (by rwa [← Category.assoc]))

/-- **An essential monomorphism that splits is an isomorphism.** -/
theorem isIso_of_isSplitMono {M I : C} {ι : M ⟶ I} (hι : IsEssentialMono ι)
    [IsSplitMono ι] : IsIso ι := by
  have : Mono (retraction ι) := hι.mono_of_mono_comp _ (by rw [IsSplitMono.id]; infer_instance)
  exact IsIso.of_mono_retraction ι

/-- **An injective object is its own injective envelope.** An essential monomorphism from an
injective object splits, hence is an isomorphism. -/
theorem isIso_of_injective_source {M I : C} [Injective M] {ι : M ⟶ I}
    (hι : IsEssentialMono ι) : IsIso ι := by
  have := hι.mono
  have : IsSplitMono ι := .mk' ⟨Injective.factorThru (𝟙 M) ι, Injective.comp_factorThru _ _⟩
  exact hι.isIso_of_isSplitMono

/-- **Rigidity of an injective envelope.** If `ι : M ⟶ I` and `ι' : M ⟶ I'` are
essential monomorphisms with `I` injective, then any `h : I ⟶ I'` under `M` is an isomorphism.
Only the source of `h` has to be injective; taking `ι' = ι` this says that an endomorphism of an
injective envelope fixing `M` is automatically an isomorphism. -/
theorem isIso_of_comp_eq {M I I' : C} [Injective I] {ι : M ⟶ I} {ι' : M ⟶ I'}
    (hι : IsEssentialMono ι) (hι' : IsEssentialMono ι') {h : I ⟶ I'}
    (hh : ι ≫ h = ι') : IsIso h :=
  -- `h` is itself an essential monomorphism, out of the injective object `I`.
  isIso_of_injective_source
    { mono := hι.mono_of_mono_comp h (hh ▸ hι'.mono)
      mono_of_mono_comp g hg := hι'.mono_of_mono_comp g <| by
        rw [← hh, Category.assoc]
        exact mono_comp' hι.mono hg }

/-- **The injective envelope is unique.** Two essential monomorphisms out of `M` into injective
objects are related by an isomorphism of their targets commuting with them. -/
theorem exists_iso {M I I' : C} [Injective I] [Injective I'] {ι : M ⟶ I} {ι' : M ⟶ I'}
    (hι : IsEssentialMono ι) (hι' : IsEssentialMono ι') :
    ∃ e : I ≅ I', ι ≫ e.hom = ι' := by
  have := hι.mono
  have hcomp := Injective.comp_factorThru ι' ι
  have := hι.isIso_of_comp_eq hι' hcomp
  exact ⟨asIso (Injective.factorThru ι' ι), hcomp⟩

/-- **The injective envelope is minimal.** Every monomorphism from `M` into an injective object
extends along an injective envelope by a split monomorphism, so the envelope is a retract of every
injective copresentation of `M`. -/
theorem exists_comp_eq_and_isSplitMono {M I : C} [Injective I] {ι : M ⟶ I}
    (hι : IsEssentialMono ι) {X : C} [Injective X] {f : M ⟶ X} (hf : Mono f) :
    ∃ g : I ⟶ X, ι ≫ g = f ∧ IsSplitMono g := by
  have := hι.mono
  have hcomp := Injective.comp_factorThru f ι
  have : Mono (Injective.factorThru f ι) := hι.mono_of_mono_comp _ (by rwa [hcomp])
  exact ⟨_, hcomp, .mk' ⟨Injective.factorThru (𝟙 I) _, Injective.comp_factorThru _ _⟩⟩

end IsEssentialMono

end TauCeti
