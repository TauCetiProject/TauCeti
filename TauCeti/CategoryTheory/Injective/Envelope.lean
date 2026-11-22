/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
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
* `TauCeti.isEssentialMono_cokernelDesc_iff_of_eq_zero` and
  `TauCeti.isEssentialMono_cokernelDesc_epi_comp_iff`: the map out of a cokernel induced by `g` is
  essential exactly when `g` is, if the morphism divided out is zero, and dividing out `p ≫ f` for
  an epimorphism `p` is the same as dividing out `f`.
* `CategoryTheory.Functor.isEssentialMono_map_iff`: equivalences preserve and reflect essential
  monomorphisms.
* `CategoryTheory.Functor.isEssentialMono_cokernelDesc_map_iff`: equivalences preserve the
  essentiality of the map out of a cokernel.

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
@[simp]
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

/-- Precomposing with an isomorphism does not change essentiality. -/
@[simp]
theorem isEssentialMono_isIso_comp_iff {M M' I : C} (e : M ⟶ M') [IsIso e] (f : M' ⟶ I) :
    IsEssentialMono (e ≫ f) ↔ IsEssentialMono f :=
  ⟨fun h ↦ by simpa using (isEssentialMono_of_isIso (inv e)).comp h,
    fun h ↦ (isEssentialMono_of_isIso e).comp h⟩

/-- Postcomposing with an isomorphism does not change essentiality. -/
@[simp]
theorem isEssentialMono_comp_isIso_iff {M I I' : C} (f : M ⟶ I) (e : I ⟶ I') [IsIso e] :
    IsEssentialMono (f ≫ e) ↔ IsEssentialMono f :=
  ⟨fun h ↦ by simpa using h.comp (isEssentialMono_of_isIso (inv e)),
    fun h ↦ h.comp (isEssentialMono_of_isIso e)⟩

section Cokernel

open Limits

variable [HasZeroMorphisms C]

/-- If `f = f'` and `g = g'`, then `cokernel.desc f g w` is an essential monomorphism exactly when
`cokernel.desc f' g' w'` is. -/
theorem isEssentialMono_cokernelDesc_congr {A B D : C} {f f' : A ⟶ B} {g g' : B ⟶ D}
    [HasCokernel f] [HasCokernel f'] (hf : f = f') (hg : g = g') (w : f ≫ g = 0)
    (w' : f' ≫ g' = 0) :
    IsEssentialMono (cokernel.desc f g w) ↔ IsEssentialMono (cokernel.desc f' g' w') := by
  subst hf hg
  rfl

/-- Dividing out by a zero morphism does not change essentiality. -/
theorem isEssentialMono_cokernelDesc_iff_of_eq_zero {A B D : C} {f : A ⟶ B} [HasCokernel f]
    (hf : f = 0) {g : B ⟶ D} (w : f ≫ g = 0) :
    IsEssentialMono (cokernel.desc f g w) ↔ IsEssentialMono g := by
  subst hf
  have : cokernel.desc (0 : A ⟶ B) g w = inv (cokernel.π (0 : A ⟶ B)) ≫ g := by
    simp [← cancel_epi (cokernel.π (0 : A ⟶ B))]
  rw [this, isEssentialMono_isIso_comp_iff]

/-- Precomposing with an epimorphism does not change the essentiality of the induced map out of
the cokernel. -/
theorem isEssentialMono_cokernelDesc_epi_comp_iff {A A' B D : C} (p : A' ⟶ A) [Epi p]
    (f : A ⟶ B) [HasCokernel f] {g : B ⟶ D} (w : (p ≫ f) ≫ g = 0) (w' : f ≫ g = 0) :
    IsEssentialMono (cokernel.desc (p ≫ f) g w) ↔ IsEssentialMono (cokernel.desc f g w') := by
  have : cokernel.desc (p ≫ f) g w = (cokernelEpiComp f p).hom ≫ cokernel.desc f g w' := by
    ext
    simp [cokernelEpiComp]
  rw [this, isEssentialMono_isIso_comp_iff]

end Cokernel

/-- **Equivalences preserve and reflect essential monomorphisms.** -/
@[simp]
theorem _root_.CategoryTheory.Functor.isEssentialMono_map_iff {D : Type*} [Category* D]
    (F : C ⥤ D) [F.IsEquivalence] {M I : C} (ι : M ⟶ I) :
    IsEssentialMono (F.map ι) ↔ IsEssentialMono ι := by
  refine ⟨fun h ↦ ⟨F.mono_of_mono_map h.mono, fun g hg ↦ F.mono_of_mono_map ?_⟩,
    fun h ↦ ⟨have := h.mono; inferInstance, fun {X} g hg ↦ ?_⟩⟩
  · exact h.mono_of_mono_comp _ (by simpa using F.map_mono (ι ≫ g))
  · -- `X` is isomorphic to `F.obj X'`, and `g` composed with this isomorphism is `F.map g'`.
    let e := F.objObjPreimageIso X
    let g' : I ⟶ F.objPreimage X := F.preimage (g ≫ e.inv)
    have hg' : F.map g' = g ≫ e.inv := F.map_preimage _
    have : Mono g' := h.mono_of_mono_comp g' <| F.mono_of_mono_map <| by
      rw [F.map_comp, hg', ← Category.assoc]
      infer_instance
    have : Mono (g ≫ e.inv) := hg' ▸ F.map_mono g'
    exact mono_of_mono g e.inv

open Limits in
/-- **Equivalences preserve the essentiality of the map out of a cokernel**: for `w : f ≫ g = 0`,
the map `cokernel (F.map f) ⟶ F.obj Z` induced by `F.map g` is an essential monomorphism exactly
when `cokernel.desc f g w` is. -/
theorem _root_.CategoryTheory.Functor.isEssentialMono_cokernelDesc_map_iff {D : Type*}
    [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.IsEquivalence]
    {A B Z : C} (f : A ⟶ B) [HasCokernel f] [HasCokernel (F.map f)] (g : B ⟶ Z) (w : f ≫ g = 0)
    (w' : F.map f ≫ F.map g = 0) :
    IsEssentialMono (cokernel.desc (F.map f) (F.map g) w') ↔
      IsEssentialMono (cokernel.desc f g w) := by
  have : cokernel.desc (F.map f) (F.map g) w' =
      cokernelComparison f F ≫ F.map (cokernel.desc f g w) := by
    ext
    simp
  rw [this, isEssentialMono_isIso_comp_iff, F.isEssentialMono_map_iff]

end TauCeti
