/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Detecting monomorphisms and epimorphisms by maps to injective objects

In a category with enough injective objects, the injective objects detect monomorphisms and
epimorphisms through the maps `g ↦ f ≫ g` that precompose with a morphism `f : X ⟶ Y`:

* `f` is a monomorphism exactly when, for every injective object `I`, every morphism `X ⟶ I`
  extends along `f`, that is, `g ↦ f ≫ g` from `Y ⟶ I` to `X ⟶ I` is surjective
  (`CategoryTheory.Injective.mono_iff_forall_surjective_comp`);
* the injective objects are coseparating (`CategoryTheory.Injective.isCoseparating_isInjective`):
  two morphisms `Y ⟶ Z` agree once they agree after the embedding of `Z` into an injective object.
  So, by Mathlib's `CategoryTheory.ObjectProperty.IsCoseparating.epi_iff`, `f` is an epimorphism
  exactly when, for every injective object `I`, a morphism `Y ⟶ I` is determined by its composite
  with `f`.

This is how a map of modules is shown bijective from the bijectivity of its transposes with
injective coefficients, for instance through the universal coefficient theorem with injective
coefficients.
-/

public section

namespace CategoryTheory.Injective

variable {C : Type*} [Category* C] [EnoughInjectives C]

/-- **The injective objects are coseparating**: in a category with enough injectives, two morphisms
with the same composites with every morphism to an injective object are equal. -/
theorem isCoseparating_isInjective : (isInjective C).IsCoseparating :=
  fun _ Y _ _ h ↦ (cancel_mono (ι Y)).1 (h (under Y) inferInstance (ι Y))

/-- **Monomorphisms are detected by injective objects**: in a category with enough injectives, a
morphism `f : X ⟶ Y` is a monomorphism exactly when, for every injective object `I`, every morphism
`X ⟶ I` is the composite of `f` with a morphism `Y ⟶ I`. -/
theorem mono_iff_forall_surjective_comp {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ ∀ (I : C) [Injective I], Function.Surjective fun g : Y ⟶ I ↦ f ≫ g := by
  refine ⟨fun _ I _ g ↦ ⟨factorThru g f, comp_factorThru g f⟩, fun h ↦ ?_⟩
  -- Extend the embedding of `X` into an injective object along `f`.
  obtain ⟨g, hg : f ≫ g = ι X⟩ := h (under X) (ι X)
  exact mono_of_mono_fac hg

end CategoryTheory.Injective
