/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Module.Shrink
import TauCeti.Algebra.Category.FGModuleCat.Basic

/-!
# Injective finitely generated modules

A monomorphism of finitely generated modules is an injective linear map, so the inclusion of
`FGModuleCat R` into `ModuleCat R` preserves monomorphisms. Consequently, a finitely generated
module that is injective as a module is an injective object of `FGModuleCat R`. Over a left
Noetherian ring the converse holds by Baer's criterion, since the ideals are finitely generated.

## Main results

* `FGModuleCat.forget₂_preservesMonomorphisms`: the inclusion of finitely generated modules into
  all modules preserves monomorphisms.
* `FGModuleCat.injective_of_moduleInjective`: an injective module that is finitely generated is an
  injective object of `FGModuleCat R`.
* `FGModuleCat.moduleInjective_of_injective`: over a left Noetherian ring, an injective object of
  `FGModuleCat R` is an injective module.
-/

public section

namespace FGModuleCat

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- The inclusion of finitely generated modules into all modules preserves monomorphisms: a
monomorphism of finitely generated modules is an injective linear map. -/
instance forget₂_preservesMonomorphisms :
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).PreservesMonomorphisms where
  preserves {A B} f _ := by
    refine (ModuleCat.mono_iff_injective _).mpr <|
      (injective_iff_map_eq_zero _).mpr fun a ha ↦ ?_
    simp only [forget₂, HasForget₂.forget₂, ObjectProperty.ι_map] at ha
    -- Test `f` on the inclusion of the cyclic submodule `R ∙ a`, which is finitely generated.
    let i : FGModuleCat.of R (R ∙ a) ⟶ A := ObjectProperty.homMk (ModuleCat.ofHom (R ∙ a).subtype)
    have hi : i = 0 := (cancel_mono f).mp <| by
      ext ⟨x, hx⟩
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [i, ha]
    simpa [i] using congr(($hi).hom.hom ⟨a, Submodule.mem_span_singleton_self a⟩)

/-- A finitely generated injective module is an injective object of `FGModuleCat R`. -/
theorem injective_of_moduleInjective (X : FGModuleCat.{v} R)
    [Module.Injective R X] : Injective X :=
  (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).injective_of_map_injective
    ((Module.injective_iff_injective_object R X).mp inferInstance)

/-- **Baer's criterion in `FGModuleCat R`.** Over a left Noetherian ring, an injective object among
the finitely generated modules is an injective `R`-module: the ideals of `R` are finitely
generated, so `FGModuleCat R` contains the inclusions that Baer's criterion tests. The smallness
hypothesis holds automatically when the modules live in a universe containing `R`. -/
theorem moduleInjective_of_injective [IsNoetherianRing R] [Small.{v} R] (X : FGModuleCat.{v} R)
    [Injective X] : Module.Injective R X := by
  refine Module.Baer.injective fun I g ↦ ?_
  let eI := Shrink.linearEquiv.{v} R I
  let eR := Shrink.linearEquiv.{v} R R
  have : Module.Finite R (Shrink.{v} I) := Module.Finite.equiv eI.symm
  have : Module.Finite R (Shrink.{v} R) := Module.Finite.equiv eR.symm
  -- The inclusion of the ideal, between finitely generated modules in the universe of `X`.
  let i : of R (Shrink.{v} I) ⟶ of R (Shrink.{v} R) :=
    ofHom (eR.symm.toLinearMap ∘ₗ I.subtype ∘ₗ eI.toLinearMap)
  have : Mono i := ConcreteCategory.mono_of_injective i
    (eR.symm.injective.comp (Subtype.val_injective.comp eI.injective))
  have h := Injective.comp_factorThru (ofHom (g ∘ₗ eI.toLinearMap)) i
  refine ⟨(Injective.factorThru (ofHom (g ∘ₗ eI.toLinearMap)) i).hom.hom ∘ₗ eR.symm.toLinearMap,
    fun x hx ↦ ?_⟩
  simpa [i, -Injective.comp_factorThru] using congrArg (fun φ ↦ φ.hom.hom (eI.symm ⟨x, hx⟩)) h

end FGModuleCat
