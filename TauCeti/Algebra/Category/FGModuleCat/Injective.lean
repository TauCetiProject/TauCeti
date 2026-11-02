/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Injective finitely generated modules

A monomorphism of finitely generated modules is an injective linear map, so the inclusion of
`FGModuleCat R` into `ModuleCat R` preserves monomorphisms. Consequently, a finitely generated
module that is injective as a module is an injective object of `FGModuleCat R`.

## Main results

* `FGModuleCat.forget₂_preservesMonomorphisms`: the inclusion of finitely generated modules into
  all modules preserves monomorphisms.
* `FGModuleCat.injective_of_moduleInjective`: an injective module that is finitely generated is an
  injective object of `FGModuleCat R`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- The inclusion of finitely generated modules into all modules preserves monomorphisms: a
monomorphism of finitely generated modules is an injective linear map. -/
instance _root_.FGModuleCat.forget₂_preservesMonomorphisms :
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
theorem _root_.FGModuleCat.injective_of_moduleInjective (X : FGModuleCat.{v} R)
    [Module.Injective R X] : Injective X :=
  (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).injective_of_map_injective
    ((Module.injective_iff_injective_object R X).mp inferInstance)

end TauCeti
