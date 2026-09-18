/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Injective finitely generated modules

A finitely generated module that is injective as a module is an injective object of
`FGModuleCat R`.

## Main results

* `FGModuleCat.injective_of_moduleInjective`: an injective module that is finitely generated is an
  injective object of `FGModuleCat R`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {R : Type u} [Ring R]

/-- A finitely generated injective module is an injective object of `FGModuleCat R`. -/
theorem _root_.FGModuleCat.injective_of_moduleInjective (X : FGModuleCat.{v} R)
    [Module.Injective R X] : Injective X := by
  -- A monomorphism of finitely generated modules is injective: test it on cyclic submodules.
  have : (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).PreservesMonomorphisms := by
    refine ⟨fun {A B} f _ ↦ (ModuleCat.mono_iff_injective _).mpr ?_⟩
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro (a : A) ha
    let C := FGModuleCat.of R (R ∙ a)
    have h := (cancel_mono f).mp (show FGModuleCat.ofHom (R ∙ a).subtype ≫ f = 0 ≫ f by
      ext ⟨x, hx⟩
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [Limits.zero_comp]
      change f.hom.hom (r • a) = 0
      rw [map_smul, show f.hom.hom a = 0 from ha, smul_zero])
    exact congrArg (fun g : C ⟶ A ↦ g.hom.hom ⟨a, Submodule.mem_span_singleton_self a⟩) h
  exact (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).injective_of_map_injective
    ((Module.injective_iff_injective_object R X).mp inferInstance)

end TauCeti
