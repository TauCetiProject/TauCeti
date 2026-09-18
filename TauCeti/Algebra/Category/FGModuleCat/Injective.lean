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
monomorphism of finitely generated modules is injective, as one sees by testing it on cyclic
submodules. -/
instance _root_.FGModuleCat.forget₂_preservesMonomorphisms :
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).PreservesMonomorphisms := by
  refine ⟨fun {A B} f _ ↦ (ModuleCat.mono_iff_injective _).mpr ?_⟩
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro (a : A) ha
  have ha_zero : f.hom.hom a = 0 := ha
  let C := FGModuleCat.of R (R ∙ a)
  let i : C ⟶ A := FGModuleCat.ofHom (R ∙ a).subtype
  have hi_comp : i ≫ f = 0 := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    calc
      (i ≫ f).hom.hom ⟨r • a, hx⟩ = f.hom.hom (r • a) := rfl
      _ = r • f.hom.hom a := map_smul f.hom.hom r a
      _ = 0 := by rw [ha_zero, smul_zero]
      _ = (0 : C ⟶ B).hom.hom ⟨r • a, hx⟩ := rfl
  have hi : i = 0 := (cancel_mono f).mp (by simpa only [Limits.zero_comp] using hi_comp)
  exact congrArg (fun g : C ⟶ A ↦ g.hom.hom ⟨a, Submodule.mem_span_singleton_self a⟩) hi

/-- A finitely generated injective module is an injective object of `FGModuleCat R`. -/
theorem _root_.FGModuleCat.injective_of_moduleInjective (X : FGModuleCat.{v} R)
    [Module.Injective R X] : Injective X :=
  (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).injective_of_map_injective
    ((Module.injective_iff_injective_object R X).mp inferInstance)

end TauCeti
