/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Flat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Projective presheaves of modules

Let `R` be a presheaf of rings on a small category `C`. Morphisms out of the free presheaf of
modules on the presheaf represented by `U` are the sections over `U`
(Mathlib's `PresheafOfModules.freeYonedaEquiv`), and epimorphisms of presheaves of modules are
surjective on sections, so these free presheaves are projective. Every presheaf of modules is a
quotient of a coproduct of them (Mathlib's `PresheafOfModules.fromFreeYonedaCoproduct`), so the
category of presheaves of modules has enough projectives.

A projective presheaf of modules is a retract of such a coproduct, which is the free presheaf of
modules on a coproduct of representable presheaves. Over a presheaf of commutative rings its
modules of sections are therefore flat. Sheafifying projective presheaves of modules thus gives
flat sheaves of modules.

## Main declarations

* `PresheafOfModules.projective_free_obj_yoneda`: the free presheaf of modules on a representable
  presheaf is projective.
* `PresheafOfModules.enoughProjectives`: presheaves of modules have enough projectives.
* `PresheafOfModulesOfCommRing.flat_obj_of_projective`: the modules of sections of a projective
  presheaf of modules over a presheaf of commutative rings are flat.
-/

public section

open CategoryTheory Limits

universe v u

namespace PresheafOfModules

section

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

/-- The free presheaf of modules on the presheaf represented by an object `U` is projective. -/
instance projective_free_obj_yoneda (U : C) : Projective ((free R).obj (yoneda.obj U)) where
  factors {_ _} f e _ := by
    obtain ⟨m, hm⟩ := surjective_of_epi e _ (freeYonedaEquiv f)
    exact ⟨freeYonedaEquiv.symm m, freeYonedaEquiv.injective (by
      rw [freeYonedaEquiv_comp, Equiv.apply_symm_apply, hm])⟩

end

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- Presheaves of modules over a presheaf of rings on a small category have enough projectives:
every presheaf of modules is a quotient of a coproduct of free presheaves of modules on
representable presheaves. -/
instance enoughProjectives : EnoughProjectives (PresheafOfModules.{u} R) where
  presentation M := ⟨{ p := M.freeYonedaCoproduct, f := M.fromFreeYonedaCoproduct }⟩

end PresheafOfModules

namespace PresheafOfModulesOfCommRing

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The modules of sections of a projective presheaf of modules over a presheaf of commutative
rings are flat. -/
instance flat_obj_of_projective (P : PresheafOfModulesOfCommRing.{u} R) [Projective P]
    (X : Cᵒᵖ) : Module.Flat (R.obj X) (P.obj X) := by
  -- `P` is a retract of the coproduct `F` of free presheaves of modules on representables, and
  -- `F` is the free presheaf of modules on a coproduct of representables, which is sectionwise
  -- free.
  let F := P.freeYonedaCoproduct
  let s : P ⟶ F := Projective.factorThru (𝟙 P) P.fromFreeYonedaCoproduct
  have hs : s ≫ P.fromFreeYonedaCoproduct = 𝟙 P := Projective.factorThru_comp _ _
  have := (PresheafOfModules.freeAdjunction (R ⋙ forget₂ _ _)).leftAdjoint_preservesColimits
  let e : F ≅ (PresheafOfModules.free _).obj (∐ fun m : P.Elements ↦ yoneda.obj m.1.unop) :=
    (PreservesCoproduct.iso (PresheafOfModules.free _) _).symm
  let e' : PresheafOfModulesOfCommRing.obj F X ≃ₗ[R.obj X] PresheafOfModulesOfCommRing.obj
      (PresheafOfModules.freeObj (∐ fun m : P.Elements ↦ yoneda.obj m.1.unop)) X :=
    ((PresheafOfModules.evaluation _ X).mapIso e).toLinearEquiv
  have : Module.Flat (R.obj X) (PresheafOfModulesOfCommRing.obj F X) :=
    (Module.Flat.equiv_iff e').2 (flat_freeObj_obj _ X)
  exact Module.Flat.of_retract (s.app X).hom (P.fromFreeYonedaCoproduct.app X).hom
    (by ext x; simpa using congr_arg (fun f : P ⟶ P ↦ (f.app X).hom x) hs)

end PresheafOfModulesOfCommRing
