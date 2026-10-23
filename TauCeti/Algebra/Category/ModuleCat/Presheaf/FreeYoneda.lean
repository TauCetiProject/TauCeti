/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing

/-!
# Free presheaves of modules on representable presheaves

Let `R` be a presheaf of rings on a category `C` and let `U` be an object of `C`. The free
presheaf of modules `PresheafOfModules.freeObj (yoneda.obj U)` on the presheaf of sets represented
by `U` has, over `V`, the free module on the morphisms `V ⟶ U`, and Mathlib's
`PresheafOfModules.freeYonedaEquiv` identifies morphisms out of it with sections over `U`. This
file records how its basis elements behave.

## Main declarations

* `TauCeti.PresheafOfModules.freeObj_yoneda_map_freeMk`: restriction along `f` sends the basis
  element indexed by `g` to the basis element indexed by `f.unop ≫ g`;
* `TauCeti.PresheafOfModules.freeYonedaEquiv_symm_app_freeMk`: the morphism attached to a section
  `x` sends the basis element indexed by `g` to the restriction of `x` along `g`, generalizing
  Mathlib's `PresheafOfModules.freeYonedaEquiv_symm_app` from the identity to any index;
* `TauCeti.PresheafOfModules.freeYonedaEquiv_symm_comp`: the morphism attached to a section
  composed with `φ` is the morphism attached to the image of the section under `φ`;
* `TauCeti.PresheafOfModules.freeYoneda`: the free presheaf of modules on the presheaf represented
  by `U`, over a presheaf of commutative rings, for use with the monoidal structure of
  `PresheafOfModulesOfCommRing`.
-/

public section

open CategoryTheory Opposite

universe v u

noncomputable section

namespace TauCeti.PresheafOfModules

open _root_.PresheafOfModules

section Ring

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

/-- The free presheaf of modules on the presheaf of sets represented by `U` restricts the basis
element indexed by `g : X.unop ⟶ U` along `f : X ⟶ Y` to the basis element indexed by
`f.unop ≫ g`.

This is not a simp lemma: `PresheafOfModules.freeObj_map` already unfolds the restriction map
of a free presheaf, so the left-hand side is not in simp normal form. -/
theorem freeObj_yoneda_map_freeMk {U : C} {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : X.unop ⟶ U) :
    (freeObj (R := R) (yoneda.obj U)).map f (ModuleCat.freeMk g) =
      ModuleCat.freeMk (f.unop ≫ g) := by
  rw [freeObj_map]
  exact ModuleCat.freeDesc_apply _ _

variable {P Q : PresheafOfModules.{v} R}

/-- The morphism out of the free presheaf of modules on the presheaf of sets represented by `U`
corresponding to a section `x` over `U` sends the basis element indexed by `g : V ⟶ U` to the
restriction of `x` along `g`. -/
@[simp]
theorem freeYonedaEquiv_symm_app_freeMk {U V : C} (x : P.obj (op U)) (g : V ⟶ U) :
    (freeYonedaEquiv.symm x).app (op V) (ModuleCat.freeMk g) = P.map g.op x := by
  -- The basis element indexed by `g` is the restriction along `g` of the one indexed by `𝟙 U`,
  -- so the claim follows from the naturality of `freeYonedaEquiv.symm x` and its value on the
  -- latter, which is `x`.
  have h : (ModuleCat.freeMk g : ((free R).obj (yoneda.obj U)).obj (op V)) =
      ((free R).obj (yoneda.obj U)).map g.op (ModuleCat.freeMk (𝟙 U)) :=
    ((freeObj_yoneda_map_freeMk (R := R) g.op (𝟙 U)).trans
      (congrArg ModuleCat.freeMk (Category.comp_id g))).symm
  exact (congrArg (fun y ↦ (freeYonedaEquiv.symm x).app (op V) y) h).trans
    ((naturality_apply (freeYonedaEquiv.symm x) g.op (ModuleCat.freeMk (𝟙 U))).trans
      (congrArg (fun y ↦ P.map g.op y) (freeYonedaEquiv_symm_app P U x)))

/-- Composing the morphism out of the free presheaf on the presheaf represented by `U`
corresponding to a section `x` with `φ` gives the morphism corresponding to the image of `x`
under `φ`. -/
theorem freeYonedaEquiv_symm_comp {U : C} (x : P.obj (op U)) (φ : P ⟶ Q) :
    freeYonedaEquiv.symm x ≫ φ = freeYonedaEquiv.symm (φ.app (op U) x) := by
  rw [Equiv.eq_symm_apply, freeYonedaEquiv_comp, Equiv.apply_symm_apply]

end Ring

section CommRing

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{v})

/-- The free presheaf of modules on the presheaf of sets represented by `U`, over a presheaf of
commutative rings. -/
abbrev freeYoneda (U : C) : PresheafOfModulesOfCommRing.{v} R :=
  freeObj (yoneda.obj U)

end CommRing

end TauCeti.PresheafOfModules

end
