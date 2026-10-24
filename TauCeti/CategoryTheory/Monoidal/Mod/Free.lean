/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Free modules over an internal monoid

For a monoid object `A` in a monoidal category, `A ⊗ X` is the free left `A`-module
on `X`. Restriction to the generators identifies module maps out of it with maps out
of `X`, naturally in both variables. No braiding or colimit hypotheses are needed.

The construction uses Mathlib's `Mod` category. It supplies, in particular, the
free sphere modules used to construct free symmetric spectra.
-/

public section

universe v u

open CategoryTheory MonoidalCategory MonObj

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (A : C) [MonObj A]

/-- Multiplication on the first factor makes `A ⊗ X` a left `A`-module. -/
@[instance_reducible]
def freeModObj (X : C) : ModObj A (A ⊗ X) where
  smul := (α_ A A X).inv ≫ μ[A] ▷ X
  one_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight]
    simp
  mul_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionAssocIso, Category.assoc, whiskerLeft_comp]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, MonObj.mul_assoc]
    simp only [comp_whiskerRight,
      associator_inv_naturality_middle_assoc, pentagon_hom_inv_inv_inv_hom_assoc]

/-- The free left `A`-module functor. Its underlying object on `X` is `A ⊗ X`. -/
-- An abbreviation so that the underlying objects are tensor products without transports.
abbrev freeModule : C ⥤ Mod C A where
  obj X := letI := freeModObj A X; ⟨A ⊗ X⟩
  map {X Y} f := by
    letI := freeModObj A X
    letI := freeModObj A Y
    exact Mod.Hom.mk' (A ◁ f) (by
      dsimp only [ModObj.smul, freeModObj]
      simp only [selfLeftAction_actionHomRight, Category.assoc,
        associator_inv_naturality_right_assoc, whisker_exchange])
  map_id X := by ext; simp
  map_comp f g := by ext; simp

/-- The free-module action is multiplication on its first tensor factor. -/
@[simp]
lemma freeModule_smul (X : C) :
    ((freeModule A).obj X).mod.smul = (α_ A A X).inv ≫ μ[A] ▷ X := (rfl)

/-- The generators of a free module are obtained by inserting the monoid unit. -/
def freeModuleι (X : C) : X ⟶ ((freeModule A).obj X).X :=
  (λ_ X).inv ≫ η[A] ▷ X

/-- The inclusion of generators inserts the unit in the first tensor factor. -/
lemma freeModuleι_eq (X : C) :
    freeModuleι A X = (λ_ X).inv ≫ η[A] ▷ X := (rfl)

/-- Extending a map to a module by the module action. -/
def freeModuleDesc {X : C} (M : Mod C A) (f : X ⟶ M.X) :
    (freeModule A).obj X ⟶ M :=
  Mod.Hom.mk' (A := A) (A ◁ f ≫ γ[A, M.X]) (by
    dsimp only [ModObj.smul, freeModObj]
    simp only [selfLeftAction_actionHomRight, Category.assoc, whiskerLeft_comp]
    rw [← whisker_exchange_assoc, ModObj.mul_smul_self]
    simp)

/-- The extension's underlying map applies the given map and then the action. -/
@[simp]
lemma freeModuleDesc_hom {X : C} (M : Mod C A) (f : X ⟶ M.X) :
    (freeModuleDesc A M f).hom = A ◁ f ≫ γ[A, M.X] := (rfl)

/-- An extension agrees with the given map on generators. -/
-- Restrict to generators before expanding the underlying extension map.
@[simp↓, reassoc (attr := simp↓)]
lemma freeModuleι_desc {X : C} (M : Mod C A) (f : X ⟶ M.X) :
    dsimp% freeModuleι A X ≫ (freeModuleDesc A M f).hom = f := by
  simp [freeModuleι, ← whisker_exchange_assoc]

/-- Restriction followed by extension recovers every free-module map. -/
@[simp]
lemma freeModuleDesc_ι {X : C} (M : Mod C A) (f : (freeModule A).obj X ⟶ M) :
    freeModuleDesc A M (freeModuleι A X ≫ f.hom) = f := by
  ext
  simp only [freeModuleDesc_hom, whiskerLeft_comp, Category.assoc]
  have hf := f.isModHom.smul_hom
  simp only [selfLeftAction_actionHomRight] at hf
  rw [← hf]
  simp only [freeModuleι, whiskerLeft_comp, Category.assoc, freeModule_smul]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc]
  simp

/-- The universal property of a free module. -/
def freeModuleHomEquiv (X : C) (M : Mod C A) :
    ((freeModule A).obj X ⟶ M) ≃ (X ⟶ M.X) where
  toFun f := freeModuleι A X ≫ f.hom
  invFun f := freeModuleDesc A M f
  left_inv f := freeModuleDesc_ι A M f
  right_inv f := freeModuleι_desc A M f

/-- The universal bijection restricts a module map to the generators. -/
@[simp]
lemma freeModuleHomEquiv_apply (X : C) (M : Mod C A) (f : (freeModule A).obj X ⟶ M) :
    dsimp% freeModuleHomEquiv A X M f = freeModuleι A X ≫ f.hom := (rfl)

/-- The inverse universal bijection extends by the action. -/
@[simp]
lemma freeModuleHomEquiv_symm_apply (X : C) (M : Mod C A) (f : X ⟶ M.X) :
    dsimp% (freeModuleHomEquiv A X M).symm f = freeModuleDesc A M f := (rfl)

/-- The free-module functor is left adjoint to the native forgetful functor. -/
def freeModuleAdjunction : freeModule A ⊣ Mod.forget (D := C) A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := freeModuleHomEquiv A
      homEquiv_naturality_left_symm := by
        intros X Y M f g
        ext
        dsimp only [freeModuleHomEquiv, Equiv.symm, Equiv.coe_fn_mk]
        exact whiskerLeft_comp_assoc A f g (γ[A, M.X])
      homEquiv_naturality_right := by
        intros X M N f g
        dsimp only [freeModuleHomEquiv, Equiv.coe_fn_mk]
        exact (Category.assoc _ _ _).symm }

/-- The adjunction uses restriction to the chosen generators as its hom-set bijection. -/
@[simp]
lemma freeModuleAdjunction_homEquiv (X : C) (M : Mod C A) :
    (freeModuleAdjunction A).homEquiv X M = freeModuleHomEquiv A X M := by
  rw [freeModuleAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- The adjunction unit is the inclusion of generators. -/
@[simp]
lemma freeModuleAdjunction_unit_app (X : C) :
    dsimp% (freeModuleAdjunction A).unit.app X = freeModuleι A X := by
  dsimp only [freeModuleAdjunction, Adjunction.mkOfHomEquiv, freeModuleHomEquiv,
    Equiv.coe_fn_mk]
  exact Category.comp_id _

end TauCeti
