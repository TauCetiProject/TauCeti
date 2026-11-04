/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The monoidal structure on the idempotent completion

For a monoidal category `C`, the idempotent completion `Karoubi C` is again monoidal: the tensor
product of two formal direct factors `(X, p)` and `(Y, q)` is `(X ⊗ Y, p ⊗ₘ q)`, the tensor unit
is `(𝟙_ C, 𝟙)`, and a tensor product, whiskering, associator or unitor in `Karoubi C` is the
corresponding morphism of `C` composed with the relevant idempotents. The embedding
`toKaroubi C : C ⥤ Karoubi C` is strong monoidal, and when `C` is monoidal preadditive so is
`Karoubi C`. No additivity is needed for the monoidal structure itself.

This lets one tensor the summands that idempotents of a monoidal category cut out: for
idempotents `e` and `e'` of `C`, the tensor product in `Karoubi C` of the summands they split off
is the summand split off by `e ⊗ₘ e'` (`Karoubi.tensorObj_p`).

## Main declarations

* `CategoryTheory.Idempotents.Karoubi.instMonoidalCategory`: the monoidal structure on
  `Karoubi C`, characterized by the `simp` lemmas `Karoubi.tensorObj_X`, `Karoubi.tensorObj_p`,
  `Karoubi.tensorHom_f`, `Karoubi.whiskerLeft_f`, `Karoubi.whiskerRight_f`,
  `Karoubi.associator_hom_f` and their companions for the unit and unitors.
* `CategoryTheory.Idempotents.toKaroubiMonoidal`: the strong monoidal structure on `toKaroubi C`,
  whose unit and tensorator have identity underlying morphisms
  (`CategoryTheory.Idempotents.toKaroubi_ε_f`, `CategoryTheory.Idempotents.toKaroubi_μ_f`).
* `CategoryTheory.Idempotents.Karoubi.instMonoidalPreadditive`: `Karoubi C` is monoidal
  preadditive when `C` is.
-/

-- The data are exposed so that the projection lemmas below are `rfl` lemmas, usable by `dsimp`
-- to rewrite objects of `Karoubi C` occurring inside the types of morphisms.
@[expose] public section

namespace CategoryTheory.Idempotents

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace Karoubi

/-- The tensor product, unit, whiskerings, associator and unitors of `Karoubi C`: those of `C`,
composed with the idempotents of the formal direct factors involved. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Karoubi C) where
  tensorObj P Q := ⟨P.X ⊗ Q.X, P.p ⊗ₘ Q.p, by simp⟩
  tensorUnit := ⟨𝟙_ C, 𝟙 _, by simp⟩
  tensorHom f g := ⟨f.f ⊗ₘ g.f, by simp⟩
  whiskerLeft P _ _ g := ⟨P.p ⊗ₘ g.f, by simp⟩
  whiskerRight f Q := ⟨f.f ⊗ₘ Q.p, by simp⟩
  associator P Q R :=
    { hom := ⟨(α_ P.X Q.X R.X).hom ≫ (P.p ⊗ₘ Q.p ⊗ₘ R.p), by simp⟩
      inv := ⟨(α_ P.X Q.X R.X).inv ≫ ((P.p ⊗ₘ Q.p) ⊗ₘ R.p), by simp⟩
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp }
  leftUnitor P :=
    { hom := ⟨(λ_ P.X).hom ≫ P.p, by simp⟩
      inv := ⟨P.p ≫ (λ_ P.X).inv, by simp⟩
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp }
  rightUnitor P :=
    { hom := ⟨(ρ_ P.X).hom ≫ P.p, by simp⟩
      inv := ⟨P.p ≫ (ρ_ P.X).inv, by simp⟩
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp }

@[simp]
theorem tensorObj_X (P Q : Karoubi C) : (P ⊗ Q).X = P.X ⊗ Q.X := rfl

@[simp]
theorem tensorObj_p (P Q : Karoubi C) : (P ⊗ Q).p = P.p ⊗ₘ Q.p := rfl

@[simp]
theorem tensorUnit_X : (𝟙_ (Karoubi C)).X = 𝟙_ C := rfl

@[simp]
theorem tensorUnit_p : (𝟙_ (Karoubi C)).p = 𝟙 (𝟙_ C) := rfl

@[simp]
theorem tensorHom_f {P₁ Q₁ P₂ Q₂ : Karoubi C} (f : P₁ ⟶ Q₁) (g : P₂ ⟶ Q₂) :
    (f ⊗ₘ g).f = f.f ⊗ₘ g.f := rfl

@[simp]
theorem whiskerLeft_f (P : Karoubi C) {Q₁ Q₂ : Karoubi C} (g : Q₁ ⟶ Q₂) :
    (P ◁ g).f = P.p ⊗ₘ g.f := rfl

@[simp]
theorem whiskerRight_f {P₁ P₂ : Karoubi C} (f : P₁ ⟶ P₂) (Q : Karoubi C) :
    (f ▷ Q).f = f.f ⊗ₘ Q.p := rfl

@[simp]
theorem associator_hom_f (P Q R : Karoubi C) :
    (α_ P Q R).hom.f = (α_ P.X Q.X R.X).hom ≫ (P.p ⊗ₘ Q.p ⊗ₘ R.p) := rfl

@[simp]
theorem associator_inv_f (P Q R : Karoubi C) :
    (α_ P Q R).inv.f = (α_ P.X Q.X R.X).inv ≫ ((P.p ⊗ₘ Q.p) ⊗ₘ R.p) := rfl

@[simp]
theorem leftUnitor_hom_f (P : Karoubi C) : (λ_ P).hom.f = (λ_ P.X).hom ≫ P.p := rfl

@[simp]
theorem leftUnitor_inv_f (P : Karoubi C) : (λ_ P).inv.f = P.p ≫ (λ_ P.X).inv := rfl

@[simp]
theorem rightUnitor_hom_f (P : Karoubi C) : (ρ_ P).hom.f = (ρ_ P.X).hom ≫ P.p := rfl

@[simp]
theorem rightUnitor_inv_f (P : Karoubi C) : (ρ_ P).inv.f = P.p ≫ (ρ_ P.X).inv := rfl

/-- The idempotent completion of a monoidal category is monoidal. -/
instance instMonoidalCategory : MonoidalCategory (Karoubi C) :=
  .ofTensorHom
    (id_tensorHom_id := fun _ _ ↦ by ext; simp)
    (id_tensorHom := fun _ _ _ _ ↦ by ext; simp)
    (tensorHom_id := fun _ _ ↦ by ext; simp)
    (tensorHom_comp_tensorHom := fun _ _ _ _ ↦ by ext; simp)
    (associator_naturality := fun _ _ _ ↦ by ext; simp)
    (leftUnitor_naturality := fun _ ↦ by ext; simp)
    (rightUnitor_naturality := fun _ ↦ by ext; simp)
    (pentagon := fun _ _ _ _ ↦ by
      ext
      dsimp
      -- Slide the idempotents to the right through the associators, where they merge, and then
      -- apply the pentagon identity of `C`.
      simp only [Category.assoc, associator_naturality_assoc, tensorHom_comp_tensorHom,
        Karoubi.idem]
      rw [← whiskerRight_comp_tensorHom, Category.assoc, associator_naturality_assoc,
        tensorHom_comp_tensorHom, associator_naturality_assoc]
      simp [← whiskerLeft_comp_tensorHom])
    (triangle := fun _ _ ↦ by
      ext
      dsimp
      simp only [Category.assoc, tensorHom_comp_tensorHom, Karoubi.idem, id_tensorHom,
        leftUnitor_naturality_assoc]
      -- What remains is the triangle identity of `C`, followed by the idempotents.
      rw [← whiskerLeft_comp_tensorHom, triangle_assoc, whiskerRight_comp_tensorHom])

/-- If `C` is monoidal preadditive, then so is its idempotent completion. -/
instance instMonoidalPreadditive [Preadditive C] [MonoidalPreadditive C] :
    MonoidalPreadditive (Karoubi C) where
  whiskerLeft_zero := by intros; ext; simp
  zero_whiskerRight := by intros; ext; simp
  whiskerLeft_add := by intros; ext; simp [tensorHom_def]
  add_whiskerRight := by intros; ext; simp [tensorHom_def]

end Karoubi

end CategoryTheory.Idempotents

end

-- The strong monoidal structure on `toKaroubi C` stays unexposed: its unit and tensorator are
-- characterized by the projection lemmas below.
public section

namespace CategoryTheory.Idempotents

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The embedding of a monoidal category into its idempotent completion is strong monoidal, with
unit and tensorator whose underlying morphisms are identities. -/
instance toKaroubiMonoidal : (toKaroubi C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso :=
        { hom := ⟨𝟙 _, by simp⟩
          inv := ⟨𝟙 _, by simp⟩ }
      μIso X Y :=
        { hom := ⟨𝟙 _, by simp⟩
          inv := ⟨𝟙 _, by simp⟩ }
      μIso_hom_natural_left := by intros; ext; simp
      μIso_hom_natural_right := by intros; ext; simp
      associativity := by intros; ext; simp
      left_unitality := by intros; ext; simp
      right_unitality := by intros; ext; simp }

@[simp]
theorem toKaroubi_ε_f : (Functor.LaxMonoidal.ε (toKaroubi C)).f = 𝟙 (𝟙_ C) := (rfl)

@[simp]
theorem toKaroubi_η_f : (Functor.OplaxMonoidal.η (toKaroubi C)).f = 𝟙 (𝟙_ C) := (rfl)

@[simp]
theorem toKaroubi_μ_f (X Y : C) : (Functor.LaxMonoidal.μ (toKaroubi C) X Y).f = 𝟙 (X ⊗ Y) :=
  (rfl)

@[simp]
theorem toKaroubi_δ_f (X Y : C) : (Functor.OplaxMonoidal.δ (toKaroubi C) X Y).f = 𝟙 (X ⊗ Y) :=
  (rfl)

end CategoryTheory.Idempotents

end
