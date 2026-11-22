/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoidal natural automorphisms and the category of strong monoidal functors

Mathlib makes the bundled lax monoidal functors `LaxMonoidalFunctor C D` into a category whose
morphisms are the monoidal natural transformations, so for a lax monoidal functor `F` the group
`Aut (LaxMonoidalFunctor.of F)` is the group of monoidal natural automorphisms of `F`. This file
adds the injective group homomorphism `CategoryTheory.LaxMonoidalFunctor.forgetAut F` to the
group `Aut F` of all natural automorphisms of `F`. Its values are typed as automorphisms of `F`
itself rather than of `(LaxMonoidalFunctor.of F).toFunctor`, so their components compose with
other morphisms out of `F.obj X` without unfolding `LaxMonoidalFunctor.of`.

The group `Aut (LaxMonoidalFunctor.of (𝟭 C))` of monoidal natural automorphisms of the identity
functor of a monoidal category, often written `Aut_⊗(𝟭_C)`, is commutative, like Mathlib's
centre `CategoryTheory.CatCenter C` of all natural endomorphisms of `𝟭 C`. It is the group
acting on the pivotal structures of a rigid monoidal category.

A natural transformation between lax monoidal functors that is an epimorphism at the tensor unit
and compatible with the tensorators is already monoidal: compatibility with the unit comparisons
follows (`CategoryTheory.NatTrans.IsMonoidal.of_tensor`).

Bundled strong monoidal functors `TauCeti.MonoidalFunctor C D`, with the monoidal natural
transformations as morphisms, embed fully faithfully into `LaxMonoidalFunctor C D`
(`TauCeti.MonoidalFunctor.fullyFaithfulForget`). Their isomorphisms are the monoidal natural
isomorphisms, so the core of this category is the groupoid of strong monoidal functors in which
universal properties of free monoidal categories are stated. The category structure, induced
from `LaxMonoidalFunctor C D`, and its forgetful-functor API follow Mathlib's bundled lax braided
functors `CategoryTheory.LaxBraidedFunctor` (`Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean`).
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LaxMonoidalFunctor

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The underlying natural automorphism of a monoidal natural automorphism of a lax monoidal
functor `F`, as a group homomorphism `Aut (LaxMonoidalFunctor.of F) →* Aut F`. -/
def forgetAut (F : C ⥤ D) [F.LaxMonoidal] : Aut (LaxMonoidalFunctor.of F) →* Aut F where
  toFun u := Aut.of
    { hom := u.asIso.hom.hom
      inv := u.asIso.inv.hom
      hom_inv_id := congrArg Hom.hom u.asIso.hom_inv_id
      inv_hom_id := congrArg Hom.hom u.asIso.inv_hom_id }
  map_one' := rfl
  map_mul' _ _ := rfl

variable (F : C ⥤ D) [F.LaxMonoidal]

-- The right-hand sides below are typed through `(LaxMonoidalFunctor.of F).toFunctor`, which is
-- `F` only up to unfolding, so these are not `simp` lemmas: `forgetAut` is the normal form.

/-- The underlying natural transformation of `forgetAut F u` is that of `u`. -/
theorem forgetAut_apply_asIso_hom (u : Aut (LaxMonoidalFunctor.of F)) :
    (forgetAut F u).asIso.hom = u.asIso.hom.hom :=
  (rfl)

/-- The underlying natural transformation of the inverse of `forgetAut F u` is that of the
inverse of `u`. -/
theorem forgetAut_apply_asIso_inv (u : Aut (LaxMonoidalFunctor.of F)) :
    (forgetAut F u).asIso.inv = u.asIso.inv.hom :=
  (rfl)

/-- A monoidal natural automorphism is determined by its underlying natural automorphism. -/
theorem forgetAut_injective : Function.Injective (forgetAut F) := fun _ _ h ↦
  Aut.ext (Iso.ext (hom_ext (congrArg (fun w ↦ w.asIso.hom) h)))

/-- The underlying natural automorphism of a monoidal natural automorphism is monoidal. -/
instance isMonoidal_forgetAut_apply_asIso_hom (u : Aut (LaxMonoidalFunctor.of F)) :
    NatTrans.IsMonoidal (forgetAut F u).asIso.hom :=
  u.asIso.hom.isMonoidal

variable (C) in
/-- The monoidal natural automorphisms of the identity functor of a monoidal category commute. -/
instance : IsMulCommutative (Aut (LaxMonoidalFunctor.of (𝟭 C))) :=
  .of_comm fun u v ↦ Aut.ext (Iso.ext (hom_ext (NatTrans.id_comm v.asIso.hom.hom u.asIso.hom.hom)))

end CategoryTheory.LaxMonoidalFunctor

namespace CategoryTheory.NatTrans.IsMonoidal

open MonoidalCategory Functor.LaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- **The unit condition follows from the tensor condition.** A natural transformation `τ` between
lax monoidal functors that is an epimorphism at the tensor unit and compatible with the
tensorators is monoidal. -/
theorem of_tensor {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (τ : F ⟶ G)
    [Epi (τ.app (𝟙_ C))]
    (h : ∀ X Y, μ F X Y ≫ τ.app (X ⊗ Y) = (τ.app X ⊗ₘ τ.app Y) ≫ μ G X Y) :
    τ.IsMonoidal where
  unit := by
    -- `G.obj (𝟙_ C)` is a monoid in `D` with multiplication
    -- `μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom` and unit `ε G`. Transporting the left
    -- unitality of `F` along the epimorphism `τ.app (𝟙_ C)` makes `ε F ≫ τ.app (𝟙_ C)` a left
    -- unit for this multiplication (`hl`), while `ε G` is a right unit (`hr`) because the two
    -- unitors of `𝟙_ C` agree; a left unit and a right unit of a multiplication are equal.
    have hl : (ε F ≫ τ.app (𝟙_ C)) ▷ G.obj (𝟙_ C) ≫ μ G (𝟙_ C) (𝟙_ C) ≫
        G.map (λ_ (𝟙_ C)).hom = (λ_ (G.obj (𝟙_ C))).hom := by
      have : Epi (𝟙_ D ◁ τ.app (𝟙_ C)) := by rw [id_whiskerLeft]; infer_instance
      rw [← cancel_epi (𝟙_ D ◁ τ.app (𝟙_ C))]
      have e : 𝟙_ D ◁ τ.app (𝟙_ C) ≫ (ε F ≫ τ.app (𝟙_ C)) ▷ G.obj (𝟙_ C) =
          ε F ▷ F.obj (𝟙_ C) ≫ (τ.app (𝟙_ C) ⊗ₘ τ.app (𝟙_ C)) := by
        rw [comp_whiskerRight, ← Category.assoc, whisker_exchange, Category.assoc,
          ← tensorHom_def']
      calc 𝟙_ D ◁ τ.app (𝟙_ C) ≫ (ε F ≫ τ.app (𝟙_ C)) ▷ G.obj (𝟙_ C) ≫
            μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom
          = ε F ▷ F.obj (𝟙_ C) ≫ (τ.app (𝟙_ C) ⊗ₘ τ.app (𝟙_ C)) ≫ μ G (𝟙_ C) (𝟙_ C) ≫
              G.map (λ_ (𝟙_ C)).hom := by rw [← Category.assoc, e, Category.assoc]
        _ = ε F ▷ F.obj (𝟙_ C) ≫ μ F (𝟙_ C) (𝟙_ C) ≫ F.map (λ_ (𝟙_ C)).hom ≫
              τ.app (𝟙_ C) := by
            rw [← reassoc_of% h, τ.naturality]
        _ = (λ_ (F.obj (𝟙_ C))).hom ≫ τ.app (𝟙_ C) := by rw [← left_unitality_assoc]
        _ = 𝟙_ D ◁ τ.app (𝟙_ C) ≫ (λ_ (G.obj (𝟙_ C))).hom := by rw [leftUnitor_naturality]
    have hr : G.obj (𝟙_ C) ◁ ε G ≫ μ G (𝟙_ C) (𝟙_ C) ≫ G.map (λ_ (𝟙_ C)).hom =
        (ρ_ (G.obj (𝟙_ C))).hom := by
      rw [unitors_equal, right_unitality]
    calc ε F ≫ τ.app (𝟙_ C)
        = (λ_ (𝟙_ D)).inv ≫ (ε F ≫ τ.app (𝟙_ C)) ▷ 𝟙_ D ≫ (ρ_ (G.obj (𝟙_ C))).hom := by
          rw [rightUnitor_naturality, unitors_inv_equal, Iso.inv_hom_id_assoc]
      _ = (λ_ (𝟙_ D)).inv ≫ 𝟙_ D ◁ ε G ≫ (λ_ (G.obj (𝟙_ C))).hom := by
          rw [← hr, ← whisker_exchange_assoc, hl]
      _ = ε G := by rw [leftUnitor_naturality, Iso.inv_hom_id_assoc]
  tensor := h

end CategoryTheory.NatTrans.IsMonoidal

namespace CategoryTheory.NatTrans.IsMonoidal

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- Two monoidal natural transformations from a strong monoidal functor to a lax monoidal functor
agree at the tensor unit. -/
theorem app_tensorUnit_eq {F G : C ⥤ D} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
    [α.IsMonoidal] [β.IsMonoidal] : α.app (𝟙_ C) = β.app (𝟙_ C) := by
  rw [← cancel_epi (ε F)]
  exact (NatTrans.IsMonoidal.unit (τ := α)).trans (NatTrans.IsMonoidal.unit (τ := β)).symm

/-- Two monoidal natural transformations from a strong monoidal functor to a lax monoidal functor
that agree at `X` and `Y` also agree at `X ⊗ Y`. -/
theorem app_tensor_eq {F G : C ⥤ D} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
    [α.IsMonoidal] [β.IsMonoidal] {X Y : C} (hX : α.app X = β.app X) (hY : α.app Y = β.app Y) :
    α.app (X ⊗ Y) = β.app (X ⊗ Y) := by
  rw [← cancel_epi (μ F X Y)]
  refine (NatTrans.IsMonoidal.tensor (τ := α) X Y).trans ?_
  refine Eq.trans ?_ (NatTrans.IsMonoidal.tensor (τ := β) X Y).symm
  rw [hX, hY]

/-- The component at the tensor unit of a monoidal natural transformation between strong monoidal
functors is `η F ≫ ε G`. -/
theorem app_tensorUnit_eq_η_comp_ε {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G)
    [τ.IsMonoidal] : τ.app (𝟙_ C) = η F ≫ ε G := by
  rw [← cancel_epi (ε F), NatTrans.IsMonoidal.unit, Functor.Monoidal.ε_η_assoc]

/-- The component at a tensor product of a monoidal natural transformation between strong monoidal
functors conjugates the tensor product of components by `δ F` and `μ G`. -/
theorem app_tensor_eq_δ_comp_tensor_comp_μ {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G)
    [τ.IsMonoidal] (X Y : C) :
    τ.app (X ⊗ Y) = δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y) ≫ μ G X Y := by
  rw [← cancel_epi (μ F X Y), NatTrans.IsMonoidal.tensor, Functor.Monoidal.μ_δ_assoc]

/-- A natural transformation between strong monoidal functors whose unit and tensor components are
given by the canonical comparison formulas is monoidal. -/
theorem of_unit_tensor {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G)
    (hunit : τ.app (𝟙_ C) = η F ≫ ε G)
    (htensor : ∀ X Y, τ.app (X ⊗ Y) = δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y) ≫ μ G X Y) :
    τ.IsMonoidal where
  unit := by rw [hunit, Functor.Monoidal.ε_η_assoc]
  tensor X Y := by rw [htensor, Functor.Monoidal.μ_δ_assoc]

end CategoryTheory.NatTrans.IsMonoidal

namespace CategoryTheory.Functor.Monoidal

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The canonical isomorphism `F.obj (𝟙_ C) ≅ G.obj (𝟙_ C)` between the images of the tensor unit
under two strong monoidal functors. -/
@[expose] def unitIso (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] : F.obj (𝟙_ C) ≅ G.obj (𝟙_ C) :=
  (εIso F).symm ≪≫ εIso G

@[simp]
theorem unitIso_hom (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] :
    (unitIso F G).hom = η F ≫ ε G := rfl

@[simp]
theorem unitIso_inv (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] :
    (unitIso F G).inv = η G ≫ ε F := rfl

/-- The canonical isomorphism `F.obj (X ⊗ Y) ≅ G.obj (X ⊗ Y)` induced by isomorphisms
`F.obj X ≅ G.obj X` and `F.obj Y ≅ G.obj Y`. -/
@[expose] def tensorIso (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] {X Y : C}
    (iX : F.obj X ≅ G.obj X) (iY : F.obj Y ≅ G.obj Y) :
    F.obj (X ⊗ Y) ≅ G.obj (X ⊗ Y) :=
  (μIso F X Y).symm ≪≫ (iX ⊗ᵢ iY) ≪≫ μIso G X Y

@[simp]
theorem tensorIso_hom (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] {X Y : C}
    (iX : F.obj X ≅ G.obj X) (iY : F.obj Y ≅ G.obj Y) :
    (tensorIso F G iX iY).hom = δ F X Y ≫ (iX.hom ⊗ₘ iY.hom) ≫ μ G X Y := rfl

@[simp]
theorem tensorIso_inv (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] {X Y : C}
    (iX : F.obj X ≅ G.obj X) (iY : F.obj Y ≅ G.obj Y) :
    (tensorIso F G iX iY).inv = δ G X Y ≫ (iX.inv ⊗ₘ iY.inv) ≫ μ F X Y := by
  rw [← Category.assoc]
  rfl

section StructuralNaturality

attribute [local simp] whiskerLeft_comp_tensorHom whiskerLeft_comp_tensorHom_assoc
  whiskerRight_comp_tensorHom whiskerRight_comp_tensorHom_assoc tensorHom_comp_whiskerLeft
  tensorHom_comp_whiskerLeft_assoc tensorHom_comp_whiskerRight tensorHom_comp_whiskerRight_assoc

omit [MonoidalCategory C] [MonoidalCategory D] in
/-- Naturality of the inverse of any isomorphism `i : X ≅ Y` with respect to a family of morphisms
`F.obj Z ⟶ G.obj Z`, derived from naturality of `i.hom`. -/
theorem map_iso_inv_comp_eq_of_map_iso_hom {F G : C ⥤ D} {X Y : C} (i : X ≅ Y)
    {eX : F.obj X ⟶ G.obj X} {eY : F.obj Y ⟶ G.obj Y}
    (h : F.map i.hom ≫ eY = eX ≫ G.map i.hom) :
    F.map i.inv ≫ eX = eY ≫ G.map i.inv := by
  rw [← cancel_epi (F.map i.hom), ← F.map_comp_assoc, i.hom_inv_id, F.map_id,
    Category.id_comp, reassoc_of% h, ← G.map_comp, i.hom_inv_id, G.map_id, Category.comp_id]

/-- Naturality of the forward associator with respect to a family of morphisms `e` satisfying the
tensor comparison formula. -/
theorem associator_hom_naturality_of_tensor {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    {e : ∀ Z : C, F.obj Z ⟶ G.obj Z}
    (htensor : ∀ A B, e (A ⊗ B) = δ F A B ≫ (e A ⊗ₘ e B) ≫ μ G A B) (X Y Z : C) :
    F.map (α_ X Y Z).hom ≫ e (X ⊗ (Y ⊗ Z)) = e ((X ⊗ Y) ⊗ Z) ≫ G.map (α_ X Y Z).hom := by
  rw [← cancel_epi (μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z),
    ← cancel_mono (δ G X (Y ⊗ Z) ≫ G.obj X ◁ δ G Y Z)]
  simp [htensor, ← Functor.OplaxMonoidal.associativity]

/-- Naturality of the forward left unitor with respect to a family of morphisms `e` satisfying the
unit and tensor comparison formulas. -/
theorem leftUnitor_hom_naturality_of_unit_tensor {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    {e : ∀ Z : C, F.obj Z ⟶ G.obj Z}
    (hunit : e (𝟙_ C) = η F ≫ ε G)
    (htensor : ∀ A B, e (A ⊗ B) = δ F A B ≫ (e A ⊗ₘ e B) ≫ μ G A B) (X : C) :
    F.map (λ_ X).hom ≫ e X = e (𝟙_ C ⊗ X) ≫ G.map (λ_ X).hom := by
  rw [← cancel_epi (ε F ▷ F.obj X ≫ μ F (𝟙_ _) X)]
  simp [hunit, htensor]
  simp [tensorHom_def']

/-- Naturality of the forward right unitor with respect to a family of morphisms `e` satisfying the
unit and tensor comparison formulas. -/
theorem rightUnitor_hom_naturality_of_unit_tensor {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    {e : ∀ Z : C, F.obj Z ⟶ G.obj Z}
    (hunit : e (𝟙_ C) = η F ≫ ε G)
    (htensor : ∀ A B, e (A ⊗ B) = δ F A B ≫ (e A ⊗ₘ e B) ≫ μ G A B) (X : C) :
    F.map (ρ_ X).hom ≫ e X = e (X ⊗ 𝟙_ C) ≫ G.map (ρ_ X).hom := by
  rw [← cancel_epi (F.obj X ◁ ε F ≫ μ F X (𝟙_ _))]
  simp [hunit, htensor]
  simp [MonoidalCategory.tensorHom_def]

/-- Naturality of left whiskering with respect to a family of morphisms `e` satisfying the tensor
comparison formula. -/
theorem whiskerLeft_naturality_of_tensor {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    {e : ∀ Z : C, F.obj Z ⟶ G.obj Z}
    (htensor : ∀ A B, e (A ⊗ B) = δ F A B ≫ (e A ⊗ₘ e B) ≫ μ G A B)
    (X : C) {Y₁ Y₂ : C} {f : Y₁ ⟶ Y₂} (hf : F.map f ≫ e Y₂ = e Y₁ ≫ G.map f) :
    F.map (X ◁ f) ≫ e (X ⊗ Y₂) = e (X ⊗ Y₁) ≫ G.map (X ◁ f) := by
  simp only [htensor, map_whiskerLeft, Category.assoc, μ_δ_assoc,
    whiskerLeft_comp_tensorHom_assoc, tensorHom_comp_whiskerLeft_assoc, hf]

/-- Naturality of right whiskering with respect to a family of morphisms `e` satisfying the tensor
comparison formula. -/
theorem whiskerRight_naturality_of_tensor {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    {e : ∀ Z : C, F.obj Z ⟶ G.obj Z}
    (htensor : ∀ A B, e (A ⊗ B) = δ F A B ≫ (e A ⊗ₘ e B) ≫ μ G A B)
    {X₁ X₂ : C} {f : X₁ ⟶ X₂} (Y : C) (hf : F.map f ≫ e X₂ = e X₁ ≫ G.map f) :
    F.map (f ▷ Y) ≫ e (X₂ ⊗ Y) = e (X₁ ⊗ Y) ≫ G.map (f ▷ Y) := by
  simp only [htensor, map_whiskerRight, Category.assoc, μ_δ_assoc,
    whiskerRight_comp_tensorHom_assoc, tensorHom_comp_whiskerRight_assoc, hf]

end StructuralNaturality

end CategoryTheory.Functor.Monoidal

namespace TauCeti

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D]

/-- Bundled strong monoidal functors. They form a category whose morphisms are the monoidal
natural transformations, which embeds fully faithfully into `LaxMonoidalFunctor C D`. -/
structure MonoidalFunctor extends C ⥤ D where
  /-- The strong monoidal structure of the underlying functor. -/
  monoidal : toFunctor.Monoidal := by infer_instance

namespace MonoidalFunctor

attribute [instance] monoidal

variable {C D}

/-- Constructor for `MonoidalFunctor C D`. -/
@[expose, simps toFunctor]
def of (F : C ⥤ D) [F.Monoidal] : MonoidalFunctor C D where
  toFunctor := F

/-- The underlying lax monoidal functor of a strong monoidal functor. It is reducible, so that
instance search sees the strong monoidal structure on the functor underlying it. -/
abbrev toLaxMonoidalFunctor (F : MonoidalFunctor C D) : LaxMonoidalFunctor C D where
  toFunctor := F.toFunctor

/-- Strong monoidal functors and monoidal natural transformations: the category induced from
`LaxMonoidalFunctor C D` along `toLaxMonoidalFunctor`. -/
instance : Category (MonoidalFunctor C D) :=
  inferInstanceAs (Category (InducedCategory _ toLaxMonoidalFunctor))

@[ext]
theorem hom_ext {F G : MonoidalFunctor C D} {α β : F ⟶ G} (h : α.hom.hom = β.hom.hom) : α = β :=
  InducedCategory.hom_ext (LaxMonoidalFunctor.hom_ext h)

@[simp]
theorem id_hom (F : MonoidalFunctor C D) :
    InducedCategory.Hom.hom (𝟙 F) = 𝟙 F.toLaxMonoidalFunctor :=
  (rfl)

@[reassoc, simp]
theorem comp_hom {F G H : MonoidalFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom :=
  (rfl)

/-- Constructor for morphisms of strong monoidal functors. -/
@[expose, simps]
def homMk {F G : MonoidalFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G :=
  ⟨⟨f, ‹NatTrans.IsMonoidal f›⟩⟩

/-- Constructor for isomorphisms of strong monoidal functors. -/
@[expose, simps]
def isoMk {F G : MonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] : F ≅ G where
  hom := homMk e.hom
  inv := homMk e.inv
  hom_inv_id := hom_ext e.hom_inv_id
  inv_hom_id := hom_ext e.inv_hom_id

variable (C D) in
/-- The forgetful functor from strong to lax monoidal functors. -/
@[expose, simps! obj map]
def forget : MonoidalFunctor C D ⥤ LaxMonoidalFunctor C D :=
  inducedFunctor _

variable (C D) in
/-- The forgetful functor from strong to lax monoidal functors is fully faithful. -/
def fullyFaithfulForget : (forget C D).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : (forget C D).Full :=
  (fullyFaithfulForget C D).full

instance : (forget C D).Faithful :=
  (fullyFaithfulForget C D).faithful

/-- The natural isomorphism between the underlying functors of an isomorphism of strong monoidal
functors. -/
@[expose, simps]
def toFunctorIso {F G : MonoidalFunctor C D} (e : F ≅ G) : F.toFunctor ≅ G.toFunctor where
  hom := e.hom.hom.hom
  inv := e.inv.hom.hom
  hom_inv_id := congrArg (fun α ↦ α.hom.hom) e.hom_inv_id
  inv_hom_id := congrArg (fun α ↦ α.hom.hom) e.inv_hom_id

instance {F G : MonoidalFunctor C D} (e : F ≅ G) : NatTrans.IsMonoidal (toFunctorIso e).hom :=
  e.hom.hom.isMonoidal

end MonoidalFunctor

end TauCeti
