/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Bifunctors on ideal quotients

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor which is additive in each variable, and let `I₁`, `I₂`
and `J` be morphism ideals of `C₁`, `C₂` and `D`. If `F` carries `I₁` into `J` in the first
variable and `I₂` into `J` in the second, then it descends to a bifunctor

```text
I₁.map₂ I₂ J F h₁ h₂ : C₁/I₁ ⥤ C₂/I₂ ⥤ D/J
```

on the ideal quotients. For a fixed object `X₁` of `C₁`, its partial functor on the class of
`X₁` is the functor `I₂.map J (F.obj X₁)` induced by `F.obj X₁`; symmetrically, its partial
functor on the class of an object `X₂` of `C₂` is `I₁.map J (F.flip.obj X₂)`. The descended
bifunctor is additive, and linear, in each variable, and it is the unique bifunctor agreeing
with `F` on representatives.

This is the descent that turns a tensor product preserving null-homotopic maps on either side
into a tensor product on homotopy categories. It follows the construction of
`CategoryTheory.Functor.map₂HomotopyCategory` for bifunctors on homotopy categories of
complexes, using Mathlib's `CategoryTheory.Quotient.lift` and
`CategoryTheory.Quotient.natTransLift`.

## Main definitions

* `TauCeti.MorphismIdeal.map₂`: the bifunctor on ideal quotients induced by a bifunctor
  carrying the ideals into each other in each variable.

## Main results

* `TauCeti.MorphismIdeal.quotientFunctor_comp_map₂_comp_whiskeringLeft`: the descended
  bifunctor agrees with `F` on representatives.
* `TauCeti.MorphismIdeal.map₂_unique`: it is the only bifunctor with this property.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti

open CategoryTheory

namespace MorphismIdeal

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (I₁ : MorphismIdeal C₁) (I₂ : MorphismIdeal C₂) (J : MorphismIdeal D)
  (F : C₁ ⥤ C₂ ⥤ D) [∀ X₁, (F.obj X₁).Additive] [∀ X₂, (F.flip.obj X₂).Additive]
  (h₁ : ∀ X₂, I₁ ≤ J.comap (F.flip.obj X₂)) (h₂ : ∀ X₁, I₂ ≤ J.comap (F.obj X₁))

include h₁ in
/-- The bifunctor on ideal quotients induced by a bifunctor `F`, additive in each variable,
which carries `I₁` into `J` in the first variable and `I₂` into `J` in the second. On the
classes of `X₁` and `X₂` it is the class of `(F.obj X₁).obj X₂`. -/
-- Expose the construction so that its values on classes of objects and morphisms have computed
-- types, as in `CategoryTheory.Functor.map₂HomotopyCategory`.
@[expose]
noncomputable def map₂ : I₁.Quotient ⥤ I₂.Quotient ⥤ J.Quotient :=
  CategoryTheory.Quotient.lift _
    { obj X₁ := I₂.lift (F.obj X₁ ⋙ J.quotientFunctor)
        (by simpa only [kerIdeal_comp_quotientFunctor] using h₂ X₁)
      map f := CategoryTheory.Quotient.natTransLift _
        (Functor.whiskerRight (F.map f) J.quotientFunctor)
      map_id X₁ := by
        apply CategoryTheory.Quotient.natTrans_ext
        ext X₂
        simp only [F.map_id]
        exact J.quotientFunctor.map_id _
      map_comp f g := by
        apply CategoryTheory.Quotient.natTrans_ext
        ext X₂
        simp only [F.map_comp]
        exact J.quotientFunctor.map_comp _ _ }
    (fun X₁ Y₁ f g hfg ↦ by
      apply CategoryTheory.Quotient.natTrans_ext
      ext X₂
      -- Both components are classes of components of `F`; their difference lies in `J`.
      rw [Functor.whiskerLeft_app, Functor.whiskerLeft_app,
        CategoryTheory.Quotient.natTransLift_app, CategoryTheory.Quotient.natTransLift_app,
        Functor.whiskerRight_app, Functor.whiskerRight_app, quotientFunctor_map_eq_iff,
        ← Functor.flip_obj_map, ← Functor.flip_obj_map, ← Functor.map_sub]
      exact (mem_comap_hom J _).1 (le_def.1 (h₁ X₂) _ ((I₁.rel_iff).1 hfg)))

/-- The partial functor of the descended bifunctor at the class of `X₁` is the functor induced
on quotients by `F.obj X₁`. -/
theorem map₂_obj_quotientFunctor_obj (X₁ : C₁) :
    (I₁.map₂ I₂ J F h₁ h₂).obj (I₁.quotientFunctor.obj X₁) = I₂.map J (F.obj X₁) (h₂ X₁) :=
  (I₂.map_eq_lift J (F.obj X₁) (h₂ X₁)).symm

/-- On classes of objects, the descended bifunctor is the class of the value of `F`. -/
@[simp]
theorem map₂_obj_obj (X₁ : C₁) (X₂ : C₂) :
    ((I₁.map₂ I₂ J F h₁ h₂).obj (I₁.quotientFunctor.obj X₁)).obj (I₂.quotientFunctor.obj X₂) =
      J.quotientFunctor.obj ((F.obj X₁).obj X₂) :=
  (rfl)

/-- On the class of a morphism in the second variable, the descended bifunctor is the class of
the corresponding morphism of `F`. -/
@[simp]
theorem map₂_obj_map (X₁ : C₁) {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂) :
    ((I₁.map₂ I₂ J F h₁ h₂).obj (I₁.quotientFunctor.obj X₁)).map (I₂.quotientFunctor.map g) =
      J.quotientFunctor.map ((F.obj X₁).map g) :=
  (rfl)

/-- On the class of a morphism in the first variable, the components of the descended bifunctor
are the classes of the components of `F`. -/
@[simp]
theorem map₂_map_app {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) (X₂ : C₂) :
    ((I₁.map₂ I₂ J F h₁ h₂).map (I₁.quotientFunctor.map f)).app (I₂.quotientFunctor.obj X₂) =
      J.quotientFunctor.map ((F.map f).app X₂) :=
  (rfl)

/-- The descended bifunctor agrees with `F` on representatives: precomposing it with both
quotient functors gives `F` followed by the quotient functor of `J`. -/
theorem quotientFunctor_comp_map₂_comp_whiskeringLeft :
    I₁.quotientFunctor ⋙ I₁.map₂ I₂ J F h₁ h₂ ⋙
        (Functor.whiskeringLeft _ _ _).obj I₂.quotientFunctor =
      F ⋙ (Functor.whiskeringRight _ _ _).obj J.quotientFunctor :=
  (rfl)

/-- The partial functor of the descended bifunctor in the first variable at the class of `X₂` is
the functor induced on quotients by `F.flip.obj X₂`. -/
theorem map₂_flip_obj_quotientFunctor_obj (X₂ : C₂) :
    (I₁.map₂ I₂ J F h₁ h₂).flip.obj (I₂.quotientFunctor.obj X₂) =
      I₁.map J (F.flip.obj X₂) (h₁ X₂) := by
  apply CategoryTheory.Quotient.lift_unique' I₁.rel
  rw [quotientFunctor_comp_map]
  -- Evaluate the agreement of the descended bifunctor with `F` on representatives at `X₂`.
  exact congrArg (fun G ↦ G.flip.obj X₂)
    (quotientFunctor_comp_map₂_comp_whiskeringLeft I₁ I₂ J F h₁ h₂)

/-- A bifunctor on the quotients that agrees with `F` on representatives is the descended
bifunctor. -/
theorem map₂_unique (G : I₁.Quotient ⥤ I₂.Quotient ⥤ J.Quotient)
    (hG : I₁.quotientFunctor ⋙ G ⋙ (Functor.whiskeringLeft _ _ _).obj I₂.quotientFunctor =
      F ⋙ (Functor.whiskeringRight _ _ _).obj J.quotientFunctor) :
    G = I₁.map₂ I₂ J F h₁ h₂ := by
  rw [← quotientFunctor_comp_map₂_comp_whiskeringLeft I₁ I₂ J F h₁ h₂] at hG
  -- Restricting along the second quotient functor is injective on objects and faithful, so the
  -- two functors out of `C₁` agree; then they agree out of the first quotient.
  have hobj (X₁ : C₁) : G.obj (I₁.quotientFunctor.obj X₁) =
      (I₁.map₂ I₂ J F h₁ h₂).obj (I₁.quotientFunctor.obj X₁) :=
    CategoryTheory.Quotient.lift_unique' _ _ _ (Functor.congr_obj hG X₁)
  apply CategoryTheory.Quotient.lift_unique' I₁.rel
  refine CategoryTheory.Functor.ext hobj (fun X₁ Y₁ f ↦ ?_)
  apply ((Functor.whiskeringLeft _ _ J.Quotient).obj I₂.quotientFunctor).map_injective
  have h := Functor.congr_hom hG f
  simp only [Functor.comp_map] at h
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, eqToHom_map, h]

instance (Z₂ : I₂.Quotient) : ((I₁.map₂ I₂ J F h₁ h₂).flip.obj Z₂).Additive :=
  -- `Z₂` is the class of its representative `Z₂.as`.
  Functor.additive_of_iso (eqToIso (map₂_flip_obj_quotientFunctor_obj I₁ I₂ J F h₁ h₂ Z₂.as).symm)

instance (Z₁ : I₁.Quotient) : ((I₁.map₂ I₂ J F h₁ h₂).obj Z₁).Additive :=
  -- `Z₁` is the class of its representative `Z₁.as`.
  Functor.additive_of_iso (eqToIso (map₂_obj_quotientFunctor_obj I₁ I₂ J F h₁ h₂ Z₁.as).symm)

instance : (I₁.map₂ I₂ J F h₁ h₂).Additive where
  map_add {_ _ f g} := by
    apply CategoryTheory.Quotient.natTrans_ext
    ext X₂
    -- Components at `X₂` are the values of the additive partial functor in the first variable.
    simp only [Functor.whiskerLeft_app, NatTrans.app_add, ← Functor.flip_obj_map, Functor.map_add]

section Linear

variable (R : Type*) [Semiring R] [Linear R C₁] [Linear R C₂] [Linear R D]
  [∀ X₁, (F.obj X₁).Linear R] [∀ X₂, (F.flip.obj X₂).Linear R]

instance (Z₂ : I₂.Quotient) : ((I₁.map₂ I₂ J F h₁ h₂).flip.obj Z₂).Linear R :=
  -- `Z₂` is the class of its representative `Z₂.as`.
  Functor.linear_of_iso R (eqToIso (map₂_flip_obj_quotientFunctor_obj I₁ I₂ J F h₁ h₂ Z₂.as).symm)

instance (Z₁ : I₁.Quotient) : ((I₁.map₂ I₂ J F h₁ h₂).obj Z₁).Linear R :=
  -- `Z₁` is the class of its representative `Z₁.as`.
  Functor.linear_of_iso R (eqToIso (map₂_obj_quotientFunctor_obj I₁ I₂ J F h₁ h₂ Z₁.as).symm)

instance : (I₁.map₂ I₂ J F h₁ h₂).Linear R where
  map_smul {_ _} f r := by
    apply CategoryTheory.Quotient.natTrans_ext
    ext X₂
    -- Components at `X₂` are the values of the linear partial functor in the first variable.
    simp only [Functor.whiskerLeft_app, NatTrans.app_smul, ← Functor.flip_obj_map,
      Functor.map_smul]

end Linear

end MorphismIdeal

end TauCeti
