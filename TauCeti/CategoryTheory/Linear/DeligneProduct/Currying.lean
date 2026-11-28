/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.DeligneProduct.Basic
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Currying contravariant additive functors on a tensor category

Restricting an additive functor on the opposite of `LinearTensor ℤ C D` to each
variable gives an additive functor from `Cᵒᵖ` to additive functors on `Dᵒᵖ`.
This restriction is an equivalence. In particular, it describes bimodules as
additive functors valued in a category of modules. The inverse is the extension
given by `LinearTensor.lift`, and `LinearTensor.naturality_of_tmul` extends natural
transformations from the two slices.

See B. Mitchell, *Rings with several objects*, J. Algebra 8 (1972), §2, pp. 13–14,
for the covariant formulation of the additive currying isomorphism.
-/

public section

namespace TauCeti.LinearTensor

open CategoryTheory Opposite

universe u₁ u₂ u₃ v₁ v₂ v₃

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
  (D : Type u₂) [Category.{v₂} D] [Preadditive D]
  (E : Type u₃) [Category.{v₃} E] [Preadditive E]

/-- Curry an additive functor on the opposite tensor category, treating the first
variable as the outer argument. The object formula is definitional so that
component maps have the expected source and target at each pair. -/
@[expose] def curryLeft : ((LinearTensor ℤ C D)ᵒᵖ ⥤+ E) ⥤ (Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)) where
  obj F := ⟨{
    obj X := AdditiveFunctor.of (((bifunctor ℤ C D).obj X.unop).op ⋙ F.obj)
    map f := ObjectProperty.homMk
      { app Y := F.obj.map (tmul f.unop (𝟙 Y.unop)).op
        naturality Y Y' g := by
          simp [← Functor.map_comp, ← op_comp, tmul_comp_tmul] }
    map_id X := by ext Y; simp [ObjectProperty.homMk]
    map_comp f g := by
      ext Y
      simp [ObjectProperty.homMk, ← Functor.map_comp, ← op_comp, tmul_comp_tmul] }, ⟨by
      intro X Y f g
      ext Z
      -- Addition of the bundled natural transformations is pointwise.
      change F.obj.map (tmul (f + g).unop (𝟙 Z.unop)).op =
        F.obj.map (tmul f.unop (𝟙 Z.unop)).op + F.obj.map (tmul g.unop (𝟙 Z.unop)).op
      simp only [unop_add, add_tmul, op_add, Functor.map_add]⟩⟩
  map η := ObjectProperty.homMk
    { app X := ObjectProperty.homMk
        { app Y := η.hom.app (op ⟨X.unop, Y.unop⟩)
          naturality Y Y' g := η.hom.naturality (tmul (𝟙 X.unop) g.unop).op }
      naturality X Y f := by
        ext Z
        exact η.hom.naturality (tmul f.unop (𝟙 Z.unop)).op }
  map_id F := (rfl)
  map_comp η θ := (rfl)

variable {C D E}

@[simp]
theorem curryLeft_obj_obj_obj (F : (LinearTensor ℤ C D)ᵒᵖ ⥤+ E) (X : Cᵒᵖ) (Y : Dᵒᵖ) :
    (((curryLeft C D E).obj F).obj.obj X).obj.obj Y = F.obj.obj (op ⟨X.unop, Y.unop⟩) :=
  (rfl)

@[simp]
theorem curryLeft_obj_obj_map (F : (LinearTensor ℤ C D)ᵒᵖ ⥤+ E) (X : Cᵒᵖ)
    {Y Y' : Dᵒᵖ} (g : Y ⟶ Y') :
    (((curryLeft C D E).obj F).obj.obj X).obj.map g = F.obj.map (tmul (𝟙 X.unop) g.unop).op :=
  (rfl)

@[simp]
theorem curryLeft_obj_map_app (F : (LinearTensor ℤ C D)ᵒᵖ ⥤+ E)
    {X X' : Cᵒᵖ} (f : X ⟶ X') (Y : Dᵒᵖ) :
    (((curryLeft C D E).obj F).obj.map f).hom.app Y = F.obj.map (tmul f.unop (𝟙 Y.unop)).op :=
  (rfl)

@[simp]
theorem curryLeft_map_app_app {F G : (LinearTensor ℤ C D)ᵒᵖ ⥤+ E} (η : F ⟶ G)
    (X : Cᵒᵖ) (Y : Dᵒᵖ) :
    (((curryLeft C D E).map η).hom.app X).hom.app Y = η.hom.app (op ⟨X.unop, Y.unop⟩) :=
  (rfl)

/-- Natural transformations between curried functors determine natural transformations
on the tensor category because the two types of slice morphisms generate its morphisms. -/
private def fullyFaithfulCurryLeft : (curryLeft C D E).FullyFaithful where
  preimage {F G} η := ObjectProperty.homMk (NatTrans.removeRightOp {
    app P := ((η.hom.app (op P.fst)).hom.app (op P.snd)).op
    naturality P Q t := naturality_of_tmul (G := G.obj.rightOp) (G' := F.obj.rightOp)
      (fun P ↦ ((η.hom.app (op P.fst)).hom.app (op P.snd)).op)
      (fun f Y ↦ by
        have h := congrArg (fun a ↦ a.hom.app (op Y)) (η.hom.naturality f.op)
        simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
          curryLeft_obj_map_app] at h
        exact Quiver.Hom.unop_inj h.symm)
      (fun X _ _ g ↦ by
        have h := (η.hom.app (op X)).hom.naturality g.op
        simp only [curryLeft_obj_obj_map] at h
        exact Quiver.Hom.unop_inj h.symm) t })
  map_preimage η := by ext X Y; rfl
  preimage_map {F G} η := by
    ext P
    -- Structure eta for `LinearTensor` identifies the pair of projections with `P.unop`.
    rfl

/-- Reverse the arrows in both variables of a curried contravariant functor so
that the linear tensor universal property can be applied with target `Eᵒᵖ`. -/
private def rightOpBifunctor (F : Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)) : C ⥤ D ⥤ Eᵒᵖ where
  obj X := (F.obj.obj (op X)).obj.rightOp
  map f := (F.obj.map f.op).hom.rightOp
  map_id X := by ext Y; simp
  map_comp f g := by ext Y; simp

private instance (F : Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)) (X : C) :
    ((rightOpBifunctor F).obj X).Additive :=
  inferInstanceAs (F.obj.obj (op X)).obj.rightOp.Additive

private instance (F : Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)) : (rightOpBifunctor F).Additive where
  map_add := by
    intro X Y f g
    ext Z
    -- After taking `unop`, the right-opposite map is evaluation at `op Z`.
    change (F.obj.map (f + g).op).hom.app (op Z) = _
    rw [op_add]
    exact congrArg (fun η ↦ η.hom.app (op Z)) (F.obj.map_add (f := f.op) (g := g.op))

/-- The additive functor obtained by extending the two actions to the tensor category. -/
private def uncurryLeftObj (F : Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)) :
    (LinearTensor ℤ C D)ᵒᵖ ⥤+ E :=
  AdditiveFunctor.of (lift ℤ (rightOpBifunctor F)).leftOp

private theorem uncurryLeftObj_map_tmul (F : Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E))
    {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (uncurryLeftObj F).obj.map (tmul f g).op =
      (F.obj.obj (op X')).obj.map g.op ≫ (F.obj.map f.op).hom.app (op Y) := by
  -- Unbundle the additive functor and evaluate its left-opposite map to use the lift formula.
  change ((lift ℤ (rightOpBifunctor F)).map (tmul f g)).unop = _
  rw [lift_map_tmul]
  -- Evaluate the right-opposite bifunctor so the composite has explicit opposite endpoints.
  change (((F.obj.map f.op).hom.app (op Y)).op ≫ ((F.obj.obj (op X')).obj.map g.op).op).unop = _
  rw [← op_comp, Quiver.Hom.unop_op]

private def curryLeftUncurryLeftObjIso (F : Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)) :
    (curryLeft C D E).obj (uncurryLeftObj F) ≅ F :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ (NatIso.ofComponents (fun Y ↦ Iso.refl _) (by
      intro Y Y' g
      -- Evaluating the identity comparison removes the functor and subcategory projections.
      change (uncurryLeftObj F).obj.map (tmul (𝟙 X.unop) g.unop).op ≫ 𝟙 _ =
        𝟙 _ ≫ (F.obj.obj X).obj.map g
      simp only [Category.comp_id, Category.id_comp]
      simpa using! uncurryLeftObj_map_tmul F (𝟙 X.unop) g.unop))) (by
    intro X X' f
    ext Y
    -- Evaluate the identity comparison at the second argument.
    change (uncurryLeftObj F).obj.map (tmul f.unop (𝟙 Y.unop)).op ≫ 𝟙 _ =
      𝟙 _ ≫ (F.obj.map f).hom.app Y
    simp only [Category.comp_id, Category.id_comp]
    simpa using! uncurryLeftObj_map_tmul F f.unop (𝟙 Y.unop)))

@[local simp]
private theorem curryLeftUncurryLeftObjIso_hom_app_app
    (F : Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)) (X : Cᵒᵖ) (Y : Dᵒᵖ) :
    ((curryLeftUncurryLeftObjIso F).hom.hom.app X).hom.app Y = 𝟙 ((F.obj.obj X).obj.obj Y) :=
  rfl

@[local simp]
private theorem curryLeftUncurryLeftObjIso_inv_app_app
    (F : Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)) (X : Cᵒᵖ) (Y : Dᵒᵖ) :
    ((curryLeftUncurryLeftObjIso F).inv.hom.app X).hom.app Y = 𝟙 ((F.obj.obj X).obj.obj Y) :=
  rfl

variable (C D E)

/-- Extend a curried additive functor to the opposite tensor category. On pairs this
evaluates the two arguments, and on a pure tensor it composes the two actions. -/
def uncurryLeft :
    (Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)) ⥤ ((LinearTensor ℤ C D)ᵒᵖ ⥤+ E) where
  obj := uncurryLeftObj
  map {F G} η := fullyFaithfulCurryLeft.preimage
    ((curryLeftUncurryLeftObjIso F).hom ≫ η ≫ (curryLeftUncurryLeftObjIso G).inv)
  map_id F := fullyFaithfulCurryLeft.map_injective (by simp)
  map_comp η θ := fullyFaithfulCurryLeft.map_injective (by simp)

variable {C D E}

@[simp]
theorem uncurryLeft_obj_obj (F : Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)) (P : LinearTensor ℤ C D) :
    ((uncurryLeft C D E).obj F).obj.obj (op P) = (F.obj.obj (op P.fst)).obj.obj (op P.snd) :=
  (rfl)

/-- The uncurried action on a pure tensor composes the two slice actions in reverse
order, with the endpoints identified by `uncurryLeft_obj_obj`. -/
@[simp]
theorem uncurryLeft_obj_map_tmul (F : Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E))
    {X X' : C} {Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((uncurryLeft C D E).obj F).obj.map (tmul f g).op =
      eqToHom (uncurryLeft_obj_obj F ⟨X', Y'⟩) ≫ (F.obj.obj (op X')).obj.map g.op ≫
        (F.obj.map f.op).hom.app (op Y) ≫ eqToHom (uncurryLeft_obj_obj F ⟨X, Y⟩).symm := by
  -- The object identifications are definitionally reflexive inside the construction.
  change (uncurryLeftObj F).obj.map (tmul f g).op =
    𝟙 _ ≫ (F.obj.obj (op X')).obj.map g.op ≫ (F.obj.map f.op).hom.app (op Y) ≫ 𝟙 _
  simpa only [Category.id_comp, Category.comp_id] using uncurryLeftObj_map_tmul F f g

@[simp]
theorem uncurryLeft_map_app {F G : Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)} (η : F ⟶ G) (P : LinearTensor ℤ C D) :
    ((uncurryLeft C D E).map η).hom.app (op P) =
      eqToHom (uncurryLeft_obj_obj F P) ≫ (η.hom.app (op P.fst)).hom.app (op P.snd) ≫
        eqToHom (uncurryLeft_obj_obj G P).symm := by
  -- The preimage is computed by evaluation of the conjugated transformation.
  change ((((curryLeftUncurryLeftObjIso F).hom ≫ η ≫
    (curryLeftUncurryLeftObjIso G).inv).hom.app (op P.fst)).hom.app (op P.snd)) =
    𝟙 _ ≫ (η.hom.app (op P.fst)).hom.app (op P.snd) ≫ 𝟙 _
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    curryLeftUncurryLeftObjIso_hom_app_app, curryLeftUncurryLeftObjIso_inv_app_app]
  -- Both sides now evaluate to the same composite at the pointwise objects.
  rfl

private def uncurryLeftCompCurryLeftIso :
    uncurryLeft C D E ⋙ curryLeft C D E ≅ 𝟭 _ :=
  NatIso.ofComponents curryLeftUncurryLeftObjIso (by simp [uncurryLeft])

instance : (curryLeft C D E).Additive where
  map_add := by
    intro F G η θ
    ext X Y
    rfl

instance : (uncurryLeft C D E).Additive := by
  let := (fullyFaithfulCurryLeft (C := C) (D := D) (E := E)).faithful
  let : (uncurryLeft C D E ⋙ curryLeft C D E).Additive :=
    Functor.additive_of_iso uncurryLeftCompCurryLeftIso.symm
  exact Functor.additive_of_comp_faithful _ (curryLeft C D E)

variable (C D E)

/-- Additive contravariant functors on the tensor of two preadditive categories are equivalent
to additive contravariant functors in the first variable with values in the category of
additive contravariant functors in the second. -/
def curryLeftEquivalence :
    ((LinearTensor ℤ C D)ᵒᵖ ⥤+ E) ≌ (Cᵒᵖ ⥤+ (Dᵒᵖ ⥤+ E)) :=
  CategoryTheory.Equivalence.mk (curryLeft C D E) (uncurryLeft C D E)
    (NatIso.ofComponents (fun F ↦ fullyFaithfulCurryLeft.preimageIso
      (curryLeftUncurryLeftObjIso ((curryLeft C D E).obj F)).symm) (by
        intro F G η
        apply fullyFaithfulCurryLeft.map_injective
        simp only [Functor.map_comp]
        exact uncurryLeftCompCurryLeftIso.inv.naturality ((curryLeft C D E).map η)))
    uncurryLeftCompCurryLeftIso

@[simp]
theorem curryLeftEquivalence_functor :
    (curryLeftEquivalence C D E).functor = curryLeft C D E :=
  (rfl)

@[simp]
theorem curryLeftEquivalence_inverse :
    (curryLeftEquivalence C D E).inverse = uncurryLeft C D E :=
  (rfl)

end TauCeti.LinearTensor
