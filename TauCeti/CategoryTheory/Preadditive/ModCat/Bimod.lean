/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.DeligneProduct.Basic
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

/-!
# Bimodules over preadditive categories

A `(D, C)`-bimodule is an additive functor contravariant in `D` and covariant in `C`,
defined on the opposite of the linear tensor product of `D` with `Cᵒᵖ`. The tensor product
over a commutative semiring `R` identifies the two actions of `R`. The tensor product over
`ℤ` gives arbitrary preadditive bimodules.

Fixing either argument restricts a bimodule to a one-sided module. The regular bimodule
of `C` is its Hom bifunctor, with the two actions given by precomposition and
postcomposition. Its slices are the representable modules on `C` and on `Cᵒᵖ`.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §2, pp. 13–14
  and §3, p. 15 (the two-variable Hom functor).
-/

public section

noncomputable section

open CategoryTheory Opposite

namespace TauCeti.ModCat

universe w v₁ v₂ u₁ u₂

section Bimodules

variable (R : Type*) [CommSemiring R]
  (D : Type u₁) [Category.{v₁} D] [Preadditive D] [Linear R D]
  (C : Type u₂) [Category.{v₂} C] [Preadditive C] [Linear R C]

/-- The category of `R`-central `(D, C)`-bimodules, contravariant in `D` and covariant in `C`. -/
abbrev LinearBimod := ModCat.{w} (LinearTensor R D Cᵒᵖ)

omit [Linear R D] [Linear R C] in
/-- The category of `(D, C)`-bimodules over preadditive categories. -/
abbrev Bimod := LinearBimod.{w} ℤ D C

namespace LinearBimod

variable {R D C}

/-- The value of a bimodule at an object of each category. -/
abbrev eval (M : LinearBimod.{w} R D C) (d : D) (c : C) : AddCommGrpCat.{w} :=
  M.obj.obj (op ⟨d, op c⟩)

-- Expose the object evaluation so the component formulas have the original source and target.
/-- Restrict a bimodule and its morphisms to the left variable by fixing `c : C`. -/
@[expose]
def sliceLeftFunctor (c : C) : LinearBimod.{w} R D C ⥤ ModCat.{w} D :=
  let L := LinearTensor.bifunctor R D Cᵒᵖ ⋙
    (evaluation Cᵒᵖ (LinearTensor R D Cᵒᵖ)).obj (op c)
  ObjectProperty.lift _ (AdditiveFunctor.forget _ _ ⋙
    (Functor.whiskeringLeft Dᵒᵖ _ AddCommGrpCat.{w}).obj L.op) fun M ↦
      (additiveFunctor_iff _).2 (by
        have : M.obj.Additive := (additiveFunctor_iff _).1 M.property
        exact inferInstanceAs (L.op ⋙ M.obj).Additive)

-- Expose the object evaluation so the component formulas have the original source and target.
/-- Restrict a bimodule and its morphisms to the right variable by fixing `d : D`. -/
@[expose]
def sliceRightFunctor (d : D) : LinearBimod.{w} R D C ⥤ ModCat.{w} Cᵒᵖ :=
  let L := (LinearTensor.bifunctor R D Cᵒᵖ).obj d
  ObjectProperty.lift _ (AdditiveFunctor.forget _ _ ⋙
    (Functor.whiskeringLeft Cᵒᵖᵒᵖ _ AddCommGrpCat.{w}).obj L.op) fun M ↦
      (additiveFunctor_iff _).2 (by
        have : M.obj.Additive := (additiveFunctor_iff _).1 M.property
        exact inferInstanceAs (L.op ⋙ M.obj).Additive)

/-- The left `D`-module obtained by fixing the right argument of `M`. -/
abbrev sliceLeft (M : LinearBimod.{w} R D C) (c : C) : ModCat.{w} D :=
  (sliceLeftFunctor (R := R) (D := D) c).obj M

/-- The right `C`-module obtained by fixing the left argument of `M`. -/
abbrev sliceRight (M : LinearBimod.{w} R D C) (d : D) : ModCat.{w} Cᵒᵖ :=
  (sliceRightFunctor (R := R) (C := C) d).obj M

@[simp]
theorem sliceLeft_obj_obj (M : LinearBimod.{w} R D C) (c : C) (d : Dᵒᵖ) :
    (M.sliceLeft c).obj.obj d = M.eval d.unop c := (rfl)

@[simp]
theorem sliceRight_obj_obj (M : LinearBimod.{w} R D C) (d : D) (c : Cᵒᵖᵒᵖ) :
    (M.sliceRight d).obj.obj c = M.eval d c.unop.unop := (rfl)

/-- A morphism in the left slice acts by tensoring it with the identity in the right slot. -/
theorem sliceLeft_obj_map (M : LinearBimod.{w} R D C) (c : C) {d d' : Dᵒᵖ} (f : d ⟶ d') :
    (M.sliceLeft c).obj.map f = M.obj.map (LinearTensor.tmul f.unop (𝟙 (op c))).op := (rfl)

/-- A morphism in the right slice acts by tensoring it with the identity in the left slot. -/
theorem sliceRight_obj_map (M : LinearBimod.{w} R D C) (d : D) {c c' : Cᵒᵖᵒᵖ} (f : c ⟶ c') :
    (M.sliceRight d).obj.map f = M.obj.map (LinearTensor.tmul (𝟙 d) f.unop).op := (rfl)

/-- A scalar acts in the same way in either slice at the shared value `M(d, c)`. -/
theorem sliceLeft_map_smul_id_eq_sliceRight (M : LinearBimod.{w} R D C) (d : D) (c : C) (r : R) :
    (M.sliceLeft c).obj.map (r • 𝟙 (op d)) =
      (M.sliceRight d).obj.map (r • 𝟙 (op (op c))) := by
  simp only [sliceLeft_obj_map, sliceRight_obj_map, Linear.unop_smul, unop_id,
    LinearTensor.smul_tmul, LinearTensor.tmul_smul]
  -- The two occurrences of the shared value use the same object after reducing the slices.
  rfl

@[simp]
theorem sliceLeftFunctor_map_hom_app (c : C) {M N : LinearBimod.{w} R D C} (f : M ⟶ N) (d : Dᵒᵖ) :
    ((sliceLeftFunctor c).map f).hom.app d = f.hom.app (op ⟨d.unop, op c⟩) := (rfl)

@[simp]
theorem sliceRightFunctor_map_hom_app (d : D) {M N : LinearBimod.{w} R D C} (f : M ⟶ N)
    (c : Cᵒᵖᵒᵖ) :
    ((sliceRightFunctor d).map f).hom.app c = f.hom.app (op ⟨d, c.unop⟩) := (rfl)

instance (c : C) : (sliceLeftFunctor (R := R) (D := D) c :
    LinearBimod.{w} R D C ⥤ ModCat.{w} D).Additive where
  map_add := rfl

instance (d : D) : (sliceRightFunctor (R := R) (C := C) d :
    LinearBimod.{w} R D C ⥤ ModCat.{w} Cᵒᵖ).Additive where
  map_add := rfl

end LinearBimod

end Bimodules

section Regular

variable (C : Type u₂) [Category.{v₂} C] [Preadditive C]

-- Expose the carrier so that subgroups of its values can be used with morphism membership.
/-- The regular `(C, C)`-bimodule sends `(X, Y)` to the additive group of morphisms `X ⟶ Y`. -/
@[expose]
def regularBimod : Bimod.{v₂} C C := by
  let H := (preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{v₂}).rightOp ⋙
    Functor.opHom C AddCommGrpCat.{v₂}
  letI : H.Additive := ⟨by
    intro X Y f g
    apply NatTrans.ext
    funext Z
    rw [NatTrans.app_add]
    apply Quiver.Hom.unop_inj
    exact AddCommGrpCat.ext fun h ↦ Preadditive.add_comp _ _ _ _ _ _⟩
  letI (X : C) : (H.obj X).Additive :=
    inferInstanceAs (((preadditiveCoyoneda : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{v₂}).obj (op X)).op).Additive
  exact ⟨(LinearTensor.lift ℤ H).leftOp, (additiveFunctor_iff _).2 inferInstance⟩

@[simp]
theorem regularBimod_eval (X Y : C) :
    (regularBimod C).eval X Y = AddCommGrpCat.of (X ⟶ Y) := (rfl)

/-- The regular bimodule acts on a pure tensor by precomposition and postcomposition. -/
@[simp]
theorem regularBimod_map_tmul {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : X' ⟶ Y) :
    (regularBimod C).obj.map (LinearTensor.tmul f g.op).op h = f ≫ h ≫ g := by
  simp only [regularBimod, Functor.leftOp_map, Quiver.Hom.unop_op, LinearTensor.lift_map_tmul]
  rfl

/-- The left regular slice acts by precomposition. -/
@[simp]
theorem regularBimod_sliceLeft_obj_map_apply (Y : C) {Z W : Cᵒᵖ} (f : Z ⟶ W) (h : Z.unop ⟶ Y) :
    ((regularBimod C).sliceLeft Y).obj.map f h = f.unop ≫ h :=
  (regularBimod_map_tmul C f.unop (𝟙 Y) h).trans
    (congrArg (f.unop ≫ ·) (Category.comp_id h))

/-- The right regular slice acts by postcomposition. -/
@[simp]
theorem regularBimod_sliceRight_obj_map_apply (X : C) {Z W : Cᵒᵖᵒᵖ} (f : Z ⟶ W)
    (h : X ⟶ Z.unop.unop) : ((regularBimod C).sliceRight X).obj.map f h = h ≫ f.unop.unop :=
  (regularBimod_map_tmul C (𝟙 X) f.unop.unop h).trans (Category.id_comp _)

/-- The left slice of the regular bimodule is the contravariant representable. -/
def regularBimodSliceLeftIso (Y : C) : (regularBimod C).sliceLeft Y ≅ (yoneda C).obj Y :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (F := ((regularBimod C).sliceLeft Y).obj) (G := ((yoneda C).obj Y).obj)
    (fun _ ↦ Iso.refl _) (fun {Z _} f ↦
      AddCommGrpCat.ext fun (h : Z.unop ⟶ Y) ↦ regularBimod_sliceLeft_obj_map_apply C Y f h)

@[simp]
theorem regularBimodSliceLeftIso_hom_app (Y : C) (Z : Cᵒᵖ) :
    (regularBimodSliceLeftIso C Y).hom.hom.app Z = 𝟙 (AddCommGrpCat.of (Z.unop ⟶ Y)) := (rfl)

@[simp]
theorem regularBimodSliceLeftIso_inv_app (Y : C) (Z : Cᵒᵖ) :
    (regularBimodSliceLeftIso C Y).inv.hom.app Z = 𝟙 (AddCommGrpCat.of (Z.unop ⟶ Y)) := (rfl)

/-- The right slice of the regular bimodule is the representable on the opposite category. -/
def regularBimodSliceRightIso (X : C) : (regularBimod C).sliceRight X ≅
    (yoneda Cᵒᵖ).obj (op X) :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (F := ((regularBimod C).sliceRight X).obj) (G := ((yoneda Cᵒᵖ).obj (op X)).obj)
    (fun Z ↦ AddEquiv.toAddCommGrpIso
      { toEquiv := (opEquiv Z.unop (op X)).symm
        map_add' := fun g h ↦ op_add C (g : X ⟶ Z.unop.unop) h }) (fun {Z _} f ↦
      AddCommGrpCat.ext fun (h : X ⟶ Z.unop.unop) ↦
        congrArg Quiver.Hom.op (regularBimod_sliceRight_obj_map_apply C X f h))

@[simp]
theorem regularBimodSliceRightIso_hom_app (X : C) (Z : Cᵒᵖᵒᵖ) :
    (regularBimodSliceRightIso C X).hom.hom.app Z =
      AddCommGrpCat.ofHom (opHom X Z.unop.unop) := (rfl)

@[simp]
theorem regularBimodSliceRightIso_inv_app (X : C) (Z : Cᵒᵖᵒᵖ) :
    (regularBimodSliceRightIso C X).inv.hom.app Z =
      AddCommGrpCat.ofHom (unopHom Z.unop (op X)) := (rfl)

end Regular

end TauCeti.ModCat
