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

A `(D, C)`-bimodule is an additive functor to `AddCommGrpCat` from the opposite of the
linear tensor product of `D` with `Cᵒᵖ`. It is contravariant in `D` and covariant in `C`.
The tensor product over a commutative semiring `R` identifies the two actions of `R`.
The tensor product over `ℤ` gives arbitrary preadditive bimodules.

Fixing either argument restricts a bimodule to a one-sided module. The regular bimodule
of `C` is its Hom bifunctor, with the two actions given by precomposition and
postcomposition. The regular bimodule is the ambient object for two-sided ideals of `C`.
Its slices are representable modules on `C` and on `Cᵒᵖ`, and serve as ambient modules
for one-sided ideals.

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

/-- Restrict a bimodule along an additive functor into its tensor category. -/
abbrev restrict {A : Type*} [Category* A] [Preadditive A]
    (L : A ⥤ LinearTensor R D Cᵒᵖ) [L.Additive] : LinearBimod.{w} R D C ⥤ ModCat.{w} A :=
  ObjectProperty.lift _ (AdditiveFunctor.forget _ _ ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{w}).obj L.op) fun M ↦
      (additiveFunctor_iff (L.op ⋙ M.obj)).2 inferInstance

-- Expose the object evaluation so the component formulas have the original source and target.
/-- Restrict a bimodule and its morphisms to the left variable by fixing `c : C`. -/
@[expose]
def sliceLeftFunctor (c : C) : LinearBimod.{w} R D C ⥤ ModCat.{w} D :=
  restrict (LinearTensor.bifunctor R D Cᵒᵖ ⋙ (evaluation Cᵒᵖ _).obj (op c))

-- Expose the object evaluation so the component formulas have the original source and target.
/-- Restrict a bimodule and its morphisms to the right variable by fixing `d : D`. -/
@[expose]
def sliceRightFunctor (d : D) : LinearBimod.{w} R D C ⥤ ModCat.{w} Cᵒᵖ :=
  restrict ((LinearTensor.bifunctor R D Cᵒᵖ).obj d)

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

/-- The left slice applies the bimodule to the opposite of `f.unop` tensored with the
identity in the right slot. -/
@[simp]
theorem sliceLeft_obj_map (M : LinearBimod.{w} R D C) (c : C) {d d' : Dᵒᵖ} (f : d ⟶ d') :
    (M.sliceLeft c).obj.map f = M.obj.map (LinearTensor.tmul f.unop (𝟙 (op c))).op := (rfl)

/-- The right slice applies the bimodule to the opposite of the tensor of the identity in the
left slot with `f.unop`. -/
@[simp]
theorem sliceRight_obj_map (M : LinearBimod.{w} R D C) (d : D) {c c' : Cᵒᵖᵒᵖ} (f : c ⟶ c') :
    (M.sliceRight d).obj.map f = M.obj.map (LinearTensor.tmul (𝟙 d) f.unop).op := (rfl)

/-- A pure tensor acts by the right slice map followed by the left slice map. -/
theorem obj_map_tmul_op_eq_sliceRight_comp_sliceLeft (M : LinearBimod.{w} R D C)
    {d d' : D} {c c' : C} (f : d ⟶ d') (g : c ⟶ c') :
    M.obj.map (LinearTensor.tmul f g.op).op =
      (M.sliceRight d').obj.map g.op.op ≫ (M.sliceLeft c').obj.map f.op := by
  calc
    _ = M.obj.map (LinearTensor.tmul (𝟙 d') g.op).op ≫
        M.obj.map (LinearTensor.tmul f (𝟙 (op c'))).op := by
      rw [← M.obj.map_comp, ← op_comp, LinearTensor.tmul_eq_comp f g.op]
    _ = _ := by
      simp only [sliceLeft_obj_map, sliceRight_obj_map, Quiver.Hom.unop_op]
      rfl

/-- A pure tensor acts by the left slice map followed by the right slice map. -/
theorem obj_map_tmul_op_eq_sliceLeft_comp_sliceRight (M : LinearBimod.{w} R D C)
    {d d' : D} {c c' : C} (f : d ⟶ d') (g : c ⟶ c') :
    M.obj.map (LinearTensor.tmul f g.op).op =
      (M.sliceLeft c).obj.map f.op ≫ (M.sliceRight d).obj.map g.op.op := by
  calc
    _ = M.obj.map (LinearTensor.tmul f (𝟙 (op c))).op ≫
        M.obj.map (LinearTensor.tmul (𝟙 d) g.op).op := by
      rw [← M.obj.map_comp, ← op_comp]
      simp
    _ = _ := by
      simp only [sliceLeft_obj_map, sliceRight_obj_map, Quiver.Hom.unop_op]
      rfl

/-- A scalar acts in the same way in either slice at the shared value `M(d, c)`. -/
theorem sliceLeft_obj_map_smul_id_eq_sliceRight_obj_map_smul_id
    (M : LinearBimod.{w} R D C) (d : D) (c : C) (r : R) :
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
    LinearBimod.{w} R D C ⥤ ModCat.{w} D).Additive := by
  unfold sliceLeftFunctor
  infer_instance

instance (d : D) : (sliceRightFunctor (R := R) (C := C) d :
    LinearBimod.{w} R D C ⥤ ModCat.{w} Cᵒᵖ).Additive := by
  unfold sliceRightFunctor
  infer_instance

end LinearBimod

end Bimodules

section Regular

variable (R : Type*) [CommSemiring R] (C : Type u₂) [Category.{v₂} C]
  [Preadditive C] [Linear R C]

-- Mathlib's `CategoryTheory.preadditiveCoyoneda` supplies the Hom groups.
-- `TensorProduct.lift` extends the action to all tensor morphisms using the `R`-linearity of
-- precomposition and postcomposition.
-- Expose the carrier so that subgroups of its values can be used with morphism membership.
/-- The regular `R`-central bimodule assigns the additive group `X ⟶ Y` to `(X, Y)`.
For `f : X ⟶ X'` and `g : Y ⟶ Y'`, the pure tensor of `f` and `g.op` acts on
`h : X' ⟶ Y` by `h ↦ f ≫ h ≫ g`. -/
@[expose]
def linearRegularBimod : LinearBimod.{v₂} R C C := by
  let action (P Q : LinearTensor R C Cᵒᵖ) :
      (P ⟶ Q) →ₗ[R] ((Q.fst ⟶ Q.snd.unop) →ₗ[R] (P.fst ⟶ P.snd.unop)) :=
    TensorProduct.lift (LinearMap.mk₂ R
      (fun f g ↦ (Linear.rightComp R P.fst g.unop).comp (Linear.leftComp R Q.snd.unop f))
      (fun f f' g ↦ LinearMap.ext fun h ↦ by simp [Preadditive.add_comp])
      (fun r f g ↦ LinearMap.ext fun h ↦ by simp)
      (fun f g g' ↦ LinearMap.ext fun h ↦ by simp [unop_add, Preadditive.comp_add])
      (fun r f g ↦ LinearMap.ext fun h ↦ by simp [Linear.unop_smul]))
  have action_tmul {X X' : C} {Y Y' : Cᵒᵖ} (f : X ⟶ X') (g : Y ⟶ Y') (h : X' ⟶ Y'.unop) :
      action ⟨X, Y⟩ ⟨X', Y'⟩ (LinearTensor.tmul f g) h = (f ≫ h) ≫ g.unop := rfl
  let F : LinearTensor R C Cᵒᵖ ⥤ AddCommGrpCat.{v₂}ᵒᵖ :=
    { obj P := op ((preadditiveCoyoneda.obj (op P.fst)).obj P.snd.unop)
      map {P Q} t := (AddCommGrpCat.ofHom (action P Q t).toAddMonoidHom).op
      map_id P := by
        obtain ⟨X, Y⟩ := P
        refine Quiver.Hom.unop_inj <| AddCommGrpCat.ext fun h ↦ ?_
        -- The identity in the opposite category acts as the identity on the Hom group.
        change action ⟨X, Y⟩ ⟨X, Y⟩ (𝟙 _) h = h
        rw [← LinearTensor.tmul_id_id (k := R) X Y, action_tmul]
        simp
      map_comp {P Q S} t u := by
        obtain ⟨X, Y⟩ := P
        obtain ⟨X', Y'⟩ := Q
        obtain ⟨X'', Y''⟩ := S
        refine Quiver.Hom.unop_inj <| AddCommGrpCat.ext fun h ↦ ?_
        -- Unwrap the opposite maps so tensor induction works on linear-map applications.
        change action ⟨X, Y⟩ ⟨X'', Y''⟩ (t ≫ u) h =
          action ⟨X, Y⟩ ⟨X', Y'⟩ t (action ⟨X', Y'⟩ ⟨X'', Y''⟩ u h)
        induction t using LinearTensor.hom_induction_on with
        | add t t' ht ht' =>
          simp [Preadditive.add_comp, map_add, ht, ht']
        | tmul f g =>
          induction u using LinearTensor.hom_induction_on with
          | add u u' hu hu' =>
            simp [Preadditive.comp_add, map_add, hu, hu']
          | tmul f' g' =>
            simp [LinearTensor.tmul_comp_tmul, action_tmul, Category.assoc] }
  letI : F.Additive := ⟨by
    intro P Q t u
    refine Quiver.Hom.unop_inj <| AddCommGrpCat.ext fun h ↦ ?_
    -- Addition of the opposite morphisms is pointwise addition of the underlying linear maps.
    change action P Q (t + u) h = action P Q t h + action P Q u h
    rw [map_add]
    rfl⟩
  exact AdditiveFunctor.of F.leftOp

/-- The regular bimodule of a preadditive category, using the tensor product over `ℤ`. -/
abbrev regularBimod : Bimod.{v₂} C C := linearRegularBimod ℤ C

@[simp]
theorem linearRegularBimod_eval (X Y : C) :
    (linearRegularBimod R C).eval X Y = AddCommGrpCat.of (X ⟶ Y) := (rfl)

/-- The regular bimodule acts on a pure tensor by precomposition and postcomposition. -/
@[simp]
theorem linearRegularBimod_obj_map_tmul_apply {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : X' ⟶ Y) :
    (linearRegularBimod R C).obj.map (LinearTensor.tmul f g.op).op h = f ≫ h ≫ g :=
  Category.assoc f h g

-- Simplify regular slice applications before the general simp rules rewrite their slice maps.
/-- The left regular slice acts by precomposition. -/
@[simp↓]
theorem linearRegularBimod_sliceLeft_obj_map_apply (Y : C) {Z W : Cᵒᵖ}
    (f : Z ⟶ W) (h : Z.unop ⟶ Y) :
    ((linearRegularBimod R C).sliceLeft Y).obj.map f h = f.unop ≫ h := by
  rw [LinearBimod.sliceLeft_obj_map]
  simpa only [op_id, Category.comp_id] using!
    linearRegularBimod_obj_map_tmul_apply R C f.unop (𝟙 Y) h

/-- The right regular slice acts by postcomposition. -/
@[simp↓]
theorem linearRegularBimod_sliceRight_obj_map_apply (X : C) {Z W : Cᵒᵖᵒᵖ} (f : Z ⟶ W)
    (h : X ⟶ Z.unop.unop) :
    ((linearRegularBimod R C).sliceRight X).obj.map f h = h ≫ f.unop.unop := by
  rw [LinearBimod.sliceRight_obj_map]
  simpa only [Quiver.Hom.op_unop, Category.id_comp] using!
    linearRegularBimod_obj_map_tmul_apply R C (𝟙 X) f.unop.unop h

/-- The left slice of the regular bimodule is the contravariant representable. -/
def linearRegularBimodSliceLeftIso (Y : C) :
    (linearRegularBimod R C).sliceLeft Y ≅ (yoneda C).obj Y :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (F := ((linearRegularBimod R C).sliceLeft Y).obj) (G := ((yoneda C).obj Y).obj)
    (fun _ ↦ Iso.refl _) (fun {Z _} f ↦
      AddCommGrpCat.ext fun (h : Z.unop ⟶ Y) ↦ linearRegularBimod_sliceLeft_obj_map_apply R C Y f h)

@[simp]
theorem linearRegularBimodSliceLeftIso_hom_hom_app (Y : C) (Z : Cᵒᵖ) :
    (linearRegularBimodSliceLeftIso R C Y).hom.hom.app Z =
      𝟙 (AddCommGrpCat.of (Z.unop ⟶ Y)) := (rfl)

@[simp]
theorem linearRegularBimodSliceLeftIso_inv_hom_app (Y : C) (Z : Cᵒᵖ) :
    (linearRegularBimodSliceLeftIso R C Y).inv.hom.app Z =
      𝟙 (AddCommGrpCat.of (Z.unop ⟶ Y)) := (rfl)

/-- The right slice of the regular bimodule is the representable on the opposite category. -/
def linearRegularBimodSliceRightIso (X : C) : (linearRegularBimod R C).sliceRight X ≅
    (yoneda Cᵒᵖ).obj (op X) :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (F := ((linearRegularBimod R C).sliceRight X).obj) (G := ((yoneda Cᵒᵖ).obj (op X)).obj)
    (fun Z ↦ AddEquiv.toAddCommGrpIso
      { toEquiv := (opEquiv Z.unop (op X)).symm
        map_add' := fun g h ↦ op_add C (g : X ⟶ Z.unop.unop) h }) (fun {Z _} f ↦
      AddCommGrpCat.ext fun (h : X ⟶ Z.unop.unop) ↦
        congrArg Quiver.Hom.op (linearRegularBimod_sliceRight_obj_map_apply R C X f h))

@[simp]
theorem linearRegularBimodSliceRightIso_hom_hom_app (X : C) (Z : Cᵒᵖᵒᵖ) :
    (linearRegularBimodSliceRightIso R C X).hom.hom.app Z =
      AddCommGrpCat.ofHom (opHom X Z.unop.unop) := (rfl)

@[simp]
theorem linearRegularBimodSliceRightIso_inv_hom_app (X : C) (Z : Cᵒᵖᵒᵖ) :
    (linearRegularBimodSliceRightIso R C X).inv.hom.app Z =
      AddCommGrpCat.ofHom (unopHom Z.unop (op X)) := (rfl)

end Regular

end TauCeti.ModCat
