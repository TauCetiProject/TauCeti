/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Quotient.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Duals in quotients by monoidal relations

The quotient of a monoidal category by a monoidal relation inherits the chosen left and
right duals of its objects. Its evaluations and coevaluations are the classes of the original
ones, and taking adjoint mates commutes with the quotient functor. In particular, left rigidity,
right rigidity and rigidity descend to the quotient.

The duals follow `CategoryTheory.Functor.mapHasLeftDual` and
`CategoryTheory.Functor.mapHasRightDual`, reusing `CategoryTheory.Functor.mapExactPairing` along
the strong monoidal quotient functor. Their carriers are specified explicitly so that the
evaluation equations can be used without unfolding the generic dual-transfer constructions.
The per-object dual instances use the caller's dual of the underlying object `X.as`, so they
need a dual only on the corresponding side, not rigidity of the whole source category.

The right-dual comparison of the quotient functor is the identity. A morphism from the chosen
right dual of the image of `X` into the image of a right dual `Y` of `X` can be identified as a
mapped morphism by right-whiskering with the image of `X` and composing with the image of
`ε_ X Y`. For a right rigid source, the right-dual tensor comparison and unit dual identification
descend, as do the tensor and unit comparisons of the double-right-dual functor (`μ`, `δ`, `ε`,
`η`). These equations supply the comparison data for descent of pivotal structures. The bidual
comparison of the quotient functor is the identity, and factoring a strong monoidal functor
through the quotient retains its dual and bidual comparisons.

In particular, this gives the rigid structure used in semisimplification of diagram categories
by tensor ideals. For the Temperley–Lieb setting, see F. M. Goodman and H. Wenzl, *Ideals in the
Temperley–Lieb category*, appendix to M. H. Freedman, *A magnetic model with a possible
Chern–Simons phase*, Comm. Math. Phys. 234 (2003), 129–183.
-/

public section

universe v u

namespace CategoryTheory.Quotient

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {r : HomRel C} [r.IsMonoidal]

/-- The left dual of a quotient object is the class of its underlying object's chosen left
dual. -/
noncomputable instance instHasLeftDual (X : Quotient r) [HasLeftDual X.as] :
    HasLeftDual X where
  leftDual := (functor r).obj (ᘁ(X.as) : C)
  exact := (functor r).mapExactPairing (ᘁ(X.as) : C) X.as

/-- The right dual of a quotient object is the class of its underlying object's chosen right
dual. -/
noncomputable instance instHasRightDual (X : Quotient r) [HasRightDual X.as] :
    HasRightDual X where
  rightDual := (functor r).obj ((X.as)ᘁ : C)
  exact := (functor r).mapExactPairing X.as ((X.as)ᘁ : C)

-- Typeclass search does not unfold the quotient functor's object map to identify its underlying
-- object. These delegates preserve the source dual choices at that public presentation too.
/-- The image of an object with a left dual has the descended left dual. -/
noncomputable instance instHasLeftDualObj (X : C) [HasLeftDual X] :
    HasLeftDual ((functor r).obj X) :=
  inferInstanceAs (HasLeftDual (Quotient.mk X : Quotient r))

/-- The image of an object with a right dual has the descended right dual. -/
noncomputable instance instHasRightDualObj (X : C) [HasRightDual X] :
    HasRightDual ((functor r).obj X) :=
  inferInstanceAs (HasRightDual (Quotient.mk X : Quotient r))

/-- The left dual in the quotient is the class of the chosen left dual in the source. -/
@[simp]
theorem leftDual_eq (X : Quotient r) [HasLeftDual X.as] :
    (ᘁX : Quotient r) = (functor r).obj (ᘁ(X.as) : C) :=
  (rfl)

/-- The right dual in the quotient is the class of the chosen right dual in the source. -/
@[simp]
theorem rightDual_eq (X : Quotient r) [HasRightDual X.as] :
    Xᘁ = (functor r).obj ((X.as)ᘁ : C) :=
  (rfl)

/-- The evaluation for the descended left dual is the class of the original evaluation. -/
@[simp]
theorem evaluation_leftDual (X : Quotient r) [HasLeftDual X.as] :
    ε_ (ᘁX) X = (functor r).map (ε_ (ᘁ(X.as) : C) X.as) := by
  exact (Functor.mapExactPairing_evaluation
    (F := functor r) (ᘁ(X.as) : C) X.as).trans (by simp)

/-- The coevaluation for the descended left dual is the class of the original coevaluation. -/
@[simp]
theorem coevaluation_leftDual (X : Quotient r) [HasLeftDual X.as] :
    η_ (ᘁX) X = (functor r).map (η_ (ᘁ(X.as) : C) X.as) := by
  exact (Functor.mapExactPairing_coevaluation
    (F := functor r) (ᘁ(X.as) : C) X.as).trans (by simp)

/-- The evaluation for the descended right dual is the class of the original evaluation. -/
@[simp]
theorem evaluation_rightDual (X : Quotient r) [HasRightDual X.as] :
    ε_ X Xᘁ = (functor r).map (ε_ X.as ((X.as)ᘁ : C)) := by
  exact (Functor.mapExactPairing_evaluation
    (F := functor r) X.as ((X.as)ᘁ : C)).trans (by simp)

/-- The coevaluation for the descended right dual is the class of the original coevaluation. -/
@[simp]
theorem coevaluation_rightDual (X : Quotient r) [HasRightDual X.as] :
    η_ X Xᘁ = (functor r).map (η_ X.as ((X.as)ᘁ : C)) := by
  exact (Functor.mapExactPairing_coevaluation
    (F := functor r) X.as ((X.as)ᘁ : C)).trans (by simp)

-- These equations retain the literal source object and its caller-provided dual instance.
-- Rewriting the general equations first leaves a dependent dual of the underlying-object
-- projection, which the simplifier cannot identify with that caller's instance. The mapped-object
-- rules therefore run before simplification of their dependent arguments.
/-- The left dual of the image of an object is the image of its chosen left dual. -/
@[simp↓]
theorem leftDual_obj (X : C) [HasLeftDual X] :
    (ᘁ((functor r).obj X) : Quotient r) = (functor r).obj (ᘁX) :=
  leftDual_eq (Quotient.mk X)

/-- The right dual of the image of an object is the image of its chosen right dual. -/
@[simp↓]
theorem rightDual_obj (X : C) [HasRightDual X] :
    ((functor r).obj X)ᘁ = (functor r).obj (Xᘁ) :=
  rightDual_eq (Quotient.mk X)

/-- Evaluation on the image of an object with its descended left dual. -/
@[simp↓]
theorem evaluation_leftDual_obj (X : C) [HasLeftDual X] :
    ε_ (ᘁ((functor r).obj X)) ((functor r).obj X) = (functor r).map (ε_ (ᘁX) X) :=
  evaluation_leftDual (Quotient.mk X)

/-- Coevaluation on the image of an object with its descended left dual. -/
@[simp↓]
theorem coevaluation_leftDual_obj (X : C) [HasLeftDual X] :
    η_ (ᘁ((functor r).obj X)) ((functor r).obj X) = (functor r).map (η_ (ᘁX) X) :=
  coevaluation_leftDual (Quotient.mk X)

/-- Evaluation on the image of an object with its descended right dual. -/
@[simp↓]
theorem evaluation_rightDual_obj (X : C) [HasRightDual X] :
    ε_ ((functor r).obj X) ((functor r).obj X)ᘁ = (functor r).map (ε_ X Xᘁ) :=
  evaluation_rightDual (Quotient.mk X)

/-- Coevaluation on the image of an object with its descended right dual. -/
@[simp↓]
theorem coevaluation_rightDual_obj (X : C) [HasRightDual X] :
    η_ ((functor r).obj X) ((functor r).obj X)ᘁ = (functor r).map (η_ X Xᘁ) :=
  coevaluation_rightDual (Quotient.mk X)

/-- A quotient by a monoidal relation of a left rigid monoidal category is left rigid. -/
noncomputable instance instLeftRigidCategory [LeftRigidCategory C] :
    LeftRigidCategory (Quotient r) where

/-- A quotient by a monoidal relation of a right rigid monoidal category is right rigid. -/
noncomputable instance instRightRigidCategory [RightRigidCategory C] :
    RightRigidCategory (Quotient r) where

/-- A quotient by a monoidal relation of a rigid monoidal category is rigid. -/
noncomputable instance instRigidCategory [RigidCategory C] :
    RigidCategory (Quotient r) where

/-- The left adjoint mate of a class is the class of the left adjoint mate. -/
@[simp]
theorem leftAdjointMate_map {X Y : C} [HasLeftDual X] [HasLeftDual Y] (f : X ⟶ Y) :
    (ᘁ((functor r).map f)) = (functor r).map (ᘁf) := by
  apply ExactPairing.leftDualHom_ext (Y := (functor r).obj X)
  rw [leftAdjointMate_comp_evaluation]
  simp only [evaluation_leftDual_obj, whiskerLeft_map, ← Functor.map_comp]
  -- Rewriting `leftDual_obj` here gives an ill-typed motive: the following mapped evaluation
  -- has fixed source the image of `Y ⊗ ᘁY`, while rewriting abstracts its dual object alone.
  -- The chosen dual and quotient whiskering are definitionally the source images, so applying
  -- `map` to the characteristic equation identifies the entire composite without transport.
  exact congrArg (functor r).map (leftAdjointMate_comp_evaluation f).symm

/-- The right adjoint mate of a class is the class of the right adjoint mate. -/
@[simp]
theorem rightAdjointMate_map {X Y : C} [HasRightDual X] [HasRightDual Y] (f : X ⟶ Y) :
    ((functor r).map f)ᘁ = (functor r).map (fᘁ) := by
  apply ExactPairing.rightHom_ext (X := (functor r).obj X)
  rw [rightAdjointMate_comp_evaluation]
  simp only [evaluation_rightDual_obj, map_whiskerRight, ← Functor.map_comp]
  -- As above, rewriting `rightDual_obj` abstracts the whiskering object but leaves the mapped
  -- evaluation's fixed source, the image of `Yᘁ ⊗ Y`; the resulting motive is ill-typed.
  -- The descended dual and whiskering are definitionally the source images, allowing `map`
  -- to identify the entire characteristic composite without transporting its evaluation.
  exact congrArg (functor r).map (rightAdjointMate_comp_evaluation f).symm

/-- The dual comparison for the quotient functor is the identity: its chosen duals are
exactly the images of the source duals. -/
@[simp]
theorem mapRightDualIso_eq_refl (X : C) [HasRightDual X] :
    (functor r).mapRightDualIso X = Iso.refl _ := by
  apply Iso.ext
  apply ExactPairing.rightHom_ext (X := (functor r).obj X)
  simpa using Functor.mapRightDualIso_hom_whiskerRight_evaluation (F := functor r) X

/-- A morphism from the chosen right dual of the image of `X` into the image of a right dual
`Y` of `X` equals the image of `g : Xᘁ ⟶ Y` if their right-whiskered composites with the
mapped evaluation of the pairing `(X, Y)` agree. -/
theorem eq_map_of_whiskerRight_evaluation {X Y : C} [HasRightDual X] [ExactPairing X Y]
    (f : ((functor r).obj X)ᘁ ⟶ (functor r).obj Y) (g : Xᘁ ⟶ Y)
    (h : f ▷ (functor r).obj X ≫ (functor r).map (ε_ X Y) =
      (functor r).map (g ▷ X ≫ ε_ X Y)) :
    f = (functor r).map g := by
  let := (functor r).mapExactPairing X Y
  apply ExactPairing.rightHom_ext (X := (functor r).obj X)
  simpa only [Functor.mapExactPairing_evaluation, functor_μ, functor_η,
    Category.id_comp, Category.comp_id, map_whiskerRight, ← Functor.map_comp] using h

section RightRigid

variable [RightRigidCategory C]

/-- The bidual comparison for the quotient functor is the identity. -/
@[simp]
theorem mapDoubleRightDualIso_eq_refl (X : C) :
    (functor r).mapDoubleRightDualIso X = Iso.refl _ := by
  apply Iso.ext
  simp only [Functor.mapDoubleRightDualIso_hom, mapRightDualIso_eq_refl,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  exact rightAdjointMate_id

/-- The tensor comparison of the right dual descends to the quotient. -/
@[simp]
theorem rightDualTensorIso_obj_hom (X Y : C) :
    (rightDualTensorIso ((functor r).obj X) ((functor r).obj Y)).hom =
      (functor r).map (rightDualTensorIso X Y).hom := by
  apply eq_map_of_whiskerRight_evaluation (X := X ⊗ Y) (Y := Yᘁ ⊗ Xᘁ)
  have h := TauCeti.rightDualTensorIso_hom_whiskerRight_evaluation
    (X := (functor r).obj X) (Y := (functor r).obj Y)
  simp only [ExactPairing.tensor_evaluation, evaluation_rightDual] at h ⊢
  -- With the descended evaluations explicit, the quotient's tensor and whiskering composites
  -- are the source composites mapped as a whole, without transporting their dependent endpoints.
  exact h.trans (congrArg (functor r).map
    (TauCeti.rightDualTensorIso_hom_whiskerRight_evaluation (X := X) (Y := Y)).symm)

/-- The inverse tensor comparison of the right dual also descends. -/
@[simp]
theorem rightDualTensorIso_obj_inv (X Y : C) :
    (rightDualTensorIso ((functor r).obj X) ((functor r).obj Y)).inv =
      (functor r).map (rightDualTensorIso X Y).inv := by
  have h : rightDualTensorIso ((functor r).obj X) ((functor r).obj Y) =
      (functor r).mapIso (rightDualTensorIso X Y) := Iso.ext (rightDualTensorIso_obj_hom X Y)
  exact congrArg Iso.inv h

/-- The tensorator of the double right dual is the class of its original tensorator. -/
@[simp]
theorem doubleRightDualFunctor_μ_obj (X Y : C) :
    μ (doubleRightDualFunctor (Quotient r)) ((functor r).obj X) ((functor r).obj Y) =
      (functor r).map (μ (doubleRightDualFunctor C) X Y) := by
  rw [doubleRightDualFunctor_μ, doubleRightDualFunctor_μ, rightDualTensorIso_obj_hom]
  -- Rewriting the inverse comparison cannot match the descended duals with mapped source
  -- duals at the rewriter's transparency, including the composite's fixed bidual endpoints.
  -- Compose the descent equations as terms, using the chosen duals' definitional identification.
  exact (congrArg₂ (· ≫ ·) (rightDualTensorIso_obj_inv Yᘁ Xᘁ)
    (rightAdjointMate_map (r := r) (rightDualTensorIso X Y).hom)).trans
      ((functor r).map_comp _ _).symm

/-- The inverse tensorator of the double right dual descends to the quotient. -/
@[simp]
theorem doubleRightDualFunctor_δ_obj (X Y : C) :
    δ (doubleRightDualFunctor (Quotient r)) ((functor r).obj X) ((functor r).obj Y) =
      (functor r).map (δ (doubleRightDualFunctor C) X Y) := by
  rw [doubleRightDualFunctor_δ, doubleRightDualFunctor_δ, rightDualTensorIso_obj_inv]
  -- As for the tensorator, rewriting cannot match the tensor comparison at descended duals
  -- with its mapped-source form while retaining the composite's fixed bidual endpoints.
  -- Term congruence uses their definitional identification without abstracting those endpoints.
  exact (congrArg₂ (· ≫ ·) (rightAdjointMate_map (r := r) (rightDualTensorIso X Y).inv)
    (rightDualTensorIso_obj_hom Yᘁ Xᘁ)).trans ((functor r).map_comp _ _).symm

/-- The identification of the chosen right dual of the unit with the unit descends. The
rigid category's choice is explicit, since the unit also has a canonical self-duality. -/
@[simp]
theorem rightDualIso_exactPairingUnit_hom :
    (rightDualIso (RightRigidCategory.rightDual (𝟙_ (Quotient r))).exact exactPairingUnit).hom =
      (functor r).map (rightDualIso
        (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom := by
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
  apply eq_map_of_whiskerRight_evaluation (X := 𝟙_ C) (Y := 𝟙_ C)
  refine (ExactPairing.rightDualIso_hom_whiskerRight_evaluation
    (RightRigidCategory.rightDual (𝟙_ (Quotient r))).exact exactPairingUnit).trans ?_
  exact (evaluation_rightDual_obj (𝟙_ C)).trans
    (congrArg (functor r).map (ExactPairing.rightDualIso_hom_whiskerRight_evaluation
      (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).symm)

/-- The inverse identification of the chosen unit dual descends. -/
@[simp]
theorem rightDualIso_exactPairingUnit_inv :
    (rightDualIso (RightRigidCategory.rightDual (𝟙_ (Quotient r))).exact exactPairingUnit).inv =
      (functor r).map (rightDualIso
        (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).inv := by
  have h : rightDualIso (RightRigidCategory.rightDual (𝟙_ (Quotient r))).exact
      exactPairingUnit = (functor r).mapIso
        (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit) :=
    Iso.ext rightDualIso_exactPairingUnit_hom
  exact congrArg Iso.inv h

/-- The unit comparison of the double right dual descends, using the rigid structure's
chosen dual of the unit on both sides. -/
@[simp]
theorem doubleRightDualFunctor_ε_eq_map :
    ε (doubleRightDualFunctor (Quotient r)) = (functor r).map (ε (doubleRightDualFunctor C)) := by
  -- Select the rigid structure's unit dual rather than its canonical self-duality.
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
  rw [doubleRightDualFunctor_ε_eq_rightAdjointMate,
    doubleRightDualFunctor_ε_eq_rightAdjointMate,
    rightDualIso_exactPairingUnit_hom, rightDualIso_exactPairingUnit_inv]
  -- Rewriting the mate and map_comp leaves dual-instance presentations of the unit that
  -- rw cannot identify. Term congruence identifies the rigidly chosen dual and its image
  -- definitionally, keeping the composite's unit and bidual endpoints together.
  exact (congrArg₂ (· ≫ ·) (Eq.refl _)
    (rightAdjointMate_map (r := r) (rightDualIso
      (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom)).trans
        ((functor r).map_comp _ _).symm

/-- The inverse unit comparison of the double right dual descends to the quotient. -/
@[simp]
theorem doubleRightDualFunctor_η_eq_map :
    η (doubleRightDualFunctor (Quotient r)) = (functor r).map (η (doubleRightDualFunctor C)) := by
  apply (cancel_epi (ε (doubleRightDualFunctor (Quotient r)))).mp
  rw [Functor.Monoidal.ε_η, doubleRightDualFunctor_ε_eq_map]
  -- rw [← Functor.map_comp] cannot match the mapped bidual of the source unit with the
  -- quotient unit's bidual at its transparency. Map the entire inverse law instead;
  -- these endpoints are definitionally equal for the descended rigid dual choices.
  exact ((functor r).map_comp _ _).symm.trans
    (congrArg (functor r).map (Functor.Monoidal.ε_η (doubleRightDualFunctor C)))
      |>.trans ((functor r).map_id _) |>.symm

end RightRigid

section Lift

variable {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
  (H : ∀ (X Y : C) (f g : X ⟶ Y), r f g → F.map f = F.map g)

/-- The right-dual comparison of a factored functor is its original comparison. -/
@[simp]
theorem lift_mapRightDualIso (X : Quotient r) [HasRightDual X.as]
    [hFX : HasRightDual ((lift r F H).obj X)] :
    (lift r F H).mapRightDualIso X = F.mapRightDualIso X.as (hFX := hFX) := by
  -- The lift's object map computes to `F.obj X.as`; keep the same target dual at both
  -- presentations, since instance search does not unfold that object map.
  let : HasRightDual (F.obj X.as) := hFX
  apply Iso.ext
  apply ExactPairing.rightHom_ext (X := (lift r F H).obj X)
  have h := Functor.mapRightDualIso_hom_whiskerRight_evaluation (F := lift r F H) X
  simp only [evaluation_rightDual] at h
  exact h.trans (Functor.mapRightDualIso_hom_whiskerRight_evaluation (F := F) X.as).symm

/-- On an image object, the factored functor retains the source right-dual comparison. -/
@[simp↓]
theorem lift_mapRightDualIso_obj (X : C) [HasRightDual X]
    [hFX : HasRightDual ((lift r F H).obj ((functor r).obj X))] :
    (lift r F H).mapRightDualIso ((functor r).obj X) = F.mapRightDualIso X (hFX := hFX) := by
  let : HasRightDual ((lift r F H).obj (Quotient.mk X : Quotient r)) := hFX
  exact lift_mapRightDualIso F H (Quotient.mk X)

variable [RightRigidCategory C] [RightRigidCategory D]

/-- The bidual comparison of a factored functor is its original comparison. -/
@[simp]
theorem lift_mapDoubleRightDualIso (X : Quotient r) :
    (lift r F H).mapDoubleRightDualIso X = F.mapDoubleRightDualIso X.as := by
  apply Iso.ext
  simp only [Functor.mapDoubleRightDualIso_hom, lift_mapRightDualIso]
  -- The underlying object of the descended dual is the chosen source dual; term equality
  -- identifies these presentations without rewriting the comparisons' dependent endpoints.
  exact Eq.refl _

/-- On an image object, the factored functor retains the source bidual comparison. -/
@[simp↓]
theorem lift_mapDoubleRightDualIso_obj (X : C) :
    (lift r F H).mapDoubleRightDualIso ((functor r).obj X) = F.mapDoubleRightDualIso X :=
  lift_mapDoubleRightDualIso F H (Quotient.mk X)

end Lift

end CategoryTheory.Quotient
