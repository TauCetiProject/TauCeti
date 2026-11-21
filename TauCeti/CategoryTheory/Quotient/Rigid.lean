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
`CategoryTheory.Functor.mapHasRightDual` along the strong monoidal quotient functor. The
pairings are defined directly by mapping evaluations and coevaluations, without identity
comparison morphisms. These evaluations and coevaluations compute to the mapped source
morphisms, as do exposed `CategoryTheory.rightDualIso` comparisons built directly from them,
such as `TauCeti.drinfeldIso`.
The per-object dual instances use the caller's dual of the underlying object `X.as`, so they
need a dual only on the corresponding side, not rigidity of the whole source category.

The right-dual comparison of the quotient functor is the identity.
The right-dual tensor comparison descends whenever the two objects and their tensor product
have chosen right duals. For a right rigid source, the unit dual identification descends, as do
the tensor and unit comparisons of the double-right-dual functor (`μ`, `δ`, `ε`, `η`). These
equations supply the comparison data for descent of pivotal structures. The bidual
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
noncomputable instance (priority := low) instHasLeftDual (X : Quotient r) [HasLeftDual X.as] :
    HasLeftDual X where
  leftDual := (functor r).obj (ᘁ(X.as) : C)
  exact := {
    coevaluation' := (functor r).map (η_ (ᘁ(X.as) : C) X.as)
    evaluation' := (functor r).map (ε_ (ᘁ(X.as) : C) X.as)
    coevaluation_evaluation' := congrArg (functor r).map
      (ExactPairing.coevaluation_evaluation' (X := ᘁ(X.as)) (Y := X.as))
    evaluation_coevaluation' := congrArg (functor r).map
      (ExactPairing.evaluation_coevaluation' (X := ᘁ(X.as)) (Y := X.as)) }

/-- The right dual of a quotient object is the class of its underlying object's chosen right
dual. -/
noncomputable instance (priority := low) instHasRightDual (X : Quotient r) [HasRightDual X.as] :
    HasRightDual X where
  rightDual := (functor r).obj ((X.as)ᘁ : C)
  exact := {
    coevaluation' := (functor r).map (η_ X.as ((X.as)ᘁ : C))
    evaluation' := (functor r).map (ε_ X.as ((X.as)ᘁ : C))
    coevaluation_evaluation' := congrArg (functor r).map
      (ExactPairing.coevaluation_evaluation' (X := X.as) (Y := (X.as)ᘁ))
    evaluation_coevaluation' := congrArg (functor r).map
      (ExactPairing.evaluation_coevaluation' (X := X.as) (Y := (X.as)ᘁ)) }

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

/-- The tensor of two image objects has the descended right dual of their source tensor. -/
noncomputable instance instHasRightDualTensorObj (X Y : C) [HasRightDual (X ⊗ Y)] :
    HasRightDual ((functor r).obj X ⊗ (functor r).obj Y) :=
  inferInstanceAs (HasRightDual (Quotient.mk (X ⊗ Y) : Quotient r))

/-- The left dual in the quotient is the class of the chosen left dual in the source. -/
theorem leftDual_eq (X : Quotient r) [HasLeftDual X.as] :
    (ᘁX : Quotient r) = (functor r).obj (ᘁ(X.as) : C) :=
  (rfl)

/-- The right dual in the quotient is the class of the chosen right dual in the source. -/
theorem rightDual_eq (X : Quotient r) [HasRightDual X.as] :
    Xᘁ = (functor r).obj ((X.as)ᘁ : C) :=
  (rfl)

/-- The evaluation for the descended left dual is the class of the original evaluation. -/
theorem evaluation_leftDual (X : Quotient r) [HasLeftDual X.as] :
    ε_ (ᘁX) X = (functor r).map (ε_ (ᘁ(X.as) : C) X.as) :=
  (rfl)

/-- The coevaluation for the descended left dual is the class of the original coevaluation. -/
theorem coevaluation_leftDual (X : Quotient r) [HasLeftDual X.as] :
    η_ (ᘁX) X = (functor r).map (η_ (ᘁ(X.as) : C) X.as) :=
  (rfl)

/-- The evaluation for the descended right dual is the class of the original evaluation. -/
theorem evaluation_rightDual (X : Quotient r) [HasRightDual X.as] :
    ε_ X Xᘁ = (functor r).map (ε_ X.as ((X.as)ᘁ : C)) :=
  (rfl)

/-- The coevaluation for the descended right dual is the class of the original coevaluation. -/
theorem coevaluation_rightDual (X : Quotient r) [HasRightDual X.as] :
    η_ X Xᘁ = (functor r).map (η_ X.as ((X.as)ᘁ : C)) :=
  (rfl)

-- Keep dual-object equalities as explicit rewrites: simplifying dual arguments first would
-- prevent the simplifier from recognizing dual-indexed trace and dimension identities.
-- Keep their morphism descent equations explicit too, so inner rewrites do not obstruct
-- outer rigid cancellation laws.
/-- The left dual of the image of an object is the image of its chosen left dual. -/
theorem leftDual_obj (X : C) [HasLeftDual X] :
    (ᘁ((functor r).obj X) : Quotient r) = (functor r).obj (ᘁX) :=
  leftDual_eq (Quotient.mk X)

/-- The right dual of the image of an object is the image of its chosen right dual. -/
theorem rightDual_obj (X : C) [HasRightDual X] :
    ((functor r).obj X)ᘁ = (functor r).obj (Xᘁ) :=
  rightDual_eq (Quotient.mk X)

/-- Evaluation on the image of an object with its descended left dual. -/
theorem evaluation_leftDual_obj (X : C) [HasLeftDual X] :
    ε_ (ᘁ((functor r).obj X)) ((functor r).obj X) = (functor r).map (ε_ (ᘁX) X) :=
  evaluation_leftDual (Quotient.mk X)

/-- Coevaluation on the image of an object with its descended left dual. -/
theorem coevaluation_leftDual_obj (X : C) [HasLeftDual X] :
    η_ (ᘁ((functor r).obj X)) ((functor r).obj X) = (functor r).map (η_ (ᘁX) X) :=
  coevaluation_leftDual (Quotient.mk X)

/-- Evaluation on the image of an object with its descended right dual. -/
theorem evaluation_rightDual_obj (X : C) [HasRightDual X] :
    ε_ ((functor r).obj X) ((functor r).obj X)ᘁ = (functor r).map (ε_ X Xᘁ) :=
  evaluation_rightDual (Quotient.mk X)

/-- Coevaluation on the image of an object with its descended right dual. -/
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
theorem functor_mapRightDualIso (X : C) [HasRightDual X] :
    (functor r).mapRightDualIso X = Iso.refl _ := by
  apply Iso.ext
  apply ExactPairing.rightHom_ext (X := (functor r).obj X)
  simpa [evaluation_rightDual_obj] using
    Functor.mapRightDualIso_hom_whiskerRight_evaluation (F := functor r) X

/-- The forward dual comparison is the identity on the image of the source dual. -/
@[simp]
theorem functor_mapRightDualIso_hom (X : C) [HasRightDual X] :
    ((functor r).mapRightDualIso X).hom = 𝟙 ((functor r).obj Xᘁ) := by
  rw [functor_mapRightDualIso, Iso.refl_hom]

/-- The inverse dual comparison is the identity on the descended dual. -/
@[simp]
theorem functor_mapRightDualIso_inv (X : C) [HasRightDual X] :
    ((functor r).mapRightDualIso X).inv = 𝟙 (((functor r).obj X)ᘁ) := by
  exact congrArg Iso.inv (functor_mapRightDualIso (r := r) X)

private theorem rightDualIso_eq_mapIso {X Y₁ Y₂ : C}
    (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂)
    (q₁ : ExactPairing ((functor r).obj X) ((functor r).obj Y₁))
    (q₂ : ExactPairing ((functor r).obj X) ((functor r).obj Y₂))
    (h₁ : @ExactPairing.evaluation _ _ _ _ _ q₁ =
      (functor r).map (@ExactPairing.evaluation _ _ _ _ _ p₁))
    (h₂ : @ExactPairing.evaluation _ _ _ _ _ q₂ =
      (functor r).map (@ExactPairing.evaluation _ _ _ _ _ p₂)) :
    rightDualIso q₁ q₂ = (functor r).mapIso (rightDualIso p₁ p₂) := by
  let := q₂
  apply Iso.ext
  apply ExactPairing.rightHom_ext (X := (functor r).obj X)
  rw [ExactPairing.rightDualIso_hom_whiskerRight_evaluation, h₁, h₂, Functor.mapIso_hom,
    map_whiskerRight, ← Functor.map_comp, ExactPairing.rightDualIso_hom_whiskerRight_evaluation]

section RightRigid

variable [RightRigidCategory C]

/-- The bidual comparison for the quotient functor is the identity. -/
theorem functor_mapDoubleRightDualIso (X : C) :
    (functor r).mapDoubleRightDualIso X = Iso.refl _ := by
  apply Iso.ext
  simp only [Functor.mapDoubleRightDualIso_hom, functor_mapRightDualIso,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  exact rightAdjointMate_id

/-- The forward bidual comparison is the identity on the image of the source bidual. -/
@[simp]
theorem functor_mapDoubleRightDualIso_hom (X : C) :
    ((functor r).mapDoubleRightDualIso X).hom = 𝟙 ((functor r).obj Xᘁᘁ) := by
  rw [functor_mapDoubleRightDualIso, Iso.refl_hom]

/-- The inverse bidual comparison is the identity on the descended bidual. -/
@[simp]
theorem functor_mapDoubleRightDualIso_inv (X : C) :
    ((functor r).mapDoubleRightDualIso X).inv =
      𝟙 ((((functor r).obj X : Quotient r)ᘁ : Quotient r)ᘁ) := by
  exact congrArg Iso.inv (functor_mapDoubleRightDualIso (r := r) X)

end RightRigid

/-- The tensor comparison of the right dual descends to the quotient. -/
theorem rightDualTensorIso_hom_obj (X Y : C) [HasRightDual X] [HasRightDual Y]
    [HasRightDual (X ⊗ Y)] :
    (rightDualTensorIso ((functor r).obj X) ((functor r).obj Y)).hom =
      (functor r).map (rightDualTensorIso X Y).hom := by
  exact congrArg Iso.hom (rightDualIso_eq_mapIso (r := r)
    (X := X ⊗ Y) (Y₁ := (X ⊗ Y)ᘁ) (Y₂ := Yᘁ ⊗ Xᘁ)
    HasRightDual.exact (ExactPairing.tensor (X₁ := X) (X₂ := Y)
      (Y₁ := Xᘁ) (Y₂ := Yᘁ)) HasRightDual.exact
    (@ExactPairing.tensor _ _ _ _ _ _ _
      (instHasRightDualObj (r := r) X).exact (instHasRightDualObj (r := r) Y).exact)
    (evaluation_rightDual_obj (X ⊗ Y)) (by
      have tensor_eval {D : Type u} [Category.{v} D] [MonoidalCategory D]
          {X₁ X₂ Y₁ Y₂ : D} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
          ε_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) = (α_ _ _ _).hom ≫ Y₂ ◁ (α_ _ _ _).inv ≫
            Y₂ ◁ ε_ X₁ Y₁ ▷ X₂ ≫ Y₂ ◁ (λ_ X₂).hom ≫ ε_ X₂ Y₂ := by
        simp [ExactPairing.tensor_evaluation, monoidalComp]
      have hQ := tensor_eval
        (X₁ := (functor r).obj X) (X₂ := (functor r).obj Y)
        (Y₁ := (((functor r).obj X)ᘁ : Quotient r))
        (Y₂ := (((functor r).obj Y)ᘁ : Quotient r))
      have hC := congrArg (functor r).map
        (tensor_eval (X₁ := X) (X₂ := Y) (Y₁ := Xᘁ) (Y₂ := Yᘁ))
      simp only [evaluation_rightDual_obj] at hQ
      -- After expanding coherence, only primitive quotient associators, unitors and
      -- whiskering remain; these compute to the source composites with fixed endpoints.
      exact hQ.trans hC.symm))

/-- The inverse tensor comparison of the right dual also descends. -/
theorem rightDualTensorIso_inv_obj (X Y : C) [HasRightDual X] [HasRightDual Y]
    [HasRightDual (X ⊗ Y)] :
    (rightDualTensorIso ((functor r).obj X) ((functor r).obj Y)).inv =
      (functor r).map (rightDualTensorIso X Y).inv := by
  have h : rightDualTensorIso ((functor r).obj X) ((functor r).obj Y) =
      (functor r).mapIso (rightDualTensorIso X Y) := Iso.ext (rightDualTensorIso_hom_obj X Y)
  exact congrArg Iso.inv h

section RightRigid

variable [RightRigidCategory C]

/-- The tensorator of the double right dual is the class of its original tensorator. -/
theorem doubleRightDualFunctor_μ_obj (X Y : C) :
    μ (doubleRightDualFunctor (Quotient r)) ((functor r).obj X) ((functor r).obj Y) =
      (functor r).map (μ (doubleRightDualFunctor C) X Y) := by
  rw [doubleRightDualFunctor_μ, doubleRightDualFunctor_μ, rightDualTensorIso_hom_obj]
  -- Rewriting the inverse comparison cannot match the descended duals with mapped source
  -- duals at the rewriter's transparency, including the composite's fixed bidual endpoints.
  -- Compose the descent equations as terms, using the chosen duals' definitional identification.
  exact (congrArg₂ (· ≫ ·) (rightDualTensorIso_inv_obj Yᘁ Xᘁ)
    (rightAdjointMate_map (r := r) (rightDualTensorIso X Y).hom)).trans
      ((functor r).map_comp _ _).symm

/-- The inverse tensorator of the double right dual descends to the quotient. -/
theorem doubleRightDualFunctor_δ_obj (X Y : C) :
    δ (doubleRightDualFunctor (Quotient r)) ((functor r).obj X) ((functor r).obj Y) =
      (functor r).map (δ (doubleRightDualFunctor C) X Y) := by
  rw [doubleRightDualFunctor_δ, doubleRightDualFunctor_δ, rightDualTensorIso_inv_obj]
  -- As for the tensorator, rewriting cannot match the tensor comparison at descended duals
  -- with its mapped-source form while retaining the composite's fixed bidual endpoints.
  -- Term congruence uses their definitional identification without abstracting those endpoints.
  exact (congrArg₂ (· ≫ ·) (rightAdjointMate_map (r := r) (rightDualTensorIso X Y).inv)
    (rightDualTensorIso_hom_obj Yᘁ Xᘁ)).trans ((functor r).map_comp _ _).symm

/-- The identification of the chosen right dual of the unit with the unit descends. The
rigid category's choice is explicit, since the unit also has a canonical self-duality. -/
theorem rightDualIso_exactPairingUnit_hom :
    (rightDualIso (RightRigidCategory.rightDual (𝟙_ (Quotient r))).exact exactPairingUnit).hom =
      (functor r).map (rightDualIso
        (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom := by
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
  exact congrArg Iso.hom (rightDualIso_eq_mapIso (r := r)
    (RightRigidCategory.rightDual (𝟙_ C)).exact (exactPairingUnit (C := C))
    (RightRigidCategory.rightDual (𝟙_ (Quotient r))).exact
    (exactPairingUnit (C := Quotient r))
    (evaluation_rightDual_obj (𝟙_ C)) (by
      exact (ExactPairing.unit_evaluation (C := Quotient r)).trans
        ((rightUnitor_hom_obj (r := r) (𝟙_ C)).trans
          (congrArg (functor r).map (ExactPairing.unit_evaluation (C := C))).symm)))

/-- The inverse identification of the chosen unit dual descends. -/
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
    (lift r F H).mapRightDualIso X = F.mapRightDualIso X.as (_hFX := hFX) := by
  -- The lift's object map computes to `F.obj X.as`; keep the same target dual at both
  -- presentations, since instance search does not unfold that object map.
  let : HasRightDual (F.obj X.as) := hFX
  apply Iso.ext
  apply ExactPairing.rightHom_ext (X := (lift r F H).obj X)
  have h := Functor.mapRightDualIso_hom_whiskerRight_evaluation (F := lift r F H) X
  simp only [evaluation_rightDual, lift_η] at h
  -- The lift's tensorator at Xᘁ, X is definitionally μ F (X.as)ᘁ X.as;
  -- its map on a class (functor r).map f is definitionally F.map f.
  exact h.trans (Functor.mapRightDualIso_hom_whiskerRight_evaluation (F := F) X.as).symm

/-- On an image object, the factored functor retains the source right-dual comparison. -/
@[simp↓]
theorem lift_mapRightDualIso_obj (X : C) [HasRightDual X]
    [hFX : HasRightDual ((lift r F H).obj ((functor r).obj X))] :
    (lift r F H).mapRightDualIso ((functor r).obj X) = F.mapRightDualIso X (_hFX := hFX) := by
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
