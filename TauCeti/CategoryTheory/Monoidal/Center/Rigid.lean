/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import TauCeti.CategoryTheory.Monoidal.Center.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Mate

/-!
# The Drinfeld centre of a rigid category is rigid

An object of the Drinfeld centre `Center C` is an object `X : C` with a half-braiding
`β U : X ⊗ U ≅ U ⊗ X`. If `X` has a right dual `X'` in `C`, then `X'` carries a canonical
half-braiding: its component at `U` is the mate

`X' ⊗ U ⟶ X' ⊗ U ⊗ X ⊗ X' ⟶ X' ⊗ X ⊗ U ⊗ X' ⟶ U ⊗ X'`

of `(β U).inv`, which inserts the coevaluation of `X`, moves `X` past `U` with the inverse
half-braiding, and evaluates it against `X'`. Naturality and monoidality in `U` follow from those
of `β`, and need no duals other than `X'`. Invertibility is where left duals of `C` enter: with
respect to an exact pairing of `V` and `U`, this mate is also the mate of `β V` taken with respect
to the tensor product pairings, so its inverse is the mate of `(β ᘁU).inv`. The coevaluation and
evaluation of `X` and `X'` are then morphisms of the centre, so `X'` with the induced
half-braiding is a right dual of `X` in `Center C`.

Thus the centre of a rigid category is right rigid, with duals computed in `C`, and since the
centre is braided it is rigid: Mathlib's `BraidedCategory.hasLeftDualOfHasRightDual` turns the
right duals into left duals using the braiding of the centre. This is the rigid structure needed to
speak of pivotal structures on the centre, and of the centre of a fusion category as a fusion
category.

## Main declarations

* `CategoryTheory.HalfBraiding.rightDualβHom`: the components of the half-braiding induced on a
  right dual, characterized by `CategoryTheory.HalfBraiding.rightDualβHom_whiskerRight_evaluation`
  and `CategoryTheory.HalfBraiding.coevaluation_whiskerRight_whiskerLeft_rightDualβHom`, and
  natural and monoidal in `U`;
* `CategoryTheory.HalfBraiding.rightDualβHom_eq_rightMate`: the same components as mates of the
  half-braiding at a left dual;
* `CategoryTheory.HalfBraiding.rightDual`: the half-braiding induced on a right dual, in a left
  rigid category;
* `CategoryTheory.Center.rightDualObj` and `CategoryTheory.Center.exactPairingRightDualObj`: a
  right dual of the underlying object of `X : Center C` lifts to a right dual of `X`;
* `CategoryTheory.Center.rigidCategory`: the centre of a rigid category is rigid, with right
  duals and their evaluation, coevaluation and mates computed in `C`
  (`CategoryTheory.Center.rightDual_fst`, `CategoryTheory.Center.coevaluation_f`,
  `CategoryTheory.Center.evaluation_f`, `CategoryTheory.Center.rightAdjointMate_f`).

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace HalfBraiding

variable {X : C} (b : HalfBraiding X)

variable (X' : C) [ExactPairing X X']

/-- The component at `U` of the half-braiding induced on a right dual `X'` of `X`: the mate of
`(b.β U).inv : U ⊗ X ⟶ X ⊗ U`, which inserts the coevaluation of `X` on the right, moves `X`
past `U` with the inverse half-braiding, and evaluates it against `X'` on the left. -/
def rightDualβHom (U : C) : X' ⊗ U ⟶ U ⊗ X' :=
  tensorRightHomEquiv (X' ⊗ U) X X' U
    ((α_ X' U X).hom ≫ X' ◁ (b.β U).inv ≫ (α_ X' X U).inv ≫ ε_ X X' ▷ U ≫ (λ_ U).hom)

/-- Evaluating `X'` against `X` after `rightDualβHom` is the same as moving `X` past `U` with the
inverse half-braiding and evaluating. -/
@[reassoc]
theorem rightDualβHom_whiskerRight_evaluation (U : C) :
    b.rightDualβHom X' U ▷ X ≫ (α_ U X' X).hom ≫ U ◁ ε_ X X' ≫ (ρ_ U).hom =
      (α_ X' U X).hom ≫ X' ◁ (b.β U).inv ≫ (α_ X' X U).inv ≫ ε_ X X' ▷ U ≫ (λ_ U).hom :=
  (tensorRightHomEquiv (X' ⊗ U) X X' U).symm_apply_apply _

/-- Inserting the coevaluation of `X` on the left of `rightDualβHom` is the same as inserting it
on the right of `U` and moving `X` past `U` with the inverse half-braiding. -/
theorem coevaluation_whiskerRight_whiskerLeft_rightDualβHom (U : C) :
    η_ X X' ▷ U ⊗≫ X ◁ b.rightDualβHom X' U =
      𝟙 _ ⊗≫ U ◁ η_ X X' ⊗≫ (b.β U).inv ▷ X' ⊗≫ 𝟙 _ := by
  rw [rightDualβHom]
  simp only [tensorRightHomEquiv, Equiv.coe_fn_mk]
  calc
    _ = 𝟙 _ ⊗≫ (η_ X X' ▷ (U ⊗ 𝟙_ C) ≫ (X ⊗ X') ◁ U ◁ η_ X X') ⊗≫
          X ◁ X' ◁ (b.β U).inv ▷ X' ⊗≫ X ◁ ε_ X X' ▷ U ▷ X' ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ U ◁ η_ X X' ⊗≫ (η_ X X' ▷ ((U ⊗ X) ⊗ X') ≫ (X ⊗ X') ◁ (b.β U).inv ▷ X') ⊗≫
          X ◁ ε_ X X' ▷ U ▷ X' ⊗≫ 𝟙 _ := by rw [← whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ U ◁ η_ X X' ⊗≫ (b.β U).inv ▷ X' ⊗≫
          (η_ X X' ▷ X ⊗≫ X ◁ ε_ X X') ▷ U ▷ X' ⊗≫ 𝟙 _ := by rw [← whisker_exchange]; monoidal
    _ = _ := by rw [ExactPairing.evaluation_coevaluation'']; monoidal

/-- The family `rightDualβHom` is natural in `U`. -/
@[reassoc]
theorem rightDualβHom_naturality {U U' : C} (f : U ⟶ U') :
    X' ◁ f ≫ b.rightDualβHom X' U' = b.rightDualβHom X' U ≫ f ▷ X' := by
  -- Both sides are determined by their composites with the evaluation of `X` and `X'`.
  apply (tensorRightHomEquiv _ X X' _).symm.injective
  simp only [tensorRightHomEquiv, Equiv.coe_fn_symm_mk]
  calc
    _ = 𝟙 _ ⊗≫ X' ◁ f ▷ X ⊗≫
          (b.rightDualβHom X' U' ▷ X ≫ (α_ _ _ _).hom ≫ U' ◁ ε_ X X' ≫ (ρ_ U').hom) := by
      monoidal
    _ = 𝟙 _ ⊗≫ X' ◁ (f ▷ X ≫ (b.β U').inv) ⊗≫ ε_ X X' ▷ U' ⊗≫ 𝟙 U' := by
      rw [rightDualβHom_whiskerRight_evaluation]; monoidal
    _ = 𝟙 _ ⊗≫ X' ◁ (b.β U).inv ⊗≫ ((X' ⊗ X) ◁ f ≫ ε_ X X' ▷ U') ⊗≫ 𝟙 U' := by
      rw [naturality_inv]; monoidal
    _ = (b.rightDualβHom X' U ▷ X ≫ (α_ _ _ _).hom ≫ U ◁ ε_ X X' ≫ (ρ_ U).hom) ≫ f := by
      rw [whisker_exchange, rightDualβHom_whiskerRight_evaluation]; monoidal
    _ = 𝟙 _ ⊗≫ b.rightDualβHom X' U ▷ X ⊗≫ (U ◁ ε_ X X' ≫ f ▷ 𝟙_ C) ⊗≫ 𝟙 U' := by monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

/-- The family `rightDualβHom` is monoidal in `U`. -/
theorem rightDualβHom_monoidal (U U' : C) :
    b.rightDualβHom X' (U ⊗ U') =
      (α_ _ _ _).inv ≫ b.rightDualβHom X' U ▷ U' ≫ (α_ _ _ _).hom ≫
        U ◁ b.rightDualβHom X' U' ≫ (α_ _ _ _).inv := by
  -- Both sides are determined by their composites with the evaluation of `X` and `X'`.
  apply (tensorRightHomEquiv _ X X' _).symm.injective
  simp only [tensorRightHomEquiv, Equiv.coe_fn_symm_mk]
  symm
  calc
    _ = 𝟙 _ ⊗≫ b.rightDualβHom X' U ▷ U' ▷ X ⊗≫
          U ◁ (b.rightDualβHom X' U' ▷ X ≫ (α_ _ _ _).hom ≫ U' ◁ ε_ X X' ≫ (ρ_ U').hom) ⊗≫
            𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ (b.rightDualβHom X' U ▷ (U' ⊗ X) ≫ (U ⊗ X') ◁ (b.β U').inv) ⊗≫
          U ◁ ε_ X X' ▷ U' ⊗≫ 𝟙 _ := by
      rw [rightDualβHom_whiskerRight_evaluation]; monoidal
    _ = 𝟙 _ ⊗≫ X' ◁ U ◁ (b.β U').inv ⊗≫
          (b.rightDualβHom X' U ▷ X ≫ (α_ _ _ _).hom ≫ U ◁ ε_ X X' ≫ (ρ_ U).hom) ▷ U' ⊗≫
            𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = b.rightDualβHom X' (U ⊗ U') ▷ X ≫ (α_ _ _ _).hom ≫ (U ⊗ U') ◁ ε_ X X' ≫
          (ρ_ (U ⊗ U')).hom := by
      rw [rightDualβHom_whiskerRight_evaluation, rightDualβHom_whiskerRight_evaluation,
        monoidal_inv]
      monoidal

/-- With respect to any exact pairing of `V` and `U`, `rightDualβHom` at `U` is the mate of the
half-braiding at `V`, taken with respect to the tensor product pairings of `(X, X')` and
`(V, U)`. -/
theorem rightDualβHom_eq_rightMate {U V : C} [ExactPairing V U] :
    b.rightDualβHom X' U =
      ExactPairing.rightMate (ExactPairing.tensor : ExactPairing (X ⊗ V) (U ⊗ X'))
        (ExactPairing.tensor : ExactPairing (V ⊗ X) (X' ⊗ U)) (b.β V).hom := by
  refine ExactPairing.rightHom_ext (X := X ⊗ V) ?_
  rw [ExactPairing.rightMate_comp_evaluation, ExactPairing.tensor_evaluation,
    ExactPairing.tensor_evaluation]
  calc
    _ = 𝟙 _ ⊗≫ (b.rightDualβHom X' U ▷ X ≫ (α_ _ _ _).hom ≫ U ◁ ε_ X X' ≫ (ρ_ U).hom) ▷ V ⊗≫
          ε_ V U := by
      monoidal
    _ = 𝟙 _ ⊗≫ X' ◁ (b.β U).inv ▷ V ⊗≫ (ε_ X X' ▷ (U ⊗ V) ≫ 𝟙_ C ◁ ε_ V U) ⊗≫ 𝟙 _ := by
      rw [rightDualβHom_whiskerRight_evaluation]; monoidal
    _ = 𝟙 _ ⊗≫ X' ◁ ((b.β U).inv ▷ V ⊗≫ X ◁ ε_ V U ⊗≫ 𝟙 X) ⊗≫ ε_ X X' := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by rw [inv_whiskerRight_comp_whiskerLeft]; monoidal

/-- The coevaluation of `X` and `X'` commutes with the half-braidings of the unit and of
`X ⊗ X'`, the latter built from `b` and `rightDualβHom`. -/
private theorem coevaluation_comm (U : C) :
    η_ X X' ▷ U ≫ (α_ _ _ _).hom ≫ X ◁ b.rightDualβHom X' U ≫ (α_ _ _ _).inv ≫
      (b.β U).hom ▷ X' ≫ (α_ _ _ _).hom = ((λ_ U).hom ≫ (ρ_ U).inv) ≫ U ◁ η_ X X' := by
  calc
    _ = 𝟙 _ ⊗≫ (η_ X X' ▷ U ⊗≫ X ◁ b.rightDualβHom X' U) ⊗≫ (b.β U).hom ▷ X' ⊗≫ 𝟙 _ := by
      monoidal
    _ = 𝟙 _ ⊗≫ U ◁ η_ X X' ⊗≫ ((b.β U).inv ▷ X' ≫ (b.β U).hom ▷ X') ⊗≫ 𝟙 _ := by
      rw [coevaluation_whiskerRight_whiskerLeft_rightDualβHom]; monoidal
    _ = _ := by rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]; monoidal

/-- The evaluation of `X` and `X'` commutes with the half-braidings of `X' ⊗ X`, built from
`rightDualβHom` and `b`, and of the unit. -/
private theorem evaluation_comm (U : C) :
    ε_ X X' ▷ U ≫ (λ_ U).hom ≫ (ρ_ U).inv =
      ((α_ _ _ _).hom ≫ X' ◁ (b.β U).hom ≫ (α_ _ _ _).inv ≫ b.rightDualβHom X' U ▷ X ≫
        (α_ _ _ _).hom) ≫ U ◁ ε_ X X' := by
  symm
  calc
    _ = (𝟙 _ ⊗≫ X' ◁ (b.β U).hom ⊗≫
          (b.rightDualβHom X' U ▷ X ≫ (α_ _ _ _).hom ≫ U ◁ ε_ X X' ≫ (ρ_ U).hom)) ≫
            (ρ_ U).inv := by
      monoidal
    _ = (𝟙 _ ⊗≫ X' ◁ ((b.β U).hom ≫ (b.β U).inv) ⊗≫ ε_ X X' ▷ U ⊗≫ 𝟙 U) ≫ (ρ_ U).inv := by
      rw [rightDualβHom_whiskerRight_evaluation]; monoidal
    _ = _ := by rw [Iso.hom_inv_id]; monoidal

/-- The half-braiding induced on a right dual `X'` of `X`, at the object `U`. Its inverse is the
mate of the inverse half-braiding at the left dual `ᘁU`. -/
def rightDualβ (U : C) [HasLeftDual U] : X' ⊗ U ≅ U ⊗ X' where
  hom := b.rightDualβHom X' U
  inv := ExactPairing.rightMate (ExactPairing.tensor (X₁ := ᘁU) (X₂ := X) (Y₁ := U) (Y₂ := X'))
    (ExactPairing.tensor (X₁ := X) (X₂ := ᘁU) (Y₁ := X') (Y₂ := U)) (b.β ᘁU).inv
  hom_inv_id := by
    rw [b.rightDualβHom_eq_rightMate X' (U := U) (V := ᘁU), ← ExactPairing.comp_rightMate,
      Iso.inv_hom_id, ExactPairing.rightMate_id]
  inv_hom_id := by
    rw [b.rightDualβHom_eq_rightMate X' (U := U) (V := ᘁU), ← ExactPairing.comp_rightMate,
      Iso.hom_inv_id, ExactPairing.rightMate_id]

/-- The half-braiding of a right dual is `rightDualβHom`. -/
@[simp]
theorem rightDualβ_hom (U : C) [HasLeftDual U] :
    (b.rightDualβ X' U).hom = b.rightDualβHom X' U :=
  (rfl)

/-- The inverse of the half-braiding of a right dual at `U` is the mate of the inverse
half-braiding at `ᘁU`. -/
theorem rightDualβ_inv (U : C) [HasLeftDual U] :
    (b.rightDualβ X' U).inv =
      ExactPairing.rightMate (ExactPairing.tensor (X₁ := ᘁU) (X₂ := X) (Y₁ := U) (Y₂ := X'))
        (ExactPairing.tensor (X₁ := X) (X₂ := ᘁU) (Y₁ := X') (Y₂ := U)) (b.β ᘁU).inv :=
  (rfl)

variable [LeftRigidCategory C]

/-- The half-braiding on a right dual `X'` of an object `X` with a half-braiding `b`: its
component at `U` is the mate `HalfBraiding.rightDualβHom` of `(b.β U).inv`. -/
def rightDual : HalfBraiding X' where
  β U := b.rightDualβ X' U
  monoidal U U' := b.rightDualβHom_monoidal X' U U'
  naturality f := b.rightDualβHom_naturality X' f

/-- The components of `HalfBraiding.rightDual` are the isomorphisms `rightDualβ`. -/
@[simp]
theorem rightDual_β (U : C) : (b.rightDual X').β U = b.rightDualβ X' U :=
  (rfl)

end HalfBraiding

namespace Center

variable [LeftRigidCategory C]

variable (X : Center C) (X' : C) [ExactPairing X.1 X']

/-- A right dual `X'` in `C` of the underlying object of `X : Center C`, as an object of the centre
with the half-braiding `HalfBraiding.rightDual` induced from that of `X`. -/
@[expose]
def rightDualObj : Center C :=
  ⟨X', X.2.rightDual X'⟩

/-- The underlying object of `rightDualObj X X'` is `X'`. -/
@[simp]
theorem rightDualObj_fst : (rightDualObj X X').1 = X' :=
  rfl

/-- The half-braiding of `rightDualObj X X'` is `HalfBraiding.rightDual`. -/
@[simp]
theorem rightDualObj_snd : (rightDualObj X X').2 = X.2.rightDual X' :=
  rfl

/-- The coevaluation of an exact pairing of `X.1` with `X'`, as a morphism of the centre. -/
def rightDualCoevaluation : 𝟙_ (Center C) ⟶ X ⊗ rightDualObj X X' where
  f := η_ X.1 X'
  comm U := by
    simp only [tensor_β, tensorUnit_β, Iso.trans_hom, Iso.symm_hom,
      MonoidalCategory.whiskerLeftIso_hom, MonoidalCategory.whiskerRightIso_hom, rightDualObj_fst,
      rightDualObj_snd, HalfBraiding.rightDual_β, HalfBraiding.rightDualβ_hom]
    exact X.2.coevaluation_comm X' U

/-- The underlying morphism of `rightDualCoevaluation` is the coevaluation in `C`. -/
@[simp]
theorem rightDualCoevaluation_f : (rightDualCoevaluation X X').f = η_ X.1 X' :=
  (rfl)

/-- The evaluation of an exact pairing of `X.1` with `X'`, as a morphism of the centre. -/
def rightDualEvaluation : rightDualObj X X' ⊗ X ⟶ 𝟙_ (Center C) where
  f := ε_ X.1 X'
  comm U := by
    simp only [tensor_β, tensorUnit_β, Iso.trans_hom, Iso.symm_hom,
      MonoidalCategory.whiskerLeftIso_hom, MonoidalCategory.whiskerRightIso_hom, rightDualObj_fst,
      rightDualObj_snd, HalfBraiding.rightDual_β, HalfBraiding.rightDualβ_hom]
    exact X.2.evaluation_comm X' U

/-- The underlying morphism of `rightDualEvaluation` is the evaluation in `C`. -/
@[simp]
theorem rightDualEvaluation_f : (rightDualEvaluation X X').f = ε_ X.1 X' :=
  (rfl)

/-- An exact pairing of the underlying object of `X : Center C` with `X'` in `C` lifts to an exact
pairing of `X` with `rightDualObj X X'`. -/
instance exactPairingRightDualObj : ExactPairing X (rightDualObj X X') where
  coevaluation' := rightDualCoevaluation X X'
  evaluation' := rightDualEvaluation X X'
  coevaluation_evaluation' := by
    ext
    simp only [comp_f, whiskerLeft_f, whiskerRight_f, associator_inv_f, rightUnitor_hom_f,
      leftUnitor_inv_f, rightDualCoevaluation_f, rightDualEvaluation_f]
    exact ExactPairing.coevaluation_evaluation X.1 X'
  evaluation_coevaluation' := by
    ext
    simp only [comp_f, whiskerLeft_f, whiskerRight_f, associator_hom_f, leftUnitor_hom_f,
      rightUnitor_inv_f, rightDualCoevaluation_f, rightDualEvaluation_f]
    exact ExactPairing.evaluation_coevaluation X.1 X'

/-- The coevaluation of the lifted pairing is `rightDualCoevaluation`. -/
@[simp]
theorem coevaluation_rightDualObj : η_ X (rightDualObj X X') = rightDualCoevaluation X X' :=
  rfl

/-- The evaluation of the lifted pairing is `rightDualEvaluation`. -/
@[simp]
theorem evaluation_rightDualObj : ε_ X (rightDualObj X X') = rightDualEvaluation X X' :=
  rfl

/-- An object of the centre whose underlying object has a right dual has a right dual: the right
dual of the underlying object, with the induced half-braiding. -/
instance hasRightDual (X : Center C) [HasRightDual X.1] : HasRightDual X where
  rightDual := rightDualObj X X.1ᘁ

variable {X} [HasRightDual X.1]

/-- The right dual of an object of the centre has the right dual of its underlying object as
underlying object. -/
@[simp]
theorem rightDual_fst : (Xᘁ).1 = X.1ᘁ :=
  rfl

/-- The half-braiding of the right dual of `X : Center C` is induced from that of `X`. -/
@[simp]
theorem rightDual_snd : (Xᘁ).2 = X.2.rightDual X.1ᘁ :=
  rfl

/-- The coevaluation of `X : Center C` and its right dual is computed in `C`. -/
@[simp]
theorem coevaluation_f : (η_ X Xᘁ).f = η_ X.1 X.1ᘁ :=
  (rfl)

/-- The evaluation of `X : Center C` and its right dual is computed in `C`. -/
@[simp]
theorem evaluation_f : (ε_ X Xᘁ).f = ε_ X.1 X.1ᘁ :=
  (rfl)

/-- The right adjoint mate of a morphism of the centre is computed in `C`. -/
@[simp]
theorem rightAdjointMate_f {Y : Center C} [HasRightDual Y.1] (f : X ⟶ Y) :
    (fᘁ).f = (f.f)ᘁ := by
  rw [rightAdjointMate, rightAdjointMate]
  simp only [comp_f, whiskerLeft_f, whiskerRight_f, associator_inv_f, rightUnitor_inv_f,
    leftUnitor_hom_f, coevaluation_f, evaluation_f]
  -- The remaining difference is only in how the objects `(Xᘁ).1` and `X.1ᘁ` are written.
  rfl

end Center

/-- The Drinfeld centre of a rigid category is rigid. Right duals are computed in `C` and carry
the induced half-braiding `HalfBraiding.rightDual`; left duals are obtained from right duals using
the braiding of the centre. -/
noncomputable instance Center.rigidCategory [RigidCategory C] : RigidCategory (Center C) where
  leftDual X := BraidedCategory.hasLeftDualOfHasRightDual (X := X)

end CategoryTheory
