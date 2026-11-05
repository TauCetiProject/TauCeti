/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import TauCeti.CategoryTheory.Monoidal.Center.Basic
public import TauCeti.CategoryTheory.Monoidal.Center.Induction.End
public import TauCeti.CategoryTheory.Monoidal.Center.Preadditive

/-!
# Induction to the Drinfeld centre and its right adjunction

Let `C` be a finite semisimple rigid `k`-linear monoidal category over an algebraically closed
field `k`, with finitely many isomorphism classes of simple objects and finite-dimensional simple
endomorphism spaces. In `TauCeti.CategoryTheory.Monoidal.Center.Induction.End`, the categorical end
`∫_{Y ∈ C} (Y ⊗ X) ⊗ Yᘁ` is realized for each `X : C` as the finite biproduct

```
I(X) = ⨁ (S : SimpleClasses C), (S.repr ⊗ X) ⊗ S.reprᘁ
```

with canonical dinatural projections `centerInductionCodinat X Y : I(X) ⟶ (Y ⊗ X) ⊗ Yᘁ` and
universal end property preserved by any additive functor.

Using this universal end property under `tensorLeft U` and `tensorRight U`, this file equips `I(X)`
with its canonical half-braiding `I(X) ⊗ U ≅ U ⊗ I(X)` determined on each wedge projection
`U ◁ centerInductionCodinat X Y` by evaluating `centerInductionCodinat X (U ⊗ Y)` against `U`. This
defines the additive `k`-linear induction functor `centerInduction k C : C ⥤ Center C` and makes it
right adjoint to `Center.forget C` (`centerInductionAdjunctionRight k C`), without assuming
simplicity of the tensor unit or a pivotal structure.

## Main declarations

* `TauCeti.centerInductionHalfBraiding`: the canonical half-braiding on
  `⨁ S : SimpleClasses C, (S.repr ⊗ X) ⊗ S.reprᘁ`;
* `TauCeti.centerInduction`: the centre induction functor `C ⥤ Center C`, together with its
  `Functor.Additive`, `Functor.Linear k`, and `Functor.IsRightAdjoint` instances (hence
  limit preservation);
* `TauCeti.centerInductionAdjunctionRight`: the right adjunction
  `Center.forget C ⊣ centerInduction k C`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §§2, 8
* M. Müger, *From subfactors to categories and topology II: The quantum double of tensor
  categories and subfactors*, J. Pure Appl. Algebra **180** (2003), 159–219
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13, 9.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory ExactPairing

universe w v u

namespace TauCeti

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RigidCategory C] [IsFiniteSemisimpleCategory C]
  [Finite (SimpleClasses C)] [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CenterInduction

/-- The underlying object `⨁ S : SimpleClasses C, (S.repr ⊗ X) ⊗ S.reprᘁ` of `(centerInduction k
C).obj X`. -/
private abbrev Obj (X : C) : C :=
  ⨁ fun S : SimpleClasses C ↦ (S.repr ⊗ X) ⊗ S.reprᘁ

/-! ### String-pulling helpers for `tensorRightHomEquiv` -/

omit [Abelian C] [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]
  [Finite (SimpleClasses C)] in
private theorem tensorRightHomEquiv_whiskerLeft_symm {A U U' Z : C} (f : U ⟶ U')
    (g' : A ⟶ Z ⊗ U'ᘁ) :
    tensorRightHomEquiv A U Uᘁ Z (A ◁ f ≫ (tensorRightHomEquiv A U' U'ᘁ Z).symm g') =
      g' ≫ Z ◁ rightAdjointMate f := by
  dsimp only [tensorRightHomEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, rightAdjointMate,
    rightMate]
  calc _ = 𝟙 _ ⊗≫ (A ◁ (η_ U Uᘁ ≫ f ▷ Uᘁ) ≫ g' ▷ (U' ⊗ Uᘁ)) ⊗≫
            Z ◁ ε_ U' U'ᘁ ▷ Uᘁ ⊗≫ 𝟙 _ := by
          simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
          monoidal
    _ = g' ⊗≫ Z ◁ (U'ᘁ ◁ (η_ U Uᘁ ≫ f ▷ Uᘁ) ⊗≫ ε_ U' U'ᘁ ▷ Uᘁ) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]; monoidal
    _ = g' ≫ Z ◁ _ := by
          simp only [MonoidalCategory.whiskerLeft_comp]
          monoidal

omit [Abelian C] [MonoidalPreadditive C] [RigidCategory C] [IsFiniteSemisimpleCategory C]
  [Finite (SimpleClasses C)] in
@[reassoc]
private theorem tensorRightHomEquiv_symm_comp {A U U' B B' : C} [ExactPairing U U']
    (φ : A ⟶ B ⊗ U') (g : B ⟶ B') :
    (tensorRightHomEquiv A U U' B).symm φ ≫ g =
      (tensorRightHomEquiv A U U' B').symm (φ ≫ (g ▷ U')) := by
  apply (tensorRightHomEquiv A U U' B').injective
  rw [tensorRightHomEquiv_naturality, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

omit [Abelian C] [MonoidalPreadditive C] [RigidCategory C] [IsFiniteSemisimpleCategory C]
  [Finite (SimpleClasses C)] in
private theorem tensorRightHomEquiv_whiskerRight_comp {A A' U U' B : C} [ExactPairing U U']
    (f : A ⟶ A') (h : A' ⊗ U ⟶ B) :
    tensorRightHomEquiv A U U' B ((f ▷ U) ≫ h) = f ≫ tensorRightHomEquiv A' U U' B h := by
  apply (tensorRightHomEquiv A U U' B).symm.injective
  rw [Equiv.symm_apply_apply, tensorRightHomEquiv_symm_naturality, Equiv.symm_apply_apply]

omit [Abelian C] [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]
  [Finite (SimpleClasses C)] in
private theorem tensorRightHomEquiv_tensor_rightDualTensorIso {A U V Z : C}
    (g : (A ⊗ U) ⊗ V ⟶ Z) :
    tensorRightHomEquiv A (U ⊗ V) (U ⊗ V)ᘁ Z ((α_ A U V).inv ≫ g) ≫
        Z ◁ (rightDualTensorIso U V).hom =
      tensorRightHomEquiv A U Uᘁ (Z ⊗ Vᘁ) (tensorRightHomEquiv (A ⊗ U) V Vᘁ Z g) ≫
        (α_ Z Vᘁ Uᘁ).hom := by
  have hcoev : η_ (U ⊗ V) (U ⊗ V)ᘁ ≫ (U ⊗ V) ◁ (rightDualTensorIso U V).hom =
      η_ (U ⊗ V) (Vᘁ ⊗ Uᘁ) :=
    coevaluation_comp_whiskerLeft_rightDualTensorIso_hom U V
  dsimp only [tensorRightHomEquiv, Equiv.coe_fn_mk]
  calc _ = 𝟙 _ ⊗≫ A ◁ (η_ (U ⊗ V) (U ⊗ V)ᘁ ≫ (U ⊗ V) ◁ (rightDualTensorIso U V).hom) ⊗≫
            g ▷ (Vᘁ ⊗ Uᘁ) ⊗≫ 𝟙 _ := by
          simp only [Category.assoc, comp_whiskerRight]
          rw [← whisker_exchange]
          monoidal
    _ = _ := by
          rw [hcoev]
          simp only [ExactPairing.tensor_coevaluation, Category.assoc, comp_whiskerRight]
          monoidal

/-! ### The half-braiding on `Obj X` -/

/-- Reassociation isomorphism `((U ⊗ Y) ⊗ X) ⊗ (Z ⊗ Uᘁ) ⟶ (U ⊗ ((Y ⊗ X) ⊗ Z)) ⊗ Uᘁ`. -/
private def reassocRight (U Y X Z : C) :
    ((U ⊗ Y) ⊗ X) ⊗ (Z ⊗ Uᘁ) ⟶ (U ⊗ ((Y ⊗ X) ⊗ Z)) ⊗ Uᘁ :=
  ((α_ U Y X).hom ▷ (Z ⊗ Uᘁ)) ≫ (α_ (U ⊗ (Y ⊗ X)) Z Uᘁ).inv ≫ ((α_ U (Y ⊗ X) Z).hom ▷ Uᘁ)

/-- Reassociation isomorphism `(((ᘁU : C) ⊗ Y) ⊗ X) ⊗ (Z ⊗ U) ⟶ (ᘁU : C) ⊗ (((Y ⊗ X) ⊗ Z) ⊗ U)`. -/
private def reassocLeft (U Y X Z : C) :
    (((ᘁU : C) ⊗ Y) ⊗ X) ⊗ (Z ⊗ U) ⟶ (ᘁU : C) ⊗ (((Y ⊗ X) ⊗ Z) ⊗ U) :=
  ((α_ (ᘁU : C) Y X).hom ▷ (Z ⊗ U)) ≫ (α_ (ᘁU : C) (Y ⊗ X) (Z ⊗ U)).hom ≫
    ((ᘁU : C) ◁ (α_ (Y ⊗ X) Z U).inv)

/-- Canonical identification `((ᘁU ⊗ Y)ᘁ) ≅ Yᘁ ⊗ U`. -/
private abbrev rightDualLeftDualTensorIso (U Y : C) : ((ᘁU : C) ⊗ Y)ᘁ ≅ Yᘁ ⊗ U :=
  rightDualIso (RightRigidCategory.rightDual ((ᘁU : C) ⊗ Y)).exact
    (ExactPairing.tensor (X₁ := (ᘁU : C)) (X₂ := Y) (Y₁ := U) (Y₂ := Yᘁ))

/-- The `Y`-component wedge defining `βHom X U : Obj X ⊗ U ⟶ U ⊗ Obj X`. -/
private def βHomWedge (X U Y : C) : Obj X ⊗ U ⟶ U ⊗ ((Y ⊗ X) ⊗ Yᘁ) :=
  (tensorRightHomEquiv (Obj X) U Uᘁ (U ⊗ ((Y ⊗ X) ⊗ Yᘁ))).symm
    (centerInductionCodinat X (U ⊗ Y) ≫
      ((U ⊗ Y) ⊗ X) ◁ (rightDualTensorIso U Y).hom ≫
      reassocRight U Y X Yᘁ)

/-- The `Y`-component wedge defining `βInv X U : U ⊗ Obj X ⟶ Obj X ⊗ U`. -/
private def βInvWedge (X U Y : C) : U ⊗ Obj X ⟶ ((Y ⊗ X) ⊗ Yᘁ) ⊗ U :=
  (tensorLeftHomEquiv (Obj X) (ᘁU : C) U (((Y ⊗ X) ⊗ Yᘁ) ⊗ U)).symm
    (centerInductionCodinat X ((ᘁU : C) ⊗ Y) ≫
      (((ᘁU : C) ⊗ Y) ⊗ X) ◁ (rightDualLeftDualTensorIso U Y).hom ≫
      reassocLeft U Y X Yᘁ)

include k in
private theorem βHomWedge_dinatural (X U : C) {Y Y' : C} (g : Y ⟶ Y') :
    βHomWedge X U Y ≫ U ◁ ((g ▷ X) ▷ Yᘁ) =
      βHomWedge X U Y' ≫ U ◁ ((Y' ⊗ X) ◁ rightAdjointMate g) := by
  apply (tensorRightHomEquiv (Obj X) U Uᘁ (U ⊗ ((Y' ⊗ X) ⊗ Yᘁ))).injective
  rw [tensorRightHomEquiv_naturality, tensorRightHomEquiv_naturality]
  simp only [βHomWedge, Equiv.apply_symm_apply, Category.assoc]
  have h1 : reassocRight U Y X Yᘁ ≫ (U ◁ ((g ▷ X) ▷ Yᘁ)) ▷ Uᘁ =
      ((((U ◁ g) ▷ X) ▷ (Yᘁ ⊗ Uᘁ)) ≫ reassocRight U Y' X Yᘁ) := by
    dsimp only [reassocRight]; monoidal
  have h2 : reassocRight U Y' X Y'ᘁ ≫ (U ◁ ((Y' ⊗ X) ◁ rightAdjointMate g)) ▷ Uᘁ =
      ((((U ⊗ Y') ⊗ X) ◁ (rightAdjointMate g ▷ Uᘁ)) ≫ reassocRight U Y' X Yᘁ) := by
    dsimp only [reassocRight]; monoidal
  have hdual : rightAdjointMate (U ◁ g) ≫ (rightDualTensorIso U Y).hom =
      (rightDualTensorIso U Y').hom ≫ (rightAdjointMate g ▷ Uᘁ) := by
    simpa using rightDualTensorIso_hom_naturality (𝟙 U) g
  rw [h1, h2, whisker_exchange_assoc,
    centerInductionCodinat_dinatural_assoc k X (U ◁ g),
    ← MonoidalCategory.whiskerLeft_comp_assoc, hdual, MonoidalCategory.whiskerLeft_comp_assoc]

include k in
private theorem βInvWedge_dinatural (X U : C) {Y Y' : C} (g : Y ⟶ Y') :
    βInvWedge X U Y ≫ (((g ▷ X) ▷ Yᘁ) ▷ U) =
      βInvWedge X U Y' ≫ (((Y' ⊗ X) ◁ rightAdjointMate g) ▷ U) := by
  apply (tensorLeftHomEquiv (Obj X) (ᘁU : C) U (((Y' ⊗ X) ⊗ Yᘁ) ⊗ U)).injective
  rw [tensorLeftHomEquiv_naturality, tensorLeftHomEquiv_naturality]
  simp only [βInvWedge, Equiv.apply_symm_apply, Category.assoc]
  have h1 : reassocLeft U Y X Yᘁ ≫ (ᘁU : C) ◁ (((g ▷ X) ▷ Yᘁ) ▷ U) =
      ((((((ᘁU : C) ◁ g) ▷ X) ▷ (Yᘁ ⊗ U)) ≫ reassocLeft U Y' X Yᘁ)) := by
    dsimp only [reassocLeft]; monoidal
  have h2 : reassocLeft U Y' X Y'ᘁ ≫ (ᘁU : C) ◁ (((Y' ⊗ X) ◁ rightAdjointMate g) ▷ U) =
      ((((((ᘁU : C) ⊗ Y') ⊗ X) ◁ (rightAdjointMate g ▷ U)) ≫ reassocLeft U Y' X Yᘁ)) := by
    dsimp only [reassocLeft]; monoidal
  have hdual : rightAdjointMate ((ᘁU : C) ◁ g) ≫ (rightDualLeftDualTensorIso U Y).hom =
      (rightDualLeftDualTensorIso U Y').hom ≫ (rightAdjointMate g ▷ U) := by
    simp only [rightDualLeftDualTensorIso, rightDualIso_hom, rightAdjointMate_eq_rightMate,
      ← rightMate_whiskerLeft (HasRightDual.exact (X := Y)) (HasRightDual.exact (X := Y'))
        (HasLeftDual.exact (Y := U)) g,
      ← comp_rightMate, Category.id_comp, Category.comp_id]
  rw [h1, h2, whisker_exchange_assoc,
    centerInductionCodinat_dinatural_assoc k X ((ᘁU : C) ◁ g),
    ← MonoidalCategory.whiskerLeft_comp_assoc, hdual, MonoidalCategory.whiskerLeft_comp_assoc]

/-- Forward component of the half-braiding on `Obj X`. -/
private def βHom (X U : C) : Obj X ⊗ U ⟶ U ⊗ Obj X :=
  centerInductionMapLift (F := tensorLeft U) (βHomWedge X U)

/-- Inverse component of the half-braiding on `Obj X`. -/
private def βInv (X U : C) : U ⊗ Obj X ⟶ Obj X ⊗ U :=
  centerInductionMapLift (F := tensorRight U) (βInvWedge X U)

include k in
@[reassoc]
private theorem βHom_comp_whiskerLeft_codinat (X U Y : C) :
    βHom X U ≫ U ◁ centerInductionCodinat X Y = βHomWedge X U Y :=
  centerInductionMapLift_comp_map_codinat (F := tensorLeft U) (βHomWedge X U)
    (βHomWedge_dinatural k X U) Y

include k in
@[reassoc]
private theorem βInv_comp_codinat_whiskerRight (X U Y : C) :
    βInv X U ≫ (centerInductionCodinat X Y ▷ U) = βInvWedge X U Y :=
  centerInductionMapLift_comp_map_codinat (F := tensorRight U) (βInvWedge X U)
    (βInvWedge_dinatural k X U) Y

omit [Abelian C] [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]
  [Finite (SimpleClasses C)] in
private theorem rightAdjointMate_eval_leftDual (U Y : C) :
    rightAdjointMate ((α_ U (ᘁU : C) Y).inv ≫ ε_ (ᘁU : C) U ▷ Y ≫ (λ_ Y).hom) ≫
        (rightDualTensorIso U ((ᘁU : C) ⊗ Y)).hom ≫
        ((rightDualLeftDualTensorIso U Y).hom ▷ Uᘁ) =
      (ρ_ Yᘁ).inv ≫ Yᘁ ◁ η_ U Uᘁ ≫ (α_ Yᘁ U Uᘁ).inv := by
  have hassoc : rightMate
      (ExactPairing.tensor (X₁ := U) (X₂ := (ᘁU : C) ⊗ Y) (Y₁ := Uᘁ) (Y₂ := Yᘁ ⊗ U))
      (ExactPairing.tensor (X₁ := U ⊗ (ᘁU : C)) (X₂ := Y) (Y₁ := U ⊗ Uᘁ) (Y₂ := Yᘁ))
      (α_ U (ᘁU : C) Y).inv = (α_ Yᘁ U Uᘁ).inv := by
    rw [← cancel_mono (α_ Yᘁ U Uᘁ).hom, Iso.inv_hom_id,
      ← rightMate_associator_hom (HasRightDual.exact (X := U))
        (HasLeftDual.exact (Y := U)) (HasRightDual.exact (X := Y)),
      ← comp_rightMate, Iso.hom_inv_id, rightMate_id]
  simp only [rightDualTensorIso, rightDualLeftDualTensorIso, rightDualIso_hom,
    rightAdjointMate_eq_rightMate]
  rw [← rightMate_whiskerLeft _ _ (HasRightDual.exact (X := U)),
    ← comp_rightMate, ← comp_rightMate, MonoidalCategory.whiskerLeft_id,
    Category.comp_id, Category.id_comp,
    comp_rightMate (pY := ExactPairing.tensor (X₁ := U ⊗ (ᘁU : C)) (X₂ := Y)
      (Y₁ := U ⊗ Uᘁ) (Y₂ := Yᘁ)),
    comp_rightMate (pY := ExactPairing.tensor (X₁ := 𝟙_ C) (X₂ := Y)
      (Y₁ := 𝟙_ C) (Y₂ := Yᘁ)),
    rightMate_leftUnitor_hom,
    rightMate_whiskerRight
      (ExactPairing.tensor (X₁ := U) (X₂ := (ᘁU : C)) (Y₁ := Uᘁ) (Y₂ := U))
      exactPairingUnit (HasRightDual.exact (X := Y)),
    rightMate_evaluation (HasLeftDual.exact (Y := U)) (HasRightDual.exact (X := U)),
    hassoc, Category.assoc]

include k in
private theorem βHom_comp_βInv (X U : C) : βHom X U ≫ βInv X U = 𝟙 (Obj X ⊗ U) := by
  refine centerInduction_map_hom_ext (F := tensorRight U) fun S ↦ ?_
  rw [Functor.flip_obj_map, curriedTensor_map_app, Category.id_comp, Category.assoc,
    ← centerInductionCodinat_repr k X S, βInv_comp_codinat_whiskerRight k]
  dsimp only [βInvWedge, tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]
  simp only [MonoidalCategory.whiskerLeft_comp, ← Category.assoc]
  rw [βHom_comp_whiskerLeft_codinat k X U ((ᘁU : C) ⊗ S.repr)]
  simp only [Category.assoc]
  apply (tensorRightHomEquiv (Obj X) U Uᘁ (((S.repr ⊗ X) ⊗ S.reprᘁ) ⊗ U)).injective
  rw [βHomWedge, tensorRightHomEquiv_naturality, Equiv.apply_symm_apply,
    ← Category.comp_id (centerInductionCodinat X S.repr ▷ U),
    tensorRightHomEquiv_whiskerRight_comp]
  dsimp only [tensorRightHomEquiv, Equiv.coe_fn_mk]
  let m : U ⊗ ((ᘁU : C) ⊗ S.repr) ⟶ S.repr :=
    (α_ U (ᘁU : C) S.repr).inv ≫ ε_ (ᘁU : C) U ▷ S.repr ≫ (λ_ S.repr).hom
  have h1 : reassocRight U ((ᘁU : C) ⊗ S.repr) X ((ᘁU : C) ⊗ S.repr)ᘁ ≫
      (U ◁ ((((ᘁU : C) ⊗ S.repr) ⊗ X) ◁ (rightDualLeftDualTensorIso U S.repr).hom)) ▷ Uᘁ =
      (((U ⊗ ((ᘁU : C) ⊗ S.repr)) ⊗ X) ◁ ((rightDualLeftDualTensorIso U S.repr).hom ▷ Uᘁ)) ≫
        reassocRight U ((ᘁU : C) ⊗ S.repr) X (S.reprᘁ ⊗ U) := by
    dsimp only [reassocRight]; monoidal
  have h2 : reassocRight U ((ᘁU : C) ⊗ S.repr) X (S.reprᘁ ⊗ U) ≫
      ((U ◁ reassocLeft U S.repr X S.reprᘁ) ▷ Uᘁ) ≫
      ((α_ U (ᘁU : C) (((S.repr ⊗ X) ⊗ S.reprᘁ) ⊗ U)).inv ▷ Uᘁ) ≫
      ((ε_ (ᘁU : C) U ▷ (((S.repr ⊗ X) ⊗ S.reprᘁ) ⊗ U)) ▷ Uᘁ) ≫
      ((λ_ (((S.repr ⊗ X) ⊗ S.reprᘁ) ⊗ U)).hom ▷ Uᘁ) =
      ((m ▷ X) ▷ ((S.reprᘁ ⊗ U) ⊗ Uᘁ)) ≫
        ((S.repr ⊗ X) ◁ (α_ S.reprᘁ U Uᘁ).hom) ≫
        (α_ (S.repr ⊗ X) S.reprᘁ (U ⊗ Uᘁ)).inv ≫
        (α_ ((S.repr ⊗ X) ⊗ S.reprᘁ) U Uᘁ).inv := by
    dsimp only [reassocRight, reassocLeft, m]
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    monoidal
  simp only [comp_whiskerRight, id_whiskerRight, Category.comp_id, Category.assoc]
  rw [reassoc_of% h1, h2, ← MonoidalCategory.whiskerLeft_comp_assoc,
    whisker_exchange_assoc (m ▷ X), centerInductionCodinat_dinatural_assoc k X m,
    ← MonoidalCategory.whiskerLeft_comp_assoc, rightAdjointMate_eval_leftDual U S.repr]
  congr 1
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

omit [Abelian C] [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]
  [Finite (SimpleClasses C)] in
private theorem rightAdjointMate_coeval_leftDual (U Y : C) :
    (rightDualLeftDualTensorIso U (U ⊗ Y)).hom ≫
        ((rightDualTensorIso U Y).hom ▷ U) ≫
        (α_ Yᘁ Uᘁ U).hom ≫ Yᘁ ◁ ε_ U Uᘁ ≫ (ρ_ Yᘁ).hom =
      rightAdjointMate ((λ_ Y).inv ≫ η_ (ᘁU : C) U ▷ Y ≫ (α_ (ᘁU : C) U Y).hom) := by
  let pU := HasRightDual.exact (X := U)
  let pLU := HasLeftDual.exact (Y := U)
  let pY := HasRightDual.exact (X := Y)
  have hunitor : rightMate pY
      (ExactPairing.tensor (X₁ := 𝟙_ C) (X₂ := Y) (Y₁ := 𝟙_ C) (Y₂ := Yᘁ))
      (λ_ Y).inv = (ρ_ Yᘁ).hom := by
    rw [← cancel_mono (ρ_ Yᘁ).inv, Iso.hom_inv_id, ← rightMate_leftUnitor_hom pY,
      ← comp_rightMate, Iso.hom_inv_id, rightMate_id]
  have h1' : (rightDualLeftDualTensorIso U (U ⊗ Y)).hom ≫
      ((rightDualTensorIso U Y).hom ▷ U) =
      rightMate
        (ExactPairing.tensor (X₁ := (ᘁU : C)) (X₂ := U ⊗ Y) (Y₁ := U) (Y₂ := Yᘁ ⊗ Uᘁ))
        (HasRightDual.exact (X := (ᘁU : C) ⊗ (U ⊗ Y)))
        (𝟙 _) := by
    simp only [rightDualLeftDualTensorIso, rightDualTensorIso, rightDualIso_hom]
    rw [← rightMate_whiskerLeft _ _ pLU, MonoidalCategory.whiskerLeft_id, ← comp_rightMate,
      Category.id_comp]
  rw [reassoc_of% h1',
    ← rightMate_associator_hom pLU pU pY,
    ← rightMate_coevaluation pLU pU,
    ← rightMate_whiskerRight exactPairingUnit
      (ExactPairing.tensor (X₁ := (ᘁU : C)) (X₂ := U) (Y₁ := U) (Y₂ := Uᘁ)) pY,
    ← hunitor,
    ← comp_rightMate, ← comp_rightMate, ← comp_rightMate,
    Category.comp_id, rightAdjointMate_eq_rightMate]
  simp only [Category.assoc]
  rfl

include k in
private theorem βInv_comp_βHom (X U : C) : βInv X U ≫ βHom X U = 𝟙 (U ⊗ Obj X) := by
  refine centerInduction_map_hom_ext (F := tensorLeft U) fun S ↦ ?_
  rw [curriedTensor_obj_map, Category.id_comp, Category.assoc, ← centerInductionCodinat_repr k X S,
    βHom_comp_whiskerLeft_codinat k]
  dsimp only [βHomWedge, tensorRightHomEquiv, Equiv.coe_fn_symm_mk]
  simp only [comp_whiskerRight, ← Category.assoc]
  rw [βInv_comp_codinat_whiskerRight k X U (U ⊗ S.repr)]
  simp only [Category.assoc]
  apply (tensorLeftHomEquiv (Obj X) (ᘁU : C) U (U ⊗ ((S.repr ⊗ X) ⊗ S.reprᘁ))).injective
  have hrhs : tensorLeftHomEquiv (Obj X) (ᘁU : C) U (U ⊗ ((S.repr ⊗ X) ⊗ S.reprᘁ))
      (U ◁ centerInductionCodinat X S.repr) =
      centerInductionCodinat X S.repr ≫
        (λ_ ((S.repr ⊗ X) ⊗ S.reprᘁ)).inv ≫
        η_ (ᘁU : C) U ▷ ((S.repr ⊗ X) ⊗ S.reprᘁ) ≫
        (α_ (ᘁU : C) U ((S.repr ⊗ X) ⊗ S.reprᘁ)).hom := by
    dsimp only [tensorLeftHomEquiv, Equiv.coe_fn_mk]
    rw [← associator_naturality_right, ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  rw [βInvWedge, tensorLeftHomEquiv_naturality, Equiv.apply_symm_apply, hrhs]
  let n : S.repr ⟶ (ᘁU : C) ⊗ (U ⊗ S.repr) :=
    (λ_ S.repr).inv ≫ η_ (ᘁU : C) U ▷ S.repr ≫ (α_ (ᘁU : C) U S.repr).hom
  have h1 : reassocLeft U (U ⊗ S.repr) X (U ⊗ S.repr)ᘁ ≫
      (ᘁU : C) ◁ ((((U ⊗ S.repr) ⊗ X) ◁ (rightDualTensorIso U S.repr).hom) ▷ U) =
      ((((ᘁU : C) ⊗ (U ⊗ S.repr)) ⊗ X) ◁ ((rightDualTensorIso U S.repr).hom ▷ U)) ≫
        reassocLeft U (U ⊗ S.repr) X (S.reprᘁ ⊗ Uᘁ) := by
    dsimp only [reassocLeft]; monoidal
  let r2 : (((ᘁU : C) ⊗ (U ⊗ S.repr)) ⊗ X) ⊗ S.reprᘁ ⟶
      (ᘁU : C) ⊗ (U ⊗ ((S.repr ⊗ X) ⊗ S.reprᘁ)) :=
    ((α_ (ᘁU : C) (U ⊗ S.repr) X).hom ▷ S.reprᘁ) ≫
      (α_ (ᘁU : C) ((U ⊗ S.repr) ⊗ X) S.reprᘁ).hom ≫
      ((ᘁU : C) ◁ ((α_ U S.repr X).hom ▷ S.reprᘁ)) ≫
      ((ᘁU : C) ◁ (α_ U (S.repr ⊗ X) S.reprᘁ).hom)
  have h2 : reassocLeft U (U ⊗ S.repr) X (S.reprᘁ ⊗ Uᘁ) ≫
      ((ᘁU : C) ◁ (reassocRight U S.repr X S.reprᘁ ▷ U)) ≫
      ((ᘁU : C) ◁ (α_ (U ⊗ ((S.repr ⊗ X) ⊗ S.reprᘁ)) Uᘁ U).hom) ≫
      ((ᘁU : C) ◁ ((U ⊗ ((S.repr ⊗ X) ⊗ S.reprᘁ)) ◁ ε_ U Uᘁ)) ≫
      ((ᘁU : C) ◁ (ρ_ (U ⊗ ((S.repr ⊗ X) ⊗ S.reprᘁ))).hom) =
      ((((ᘁU : C) ⊗ (U ⊗ S.repr)) ⊗ X) ◁
        ((α_ S.reprᘁ Uᘁ U).hom ≫ S.reprᘁ ◁ ε_ U Uᘁ ≫ (ρ_ S.reprᘁ).hom)) ≫ r2 := by
    dsimp only [reassocLeft, reassocRight, r2]
    simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    monoidal
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% h1, h2, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [rightAdjointMate_coeval_leftDual U S.repr, ← centerInductionCodinat_dinatural_assoc k X n]
  congr 1
  dsimp only [n, r2]
  simp only [comp_whiskerRight, Category.assoc]
  monoidal

include k in
private theorem βHom_naturality (X : C) {U U' : C} (f : U ⟶ U') :
    (Obj X ◁ f) ≫ βHom X U' = βHom X U ≫ (f ▷ Obj X) := by
  refine centerInduction_map_hom_ext (F := tensorLeft U') fun S ↦ ?_
  rw [curriedTensor_obj_map, Category.assoc, Category.assoc, ← centerInductionCodinat_repr k X S,
    βHom_comp_whiskerLeft_codinat k, ← whisker_exchange, ← Category.assoc,
    βHom_comp_whiskerLeft_codinat k]
  apply (tensorRightHomEquiv (Obj X) U Uᘁ (U' ⊗ ((S.repr ⊗ X) ⊗ S.reprᘁ))).injective
  rw [βHomWedge, tensorRightHomEquiv_whiskerLeft_symm,
    βHomWedge, tensorRightHomEquiv_naturality, Equiv.apply_symm_apply]
  simp only [Category.assoc]
  let r : ((U' ⊗ S.repr) ⊗ X) ⊗ (S.reprᘁ ⊗ Uᘁ) ⟶ (U' ⊗ ((S.repr ⊗ X) ⊗ S.reprᘁ)) ⊗ Uᘁ :=
    ((α_ U' S.repr X).hom ▷ (S.reprᘁ ⊗ Uᘁ)) ≫
      (α_ (U' ⊗ (S.repr ⊗ X)) S.reprᘁ Uᘁ).inv ≫
      ((α_ U' (S.repr ⊗ X) S.reprᘁ).hom ▷ Uᘁ)
  have h1 : reassocRight U' S.repr X S.reprᘁ ≫
      (U' ⊗ ((S.repr ⊗ X) ⊗ S.reprᘁ)) ◁ rightAdjointMate f =
      (((U' ⊗ S.repr) ⊗ X) ◁ (S.reprᘁ ◁ rightAdjointMate f)) ≫ r := by
    dsimp only [reassocRight, r]; monoidal
  have h2 : reassocRight U S.repr X S.reprᘁ ≫ ((f ▷ ((S.repr ⊗ X) ⊗ S.reprᘁ)) ▷ Uᘁ) =
      ((((f ▷ S.repr) ▷ X) ▷ (S.reprᘁ ⊗ Uᘁ)) ≫ r) := by
    dsimp only [reassocRight, r]; monoidal
  have hdual : rightAdjointMate (f ▷ S.repr) ≫ (rightDualTensorIso U S.repr).hom =
      (rightDualTensorIso U' S.repr).hom ≫ (S.reprᘁ ◁ rightAdjointMate f) := by
    simpa using rightDualTensorIso_hom_naturality f (𝟙 S.repr)
  rw [h1, h2, whisker_exchange_assoc ((f ▷ S.repr) ▷ X),
    centerInductionCodinat_dinatural_assoc k X (f ▷ S.repr),
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← hdual, MonoidalCategory.whiskerLeft_comp_assoc]

omit [Abelian C] [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]
  [Finite (SimpleClasses C)] in
private theorem reassocRight_pentagon (U V Y X : C) :
    reassocRight U (V ⊗ Y) X (V ⊗ Y)ᘁ ≫
        (U ◁ (((V ⊗ Y) ⊗ X) ◁ (rightDualTensorIso V Y).hom ≫ reassocRight V Y X Yᘁ)) ▷ Uᘁ ≫
        ((α_ U (V ⊗ ((Y ⊗ X) ⊗ Yᘁ)) Vᘁ).inv ▷ Uᘁ) ≫
        (((α_ U V ((Y ⊗ X) ⊗ Yᘁ)).inv ▷ Vᘁ) ▷ Uᘁ) ≫
        (α_ ((U ⊗ V) ⊗ ((Y ⊗ X) ⊗ Yᘁ)) Vᘁ Uᘁ).hom =
      (((U ⊗ (V ⊗ Y)) ⊗ X) ◁ (((rightDualTensorIso V Y).hom ▷ Uᘁ) ≫ (α_ Yᘁ Vᘁ Uᘁ).hom)) ≫
        (((α_ U V Y).inv ▷ X) ▷ (Yᘁ ⊗ (Vᘁ ⊗ Uᘁ))) ≫
        ((α_ (U ⊗ V) Y X).hom ▷ (Yᘁ ⊗ (Vᘁ ⊗ Uᘁ))) ≫
        (α_ ((U ⊗ V) ⊗ (Y ⊗ X)) Yᘁ (Vᘁ ⊗ Uᘁ)).inv ≫
        ((α_ (U ⊗ V) (Y ⊗ X) Yᘁ).hom ▷ (Vᘁ ⊗ Uᘁ)) := by
  have hpullV : reassocRight U (V ⊗ Y) X (V ⊗ Y)ᘁ ≫
      (U ◁ (((V ⊗ Y) ⊗ X) ◁ (rightDualTensorIso V Y).hom)) ▷ Uᘁ =
      (((U ⊗ (V ⊗ Y)) ⊗ X) ◁ ((rightDualTensorIso V Y).hom ▷ Uᘁ)) ≫
        reassocRight U (V ⊗ Y) X (Yᘁ ⊗ Vᘁ) := by
    dsimp only [reassocRight]; monoidal
  have hcoh : reassocRight U (V ⊗ Y) X (Yᘁ ⊗ Vᘁ) ≫
      (U ◁ reassocRight V Y X Yᘁ) ▷ Uᘁ ≫
      ((α_ U (V ⊗ ((Y ⊗ X) ⊗ Yᘁ)) Vᘁ).inv ▷ Uᘁ) ≫
      (((α_ U V ((Y ⊗ X) ⊗ Yᘁ)).inv ▷ Vᘁ) ▷ Uᘁ) ≫
      (α_ ((U ⊗ V) ⊗ ((Y ⊗ X) ⊗ Yᘁ)) Vᘁ Uᘁ).hom =
      (((U ⊗ (V ⊗ Y)) ⊗ X) ◁ (α_ Yᘁ Vᘁ Uᘁ).hom) ≫
        (((α_ U V Y).inv ▷ X) ▷ (Yᘁ ⊗ (Vᘁ ⊗ Uᘁ))) ≫
        ((α_ (U ⊗ V) Y X).hom ▷ (Yᘁ ⊗ (Vᘁ ⊗ Uᘁ))) ≫
        (α_ ((U ⊗ V) ⊗ (Y ⊗ X)) Yᘁ (Vᘁ ⊗ Uᘁ)).inv ≫
        ((α_ (U ⊗ V) (Y ⊗ X) Yᘁ).hom ▷ (Vᘁ ⊗ Uᘁ)) := by
    dsimp only [reassocRight]; monoidal
  simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  rw [reassoc_of% hpullV, hcoh]

include k in
private theorem βHom_monoidal (X U V : C) :
    βHom X (U ⊗ V) =
      (α_ (Obj X) U V).inv ≫
        (βHom X U ▷ V) ≫ (α_ U (Obj X) V).hom ≫ (U ◁ βHom X V) ≫ (α_ U V (Obj X)).inv := by
  refine centerInduction_map_hom_ext (F := tensorLeft (U ⊗ V)) fun S ↦ ?_
  rw [curriedTensor_obj_map]
  let W : C := (S.repr ⊗ X) ⊗ S.reprᘁ
  rw [← centerInductionCodinat_repr k X S, βHom_comp_whiskerLeft_codinat k]
  have hrhs1 : (U ◁ βHom X V) ≫ (α_ U V (Obj X)).inv ≫
      (U ⊗ V) ◁ centerInductionCodinat X S.repr =
      (U ◁ βHomWedge X V S.repr) ≫ (α_ U V W).inv := by
    rw [← associator_inv_naturality_right, ← MonoidalCategory.whiskerLeft_comp_assoc,
      βHom_comp_whiskerLeft_codinat k]
  simp only [Category.assoc]
  rw [hrhs1]
  have hrhs2 : (βHom X U ▷ V) ≫ (α_ U (Obj X) V).hom ≫
      (U ◁ βHomWedge X V S.repr) =
      (tensorRightHomEquiv (Obj X ⊗ U) V Vᘁ (U ⊗ (V ⊗ W))).symm
        (βHomWedge X U (V ⊗ S.repr) ≫
          U ◁ (((V ⊗ S.repr) ⊗ X) ◁ (rightDualTensorIso V S.repr).hom ≫
            reassocRight V S.repr X S.reprᘁ) ≫
          (α_ U (V ⊗ W) Vᘁ).inv) := by
    dsimp only [βHomWedge, tensorRightHomEquiv, Equiv.coe_fn_symm_mk]
    have hcomm : (βHom X U ▷ V) ≫ (α_ U (Obj X) V).hom ≫
        U ◁ (centerInductionCodinat X (V ⊗ S.repr) ▷ V) =
        ((βHomWedge X U (V ⊗ S.repr)) ▷ V) ≫ (α_ U _ V).hom := by
      rw [← associator_naturality_middle, ← comp_whiskerRight_assoc,
        βHom_comp_whiskerLeft_codinat k]
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [reassoc_of% hcomm]
    dsimp only [βHomWedge, tensorRightHomEquiv, Equiv.coe_fn_symm_mk]
    simp only [comp_whiskerRight, Category.assoc]
    monoidal
  rw [reassoc_of% hrhs2]
  apply (tensorRightHomEquiv (Obj X) (U ⊗ V) (U ⊗ V)ᘁ ((U ⊗ V) ⊗ W)).injective
  rw [βHomWedge, Equiv.apply_symm_apply,
    ← cancel_mono (((U ⊗ V) ⊗ W) ◁ (rightDualTensorIso U V).hom),
    tensorRightHomEquiv_tensor_rightDualTensorIso,
    tensorRightHomEquiv_naturality, Equiv.apply_symm_apply,
    βHomWedge, tensorRightHomEquiv_symm_comp_assoc, tensorRightHomEquiv_symm_comp,
    tensorRightHomEquiv_symm_comp, Equiv.apply_symm_apply]
  simp only [Category.assoc]
  have hlhs : reassocRight (U ⊗ V) S.repr X S.reprᘁ ≫
      ((U ⊗ V) ⊗ W) ◁ (rightDualTensorIso U V).hom =
      ((((U ⊗ V) ⊗ S.repr) ⊗ X) ◁ (S.reprᘁ ◁ (rightDualTensorIso U V).hom)) ≫
        ((α_ (U ⊗ V) S.repr X).hom ▷ (S.reprᘁ ⊗ (Vᘁ ⊗ Uᘁ))) ≫
        (α_ ((U ⊗ V) ⊗ (S.repr ⊗ X)) S.reprᘁ (Vᘁ ⊗ Uᘁ)).inv ≫
        ((α_ (U ⊗ V) (S.repr ⊗ X) S.reprᘁ).hom ▷ (Vᘁ ⊗ Uᘁ)) := by
    dsimp only [reassocRight, W]; monoidal
  rw [hlhs, reassocRight_pentagon U V S.repr X]
  have hdinat : centerInductionCodinat X ((U ⊗ V) ⊗ S.repr) =
      centerInductionCodinat X (U ⊗ (V ⊗ S.repr)) ≫
        (((U ⊗ (V ⊗ S.repr)) ⊗ X) ◁ rightAdjointMate (α_ U V S.repr).hom) ≫
        (((α_ U V S.repr).inv ▷ X) ▷ ((U ⊗ V) ⊗ S.repr)ᘁ) := by
    rw [← centerInductionCodinat_dinatural_assoc k X (α_ U V S.repr).hom,
      ← comp_whiskerRight, ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, id_whiskerRight,
      Category.comp_id]
  rw [hdinat]
  simp only [Category.assoc, whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    rightDualTensorIso_associativity]

include k in
/-- The canonical half-braiding on `Obj X = ⨁ S, (S.repr ⊗ X) ⊗ S.reprᘁ`. -/
private def halfBraiding (X : C) : HalfBraiding (Obj X) where
  β U :=
    { hom := βHom X U
      inv := βInv X U
      hom_inv_id := βHom_comp_βInv k X U
      inv_hom_id := βInv_comp_βHom k X U }
  monoidal U V := βHom_monoidal k X U V
  naturality f := βHom_naturality k X f

include k in
private theorem map_comm {X X' : C} (f : X ⟶ X') (U : C) :
    (biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ f) ▷ S.reprᘁ) ▷ U) ≫ βHom X' U =
      βHom X U ≫ (U ◁ biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ f) ▷ S.reprᘁ)) := by
  refine centerInduction_map_hom_ext (F := tensorLeft U) fun S ↦ ?_
  rw [curriedTensor_obj_map]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp, biproduct.map_π,
    ← centerInductionCodinat_repr k X' S, βHom_comp_whiskerLeft_codinat k,
    ← centerInductionCodinat_repr k X S, MonoidalCategory.whiskerLeft_comp,
    βHom_comp_whiskerLeft_codinat_assoc k]
  apply (tensorRightHomEquiv (Obj X) U Uᘁ (U ⊗ ((S.repr ⊗ X') ⊗ S.reprᘁ))).injective
  rw [βHomWedge, tensorRightHomEquiv_whiskerRight_comp, Equiv.apply_symm_apply,
    βHomWedge, tensorRightHomEquiv_naturality, Equiv.apply_symm_apply]
  rw [biproduct_map_comp_centerInductionCodinat_assoc]
  simp only [Category.assoc]
  congr 1
  have hcoh : reassocRight U S.repr X S.reprᘁ ≫ (U ◁ ((S.repr ◁ f) ▷ S.reprᘁ)) ▷ Uᘁ =
      ((((U ⊗ S.repr) ◁ f) ▷ (S.reprᘁ ⊗ Uᘁ)) ≫ reassocRight U S.repr X' S.reprᘁ) := by
    dsimp only [reassocRight]; monoidal
  rw [hcoh, ← whisker_exchange_assoc]

/-! ### Unit and counit of the right adjunction -/

/-- The `Y`-component wedge of the unit `A ⟶ Obj A` for a half-braiding `b` on `A`. -/
private def unitRightWedge {A : C} (b : HalfBraiding A) (Y : C) : A ⟶ (Y ⊗ A) ⊗ Yᘁ :=
  tensorRightHomEquiv A Y Yᘁ (Y ⊗ A) (b.β Y).hom

omit [Abelian C] [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]
  [Finite (SimpleClasses C)] in
private theorem unitRightWedge_dinatural {A : C} (b : HalfBraiding A) {Y Y' : C} (g : Y ⟶ Y') :
    unitRightWedge b Y ≫ ((g ▷ A) ▷ Yᘁ) =
      unitRightWedge b Y' ≫ ((Y' ⊗ A) ◁ rightAdjointMate g) := by
  rw [unitRightWedge, ← tensorRightHomEquiv_naturality, ← b.naturality g,
    ← tensorRightHomEquiv_whiskerLeft_symm, unitRightWedge, Equiv.symm_apply_apply]

/-- Underlying morphism `A ⟶ Obj A` of `(centerInductionAdjunctionRight k C).unit.app ⟨A, b⟩`. -/
private def unitRightF {A : C} (b : HalfBraiding A) : A ⟶ Obj A :=
  centerInductionLift (unitRightWedge b)

@[reassoc]
private theorem unitRightF_comp_codinat {A : C} (b : HalfBraiding A) (Y : C) :
    unitRightF b ≫ centerInductionCodinat A Y = unitRightWedge b Y :=
  centerInductionLift_comp_codinat (unitRightWedge b) (unitRightWedge_dinatural b) Y

include k in
private theorem unitRightF_comm {A : C} (b : HalfBraiding A) (U : C) :
    (unitRightF b ▷ U) ≫ βHom A U = (b.β U).hom ≫ (U ◁ unitRightF b) := by
  refine centerInduction_map_hom_ext (F := tensorLeft U) fun S ↦ ?_
  rw [curriedTensor_obj_map]
  simp only [Category.assoc]
  rw [← centerInductionCodinat_repr k A S, βHom_comp_whiskerLeft_codinat k,
    ← MonoidalCategory.whiskerLeft_comp, unitRightF_comp_codinat]
  apply (tensorRightHomEquiv A U Uᘁ (U ⊗ ((S.repr ⊗ A) ⊗ S.reprᘁ))).injective
  rw [βHomWedge, tensorRightHomEquiv_whiskerRight_comp, Equiv.apply_symm_apply,
    unitRightF_comp_codinat_assoc]
  dsimp only [unitRightWedge, tensorRightHomEquiv, Equiv.coe_fn_mk]
  have hcoev : η_ (U ⊗ S.repr) (U ⊗ S.repr)ᘁ ≫
      (U ⊗ S.repr) ◁ (rightDualTensorIso U S.repr).hom =
      η_ (U ⊗ S.repr) (S.reprᘁ ⊗ Uᘁ) :=
    coevaluation_comp_whiskerLeft_rightDualTensorIso_hom U S.repr
  calc _ = 𝟙 _ ⊗≫ (A ◁ (η_ (U ⊗ S.repr) (U ⊗ S.repr)ᘁ ≫
              (U ⊗ S.repr) ◁ (rightDualTensorIso U S.repr).hom)) ⊗≫
            ((b.β (U ⊗ S.repr)).hom ▷ (S.reprᘁ ⊗ Uᘁ)) ⊗≫ 𝟙 _ := by
          dsimp only [reassocRight]
          simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp]
          rw [← whisker_exchange_assoc]
          monoidal
    _ = 𝟙 _ ⊗≫ A ◁ η_ U Uᘁ ⊗≫
          ((A ◁ (U ◁ η_ S.repr S.reprᘁ) ⊗≫ ((b.β U).hom ▷ (S.repr ⊗ S.reprᘁ))) ▷ Uᘁ) ⊗≫
          ((U ◁ (b.β S.repr).hom) ▷ S.reprᘁ) ▷ Uᘁ ⊗≫ 𝟙 _ := by
          rw [hcoev, b.monoidal U S.repr]
          simp only [ExactPairing.tensor_coevaluation, comp_whiskerRight]
          monoidal
    _ = _ := by
          have hexch : A ◁ (U ◁ η_ S.repr S.reprᘁ) ⊗≫ ((b.β U).hom ▷ (S.repr ⊗ S.reprᘁ)) =
              𝟙 _ ⊗≫ ((b.β U).hom ▷ 𝟙_ C) ⊗≫ (U ◁ (A ◁ η_ S.repr S.reprᘁ)) ⊗≫ 𝟙 _ := by
            calc _ = 𝟙 _ ⊗≫ ((A ⊗ U) ◁ η_ S.repr S.reprᘁ ≫
                      ((b.β U).hom ▷ (S.repr ⊗ S.reprᘁ))) := by monoidal
              _ = 𝟙 _ ⊗≫ (((b.β U).hom ▷ 𝟙_ C) ≫
                    (U ⊗ A) ◁ η_ S.repr S.reprᘁ) := by rw [whisker_exchange]
              _ = _ := by monoidal
          rw [hexch]
          simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
          monoidal

include k in
private theorem unitRightF_naturality {A A' : C} {b : HalfBraiding A} {b' : HalfBraiding A'}
    (f : A ⟶ A') (hf : ∀ U : C, f ▷ U ≫ (b'.β U).hom = (b.β U).hom ≫ U ◁ f) :
    f ≫ unitRightF b' =
      unitRightF b ≫ biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ f) ▷ S.reprᘁ) := by
  refine centerInduction_map_hom_ext (F := 𝟭 C) fun S ↦ ?_
  simp only [Functor.id_map, Category.assoc, biproduct.map_π]
  rw [← centerInductionCodinat_repr k A S, ← centerInductionCodinat_repr k A' S,
    unitRightF_comp_codinat, unitRightF_comp_codinat_assoc]
  rw [unitRightWedge, unitRightWedge, ← tensorRightHomEquiv_naturality, ← hf S.repr]
  dsimp only [tensorRightHomEquiv, Equiv.coe_fn_mk]
  simp only [comp_whiskerRight]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    ← associator_inv_naturality_left_assoc]

/-- Canonical identification of `RightRigidCategory.rightDual (𝟙_ C)` with `𝟙_ C`. -/
private abbrev rightDualUnitIso :
    @HasRightDual.rightDual C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C)) ≅ 𝟙_ C :=
  rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact (Y₂ := 𝟙_ C) exactPairingUnit

/-- Component `Obj X ⟶ X` of `(centerInductionAdjunctionRight k C).counit.app X`. -/
private def counitRightF (X : C) : Obj X ⟶ X :=
  centerInductionCodinat X (𝟙_ C) ≫ ((λ_ X).hom ⊗ₘ rightDualUnitIso.hom) ≫ (ρ_ X).hom

omit [MonoidalPreadditive C] in
private theorem counitRightF_naturality {X X' : C} (f : X ⟶ X') :
    biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ f) ▷ S.reprᘁ) ≫ counitRightF X' =
      counitRightF X ≫ f := by
  dsimp only [counitRightF]
  rw [biproduct_map_comp_centerInductionCodinat_assoc, tensorHom_def, tensorHom_def]
  simp only [Category.assoc]
  congr 1
  rw [← comp_whiskerRight_assoc, leftUnitor_naturality, comp_whiskerRight_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality]

private theorem unitRight_comp_counitRight {A : C} (b : HalfBraiding A) :
    unitRightF b ≫ counitRightF A = 𝟙 A := by
  dsimp only [counitRightF]
  rw [unitRightF_comp_codinat_assoc]
  dsimp only [unitRightWedge, tensorRightHomEquiv, Equiv.coe_fn_mk]
  let η₁ := @ExactPairing.coevaluation C _ _ (𝟙_ C) _ (RightRigidCategory.rightDual (𝟙_ C)).exact
  have hcoev : η₁ ≫ 𝟙_ C ◁ rightDualUnitIso.hom = (ρ_ (𝟙_ C)).inv := by
    dsimp only [η₁, rightDualUnitIso]
    rw [rightDualIso_hom, coevaluation_comp_rightMate, id_whiskerRight, Category.comp_id,
      TauCeti.ExactPairing.unit_coevaluation]
  rw [HalfBraiding.β_tensorUnit_hom]
  calc _ = 𝟙 _ ⊗≫ A ◁ (η₁ ≫ 𝟙_ C ◁ rightDualUnitIso.hom) ⊗≫ 𝟙 A := by
          simp only [η₁, tensorHom_def', Category.assoc, comp_whiskerRight,
            MonoidalCategory.whiskerLeft_comp]
          monoidal
    _ = 𝟙 A := by rw [hcoev]; monoidal

include k in
private theorem induction_unitRight_comp_map_counitRight (X : C) :
    unitRightF (halfBraiding k X) ≫
        biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ counitRightF X) ▷ S.reprᘁ) =
      𝟙 (Obj X) := by
  refine centerInduction_map_hom_ext (F := 𝟭 C) fun S ↦ ?_
  simp only [Functor.id_map, Category.id_comp, Category.assoc, biproduct.map_π]
  rw [← centerInductionCodinat_repr k X S, ← centerInductionCodinat_repr k (Obj X) S,
    unitRightF_comp_codinat_assoc]
  -- Unfold `(halfBraiding k X).β S.repr` inside `unitRightWedge`.
  change tensorRightHomEquiv (Obj X) S.repr S.reprᘁ (S.repr ⊗ Obj X) (βHom X S.repr) ≫
      ((S.repr ◁ counitRightF X) ▷ S.reprᘁ) = centerInductionCodinat X S.repr
  rw [← tensorRightHomEquiv_naturality]
  dsimp only [counitRightF]
  rw [MonoidalCategory.whiskerLeft_comp, ← Category.assoc,
    βHom_comp_whiskerLeft_codinat k X S.repr (𝟙_ C),
    βHomWedge, tensorRightHomEquiv_naturality, Equiv.apply_symm_apply]
  have hunit : (λ_ S.reprᘁ).inv =
      rightAdjointMate (ρ_ S.repr).hom ≫
        (@rightDualTensorIso C _ _ S.repr (𝟙_ C) _ (RightRigidCategory.rightDual (𝟙_ C)) _).hom ≫
        (rightDualUnitIso.hom ▷ S.reprᘁ) :=
    @rightDualTensorIso_rightUnitality C _ _ S.repr _ (RightRigidCategory.rightDual (𝟙_ C)) _
  have hcoh : reassocRight S.repr (𝟙_ C) X
        (@HasRightDual.rightDual C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C))) ≫
      (S.repr ◁ (((λ_ X).hom ⊗ₘ rightDualUnitIso.hom) ≫ (ρ_ X).hom)) ▷ S.reprᘁ =
      ((((S.repr ⊗ 𝟙_ C) ⊗ X) ◁ (rightDualUnitIso.hom ▷ S.reprᘁ)) ≫
        (((ρ_ S.repr).hom ▷ X) ▷ (𝟙_ C ⊗ S.reprᘁ)) ≫
        ((S.repr ⊗ X) ◁ (λ_ S.reprᘁ).hom)) := by
    dsimp only [reassocRight, tensorHom_def]
    simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    monoidal
  have hdual :
      (@rightDualTensorIso C _ _ S.repr (𝟙_ C) _ (RightRigidCategory.rightDual (𝟙_ C)) _).hom ≫
        (rightDualUnitIso.hom ▷ S.reprᘁ) =
      rightAdjointMate (ρ_ S.repr).inv ≫ (λ_ S.reprᘁ).inv := by
    rw [hunit, ← Category.assoc, ← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id,
      Category.id_comp]
  have hcancel :
      rightAdjointMate (ρ_ S.repr).hom ≫ rightAdjointMate (ρ_ S.repr).inv ≫ (λ_ S.reprᘁ).inv =
        (λ_ S.reprᘁ).inv := by
    rw [← Category.assoc, ← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id,
      Category.id_comp]
  simp only [Category.assoc]
  rw [hcoh, ← MonoidalCategory.whiskerLeft_comp_assoc, hdual,
    whisker_exchange_assoc ((ρ_ S.repr).hom ▷ X),
    centerInductionCodinat_dinatural_assoc k X ((ρ_ S.repr).hom),
    ← MonoidalCategory.whiskerLeft_comp_assoc, hcancel,
    ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
    Category.comp_id]

end CenterInduction

section PublicAPI

/-- The canonical half-braiding on `⨁ S : SimpleClasses C, (S.repr ⊗ X) ⊗ S.reprᘁ`. -/
def centerInductionHalfBraiding (X : C) :
    HalfBraiding (⨁ fun S : SimpleClasses C ↦ (S.repr ⊗ X) ⊗ S.reprᘁ) :=
  CenterInduction.halfBraiding k X

variable (C)

/-- **Induction to the Drinfeld centre**: sends `X : C` to the end
`⨁ S : SimpleClasses C, (S.repr ⊗ X) ⊗ S.reprᘁ` equipped with its canonical half-braiding. -/
@[expose]
def centerInduction : C ⥤ Center C where
  obj X := ⟨⨁ fun S : SimpleClasses C ↦ (S.repr ⊗ X) ⊗ S.reprᘁ, centerInductionHalfBraiding k X⟩
  map f :=
    { f := biproduct.map fun S : SimpleClasses C ↦ (S.repr ◁ f) ▷ S.reprᘁ
      comm U := by exact CenterInduction.map_comm k f U }
  map_id X := by
    refine Center.ext _ _ ?_
    -- Unfold `Center.Hom.f` on the identity morphism in `Center C`.
    change biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ 𝟙 X) ▷ S.reprᘁ) =
      𝟙 (CenterInduction.Obj X)
    refine biproduct.hom_ext _ _ fun S ↦ ?_
    rw [biproduct.map_π, MonoidalCategory.whiskerLeft_id, id_whiskerRight,
      Category.id_comp, Category.comp_id]
  map_comp f g := by
    refine Center.ext _ _ ?_
    -- Unfold `Center.Hom.f` on the composite in `Center C`.
    change biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ (f ≫ g)) ▷ S.reprᘁ) =
      biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ f) ▷ S.reprᘁ) ≫
        biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ g) ▷ S.reprᘁ)
    refine biproduct.hom_ext _ _ fun S ↦ ?_
    rw [biproduct.map_π, Category.assoc, biproduct.map_π, biproduct.map_π_assoc,
      ← comp_whiskerRight, ← MonoidalCategory.whiskerLeft_comp]

/-- Underlying object of `(centerInduction k C).obj X`. -/
@[simp]
theorem centerInduction_obj_fst (X : C) :
    ((centerInduction k C).obj X).1 = ⨁ fun S : SimpleClasses C ↦ (S.repr ⊗ X) ⊗ S.reprᘁ :=
  (rfl)

/-- Half-braiding of `(centerInduction k C).obj X`. -/
@[simp]
theorem centerInduction_obj_snd (X : C) :
    ((centerInduction k C).obj X).2 = centerInductionHalfBraiding k X :=
  (rfl)

/-- Underlying morphism of `(centerInduction k C).map f`. -/
@[simp]
theorem centerInduction_map_f {X Y : C} (f : X ⟶ Y) :
    ((centerInduction k C).map f).f =
      biproduct.map fun S : SimpleClasses C ↦ (S.repr ◁ f) ▷ S.reprᘁ :=
  (rfl)

/-- Naturality of `centerInductionCodinat X Y` in `X`. -/
theorem centerInduction_map_f_comp_codinat {X X' : C} (f : X ⟶ X') (Y : C) :
    ((centerInduction k C).map f).f ≫ centerInductionCodinat X' Y =
      centerInductionCodinat X Y ≫ ((Y ◁ f) ▷ Yᘁ) :=
  biproduct_map_comp_centerInductionCodinat f Y

/-- Naturality of `centerInductionCodinat X Y` in `X`, reassociated. -/
theorem centerInduction_map_f_comp_codinat_assoc {X X' W : C} (f : X ⟶ X') (Y : C)
    (h : (Y ⊗ X') ⊗ Yᘁ ⟶ W) :
    ((centerInduction k C).map f).f ≫ (centerInductionCodinat X' Y ≫ h) =
      centerInductionCodinat X Y ≫ ((Y ◁ f) ▷ Yᘁ) ≫ h :=
  (Category.assoc _ _ _).symm.trans <|
    (centerInduction_map_f_comp_codinat k C f Y =≫ h).trans (Category.assoc _ _ _)

/-- Characterizing equation for the forward half-braiding of `(centerInduction k C).obj X` against
the end projections `centerInductionCodinat X Y`. -/
theorem centerInduction_β_hom_comp_whiskerLeft_codinat (X U Y : C) :
    (((centerInduction k C).obj X).2.β U).hom ≫ U ◁ centerInductionCodinat X Y =
      (tensorRightHomEquiv ((centerInduction k C).obj X).1 U Uᘁ
        (U ⊗ ((Y ⊗ X) ⊗ Yᘁ))).symm
        (centerInductionCodinat X (U ⊗ Y) ≫
          ((U ⊗ Y) ⊗ X) ◁ (rightDualTensorIso U Y).hom ≫
          ((α_ U Y X).hom ▷ (Yᘁ ⊗ Uᘁ)) ≫
          (α_ (U ⊗ (Y ⊗ X)) Yᘁ Uᘁ).inv ≫
          ((α_ U (Y ⊗ X) Yᘁ).hom ▷ Uᘁ)) :=
  CenterInduction.βHom_comp_whiskerLeft_codinat k X U Y

/-- Characterizing equation for the forward half-braiding of `(centerInduction k C).obj X` against
the end projections `centerInductionCodinat X Y`, reassociated. -/
theorem centerInduction_β_hom_comp_whiskerLeft_codinat_assoc (X U Y : C) {W : C}
    (h : U ⊗ ((Y ⊗ X) ⊗ Yᘁ) ⟶ W) :
    (((centerInduction k C).obj X).2.β U).hom ≫ (U ◁ centerInductionCodinat X Y ≫ h) =
      (tensorRightHomEquiv ((centerInduction k C).obj X).1 U Uᘁ
        (U ⊗ ((Y ⊗ X) ⊗ Yᘁ))).symm
        (centerInductionCodinat X (U ⊗ Y) ≫
          ((U ⊗ Y) ⊗ X) ◁ (rightDualTensorIso U Y).hom ≫
          ((α_ U Y X).hom ▷ (Yᘁ ⊗ Uᘁ)) ≫
          (α_ (U ⊗ (Y ⊗ X)) Yᘁ Uᘁ).inv ≫
          ((α_ U (Y ⊗ X) Yᘁ).hom ▷ Uᘁ)) ≫ h :=
  (Category.assoc _ _ _).symm.trans (centerInduction_β_hom_comp_whiskerLeft_codinat k C X U Y =≫ h)

/-- Characterizing equation for the inverse half-braiding of `(centerInduction k C).obj X` against
the end projections `centerInductionCodinat X Y`. -/
theorem centerInduction_β_inv_comp_codinat_whiskerRight (X U Y : C) :
    (((centerInduction k C).obj X).2.β U).inv ≫ (centerInductionCodinat X Y ▷ U) =
      (tensorLeftHomEquiv ((centerInduction k C).obj X).1 (ᘁU : C) U
        (((Y ⊗ X) ⊗ Yᘁ) ⊗ U)).symm
        (centerInductionCodinat X ((ᘁU : C) ⊗ Y) ≫
          (((ᘁU : C) ⊗ Y) ⊗ X) ◁
            (rightDualIso (RightRigidCategory.rightDual ((ᘁU : C) ⊗ Y)).exact
              (ExactPairing.tensor (X₁ := (ᘁU : C)) (X₂ := Y) (Y₁ := U) (Y₂ := Yᘁ))).hom ≫
          ((α_ (ᘁU : C) Y X).hom ▷ (Yᘁ ⊗ U)) ≫
          (α_ (ᘁU : C) (Y ⊗ X) (Yᘁ ⊗ U)).hom ≫
          ((ᘁU : C) ◁ (α_ (Y ⊗ X) Yᘁ U).inv)) :=
  CenterInduction.βInv_comp_codinat_whiskerRight k X U Y

/-- Characterizing equation for the inverse half-braiding of `(centerInduction k C).obj X` against
the end projections `centerInductionCodinat X Y`, reassociated. -/
theorem centerInduction_β_inv_comp_codinat_whiskerRight_assoc (X U Y : C) {W : C}
    (h : ((Y ⊗ X) ⊗ Yᘁ) ⊗ U ⟶ W) :
    (((centerInduction k C).obj X).2.β U).inv ≫ ((centerInductionCodinat X Y ▷ U) ≫ h) =
      (tensorLeftHomEquiv ((centerInduction k C).obj X).1 (ᘁU : C) U
        (((Y ⊗ X) ⊗ Yᘁ) ⊗ U)).symm
        (centerInductionCodinat X ((ᘁU : C) ⊗ Y) ≫
          (((ᘁU : C) ⊗ Y) ⊗ X) ◁
            (rightDualIso (RightRigidCategory.rightDual ((ᘁU : C) ⊗ Y)).exact
              (ExactPairing.tensor (X₁ := (ᘁU : C)) (X₂ := Y) (Y₁ := U) (Y₂ := Yᘁ))).hom ≫
          ((α_ (ᘁU : C) Y X).hom ▷ (Yᘁ ⊗ U)) ≫
          (α_ (ᘁU : C) (Y ⊗ X) (Yᘁ ⊗ U)).hom ≫
          ((ᘁU : C) ◁ (α_ (Y ⊗ X) Yᘁ U).inv)) ≫ h :=
  (Category.assoc _ _ _).symm.trans (centerInduction_β_inv_comp_codinat_whiskerRight k C X U Y =≫ h)

instance : (centerInduction k C).Additive where
  map_add {X Y} f g := by
    refine Center.ext _ _ ?_
    -- Unfold `Center.Hom.f` on the sum in `Center C`.
    change biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ (f + g)) ▷ S.reprᘁ) =
      biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ f) ▷ S.reprᘁ) +
        biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ g) ▷ S.reprᘁ)
    refine biproduct.hom_ext _ _ fun S ↦ ?_
    rw [Preadditive.add_comp, biproduct.map_π, biproduct.map_π, biproduct.map_π,
      MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight,
      Preadditive.comp_add]

instance : (centerInduction k C).Linear k where
  map_smul {X Y} f r := by
    refine Center.ext _ _ ?_
    -- Unfold `Center.Hom.f` on the scalar multiple in `Center C`.
    change biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ (r • f)) ▷ S.reprᘁ) =
      r • biproduct.map (fun S : SimpleClasses C ↦ (S.repr ◁ f) ▷ S.reprᘁ)
    refine biproduct.hom_ext _ _ fun S ↦ ?_
    rw [Linear.smul_comp, biproduct.map_π, biproduct.map_π,
      MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight, Linear.comp_smul]

/-- **Right adjunction for centre induction**: `Center.forget C ⊣ centerInduction k C`. This holds
for any rigid finite semisimple category over an algebraically closed field without assuming
simplicity of the tensor unit or a pivotal structure. -/
def centerInductionAdjunctionRight : Center.forget C ⊣ centerInduction k C :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app Z :=
            { f := CenterInduction.unitRightF Z.2
              comm U := CenterInduction.unitRightF_comm k Z.2 U }
          naturality _ _ h :=
            Center.ext _ _ (CenterInduction.unitRightF_naturality k h.f h.comm) }
      counit :=
        { app X := CenterInduction.counitRightF X
          naturality _ _ f := CenterInduction.counitRightF_naturality f }
      left_triangle := by
        refine NatTrans.ext (funext fun Z ↦ ?_)
        -- Unfold functor and natural transformation composition on `(Center.forget C).obj Z = Z.1`.
        change CenterInduction.unitRightF Z.2 ≫
            𝟙 (CenterInduction.Obj Z.1) ≫ CenterInduction.counitRightF Z.1 = 𝟙 Z.1
        rw [Category.id_comp]
        exact CenterInduction.unitRight_comp_counitRight Z.2
      right_triangle := by
        refine NatTrans.ext (funext fun X ↦ Center.ext _ _ ?_)
        -- Unfold `Center.Hom.f` on the right triangle composite at `X`.
        change CenterInduction.unitRightF (CenterInduction.halfBraiding k X) ≫
            𝟙 (CenterInduction.Obj (CenterInduction.Obj X)) ≫
            biproduct.map (fun S : SimpleClasses C ↦
              (S.repr ◁ CenterInduction.counitRightF X) ▷ S.reprᘁ) =
          𝟙 (CenterInduction.Obj X)
        rw [Category.id_comp]
        exact CenterInduction.induction_unitRight_comp_map_counitRight k X }

/-- `centerInduction k C` is a right adjoint (in particular, it preserves all limits that exist in
`C`). -/
instance : (centerInduction k C).IsRightAdjoint :=
  (centerInductionAdjunctionRight k C).isRightAdjoint

/-- Component of the unit of `centerInductionAdjunctionRight` along the end projection
`centerInductionCodinat Z.1 Y`. -/
theorem centerInductionAdjunctionRight_unit_app_f_comp_codinat (Z : Center C) (Y : C) :
    ((centerInductionAdjunctionRight k C).unit.app Z).f ≫ centerInductionCodinat Z.1 Y =
      (ρ_ Z.1).inv ≫ Z.1 ◁ η_ Y Yᘁ ≫ (α_ Z.1 Y Yᘁ).inv ≫ (Z.2.β Y).hom ▷ Yᘁ :=
  CenterInduction.unitRightF_comp_codinat Z.2 Y

/-- Component of the unit of `centerInductionAdjunctionRight` along the end projection
`centerInductionCodinat Z.1 Y`, reassociated. -/
theorem centerInductionAdjunctionRight_unit_app_f_comp_codinat_assoc (Z : Center C) (Y : C)
    {W : C} (h : (Y ⊗ Z.1) ⊗ Yᘁ ⟶ W) :
    ((centerInductionAdjunctionRight k C).unit.app Z).f ≫ (centerInductionCodinat Z.1 Y ≫ h) =
      (ρ_ Z.1).inv ≫ Z.1 ◁ η_ Y Yᘁ ≫ (α_ Z.1 Y Yᘁ).inv ≫ (Z.2.β Y).hom ▷ Yᘁ ≫ h :=
  (Category.assoc _ _ _).symm.trans <|
    (centerInductionAdjunctionRight_unit_app_f_comp_codinat k C Z Y =≫ h).trans
      (by simp only [Category.assoc])

/-- Component of the unit of `centerInductionAdjunctionRight` on the `S`-summand of
`((centerInduction k C).obj Z.1).1`. -/
@[simp]
theorem centerInductionAdjunctionRight_unit_app_f_comp_π (Z : Center C) (S : SimpleClasses C) :
    ((centerInductionAdjunctionRight k C).unit.app Z).f ≫
        biproduct.π (fun T : SimpleClasses C ↦ (T.repr ⊗ Z.1) ⊗ T.reprᘁ) S =
      (ρ_ Z.1).inv ≫ Z.1 ◁ η_ S.repr S.reprᘁ ≫ (α_ Z.1 S.repr S.reprᘁ).inv ≫
        (Z.2.β S.repr).hom ▷ S.reprᘁ := by
  exact centerInductionCodinat_repr k Z.1 S ▸
    centerInductionAdjunctionRight_unit_app_f_comp_codinat k C Z S.repr

/-- Component of the unit of `centerInductionAdjunctionRight` on the `S`-summand of
`((centerInduction k C).obj Z.1).1`, reassociated. -/
@[simp]
theorem centerInductionAdjunctionRight_unit_app_f_comp_π_assoc (Z : Center C)
    (S : SimpleClasses C) {W : C} (h : (S.repr ⊗ Z.1) ⊗ S.reprᘁ ⟶ W) :
    ((centerInductionAdjunctionRight k C).unit.app Z).f ≫
        (biproduct.π (fun T : SimpleClasses C ↦ (T.repr ⊗ Z.1) ⊗ T.reprᘁ) S ≫ h) =
      (ρ_ Z.1).inv ≫ Z.1 ◁ η_ S.repr S.reprᘁ ≫ (α_ Z.1 S.repr S.reprᘁ).inv ≫
        (Z.2.β S.repr).hom ▷ S.reprᘁ ≫ h :=
  (Category.assoc _ _ _).symm.trans <|
    (centerInductionAdjunctionRight_unit_app_f_comp_π k C Z S =≫ h).trans
      (by simp only [Category.assoc])

/-- Explicit formula for the counit of `centerInductionAdjunctionRight` at `X`. -/
@[simp]
theorem centerInductionAdjunctionRight_counit_app (X : C) :
    (centerInductionAdjunctionRight k C).counit.app X =
      centerInductionCodinat X (𝟙_ C) ≫
        ((λ_ X).hom ⊗ₘ
          (@rightDualIso C _ _ (𝟙_ C) _ _
            (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom) ≫
        (ρ_ X).hom :=
  (rfl)

end PublicAPI

end TauCeti
