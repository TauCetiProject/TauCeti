/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import TauCeti.CategoryTheory.Monoidal.Center.Induction.End
public import TauCeti.CategoryTheory.Monoidal.Center.Preadditive
public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor

/-!
# The right adjunction for induction into the Drinfeld centre

Let `C` be a rigid, `k`-linear, finite semisimple abelian monoidal category over an algebraically
closed field `k`, with finitely many isomorphism classes of simple objects and finite-dimensional
morphism spaces. In `TauCeti.CategoryTheory.Monoidal.Center.Induction.Basic`, the induction functor
`Center.induction k C : C ⥤ Center C` sends `X : C` to `inductionObj X = ⨁ S, S.repr ⊗ X ⊗ S.reprᘁ`
with half-braiding `inductionHalfBraiding k X` assembled from dual bases of `S.repr ⟶ U ⊗ T.repr`.
In `TauCeti.CategoryTheory.Monoidal.Center.Induction.End`, `inductionObj X` is equipped with its
universal dinatural end projections `inductionEndπ X Y : inductionObj X ⟶ Y ⊗ X ⊗ Yᘁ`.

This file connects the dual-basis half-braiding to the universal end structure: composing
`inductionβHom k X U` with `U ◁ inductionEndπ X Y` transposes `inductionEndπ X (U ⊗ Y)` along
the Frobenius reciprocity `tensorRightHomEquiv` (`inductionβHom_comp_whiskerLeft_inductionEndπ`).
From this characterization we equip `Center.induction k C` with its `Functor.Additive` and
`Functor.Linear k` instances and construct the right adjunction
`forgetInductionAdjunction k C : Center.forget C ⊣ Center.induction k C` (hence
`(Center.induction k C).IsRightAdjoint`), without assuming simplicity of the tensor unit or a
pivotal structure.

## Main declarations

* `CategoryTheory.Center.inductionβHom_comp_whiskerLeft_inductionEndπ`: characterizes the
  half-braiding `inductionβHom k X U` against the dinatural end projections `inductionEndπ X Y`;
* `CategoryTheory.Center.instAdditiveInduction` and `CategoryTheory.Center.instLinearInduction`:
  `Center.induction k C` is additive and `k`-linear;
* `CategoryTheory.Center.forgetInductionAdjunction` and
  `CategoryTheory.Center.instIsRightAdjointInduction`: the right adjunction
  `Center.forget C ⊣ Center.induction k C`, with unit and counit characterized by
  `CategoryTheory.Center.forgetInductionAdjunction_unit_app_f_comp_endπ`,
  `CategoryTheory.Center.forgetInductionAdjunction_unit_app_f_comp_π`, and
  `CategoryTheory.Center.forgetInductionAdjunction_counit_app`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §§2, 8
* M. Müger, *From subfactors to categories and topology II: The quantum double of tensor
  categories and subfactors*, J. Pure Appl. Algebra **180** (2003), 159–219
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13, 9.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory ExactPairing TauCeti

universe w v u

namespace CategoryTheory.Center

attribute [local instance] Abelian.hasFiniteBiproducts

section HalfBraidingEnd

variable (k : Type w) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RightRigidCategory C]

/-- Reassociation isomorphism `(U ⊗ Y) ⊗ X ⊗ (Z ⊗ Uᘁ) ⟶ (U ⊗ Y ⊗ X ⊗ Z) ⊗ Uᘁ`. -/
private def reassocRight (U Y X Z : C) :
    (U ⊗ Y) ⊗ X ⊗ (Z ⊗ Uᘁ) ⟶ (U ⊗ Y ⊗ X ⊗ Z) ⊗ Uᘁ :=
  (U ⊗ Y) ◁ (α_ X Z Uᘁ).inv ≫ (α_ (U ⊗ Y) (X ⊗ Z) Uᘁ).inv ≫ (α_ U Y (X ⊗ Z)).hom ▷ Uᘁ

/-- Transposing `inductionMate k U g : Aᘁ ⊗ U ⟶ Bᘁ` along `tensorRightHomEquiv` recovers the right
adjoint mate `gᘁ` followed by `(rightDualTensorIso U B).hom`. -/
private theorem tensorRightHomEquiv_inductionMate {U A B : C} (g : U ⊗ B ⟶ A) :
    tensorRightHomEquiv Aᘁ U Uᘁ Bᘁ (inductionMate k U g) =
      gᘁ ≫ (rightDualTensorIso U B).hom := by
  apply (tensorRightHomEquiv Aᘁ U Uᘁ Bᘁ).symm.injective
  rw [Equiv.symm_apply_apply]
  refine ExactPairing.rightHom_ext (X := B) ?_
  rw [inductionMate_whiskerRight_evaluation]
  symm
  dsimp only [tensorRightHomEquiv, Equiv.coe_fn_symm_mk]
  calc _ = (α_ Aᘁ U B).hom ≫
            ((gᘁ ≫ (rightDualTensorIso U B).hom) ▷ (U ⊗ B) ≫ ε_ (U ⊗ B) (Bᘁ ⊗ Uᘁ)) := by
          rw [ExactPairing.tensor_evaluation]
          simp only [comp_whiskerRight, Category.assoc]
          monoidal
    _ = (α_ Aᘁ U B).hom ≫ Aᘁ ◁ g ≫ ε_ A Aᘁ := by
          rw [comp_whiskerRight_assoc, rightDualTensorIso_hom_whiskerRight_evaluation,
            rightAdjointMate_comp_evaluation]

/-- Transposing `inductionTerm k X g f` along `tensorRightHomEquiv` applies `f` on the left factor
and `gᘁ ≫ (rightDualTensorIso U B).hom` on the right factor. -/
private theorem tensorRightHomEquiv_inductionTerm (X : C) {U A B : C}
    (g : U ⊗ B ⟶ A) (f : A ⟶ U ⊗ B) :
    tensorRightHomEquiv (A ⊗ X ⊗ Aᘁ) U Uᘁ (U ⊗ B ⊗ X ⊗ Bᘁ) (inductionTerm k X g f) =
      f ▷ (X ⊗ Aᘁ) ≫ (U ⊗ B) ◁ X ◁ (gᘁ ≫ (rightDualTensorIso U B).hom) ≫
        reassocRight U B X Bᘁ := by
  have hmate : inductionMate k U g =
      (tensorRightHomEquiv Aᘁ U Uᘁ Bᘁ).symm (gᘁ ≫ (rightDualTensorIso U B).hom) := by
    rw [← tensorRightHomEquiv_inductionMate k g, Equiv.symm_apply_apply]
  set φ : Aᘁ ⟶ Bᘁ ⊗ Uᘁ := gᘁ ≫ (rightDualTensorIso U B).hom
  rw [inductionTerm_apply, hmate]
  dsimp only [tensorRightHomEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, reassocRight]
  calc _ = 𝟙 _ ⊗≫ ((A ⊗ X ⊗ Aᘁ) ◁ η_ U Uᘁ ≫ (f ▷ (X ⊗ Aᘁ)) ▷ (U ⊗ Uᘁ)) ⊗≫
            ((U ⊗ B) ◁ X ◁ φ) ▷ U ▷ Uᘁ ⊗≫ U ◁ B ◁ X ◁ Bᘁ ◁ ε_ U Uᘁ ▷ Uᘁ ⊗≫ 𝟙 _ := by
          simp only [whiskerLeft_comp]
          monoidal
    _ = 𝟙 _ ⊗≫ f ▷ (X ⊗ Aᘁ) ⊗≫ (((U ⊗ B) ⊗ X ⊗ Aᘁ) ◁ η_ U Uᘁ ≫
            (((U ⊗ B) ◁ X ◁ φ) ▷ (U ⊗ Uᘁ))) ⊗≫ U ◁ B ◁ X ◁ Bᘁ ◁ ε_ U Uᘁ ▷ Uᘁ ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]; monoidal
    _ = 𝟙 _ ⊗≫ f ▷ (X ⊗ Aᘁ) ⊗≫ (U ⊗ B) ◁ X ◁ φ ⊗≫
            U ◁ B ◁ X ◁ Bᘁ ◁ ((Uᘁ : C) ◁ η_ U Uᘁ ⊗≫ ε_ U Uᘁ ▷ Uᘁ) ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]; monoidal
    _ = _ := by
          rw [ExactPairing.coevaluation_evaluation'']; monoidal

end HalfBraidingEnd

section Fusion

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RightRigidCategory C]
  [IsFiniteSemisimpleCategory C]

/-- The `Y`-component wedge of the unit `A ⟶ inductionObj A` for a half-braiding `b` on `A`. -/
private def unitWedge {A : C} (b : HalfBraiding A) (Y : C) : A ⟶ Y ⊗ A ⊗ Yᘁ :=
  tensorRightHomEquiv A Y Yᘁ (Y ⊗ A) (b.β Y).hom ≫ (α_ Y A Yᘁ).hom

omit [Abelian C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] in
private theorem unitWedge_dinatural {A : C} (b : HalfBraiding A) {Y Y' : C} (g : Y ⟶ Y') :
    unitWedge b Y ≫ g ▷ (A ⊗ Yᘁ) = unitWedge b Y' ≫ Y' ◁ A ◁ gᘁ := by
  rw [unitWedge, Category.assoc, ← associator_naturality_left, ← Category.assoc,
    ← tensorRightHomEquiv_naturality, ← b.naturality g, tensorRightHomEquiv_whiskerLeft_comp,
    Category.assoc, associator_naturality_right, ← Category.assoc, ← unitWedge]

section FiniteSimpleClasses

variable [Fintype (SimpleClasses C)]

/-- Underlying morphism `A ⟶ inductionObj A` of
`(forgetInductionAdjunction k C).unit.app ⟨A, b⟩`. -/
private def unitF {A : C} (b : HalfBraiding A) : A ⟶ inductionObj A :=
  inductionLift (unitWedge b)

omit [Linear k C] [MonoidalLinear k C] in
@[reassoc]
private theorem unitF_comp_endπ {A : C} (b : HalfBraiding A) (Y : C) :
    unitF b ≫ inductionEndπ A Y = unitWedge b Y :=
  inductionLift_comp_endπ (unitWedge b) (unitWedge_dinatural b) Y

omit [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C] [IsFiniteSemisimpleCategory C] in
private theorem unitF_naturality {A A' : C} {b : HalfBraiding A} {b' : HalfBraiding A'}
    (f : A ⟶ A') (hf : ∀ U : C, f ▷ U ≫ (b'.β U).hom = (b.β U).hom ≫ U ◁ f) :
    f ≫ unitF b' = unitF b ≫ inductionMap f := by
  refine inductionObj_map_hom_ext (F := 𝟭 C) fun S ↦ ?_
  simp only [Functor.id_map, Category.assoc, biproduct.map_π, unitF, inductionLift_comp_π,
    inductionLift_comp_π_assoc]
  rw [unitWedge, unitWedge, ← Category.assoc, ← tensorRightHomEquiv_whiskerRight_comp,
    hf S.repr, tensorRightHomEquiv_naturality, Category.assoc, associator_naturality_middle,
    Category.assoc]

/-- Component `inductionObj X ⟶ X` of `(forgetInductionAdjunction k C).counit.app X`. -/
private def counitF (X : C) : inductionObj X ⟶ X :=
  inductionEndπ X (𝟙_ C) ≫
    (λ_ (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual)).hom ≫
    X ◁ (rightDualUnitIso C).hom ≫
    (ρ_ X).hom

omit [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C] in
private theorem counitF_naturality {X X' : C} (f : X ⟶ X') :
    inductionMap f ≫ counitF X' = counitF X ≫ f := by
  dsimp only [counitF]
  rw [inductionMap_comp_inductionEndπ_assoc, Category.assoc, Category.assoc,
    leftUnitor_naturality_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]
  simp only [Category.assoc]

omit [Linear k C] [MonoidalLinear k C] in
private theorem unitF_comp_counitF {A : C} (b : HalfBraiding A) :
    unitF b ≫ counitF A = 𝟙 A := by
  dsimp only [counitF]
  rw [unitF_comp_endπ_assoc]
  dsimp only [unitWedge, tensorRightHomEquiv, Equiv.coe_fn_mk]
  let η₁ := @ExactPairing.coevaluation C _ _ (𝟙_ C) _ (RightRigidCategory.rightDual (𝟙_ C)).exact
  rw [HalfBraiding.β_tensorUnit_hom]
  calc _ = 𝟙 _ ⊗≫ A ◁ (η₁ ≫ 𝟙_ C ◁ (rightDualUnitIso C).hom) ⊗≫ 𝟙 A := by
          simp only [η₁, Category.assoc, comp_whiskerRight, whiskerLeft_comp]
          monoidal
    _ = 𝟙 A := by
          rw [coevaluation_comp_whiskerLeft_rightDualUnitIso_hom]
          monoidal

variable [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]

/-- The `Y`-component wedge of `inductionβHom k X U`. -/
private def βHomWedge (X U Y : C) : inductionObj X ⊗ U ⟶ U ⊗ Y ⊗ X ⊗ Yᘁ :=
  (tensorRightHomEquiv (inductionObj X) U Uᘁ (U ⊗ Y ⊗ X ⊗ Yᘁ)).symm
    (inductionEndπ X (U ⊗ Y) ≫
      (U ⊗ Y) ◁ X ◁ (rightDualTensorIso U Y).hom ≫
      reassocRight U Y X Yᘁ)

include k in
private theorem βHomWedge_dinatural (X U : C) {Y Y' : C} (g : Y ⟶ Y') :
    βHomWedge X U Y ≫ U ◁ (g ▷ (X ⊗ Yᘁ)) = βHomWedge X U Y' ≫ U ◁ Y' ◁ X ◁ gᘁ := by
  apply (tensorRightHomEquiv (inductionObj X) U Uᘁ (U ⊗ Y' ⊗ X ⊗ Yᘁ)).injective
  rw [tensorRightHomEquiv_naturality, tensorRightHomEquiv_naturality]
  simp only [βHomWedge, Equiv.apply_symm_apply, Category.assoc]
  have h1 : reassocRight U Y X Yᘁ ≫ (U ◁ (g ▷ (X ⊗ Yᘁ))) ▷ Uᘁ =
      (U ◁ g) ▷ (X ⊗ Yᘁ ⊗ Uᘁ) ≫ reassocRight U Y' X Yᘁ := by
    dsimp only [reassocRight]; monoidal
  have h2 : reassocRight U Y' X Y'ᘁ ≫ (U ◁ Y' ◁ X ◁ gᘁ) ▷ Uᘁ =
      (U ⊗ Y') ◁ X ◁ (gᘁ ▷ Uᘁ) ≫ reassocRight U Y' X Yᘁ := by
    dsimp only [reassocRight]; monoidal
  have hdual : (U ◁ g)ᘁ ≫ (rightDualTensorIso U Y).hom =
      (rightDualTensorIso U Y').hom ≫ gᘁ ▷ Uᘁ := by
    simpa using rightDualTensorIso_hom_naturality (𝟙 U) g
  rw [h1, h2, whisker_exchange_assoc, inductionEndπ_dinatural_assoc k X (U ◁ g),
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp, ← whiskerLeft_comp,
    hdual]

end FiniteSimpleClasses

variable [Fintype (SimpleClasses C)] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

private theorem inductionβHom_eq_inductionMapLift (X U : C) :
    inductionβHom k X U = inductionMapLift (F := tensorLeft U) (βHomWedge X U) := by
  refine inductionObj_hom_ext X fun S T ↦ ?_
  rw [ι_whiskerRight_inductionβHom_whiskerLeft_π, ← curriedTensor_obj_map,
    inductionMapLift_comp_map_π]
  apply (tensorRightHomEquiv (inductionSummand X S) U Uᘁ (U ⊗ T.repr ⊗ X ⊗ T.reprᘁ)).injective
  rw [βHomWedge, tensorRightHomEquiv_whiskerRight_comp, Equiv.apply_symm_apply]
  set b := Module.finBasis k (S.repr ⟶ U ⊗ T.repr)
  have hsum : tensorRightHomEquiv (inductionSummand X S) U Uᘁ (U ⊗ T.repr ⊗ X ⊗ T.reprᘁ)
        (inductionβComponent k X U S T) =
      ∑ i, tensorRightHomEquiv (inductionSummand X S) U Uᘁ (U ⊗ T.repr ⊗ X ⊗ T.reprᘁ)
        (inductionTerm k X (b.homDual i) (b i)) := by
    rw [inductionβComponent_eq k X U S T b, ← tensorRightHomLinearEquiv_apply k]
    simp only [map_sum, tensorRightHomLinearEquiv_apply]
  rw [hsum, ι_comp_inductionEndπ_assoc k X (U ⊗ T.repr) S b]
  simp only [tensorRightHomEquiv_inductionTerm, Preadditive.sum_comp, Category.assoc,
    whiskerLeft_comp]

/-- Characterizing equation for `inductionβHom k X U` against the dinatural end projections
`inductionEndπ X Y`: moving `U` past `inductionObj X` and projecting at `Y` transposes the
`(U ⊗ Y)`-projection along `tensorRightHomEquiv`. -/
@[reassoc]
theorem inductionβHom_comp_whiskerLeft_inductionEndπ (X U Y : C) :
    inductionβHom k X U ≫ U ◁ inductionEndπ X Y =
      (tensorRightHomEquiv (inductionObj X) U Uᘁ (U ⊗ Y ⊗ X ⊗ Yᘁ)).symm
        (inductionEndπ X (U ⊗ Y) ≫
          (U ⊗ Y) ◁ X ◁ (rightDualTensorIso U Y).hom ≫
          (U ⊗ Y) ◁ (α_ X Yᘁ Uᘁ).inv ≫
          (α_ (U ⊗ Y) (X ⊗ Yᘁ) Uᘁ).inv ≫
          (α_ U Y (X ⊗ Yᘁ)).hom ▷ Uᘁ) := by
  rw [inductionβHom_eq_inductionMapLift k X U]
  exact inductionMapLift_comp_map_endπ (F := tensorLeft U) (βHomWedge X U)
    (βHomWedge_dinatural k X U) Y

private theorem unitF_comm {A : C} (b : HalfBraiding A) (U : C) :
    unitF b ▷ U ≫ inductionβHom k A U = (b.β U).hom ≫ U ◁ unitF b := by
  refine inductionObj_map_hom_ext (F := tensorLeft U) fun S ↦ ?_
  rw [curriedTensor_obj_map]
  simp only [Category.assoc]
  rw [← inductionEndπ_repr k A S, inductionβHom_comp_whiskerLeft_inductionEndπ k,
    ← whiskerLeft_comp, unitF_comp_endπ]
  apply (tensorRightHomEquiv A U Uᘁ (U ⊗ S.repr ⊗ A ⊗ S.reprᘁ)).injective
  rw [tensorRightHomEquiv_whiskerRight_comp, Equiv.apply_symm_apply, unitF_comp_endπ_assoc]
  dsimp only [unitWedge, tensorRightHomEquiv, Equiv.coe_fn_mk]
  have hcoev : η_ (U ⊗ S.repr) (U ⊗ S.repr)ᘁ ≫
      (U ⊗ S.repr) ◁ (rightDualTensorIso U S.repr).hom =
      η_ (U ⊗ S.repr) (S.reprᘁ ⊗ Uᘁ) :=
    coevaluation_comp_whiskerLeft_rightDualTensorIso_hom U S.repr
  have hexch1 : (b.β (U ⊗ S.repr)).hom ▷ (U ⊗ S.repr)ᘁ ⊗≫
        (U ⊗ S.repr) ◁ A ◁ (rightDualTensorIso U S.repr).hom =
      𝟙 _ ⊗≫ (A ⊗ U ⊗ S.repr) ◁ (rightDualTensorIso U S.repr).hom ⊗≫
        (b.β (U ⊗ S.repr)).hom ▷ (S.reprᘁ ⊗ Uᘁ) ⊗≫ 𝟙 _ := by
    calc _ = ((b.β (U ⊗ S.repr)).hom ▷ (U ⊗ S.repr)ᘁ ≫
              ((U ⊗ S.repr) ⊗ A) ◁ (rightDualTensorIso U S.repr).hom) ⊗≫ 𝟙 _ := by monoidal
      _ = ((A ⊗ U ⊗ S.repr) ◁ (rightDualTensorIso U S.repr).hom ≫
            (b.β (U ⊗ S.repr)).hom ▷ (S.reprᘁ ⊗ Uᘁ)) ⊗≫ 𝟙 _ := by rw [← whisker_exchange]
      _ = _ := by monoidal
  calc _ = 𝟙 _ ⊗≫ A ◁ η_ (U ⊗ S.repr) (U ⊗ S.repr)ᘁ ⊗≫
            ((b.β (U ⊗ S.repr)).hom ▷ (U ⊗ S.repr)ᘁ ⊗≫
              (U ⊗ S.repr) ◁ A ◁ (rightDualTensorIso U S.repr).hom) ⊗≫ 𝟙 _ := by
          simp only [Category.assoc]
          monoidal
    _ = 𝟙 _ ⊗≫ A ◁ (η_ (U ⊗ S.repr) (U ⊗ S.repr)ᘁ ≫
            (U ⊗ S.repr) ◁ (rightDualTensorIso U S.repr).hom) ⊗≫
          (b.β (U ⊗ S.repr)).hom ▷ (S.reprᘁ ⊗ Uᘁ) ⊗≫ 𝟙 _ := by
          rw [hexch1]
          monoidal
    _ = 𝟙 _ ⊗≫ A ◁ η_ U Uᘁ ⊗≫
          ((A ◁ U ◁ η_ S.repr S.reprᘁ ⊗≫ (b.β U).hom ▷ (S.repr ⊗ S.reprᘁ)) ▷ Uᘁ) ⊗≫
          (U ◁ (b.β S.repr).hom ▷ S.reprᘁ) ▷ Uᘁ ⊗≫ 𝟙 _ := by
          rw [hcoev, b.monoidal U S.repr]
          simp only [ExactPairing.tensor_coevaluation, comp_whiskerRight]
          monoidal
    _ = _ := by
          have hexch : A ◁ U ◁ η_ S.repr S.reprᘁ ⊗≫ (b.β U).hom ▷ (S.repr ⊗ S.reprᘁ) =
              𝟙 _ ⊗≫ (b.β U).hom ▷ 𝟙_ C ⊗≫ U ◁ A ◁ η_ S.repr S.reprᘁ ⊗≫ 𝟙 _ := by
            calc _ = 𝟙 _ ⊗≫ ((A ⊗ U) ◁ η_ S.repr S.reprᘁ ≫
                      (b.β U).hom ▷ (S.repr ⊗ S.reprᘁ)) := by monoidal
              _ = 𝟙 _ ⊗≫ ((b.β U).hom ▷ 𝟙_ C ≫
                    (U ⊗ A) ◁ η_ S.repr S.reprᘁ) := by rw [whisker_exchange]
              _ = _ := by monoidal
          rw [hexch]
          simp only [comp_whiskerRight, whiskerLeft_comp]
          monoidal

variable [LeftRigidCategory C]

private theorem induction_unitF_comp_map_counitF (X : C) :
    unitF (inductionHalfBraiding k X) ≫ inductionMap (counitF X) = 𝟙 (inductionObj X) := by
  refine inductionObj_map_hom_ext (F := 𝟭 C) fun S ↦ ?_
  simp only [Functor.id_map, Category.id_comp, Category.assoc, biproduct.map_π]
  rw [← inductionEndπ_repr k X S, unitF, inductionLift_comp_π_assoc]
  dsimp only [unitWedge]
  rw [inductionHalfBraiding_β_hom, Category.assoc, ← associator_naturality_middle,
    ← Category.assoc, ← tensorRightHomEquiv_naturality]
  dsimp only [counitF]
  rw [whiskerLeft_comp, ← Category.assoc,
    inductionβHom_comp_whiskerLeft_inductionEndπ k X S.repr (𝟙_ C),
    tensorRightHomEquiv_naturality, Equiv.apply_symm_apply]
  have hunit : (λ_ S.reprᘁ).inv =
      ((ρ_ S.repr).hom)ᘁ ≫
        (@rightDualTensorIso C _ _ S.repr (𝟙_ C) _ (RightRigidCategory.rightDual (𝟙_ C)) _).hom ≫
        (rightDualUnitIso C).hom ▷ S.reprᘁ := by
    rw [rightDualUnitIso_hom]
    exact @rightDualTensorIso_rightUnitality C _ _ S.repr _ (RightRigidCategory.rightDual (𝟙_ C)) _
  have hcoh : (S.repr ⊗ 𝟙_ C) ◁ (α_ X (RightRigidCategory.rightDual (𝟙_ C)).rightDual S.reprᘁ).inv ≫
        (α_ (S.repr ⊗ 𝟙_ C) (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual) S.reprᘁ).inv ≫
        (α_ S.repr (𝟙_ C) (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual)).hom ▷ S.reprᘁ ≫
        (S.repr ◁ ((λ_ (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual)).hom ≫
          X ◁ (rightDualUnitIso C).hom ≫ (ρ_ X).hom)) ▷ S.reprᘁ ≫
        (α_ S.repr X S.reprᘁ).hom =
      (S.repr ⊗ 𝟙_ C) ◁ X ◁ ((rightDualUnitIso C).hom ▷ S.reprᘁ) ≫
        (ρ_ S.repr).hom ▷ (X ⊗ 𝟙_ C ⊗ S.reprᘁ) ≫
        S.repr ◁ X ◁ (λ_ S.reprᘁ).hom := by
    simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    monoidal
  have hdual :
      (@rightDualTensorIso C _ _ S.repr (𝟙_ C) _ (RightRigidCategory.rightDual (𝟙_ C)) _).hom ≫
        (rightDualUnitIso C).hom ▷ S.reprᘁ =
      ((ρ_ S.repr).inv)ᘁ ≫ (λ_ S.reprᘁ).inv := by
    rw [hunit, ← Category.assoc, ← comp_rightAdjointMate, Iso.hom_inv_id, rightAdjointMate_id,
      Category.id_comp]
  have hcancel :
      ((ρ_ S.repr).hom)ᘁ ≫ ((ρ_ S.repr).inv)ᘁ ≫ (λ_ S.reprᘁ).inv = (λ_ S.reprᘁ).inv := by
    rw [← Category.assoc, ← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id,
      Category.id_comp]
  simp only [Category.assoc]
  rw [hcoh, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp, hdual,
    whisker_exchange_assoc (ρ_ S.repr).hom,
    inductionEndπ_dinatural_assoc k X (ρ_ S.repr).hom,
    ← whiskerLeft_comp_assoc, ← whiskerLeft_comp, ← whiskerLeft_comp, hcancel,
    ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id, whiskerLeft_id, Category.comp_id]

/-! ### Public structure and adjunction API -/

variable (C)

/-- The induction functor `Center.induction k C` is additive. -/
instance instAdditiveInduction : (induction k C).Additive where
  map_add {X Y} f g := by
    refine Center.ext _ _ ?_
    -- Re-express the underlying morphism equality at `inductionObj X ⟶ inductionObj Y`.
    change inductionMap (f + g) = inductionMap f + inductionMap g
    refine biproduct.hom_ext _ _ fun S ↦ ?_
    simp [Preadditive.add_comp, MonoidalPreadditive.whiskerLeft_add,
      MonoidalPreadditive.add_whiskerRight]

/-- The induction functor `Center.induction k C` is `k`-linear. -/
instance instLinearInduction : (induction k C).Linear k where
  map_smul {X Y} f r := by
    refine Center.ext _ _ ?_
    -- Re-express the underlying morphism equality at `inductionObj X ⟶ inductionObj Y`.
    change inductionMap (r • f) = r • inductionMap f
    refine biproduct.hom_ext _ _ fun S ↦ ?_
    simp [Linear.smul_comp, MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight]

/-- **Right adjunction for centre induction**: `Center.forget C ⊣ Center.induction k C`. This holds
for any rigid `k`-linear finite semisimple abelian monoidal category over an algebraically closed
field with finitely many simple classes and finite-dimensional Hom spaces, without assuming
simplicity of the tensor unit or a pivotal structure. -/
def forgetInductionAdjunction : forget C ⊣ induction k C :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app Z :=
            { f := unitF (A := (forget C).obj Z) Z.2
              comm U :=
                (congrArg (unitF (A := (forget C).obj Z) Z.2 ▷ U ≫ ·)
                  (inductionHalfBraiding_β_hom k ((forget C).obj Z) U)).trans
                  (unitF_comm k (A := (forget C).obj Z) Z.2 U) }
          naturality _ _ h := Center.ext _ _ (unitF_naturality h.f h.comm) }
      counit :=
        { app X := counitF X
          naturality _ _ f := counitF_naturality f }
      left_triangle :=
        NatTrans.ext (funext fun Z ↦
          (congrArg (unitF (A := (forget C).obj Z) Z.2 ≫ ·)
            (Category.id_comp (counitF ((forget C).obj Z)))).trans
            (unitF_comp_counitF (A := (forget C).obj Z) Z.2))
      right_triangle := by
        refine NatTrans.ext (funext fun X ↦ ?_)
        dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Functor.associator_inv_app, NatTrans.id_app, Functor.comp_obj, Functor.id_obj]
        rw [Category.id_comp]
        exact Center.ext _ _ (induction_unitF_comp_map_counitF k X) }

/-- `Center.induction k C` is a right adjoint (in particular, it preserves all limits that exist in
`C`). -/
instance instIsRightAdjointInduction : (induction k C).IsRightAdjoint :=
  (forgetInductionAdjunction k C).isRightAdjoint

/-- Component of the unit of `forgetInductionAdjunction` along the end projection
`inductionEndπ Z.1 Y`. -/
@[reassoc]
theorem forgetInductionAdjunction_unit_app_f_comp_endπ (Z : Center C) (Y : C) :
    ((forgetInductionAdjunction k C).unit.app Z).f ≫ inductionEndπ Z.1 Y =
      (ρ_ Z.1).inv ≫ Z.1 ◁ η_ Y Yᘁ ≫ (α_ Z.1 Y Yᘁ).inv ≫ (Z.2.β Y).hom ▷ Yᘁ ≫
        (α_ Y Z.1 Yᘁ).hom := by
  -- Unfold the unit component of `forgetInductionAdjunction` to `unitF Z.2`.
  change unitF Z.2 ≫ inductionEndπ Z.1 Y = _
  simpa [unitWedge, tensorRightHomEquiv] using unitF_comp_endπ Z.2 Y

/-- Component of the unit of `forgetInductionAdjunction` on the `S`-summand of
`inductionObj Z.1`. -/
@[reassoc (attr := simp)]
theorem forgetInductionAdjunction_unit_app_f_comp_π (Z : Center C) (S : SimpleClasses C) :
    ((forgetInductionAdjunction k C).unit.app Z).f ≫
        biproduct.π (inductionSummand Z.1) S =
      (ρ_ Z.1).inv ≫ Z.1 ◁ η_ S.repr S.reprᘁ ≫ (α_ Z.1 S.repr S.reprᘁ).inv ≫
        (Z.2.β S.repr).hom ▷ S.reprᘁ ≫ (α_ S.repr Z.1 S.reprᘁ).hom := by
  rw [← inductionEndπ_repr k Z.1 S, forgetInductionAdjunction_unit_app_f_comp_endπ]

/-- Explicit formula for the counit of `forgetInductionAdjunction` at `X`. -/
@[reassoc, simp]
theorem forgetInductionAdjunction_counit_app (X : C) :
    (forgetInductionAdjunction k C).counit.app X =
      inductionEndπ X (𝟙_ C) ≫
        (λ_ (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual)).hom ≫
        X ◁ (rightDualUnitIso C).hom ≫
        (ρ_ X).hom :=
  (rfl)

end Fusion

end CategoryTheory.Center
