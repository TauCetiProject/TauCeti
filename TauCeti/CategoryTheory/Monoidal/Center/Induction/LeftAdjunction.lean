/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import TauCeti.CategoryTheory.Monoidal.Center.Induction.Adjunction
public import TauCeti.CategoryTheory.Monoidal.Center.Induction.Coend
public import TauCeti.CategoryTheory.Semisimple.Rigid

/-!
# The left adjunction for induction into the Drinfeld centre

Let `C` be a rigid, `k`-linear, finite semisimple abelian monoidal category over an algebraically
closed field `k`, with simple tensor unit, finitely many isomorphism classes of simple objects, and
finite-dimensional morphism spaces. Dual to the right adjunction
`forgetInductionAdjunction k C : Center.forget C ⊣ Center.induction k C` in
`TauCeti.CategoryTheory.Monoidal.Center.Induction.Adjunction`, this file constructs the left
adjunction `inductionForgetAdjunction k C : Center.induction k C ⊣ Center.forget C`, so that
`Center.induction k C` is two-sided adjoint to `Center.forget C`, exact, and faithful.

No pivotal structure or characteristic-zero assumption is used. To pin the normalization of the
averaging composite `Z ⟶ (induction k C).obj Z.1 ⟶ Z` without reference to a pivotal structure:

* the unit `(inductionForgetAdjunction k C).unit.app X : X ⟶ inductionObj X` is the `𝟙_ C`-coend
  coprojection `inductionCoendι X (𝟙_ C)` precomposed with the unitors, so it splits
  `(forgetInductionAdjunction k C).counit.app X`
  (`CategoryTheory.Center.inductionForgetAdjunction_unit_comp_forgetInductionAdjunction_counit`);
* on the `S`-summand `S.repr ⊗ Z.1 ⊗ S.reprᘁ`, the counit
  `((inductionForgetAdjunction k C).counit.app Z).f` moves `S.repr` past `Z.1` via
  `(Z.2.β S.repr).inv` and contracts `S.repr ⊗ S.reprᘁ` with the evaluation of the normalized
  swapped pairing `TauCeti.simpleSwapExactPairing S.repr`.

## Main declarations

* `CategoryTheory.Center.inductionForgetAdjunction`: the left adjunction
  `Center.induction k C ⊣ Center.forget C`;
* `CategoryTheory.Center.instIsLeftAdjointInduction`: `Center.induction k C` is a left adjoint
  (hence preserves all colimits, and together with `instIsRightAdjointInduction` is exact);
* `CategoryTheory.Center.inductionForgetAdjunction_unit_app` and
  `CategoryTheory.Center.ι_comp_inductionForgetAdjunction_counit_app_f`: explicit formulas for the
  unit and counit;
* `CategoryTheory.Center.inductionForgetAdjunction_unit_comp_forgetInductionAdjunction_counit`,
  `CategoryTheory.Center.instIsSplitMonoInductionForgetAdjunctionUnit`,
  `CategoryTheory.Center.instIsSplitEpiForgetInductionAdjunctionCounit`, and
  `CategoryTheory.Center.instFaithfulInduction`: splitting of the unit against the counit of
  `forgetInductionAdjunction`, and faithfulness of `Center.induction k C`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §§2, 8
* M. Müger, *From subfactors to categories and topology II: The quantum double of tensor
  categories and subfactors*, J. Pure Appl. Algebra **180** (2003), 159–219
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13, 9.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory ExactPairing Module TauCeti

universe w v u

namespace CategoryTheory.Center

attribute [local instance] Abelian.hasFiniteBiproducts

section SwapPairing

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [RigidCategory C] [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

/-- Evaluation `X ⊗ Xᘁ ⟶ 𝟙_ C` of the normalized swapped pairing `simpleSwapExactPairing X`. -/
private abbrev swapEval (X : C) [Simple X] : X ⊗ Xᘁ ⟶ 𝟙_ C :=
  @ExactPairing.evaluation C _ _ Xᘁ X (simpleSwapExactPairing X)

/-- Coevaluation `𝟙_ C ⟶ Xᘁ ⊗ X` of the normalized swapped pairing `simpleSwapExactPairing X`. -/
private abbrev swapCoeval (X : C) [Simple X] : 𝟙_ C ⟶ Xᘁ ⊗ X :=
  @ExactPairing.coevaluation C _ _ Xᘁ X (simpleSwapExactPairing X)

omit [Abelian C] [MonoidalPreadditive C] [RigidCategory C] [IsFiniteSemisimpleCategory C]
  [Simple (𝟙_ C)] in
@[reassoc]
private theorem rightDualUnitIso_inv_whiskerRight_evaluation [RightRigidCategory C] :
    (rightDualUnitIso C).inv ▷ 𝟙_ C ≫
      @ExactPairing.evaluation C _ _ (𝟙_ C) _ (RightRigidCategory.rightDual (𝟙_ C)).exact =
    (ρ_ (𝟙_ C)).hom := by
  rw [rightDualUnitIso_inv, ExactPairing.rightDualIso_inv_whiskerRight_evaluation,
    TauCeti.ExactPairing.unit_evaluation]

omit [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C] in
/-- Canonical isomorphism `S₀.reprᘁ ≅ (RightRigidCategory.rightDual (𝟙_ C)).rightDual` for
`S₀ = SimpleClasses.classOf (𝟙_ C)`, using the right dual assigned to `𝟙_ C` by
`RightRigidCategory` rather than `hasRightDualUnit`. -/
private def classOfUnitRightDualIso :
    (SimpleClasses.classOf (𝟙_ C)).reprᘁ ≅
      (RightRigidCategory.rightDual (𝟙_ C)).rightDual where
  hom := @rightAdjointMate C _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)) _
    (SimpleClasses.classOfReprIso (𝟙_ C)).inv
  inv := @rightAdjointMate C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C))
    (SimpleClasses.classOfReprIso (𝟙_ C)).hom
  hom_inv_id := by
    rw [← @comp_rightAdjointMate, Iso.hom_inv_id, @rightAdjointMate_id]
  inv_hom_id := by
    rw [← @comp_rightAdjointMate, Iso.inv_hom_id, @rightAdjointMate_id]

/-- On the representative `S₀.repr` of `SimpleClasses.classOf (𝟙_ C)`, the swapped evaluation
`swapEval S₀.repr` agrees with the unit pairing transported along `classOfReprIso (𝟙_ C)`. -/
private theorem swapEval_classOf_unit :
    let S₀ := SimpleClasses.classOf (𝟙_ C)
    swapEval S₀.repr =
      S₀.repr ◁ ((classOfUnitRightDualIso (C := C)).hom ≫ (rightDualUnitIso C).hom) ≫
        (SimpleClasses.classOfReprIso (𝟙_ C)).hom ▷ 𝟙_ C ≫ (ρ_ (𝟙_ C)).hom := by
  intro S₀
  let e₀ : S₀.repr ≅ 𝟙_ C := SimpleClasses.classOfReprIso (𝟙_ C)
  let i : S₀.reprᘁ ≅ 𝟙_ C := classOfUnitRightDualIso (C := C) ≪≫ rightDualUnitIso C
  let p₁ : ExactPairing S₀.reprᘁ S₀.repr := simpleSwapExactPairing S₀.repr
  let p₂ : ExactPairing S₀.reprᘁ S₀.repr :=
    @exactPairingCongr C _ _ S₀.reprᘁ (𝟙_ C) S₀.repr (𝟙_ C) exactPairingUnit i e₀
  have hp₂_eval : @ExactPairing.evaluation C _ _ S₀.reprᘁ S₀.repr p₂ =
      S₀.repr ◁ ((classOfUnitRightDualIso (C := C)).hom ≫ (rightDualUnitIso C).hom) ≫
        e₀.hom ▷ 𝟙_ C ≫ (ρ_ (𝟙_ C)).hom :=
    @exactPairingCongr_evaluation C _ _ S₀.reprᘁ (𝟙_ C) S₀.repr (𝟙_ C) exactPairingUnit i e₀
  have hp₂_coeval_iso : IsIso (@ExactPairing.coevaluation C _ _ S₀.reprᘁ S₀.repr p₂) := by
    rw [@exactPairingCongr_coevaluation C _ _ S₀.reprᘁ (𝟙_ C) S₀.repr (𝟙_ C) exactPairingUnit i e₀,
      TauCeti.ExactPairing.unit_coevaluation]
    infer_instance
  have hp₂_comp : @ExactPairing.coevaluation C _ _ S₀.reprᘁ S₀.repr p₂ ≫ ε_ S₀.repr S₀.reprᘁ =
      𝟙 (𝟙_ C) := by
    rw [@exactPairingCongr_coevaluation C _ _ S₀.reprᘁ (𝟙_ C) S₀.repr (𝟙_ C) exactPairingUnit i e₀]
    dsimp only [i, Iso.trans_inv, classOfUnitRightDualIso]
    simp only [comp_whiskerRight, Category.assoc]
    rw [@rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
      Iso.inv_hom_id, whiskerLeft_id, Category.id_comp,
      rightDualUnitIso_inv_whiskerRight_evaluation, TauCeti.ExactPairing.unit_coevaluation,
      Iso.inv_hom_id]
  have hε_eq : ε_ S₀.repr S₀.reprᘁ = inv (@ExactPairing.coevaluation C _ _ S₀.reprᘁ S₀.repr p₂) :=
    IsIso.eq_inv_of_hom_inv_id hp₂_comp
  have hε_iso : IsIso (ε_ S₀.repr S₀.reprᘁ) := by
    rw [hε_eq]
    infer_instance
  have hcoeval : swapCoeval S₀.repr = @ExactPairing.coevaluation C _ _ S₀.reprᘁ S₀.repr p₂ := by
    rw [← cancel_mono (ε_ S₀.repr S₀.reprᘁ), simpleSwapExactPairing_coevaluation_comp_evaluation,
      hp₂_comp]
  have hwhisker : (S₀.reprᘁ : C) ◁ (rightDualIso p₁ p₂).hom = 𝟙 (S₀.reprᘁ ⊗ S₀.repr) := by
    rw [← cancel_epi (@ExactPairing.coevaluation C _ _ S₀.reprᘁ S₀.repr p₂), Category.comp_id,
      ← hcoeval, ExactPairing.rightDualIso_hom,
      @ExactPairing.coevaluation_comp_rightMate C _ _ _ _ _ _ p₂ p₁ (𝟙 S₀.reprᘁ),
      id_whiskerRight, Category.comp_id, hcoeval]
  have hiso_hom : (rightDualIso p₁ p₂).hom = 𝟙 S₀.repr := by
    calc (rightDualIso p₁ p₂).hom
        = (λ_ S₀.repr).inv ≫ i.inv ▷ S₀.repr ≫ (S₀.reprᘁ : C) ◁ (rightDualIso p₁ p₂).hom ≫
            i.hom ▷ S₀.repr ≫ (λ_ S₀.repr).hom := by
          symm
          rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, i.inv_hom_id, id_whiskerRight,
            Category.id_comp, leftUnitor_naturality, Iso.inv_hom_id_assoc]
      _ = 𝟙 S₀.repr := by
          rw [hwhisker, Category.id_comp, ← comp_whiskerRight_assoc, i.inv_hom_id, id_whiskerRight,
            Category.id_comp, Iso.inv_hom_id]
  dsimp only [swapEval]
  rw [← ExactPairing.rightDualIso_hom_whiskerRight_evaluation p₁ p₂, hiso_hom, id_whiskerRight,
    Category.id_comp, hp₂_eval]

end SwapPairing

section UnitCounit

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

/-- The `S`-summand component `S.repr ⊗ A ⊗ S.reprᘁ ⟶ A` of the counit of
`inductionForgetAdjunction`. -/
private def counitLFComponent {A : C} (b : HalfBraiding A) (S : SimpleClasses C) :
    S.repr ⊗ A ⊗ S.reprᘁ ⟶ A :=
  (α_ S.repr A S.reprᘁ).inv ≫
    (b.β S.repr).inv ▷ S.reprᘁ ≫
    (α_ A S.repr S.reprᘁ).hom ≫
    A ◁ swapEval S.repr ≫
    (ρ_ A).hom

omit [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C] in
/-- Naturality and monoidality of `b` on `swapEval S.repr` rewrite `counitLFComponent b S` using the
forward half-braiding at `S.reprᘁ`. -/
private theorem counitLFComponent_eq_forward {A : C} (b : HalfBraiding A) (S : SimpleClasses C) :
    counitLFComponent b S =
      S.repr ◁ (b.β S.reprᘁ).hom ≫
        (α_ S.repr S.reprᘁ A).inv ≫
        swapEval S.repr ▷ A ≫
        (λ_ A).hom := by
  have h := congrArg (· ≫ (λ_ A).hom) (b.naturality (swapEval S.repr))
  rw [b.β_tensorUnit_hom, b.monoidal S.repr S.reprᘁ] at h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  dsimp only [counitLFComponent]
  rw [h, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id_assoc]

variable [Fintype (SimpleClasses C)]

/-- Component `X ⟶ inductionObj X` of `(inductionForgetAdjunction k C).unit.app X`. -/
private def unitLF (X : C) : X ⟶ inductionObj X :=
  (ρ_ X).inv ≫
    X ◁ (rightDualUnitIso C).inv ≫
    (λ_ (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual)).inv ≫
    inductionCoendι X (𝟙_ C)

omit [Field k] [IsAlgClosed k] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
  [Simple (𝟙_ C)] in
private theorem unitLF_naturality {X X' : C} (f : X ⟶ X') :
    unitLF X ≫ inductionMap f = f ≫ unitLF X' := by
  dsimp only [unitLF]
  rw [Category.assoc, Category.assoc, Category.assoc, inductionCoendι_comp_inductionMap,
    ← leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

include k in
private theorem inductionCoendι_tensorUnit
    [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)] (X : C) :
    inductionCoendι X (𝟙_ C) =
      𝟙_ C ◁ X ◁ (classOfUnitRightDualIso (C := C)).inv ≫
        (SimpleClasses.classOfReprIso (𝟙_ C)).inv ▷
          (X ⊗ (SimpleClasses.classOf (𝟙_ C)).reprᘁ) ≫
        biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) := by
  let S₀ := SimpleClasses.classOf (𝟙_ C)
  have hdinat : (SimpleClasses.classOfReprIso (𝟙_ C)).inv ▷ (X ⊗ S₀.reprᘁ) ≫
      biproduct.ι (inductionSummand X) S₀ =
      𝟙_ C ◁ X ◁ (classOfUnitRightDualIso (C := C)).hom ≫ inductionCoendι X (𝟙_ C) := by
    rw [← inductionCoendι_repr k X S₀]
    exact inductionCoendι_dinatural k X (SimpleClasses.classOfReprIso (𝟙_ C)).inv
  rw [hdinat, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id,
    whiskerLeft_id, Category.id_comp]

include k in
private theorem unitLF_comp_counitF [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]
    (X : C) :
    unitLF X ≫
      (inductionEndπ X (𝟙_ C) ≫
        (λ_ (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual)).hom ≫
        X ◁ (rightDualUnitIso C).hom ≫
        (ρ_ X).hom) = 𝟙 X := by
  dsimp only [unitLF]
  simp only [Category.assoc]
  rw [inductionCoendι_comp_inductionEndπ_of_simple_assoc k X (𝟙_ C), Iso.inv_hom_id_assoc,
    ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]

/-- Underlying morphism `inductionObj A ⟶ A` of
`(inductionForgetAdjunction k C).counit.app ⟨A, b⟩`. -/
private def counitLF {A : C} (b : HalfBraiding A) : inductionObj A ⟶ A :=
  ∑ S : SimpleClasses C, biproduct.π (inductionSummand A) S ≫ counitLFComponent b S

omit [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C] in
@[reassoc]
private theorem ι_comp_counitLF {A : C} (b : HalfBraiding A) (S : SimpleClasses C) :
    biproduct.ι (inductionSummand A) S ≫ counitLF b = counitLFComponent b S := by
  classical
  dsimp only [counitLF]
  simp only [Preadditive.comp_sum, biproduct.ι_π_assoc]
  rw [Finset.sum_eq_single S]
  · simp
  · intro T _ hTS
    simp [Ne.symm hTS]
  · simp

omit [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C] in
private theorem counitLF_naturality {A A' : C} {b : HalfBraiding A} {b' : HalfBraiding A'}
    (f : A ⟶ A') (hf : ∀ U : C, f ▷ U ≫ (b'.β U).hom = (b.β U).hom ≫ U ◁ f) :
    inductionMap f ≫ counitLF b' = counitLF b ≫ f := by
  refine biproduct.hom_ext' _ _ fun S ↦ ?_
  rw [biproduct.ι_map_assoc, ι_comp_counitLF, ι_comp_counitLF_assoc]
  have hinv : S.repr ◁ f ≫ (b'.β S.repr).inv = (b.β S.repr).inv ≫ f ▷ S.repr := by
    rw [← cancel_epi (b.β S.repr).hom, Iso.hom_inv_id_assoc, ← reassoc_of% (hf S.repr),
      Iso.hom_inv_id, Category.comp_id]
  dsimp only [counitLFComponent]
  calc _ = 𝟙 _ ⊗≫ (S.repr ◁ f ≫ (b'.β S.repr).inv) ▷ (S.reprᘁ : C) ⊗≫
            A' ◁ swapEval S.repr ⊗≫ 𝟙 A' := by
          monoidal
    _ = 𝟙 _ ⊗≫ (b.β S.repr).inv ▷ (S.reprᘁ : C) ⊗≫
          (f ▷ (S.repr ⊗ S.reprᘁ) ≫ A' ◁ swapEval S.repr) ⊗≫ 𝟙 _ := by
          rw [hinv, comp_whiskerRight]
          monoidal
    _ = _ := by
          rw [← whisker_exchange]
          simp only [Category.assoc]
          monoidal

include k in
/-- Right triangle identity: `unitLF A ≫ counitLF b = 𝟙 A`. -/
private theorem unitLF_comp_counitLF [∀ S : SimpleClasses C, FiniteDimensional k (S.repr ⟶ S.repr)]
    {A : C} (b : HalfBraiding A) :
    unitLF A ≫ counitLF b = 𝟙 A := by
  let e₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  have hβ : e₀.inv ▷ A ≫ (b.β (SimpleClasses.classOf (𝟙_ C)).repr).inv =
      (λ_ A).hom ≫ (ρ_ A).inv ≫ A ◁ e₀.inv := by
    rw [← cancel_epi (b.β (𝟙_ C)).hom, ← b.naturality_assoc e₀.inv, Iso.hom_inv_id,
      Category.comp_id, b.β_tensorUnit_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id_assoc]
  let S₀ := SimpleClasses.classOf (𝟙_ C)
  let j : S₀.reprᘁ ≅ 𝟙_ C := classOfUnitRightDualIso (C := C) ≪≫ rightDualUnitIso C
  dsimp only [unitLF]
  simp only [Category.assoc]
  rw [inductionCoendι_tensorUnit k A, Category.assoc, Category.assoc, ι_comp_counitLF]
  dsimp only [counitLFComponent]
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc, hβ, swapEval_classOf_unit]
  calc _ = 𝟙 _ ⊗≫ A ◁ j.inv ⊗≫
            A ◁ (e₀.inv ▷ (S₀.reprᘁ : C) ≫ S₀.repr ◁ j.hom) ⊗≫
            A ◁ e₀.hom ⊗≫ 𝟙 A := by
          dsimp only [j, Iso.trans_hom, Iso.trans_inv]
          simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
          monoidal
    _ = 𝟙 _ ⊗≫ A ◁ (j.inv ≫ j.hom) ⊗≫ A ◁ (e₀.inv ≫ e₀.hom) ⊗≫ 𝟙 A := by
          rw [← whisker_exchange]
          dsimp only [j, Iso.trans_hom, Iso.trans_inv]
          simp only [whiskerLeft_comp]
          monoidal
    _ = 𝟙 A := by
          rw [j.inv_hom_id, e₀.inv_hom_id]
          monoidal

end UnitCounit

section Completeness

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

/-- Linear equivalence `(S.repr ⟶ U ⊗ T.repr) ≃ₗ[k] (T.reprᘁ ⟶ S.reprᘁ ⊗ U)` built from the
swapped exact pairings on `T.repr` and `S.repr`. -/
private def counitDualEquiv (U : C) (S T : SimpleClasses C) :
    (S.repr ⟶ U ⊗ T.repr) ≃ₗ[k] (T.reprᘁ ⟶ S.reprᘁ ⊗ U) :=
  (@tensorRightHomLinearEquiv C _ _ _ _ k _ _ _ S.repr T.reprᘁ T.repr U
    (simpleSwapExactPairing T.repr)).symm.trans
    (@tensorLeftHomLinearEquiv C _ _ _ _ k _ _ _ T.reprᘁ S.reprᘁ S.repr U
      (simpleSwapExactPairing S.repr))

omit [IsAlgClosed k] in
private theorem tensorLeftHomEquiv_counitTerm (U : C) (S T : SimpleClasses C)
    (f : S.repr ⟶ U ⊗ T.repr) (h : S.reprᘁ ⊗ U ⟶ T.reprᘁ) :
    @tensorLeftHomEquiv C _ _ (S.reprᘁ ⊗ U) S.reprᘁ S.repr U (simpleSwapExactPairing S.repr)
      ((f ⊗ₘ h) ≫ (α_ U T.repr T.reprᘁ).hom ≫ U ◁ swapEval T.repr ≫ (ρ_ U).hom) =
      h ≫ counitDualEquiv k U S T f := by
  let φ : S.repr ⊗ T.reprᘁ ⟶ U :=
    (@tensorRightHomEquiv C _ _ S.repr T.reprᘁ T.repr U (simpleSwapExactPairing T.repr)).symm f
  have hφ : (f ⊗ₘ h) ≫ (α_ U T.repr T.reprᘁ).hom ≫ U ◁ swapEval T.repr ≫ (ρ_ U).hom =
      S.repr ◁ h ≫ φ := by
    rw [tensorHom_def', Category.assoc]
    rfl
  rw [hφ]
  simp only [counitDualEquiv, LinearEquiv.trans_apply, tensorRightHomLinearEquiv_symm_apply,
    tensorLeftHomLinearEquiv_apply, tensorLeftHomEquiv, Equiv.coe_fn_mk]
  change _ = h ≫ (λ_ T.reprᘁ).inv ≫ swapCoeval S.repr ▷ (T.reprᘁ : C) ≫
    (α_ S.reprᘁ S.repr T.reprᘁ).hom ≫ (S.reprᘁ : C) ◁ φ
  calc _ = 𝟙 _ ⊗≫ (swapCoeval S.repr ▷ (S.reprᘁ ⊗ U) ≫ ((S.reprᘁ : C) ⊗ S.repr) ◁ h) ⊗≫
            (S.reprᘁ : C) ◁ φ := by
          simp only [whiskerLeft_comp]; monoidal
    _ = _ := by
          rw [← whisker_exchange]; monoidal

/-- `counitDualEquiv k U S T` and `inductionMate k U` preserve the composition pairing of simple
morphisms. -/
private theorem homPairing_counitDualEquiv_inductionMate
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] (U : C) (S T : SimpleClasses C)
    (f : S.repr ⟶ U ⊗ T.repr) (g : U ⊗ T.repr ⟶ S.repr) :
    homPairing k T.reprᘁ (S.reprᘁ ⊗ U) (counitDualEquiv k U S T f) (inductionMate k U g) =
      homPairing k S.repr (U ⊗ T.repr) f g := by
  set c₁ := homPairing k T.reprᘁ (S.reprᘁ ⊗ U) (counitDualEquiv k U S T f) (inductionMate k U g)
  set c₂ := homPairing k S.repr (U ⊗ T.repr) f g
  refine smul_left_injective k (CategoryTheory.id_ne_zero (𝟙_ C)) ?_
  dsimp only
  have lhs : swapCoeval T.repr ≫
      (counitDualEquiv k U S T f ≫ inductionMate k U g) ▷ T.repr ≫ ε_ T.repr T.reprᘁ =
      c₁ • 𝟙 (𝟙_ C) := by
    rw [← homPairing_smul_id (k := k) (counitDualEquiv k U S T f) (inductionMate k U g),
      MonoidalLinear.smul_whiskerRight, id_whiskerRight, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, simpleSwapExactPairing_coevaluation_comp_evaluation]
  rw [← lhs, comp_whiskerRight_assoc, inductionMate_whiskerRight_evaluation]
  calc _ = 𝟙 _ ⊗≫ (𝟙_ C ◁ swapCoeval T.repr ≫ swapCoeval S.repr ▷ (T.reprᘁ ⊗ T.repr)) ⊗≫
            (S.reprᘁ : C) ◁ f ▷ (T.reprᘁ ⊗ T.repr) ⊗≫
            (S.reprᘁ : C) ◁ U ◁ swapEval T.repr ▷ T.repr ⊗≫
            (S.reprᘁ : C) ◁ g ⊗≫ ε_ S.repr S.reprᘁ := by
          simp only [counitDualEquiv, LinearEquiv.trans_apply, tensorRightHomLinearEquiv_symm_apply,
            tensorLeftHomLinearEquiv_apply, tensorLeftHomEquiv, tensorRightHomEquiv,
            Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, whiskerLeft_comp, comp_whiskerRight,
            Category.assoc]
          monoidal
    _ = 𝟙 _ ⊗≫ swapCoeval S.repr ⊗≫
          (S.reprᘁ : C) ◁ (S.repr ◁ swapCoeval T.repr ≫ f ▷ (T.reprᘁ ⊗ T.repr)) ⊗≫
          (S.reprᘁ : C) ◁ U ◁ swapEval T.repr ▷ T.repr ⊗≫
          (S.reprᘁ : C) ◁ g ⊗≫ ε_ S.repr S.reprᘁ := by
          rw [whisker_exchange]
          simp only [whiskerLeft_comp]
          monoidal
    _ = 𝟙 _ ⊗≫ swapCoeval S.repr ⊗≫ (S.reprᘁ : C) ◁ f ⊗≫
          (S.reprᘁ : C) ◁ U ◁ (T.repr ◁ swapCoeval T.repr ⊗≫ swapEval T.repr ▷ T.repr) ⊗≫
          (S.reprᘁ : C) ◁ g ⊗≫ ε_ S.repr S.reprᘁ := by
          rw [whisker_exchange]; monoidal
    _ = swapCoeval S.repr ≫ (S.reprᘁ : C) ◁ (f ≫ g) ≫ ε_ S.repr S.reprᘁ := by
          rw [@ExactPairing.coevaluation_evaluation'' C _ _ T.reprᘁ T.repr
            (simpleSwapExactPairing T.repr)]
          simp only [whiskerLeft_comp]
          monoidal
    _ = c₂ • 𝟙 (𝟙_ C) := by
          rw [← homPairing_smul_id (k := k) f g, MonoidalLinear.whiskerLeft_smul, whiskerLeft_id,
            Linear.smul_comp, Linear.comp_smul, Category.id_comp,
            simpleSwapExactPairing_coevaluation_comp_evaluation]

private theorem map_counitDualEquiv_homDual [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (U : C) (S T : SimpleClasses C) {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι k (S.repr ⟶ U ⊗ T.repr)) (i : ι) :
    (b.map (counitDualEquiv k U S T)).homDual i = inductionMate k U (b.homDual i) := by
  symm
  rw [Basis.eq_homDual_iff]
  intro j
  rw [Basis.map_apply, ← homPairing_smul_id (k := k),
    homPairing_counitDualEquiv_inductionMate k U S T, b.homPairing_homDual, b.repr_self,
    Finsupp.single_apply]
  split_ifs <;> simp

/-- Completeness identity underlying half-braiding compatibility of `counitLF`. -/
private theorem sum_counitTerm_eq [Fintype (SimpleClasses C)]
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] (U : C) (S : SimpleClasses C) :
    (∑ T : SimpleClasses C, ∑ i,
      (Module.finBasis k (S.repr ⟶ U ⊗ T.repr) i ⊗ₘ
        inductionMate k U ((Module.finBasis k (S.repr ⟶ U ⊗ T.repr)).homDual i)) ≫
        (α_ U T.repr T.reprᘁ).hom ≫ U ◁ swapEval T.repr ≫ (ρ_ U).hom) =
      (α_ S.repr S.reprᘁ U).inv ≫ swapEval S.repr ▷ U ≫ (λ_ U).hom := by
  apply (@tensorLeftHomEquiv C _ _ (S.reprᘁ ⊗ U) S.reprᘁ S.repr U
    (simpleSwapExactPairing S.repr)).injective
  have hrhs : @tensorLeftHomEquiv C _ _ (S.reprᘁ ⊗ U) S.reprᘁ S.repr U
      (simpleSwapExactPairing S.repr)
      ((α_ S.repr S.reprᘁ U).inv ≫ swapEval S.repr ▷ U ≫ (λ_ U).hom) = 𝟙 (S.reprᘁ ⊗ U) := by
    let eqv := @tensorLeftHomEquiv C _ _ (S.reprᘁ ⊗ U) S.reprᘁ S.repr U
      (simpleSwapExactPairing S.repr)
    have hsymm : eqv.symm (𝟙 (S.reprᘁ ⊗ U)) =
        (α_ S.repr S.reprᘁ U).inv ≫ swapEval S.repr ▷ U ≫ (λ_ U).hom := by
      simp [eqv, tensorLeftHomEquiv]
    rw [← hsymm, eqv.apply_symm_apply]
  rw [hrhs, ← @tensorLeftHomLinearEquiv_apply C _ _ _ _ k _ _ _ (S.reprᘁ ⊗ U) S.reprᘁ S.repr U
    (simpleSwapExactPairing S.repr)]
  simp only [map_sum, tensorLeftHomLinearEquiv_apply, tensorLeftHomEquiv_counitTerm k]
  let c (T : SimpleClasses C) :=
    (Module.finBasis k (S.repr ⟶ U ⊗ T.repr)).map (counitDualEquiv k U S T)
  have h1 : (∑ T : SimpleClasses C, ∑ i,
      inductionMate k U ((Module.finBasis k (S.repr ⟶ U ⊗ T.repr)).homDual i) ≫
        counitDualEquiv k U S T (Module.finBasis k (S.repr ⟶ U ⊗ T.repr) i)) =
      ∑ T : SimpleClasses C, ∑ i, (c T).homDual i ≫ c T i := by
    refine Finset.sum_congr rfl fun T _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← map_counitDualEquiv_homDual k U S T]
    rfl
  rw [h1, ← Equiv.sum_comp SimpleClasses.dual_involutive.toPerm]
  let e (R : SimpleClasses C) : R.repr ≅ R.dual.reprᘁ :=
    (nonempty_iso_rightDual_rightDual R.repr).some ≪≫ (SimpleClasses.dualReprIso R).rightAdjointMate
  let a (R : SimpleClasses C) :=
    (c R.dual).map (Linear.homCongr k (e R).symm (Iso.refl ((S.reprᘁ : C) ⊗ U)))
  have ha_dual (R : SimpleClasses C)
      (i : Fin (Module.finrank k (S.repr ⟶ U ⊗ R.dual.repr))) :
      (a R).homDual i = (c R.dual).homDual i ≫ (e R).inv := by
    symm
    rw [Basis.eq_homDual_iff]
    intro j
    simp only [a, Basis.map_apply, Linear.homCongr_apply, Iso.symm_inv, Iso.refl_hom,
      Category.comp_id, Category.assoc]
    rw [← Category.assoc (c R.dual j), (c R.dual).apply_comp_homDual]
    split_ifs <;> simp
  calc (∑ R : SimpleClasses C, ∑ i, (c R.dual).homDual i ≫ c R.dual i)
      = ∑ R : SimpleClasses C, ∑ i, (a R).homDual i ≫ a R i := by
          refine Finset.sum_congr rfl fun R _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
          simp [ha_dual R i, a, Linear.homCongr_apply]
    _ = 𝟙 ((S.reprᘁ : C) ⊗ U) := sum_sum_homDual_comp_eq_id ((S.reprᘁ : C) ⊗ U) a

end Completeness

section LeftAdjunction

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

omit [IsAlgClosed k] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
/-- Each `(g, f)`-term of `inductionβComponent` composed with `U ◁ counitLFComponent b T` braids
`A` to the right via `(b.β (S.reprᘁ ⊗ U)).hom` and contracts `T.repr ⊗ T.reprᘁ`. -/
private theorem inductionTerm_comp_whiskerLeft_counitLFComponent {A : C} (b : HalfBraiding A)
    (U : C) (S T : SimpleClasses C) (g : U ⊗ T.repr ⟶ S.repr) (f : S.repr ⟶ U ⊗ T.repr) :
    inductionTerm k A g f ≫ U ◁ counitLFComponent b T =
      (α_ S.repr (A ⊗ S.reprᘁ) U).hom ≫
        S.repr ◁ (α_ A S.reprᘁ U).hom ≫
        S.repr ◁ (b.β (S.reprᘁ ⊗ U)).hom ≫
        (α_ S.repr (S.reprᘁ ⊗ U) A).inv ≫
        (((f ⊗ₘ inductionMate k U g) ≫
          (α_ U T.repr T.reprᘁ).hom ≫ U ◁ swapEval T.repr ≫ (ρ_ U).hom) ▷ A) := by
  rw [inductionTerm_apply, counitLFComponent_eq_forward]
  have hnat : A ◁ inductionMate k U g ≫ (b.β T.reprᘁ).hom =
      (b.β (S.reprᘁ ⊗ U)).hom ≫ inductionMate k U g ▷ A :=
    b.naturality (inductionMate k U g)
  calc _ = 𝟙 _ ⊗≫ f ▷ (A ⊗ S.reprᘁ ⊗ U) ⊗≫
            (U ⊗ T.repr) ◁ (A ◁ inductionMate k U g ≫ (b.β T.reprᘁ).hom) ⊗≫
            U ◁ swapEval T.repr ▷ A ⊗≫ 𝟙 _ := by
          simp only [whiskerLeft_comp]
          monoidal
    _ = 𝟙 _ ⊗≫ (f ▷ (A ⊗ S.reprᘁ ⊗ U) ≫ (U ⊗ T.repr) ◁ (b.β (S.reprᘁ ⊗ U)).hom) ⊗≫
          (U ⊗ T.repr) ◁ inductionMate k U g ▷ A ⊗≫ U ◁ swapEval T.repr ▷ A ⊗≫ 𝟙 _ := by
          rw [hnat, whiskerLeft_comp]
          monoidal
    _ = _ := by
          rw [← whisker_exchange, tensorHom_def]
          simp only [comp_whiskerRight, Category.assoc]
          monoidal

/-- Off-diagonal components `inductionβComponent k X S.reprᘁ S₀ T` at `S₀ = classOf (𝟙_ C)` vanish
when `T ≠ S`. -/
private theorem inductionβComponent_rightDual_classOf_unit_of_ne (X : C) {S T : SimpleClasses C}
    (h : T ≠ S) :
    inductionβComponent k X S.reprᘁ (SimpleClasses.classOf (𝟙_ C)) T = 0 := by
  let S₀ := SimpleClasses.classOf (𝟙_ C)
  let e₀ : 𝟙_ C ≅ S₀.repr := (SimpleClasses.classOfReprIso (𝟙_ C)).symm
  have : Subsingleton (S.repr ⟶ T.repr) := SimpleClasses.homOrthogonal_repr h.symm
  have hzero (f : S₀.repr ⟶ S.reprᘁ ⊗ T.repr) : f = 0 := by
    let eqv := @tensorLeftHomEquiv C _ _ (𝟙_ C) S.reprᘁ S.repr T.repr
      (simpleSwapExactPairing S.repr)
    have hf : eqv ((ρ_ S.repr).hom ≫ (ρ_ S.repr).inv ≫ eqv.symm (e₀.hom ≫ f)) = e₀.hom ≫ f := by
      rw [Iso.hom_inv_id_assoc, eqv.apply_symm_apply]
    rw [← Category.id_comp f, ← e₀.inv_hom_id, Category.assoc, ← hf,
      Subsingleton.elim ((ρ_ S.repr).inv ≫ eqv.symm (e₀.hom ≫ f)) 0, comp_zero]
    simp [eqv, tensorLeftHomEquiv]
  rw [inductionβComponent_eq k X S.reprᘁ S₀ T (Module.finBasis k _)]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [hzero (Module.finBasis k _ i), map_zero]

/-- Diagonal component `inductionβComponent k X S.reprᘁ S₀ S` at `S₀ = classOf (𝟙_ C)`. -/
private theorem inductionβComponent_rightDual_classOf_unit_self (X : C) (S : SimpleClasses C) :
    let S₀ := SimpleClasses.classOf (𝟙_ C)
    let e₀ : 𝟙_ C ≅ S₀.repr := (SimpleClasses.classOfReprIso (𝟙_ C)).symm
    inductionβComponent k X S.reprᘁ S₀ S =
      inductionTerm k X (ε_ S.repr S.reprᘁ ≫ e₀.hom) (e₀.inv ≫ swapCoeval S.repr) := by
  intro S₀ e₀
  let v : S₀.repr ⟶ S.reprᘁ ⊗ S.repr := e₀.inv ≫ swapCoeval S.repr
  let w : S.reprᘁ ⊗ S.repr ⟶ S₀.repr := ε_ S.repr S.reprᘁ ≫ e₀.hom
  have hvw : v ≫ w = 𝟙 S₀.repr := by
    dsimp only [v, w]
    rw [Category.assoc, ← Category.assoc (swapCoeval S.repr),
      simpleSwapExactPairing_coevaluation_comp_evaluation, Category.id_comp, Iso.inv_hom_id]
  have hv : v ≠ 0 := fun h ↦
    CategoryTheory.id_ne_zero S₀.repr (by rw [← hvw, h, zero_comp])
  have hspan : ⊤ ≤ Submodule.span k (Set.range fun _ : Fin 1 ↦ v) := by
    rintro f -
    let eqv := (Linear.homCongr k e₀.symm (Iso.refl (S.reprᘁ ⊗ S.repr))).trans
      ((@tensorLeftHomLinearEquiv C _ _ _ _ k _ _ _ (𝟙_ C) S.reprᘁ S.repr S.repr
        (simpleSwapExactPairing S.repr)).symm.trans
        (Linear.homCongr k (ρ_ S.repr) (Iso.refl S.repr)))
    obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k (eqv f)
    have hfv : eqv v = 𝟙 S.repr := by
      simp only [eqv, v, LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.symm_inv,
        Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc,
        tensorLeftHomLinearEquiv_symm_apply, tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]
      calc _ = 𝟙 _ ⊗≫ (S.repr ◁ swapCoeval S.repr ⊗≫ swapEval S.repr ▷ S.repr) ⊗≫ 𝟙 _ := by
              monoidal
        _ = 𝟙 S.repr := by
              rw [@ExactPairing.coevaluation_evaluation'' C _ _ S.reprᘁ S.repr
                (simpleSwapExactPairing S.repr)]
              monoidal
    rw [Set.range_const, Submodule.mem_span_singleton]
    refine ⟨c, eqv.injective ?_⟩
    rw [map_smul, hfv, hc]
  let b : Basis (Fin 1) k (S₀.repr ⟶ S.reprᘁ ⊗ S.repr) :=
    Basis.mk (linearIndependent_unique_iff.2 hv) hspan
  have hd : b.homDual 0 = w :=
    ((b.eq_homDual_iff _ 0).2 fun i ↦ by simp [b, Fin.fin_one_eq_zero i, hvw]).symm
  rw [inductionβComponent_eq k X S.reprᘁ S₀ S b, Fin.sum_univ_one, hd, Basis.mk_apply]

omit [IsAlgClosed k] [IsFiniteSemisimpleCategory C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
/-- Evaluating `inductionMate` on `ε_ S.repr S.reprᘁ ≫ (classOfReprIso (𝟙_ C)).inv` against the
dual-unit isomorphism collapses to `(λ_ S.reprᘁ).hom`. -/
private theorem inductionMate_evaluation_classOf_unit (S : SimpleClasses C) :
    ((rightDualUnitIso C).inv ≫ (classOfUnitRightDualIso (C := C)).inv) ▷ (S.reprᘁ : C) ≫
      inductionMate k S.reprᘁ
        (ε_ S.repr S.reprᘁ ≫ (SimpleClasses.classOfReprIso (𝟙_ C)).inv) =
      (λ_ S.reprᘁ).hom := by
  let S₀ := SimpleClasses.classOf (𝟙_ C)
  let e₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  let u : 𝟙_ C ⟶ S₀.reprᘁ :=
    (rightDualUnitIso C).inv ≫ (classOfUnitRightDualIso (C := C)).inv
  have hev : u ▷ S₀.repr ≫ ε_ S₀.repr S₀.reprᘁ = 𝟙_ C ◁ e₀.hom ≫ (ρ_ (𝟙_ C)).hom := by
    dsimp only [u, classOfUnitRightDualIso]
    rw [comp_whiskerRight_assoc,
      @rightAdjointMate_comp_evaluation C _ _ _ _ _ (RightRigidCategory.rightDual (𝟙_ C)),
      ← whisker_exchange_assoc, rightDualUnitIso_inv_whiskerRight_evaluation]
  rw [inductionMate_apply]
  calc _ = 𝟙 _ ⊗≫ (u ▷ (S.reprᘁ ⊗ 𝟙_ C) ≫ (S₀.reprᘁ : C) ◁ (S.reprᘁ : C) ◁ η_ S.repr S.reprᘁ) ⊗≫
            (S₀.reprᘁ : C) ◁ (ε_ S.repr S.reprᘁ ≫ e₀.inv) ▷ (S.reprᘁ : C) ⊗≫
            ε_ S₀.repr S₀.reprᘁ ▷ (S.reprᘁ : C) ⊗≫ 𝟙 _ := by
          monoidal
    _ = 𝟙 _ ⊗≫ 𝟙_ C ◁ (S.reprᘁ : C) ◁ η_ S.repr S.reprᘁ ⊗≫
          (u ▷ ((S.reprᘁ ⊗ S.repr) ⊗ S.reprᘁ) ≫
            (S₀.reprᘁ : C) ◁ ((ε_ S.repr S.reprᘁ ≫ e₀.inv) ▷ (S.reprᘁ : C))) ⊗≫
          ε_ S₀.repr S₀.reprᘁ ▷ (S.reprᘁ : C) ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]
          monoidal
    _ = 𝟙 _ ⊗≫ 𝟙_ C ◁ (S.reprᘁ : C) ◁ η_ S.repr S.reprᘁ ⊗≫
          𝟙_ C ◁ ε_ S.repr S.reprᘁ ▷ (S.reprᘁ : C) ⊗≫
          ((𝟙_ C ◁ e₀.inv ≫ (u ▷ S₀.repr ≫ ε_ S₀.repr S₀.reprᘁ)) ▷ (S.reprᘁ : C)) ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]
          simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
          monoidal
    _ = 𝟙 _ ⊗≫ ((S.reprᘁ : C) ◁ η_ S.repr S.reprᘁ ⊗≫ ε_ S.repr S.reprᘁ ▷ (S.reprᘁ : C)) ⊗≫
          𝟙 _ := by
          rw [hev, ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]
          monoidal
    _ = (λ_ S.reprᘁ).hom := by
          rw [ExactPairing.coevaluation_evaluation'']
          monoidal

variable [Fintype (SimpleClasses C)]

/-- `counitLF b` is a morphism `(induction k C).obj A ⟶ ⟨A, b⟩` in `Center C`. -/
private theorem counitLF_comm {A : C} (b : HalfBraiding A) (U : C) :
    counitLF b ▷ U ≫ (b.β U).hom = inductionβHom k A U ≫ U ◁ counitLF b := by
  refine inductionObj_map_hom_ext_ι (F := tensorRight U) fun S ↦ ?_
  change biproduct.ι (inductionSummand A) S ▷ U ≫ (counitLF b ▷ U ≫ (b.β U).hom) =
    biproduct.ι (inductionSummand A) S ▷ U ≫ (inductionβHom k A U ≫ U ◁ counitLF b)
  rw [← Category.assoc, ← comp_whiskerRight, ι_comp_counitLF]
  have hlhs : counitLFComponent b S ▷ U ≫ (b.β U).hom =
      (α_ S.repr (A ⊗ S.reprᘁ) U).hom ≫
        S.repr ◁ (α_ A S.reprᘁ U).hom ≫
        S.repr ◁ (b.β (S.reprᘁ ⊗ U)).hom ≫
        (α_ S.repr (S.reprᘁ ⊗ U) A).inv ≫
        (((α_ S.repr S.reprᘁ U).inv ≫ swapEval S.repr ▷ U ≫ (λ_ U).hom) ▷ A) := by
    rw [counitLFComponent_eq_forward]
    calc _ = 𝟙 _ ⊗≫ S.repr ◁ (b.β S.reprᘁ).hom ▷ U ⊗≫
              (swapEval S.repr ▷ (A ⊗ U) ≫ 𝟙_ C ◁ (b.β U).hom) ⊗≫ 𝟙 _ := by
            simp only [comp_whiskerRight, Category.assoc]
            monoidal
      _ = 𝟙 _ ⊗≫ S.repr ◁ ((α_ A S.reprᘁ U).inv ≫ (b.β S.reprᘁ).hom ▷ U ≫
            (α_ S.reprᘁ A U).hom ≫ (S.reprᘁ : C) ◁ (b.β U).hom ≫ (α_ S.reprᘁ U A).inv) ⊗≫
            swapEval S.repr ▷ (U ⊗ A) ⊗≫ 𝟙 _ := by
            rw [← whisker_exchange]
            simp only [whiskerLeft_comp]
            monoidal
      _ = _ := by
            rw [← b.monoidal S.reprᘁ U]
            simp only [comp_whiskerRight]
            monoidal
  have hrhs : biproduct.ι (inductionSummand A) S ▷ U ≫ (inductionβHom k A U ≫ U ◁ counitLF b) =
      ∑ T : SimpleClasses C, inductionβComponent k A U S T ≫ U ◁ counitLFComponent b T := by
    dsimp only [counitLF]
    simp only [whiskerLeft_sum, Preadditive.comp_sum, whiskerLeft_comp,
      ι_whiskerRight_inductionβHom_whiskerLeft_π_assoc]
  rw [hlhs, hrhs, ← sum_counitTerm_eq k U S]
  have hcomponent (T : SimpleClasses C) :
      inductionβComponent k A U S T =
        ∑ i, inductionTerm k A ((Module.finBasis k (S.repr ⟶ U ⊗ T.repr)).homDual i)
          (Module.finBasis k (S.repr ⟶ U ⊗ T.repr) i) :=
    inductionβComponent_eq k A U S T (Module.finBasis k _)
  simp only [hcomponent, Preadditive.sum_comp,
    inductionTerm_comp_whiskerLeft_counitLFComponent, sum_whiskerRight, Preadditive.comp_sum]

/-- Restricting `inductionβHom k X S.reprᘁ` to the `classOf (𝟙_ C)`-summand projects onto the
single `S`-summand. -/
private theorem ι_whiskerRight_inductionβHom_rightDual (X : C) (S : SimpleClasses C) :
    biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) ▷ (S.reprᘁ : C) ≫
        inductionβHom k X S.reprᘁ =
      inductionβComponent k X S.reprᘁ (SimpleClasses.classOf (𝟙_ C)) S ≫
        (S.reprᘁ : C) ◁ biproduct.ι (inductionSummand X) S := by
  classical
  conv_lhs => rw [← Category.comp_id (inductionβHom k X S.reprᘁ),
    ← whiskerLeft_id (S.reprᘁ : C) (inductionObj X),
    ← biproduct.total (f := inductionSummand X), whiskerLeft_sum]
  simp only [Preadditive.comp_sum, whiskerLeft_comp,
    ι_whiskerRight_inductionβHom_whiskerLeft_π_assoc]
  rw [Finset.sum_eq_single S]
  · intro T _ hTS
    rw [inductionβComponent_rightDual_classOf_unit_of_ne k X hTS, zero_comp]
  · simp

/-- Left triangle identity:
`inductionMap (unitLF X) ≫ counitLF (inductionHalfBraiding k X) = 𝟙 (inductionObj X)`. -/
private theorem map_unitLF_comp_counitLF (X : C) :
    inductionMap (unitLF X) ≫ counitLF (inductionHalfBraiding k X) = 𝟙 (inductionObj X) := by
  refine biproduct.hom_ext' _ _ fun S ↦ ?_
  rw [Category.comp_id, biproduct.ι_map_assoc, ι_comp_counitLF, counitLFComponent_eq_forward,
    inductionHalfBraiding_β_hom]
  let S₀ := SimpleClasses.classOf (𝟙_ C)
  let e₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  have htail : S.repr ◁ (S.reprᘁ : C) ◁ biproduct.ι (inductionSummand X) S ≫
      (α_ S.repr S.reprᘁ (inductionObj X)).inv ≫
      swapEval S.repr ▷ inductionObj X ≫ (λ_ (inductionObj X)).hom =
      (α_ S.repr S.reprᘁ (inductionSummand X S)).inv ≫
        swapEval S.repr ▷ inductionSummand X S ≫
        (λ_ (inductionSummand X S)).hom ≫
        biproduct.ι (inductionSummand X) S := by
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, leftUnitor_naturality]
  dsimp only [unitLF]
  rw [inductionCoendι_tensorUnit k X]
  simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  rw [← whiskerLeft_comp_assoc S.repr (biproduct.ι (inductionSummand X) S₀ ▷ (S.reprᘁ : C)),
    ι_whiskerRight_inductionβHom_rightDual k X S,
    inductionβComponent_rightDual_classOf_unit_self k X S, Iso.symm_hom, Iso.symm_inv,
    inductionTerm_apply, whiskerLeft_comp_assoc, htail]
  simp only [← Category.assoc]
  refine (congrArg (· ≫ biproduct.ι (inductionSummand X) S) ?_).trans
    (Category.id_comp (biproduct.ι (inductionSummand X) S))
  dsimp only [inductionSummand]
  let u : 𝟙_ C ⟶ S₀.reprᘁ :=
    (rightDualUnitIso C).inv ≫ (classOfUnitRightDualIso (C := C)).inv
  calc _ = 𝟙 _ ⊗≫ S.repr ◁ (𝟙_ C ◁ (X ◁ u) ≫
              (e₀.inv ≫ (e₀.hom ≫ swapCoeval S.repr)) ▷ (X ⊗ S₀.reprᘁ)) ▷ (S.reprᘁ : C) ⊗≫
            (S.repr ⊗ S.reprᘁ ⊗ S.repr) ◁ X ◁
              inductionMate k S.reprᘁ (ε_ S.repr S.reprᘁ ≫ e₀.inv) ⊗≫
            swapEval S.repr ▷ (S.repr ⊗ X ⊗ S.reprᘁ) ⊗≫ 𝟙 _ := by
          dsimp only [u]
          simp only [whiskerLeft_comp, comp_whiskerRight, Category.assoc]
          monoidal
    _ = 𝟙 _ ⊗≫ (S.repr ◁ swapCoeval S.repr) ▷ (X ⊗ 𝟙_ C ⊗ S.reprᘁ) ⊗≫
          (S.repr ⊗ S.reprᘁ ⊗ S.repr) ◁ X ◁
            (u ▷ (S.reprᘁ : C) ≫ inductionMate k S.reprᘁ (ε_ S.repr S.reprᘁ ≫ e₀.inv)) ⊗≫
          swapEval S.repr ▷ (S.repr ⊗ X ⊗ S.reprᘁ) ⊗≫ 𝟙 _ := by
          rw [← Category.assoc e₀.inv, Iso.inv_hom_id, Category.id_comp, whisker_exchange]
          simp only [whiskerLeft_comp, comp_whiskerRight]
          monoidal
    _ = 𝟙 _ ⊗≫ (S.repr ◁ swapCoeval S.repr ⊗≫ swapEval S.repr ▷ S.repr) ▷ (X ⊗ S.reprᘁ) ⊗≫
          𝟙 _ := by
          dsimp only [u]
          rw [inductionMate_evaluation_classOf_unit k S]
          monoidal
    _ = 𝟙 (S.repr ⊗ X ⊗ S.reprᘁ) := by
          rw [@ExactPairing.coevaluation_evaluation'' C _ _ S.reprᘁ S.repr
            (simpleSwapExactPairing S.repr)]
          monoidal

/-! ### Public left adjunction API -/

variable (C)

/-- **Left adjunction for centre induction**: `Center.induction k C ⊣ Center.forget C`. Together
with `forgetInductionAdjunction k C`, this makes `Center.induction k C` two-sided adjoint to
`Center.forget C`. No pivotal structure or characteristic-zero assumption is required. -/
def inductionForgetAdjunction : induction k C ⊣ forget C :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app X := unitLF X
          naturality _ _ f := (unitLF_naturality f).symm }
      counit :=
        { app Z :=
            { f := counitLF (A := Z.1) Z.2
              comm U :=
                (counitLF_comm k (A := Z.1) Z.2 U).trans
                  (congrArg (· ≫ U ◁ counitLF (A := Z.1) Z.2)
                    (inductionHalfBraiding_β_hom k Z.1 U).symm) }
          naturality _ _ h := Center.ext _ _ (counitLF_naturality h.f h.comm) }
      left_triangle := by
        refine NatTrans.ext (funext fun X ↦ ?_)
        dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Functor.associator_hom_app, NatTrans.id_app, Functor.comp_obj, Functor.id_obj]
        rw [Category.id_comp]
        exact Center.ext _ _ (map_unitLF_comp_counitLF k X)
      right_triangle :=
        NatTrans.ext (funext fun Z ↦
          (congrArg (unitLF ((forget C).obj Z) ≫ ·)
            (Category.id_comp (counitLF (A := Z.1) Z.2))).trans
            (unitLF_comp_counitLF k (A := Z.1) Z.2)) }

/-- `Center.induction k C` is a left adjoint (in particular, it preserves all colimits that exist in
`C`; combined with `instIsRightAdjointInduction`, it is exact). -/
instance instIsLeftAdjointInduction : (induction k C).IsLeftAdjoint :=
  (inductionForgetAdjunction k C).isLeftAdjoint

/-- Explicit formula for the unit of `inductionForgetAdjunction` at `X`. -/
@[reassoc, simp]
theorem inductionForgetAdjunction_unit_app (X : C) :
    (inductionForgetAdjunction k C).unit.app X =
      (ρ_ X).inv ≫
        X ◁ (rightDualUnitIso C).inv ≫
        (λ_ (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual)).inv ≫
        inductionCoendι X (𝟙_ C) :=
  (rfl)

/-- Component of the counit of `inductionForgetAdjunction` on the `S`-summand of
`inductionObj Z.1`. -/
@[reassoc, simp]
theorem ι_comp_inductionForgetAdjunction_counit_app_f (Z : Center C) (S : SimpleClasses C) :
    biproduct.ι (inductionSummand Z.1) S ≫
        ((inductionForgetAdjunction k C).counit.app Z).f =
      (α_ S.repr Z.1 S.reprᘁ).inv ≫
        (Z.2.β S.repr).inv ▷ S.reprᘁ ≫
        (α_ Z.1 S.repr S.reprᘁ).hom ≫
        Z.1 ◁ @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleSwapExactPairing S.repr) ≫
        (ρ_ Z.1).hom :=
  ι_comp_counitLF Z.2 S

/-- Normalization between the two adjunctions: the unit of `inductionForgetAdjunction` followed by
the counit of `forgetInductionAdjunction` is the identity. -/
@[reassoc]
theorem inductionForgetAdjunction_unit_comp_forgetInductionAdjunction_counit (X : C) :
    (inductionForgetAdjunction k C).unit.app X ≫
      (forgetInductionAdjunction k C).counit.app X = 𝟙 X := by
  rw [inductionForgetAdjunction_unit_app, forgetInductionAdjunction_counit_app]
  exact unitLF_comp_counitF k X

/-- Each component of the unit of `inductionForgetAdjunction` is a split monomorphism. -/
instance instIsSplitMonoInductionForgetAdjunctionUnit (X : C) :
    IsSplitMono ((inductionForgetAdjunction k C).unit.app X) :=
  IsSplitMono.mk' ⟨(forgetInductionAdjunction k C).counit.app X,
    inductionForgetAdjunction_unit_comp_forgetInductionAdjunction_counit k C X⟩

/-- Each component of the counit of `forgetInductionAdjunction` is a split epimorphism. -/
instance instIsSplitEpiForgetInductionAdjunctionCounit (X : C) :
    IsSplitEpi ((forgetInductionAdjunction k C).counit.app X) :=
  IsSplitEpi.mk' ⟨(inductionForgetAdjunction k C).unit.app X,
    inductionForgetAdjunction_unit_comp_forgetInductionAdjunction_counit k C X⟩

/-- The induction functor `Center.induction k C` is faithful. -/
instance instFaithfulInduction : (induction k C).Faithful :=
  (inductionForgetAdjunction k C).faithful_L_of_mono_unit_app

end LeftAdjunction

end CategoryTheory.Center
