/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Induction.Adjunction
public import TauCeti.CategoryTheory.Semisimple.OppositePairing
public import TauCeti.CategoryTheory.Semisimple.Rigid

/-!
# The left adjunction for induction into the Drinfeld centre

Let `C` be a fusion category over an algebraically closed field `k` (`k`-linear, finite semisimple,
rigid abelian monoidal with simple tensor unit, finitely many simple classes, and finite-dimensional
morphism spaces). `TauCeti.CategoryTheory.Monoidal.Center.Induction.Adjunction` shows
`Center.forget C ⊣ Center.induction k C` without assuming `Simple (𝟙_ C)` or a pivotal structure.

When `𝟙_ C` is simple, each simple representative `S.repr` carries its canonical opposite exact
pairing `TauCeti.simpleOppositeExactPairing S.repr : ExactPairing S.reprᘁ S.repr`
(`TauCeti.CategoryTheory.Semisimple.OppositePairing`). Using these pairings, this file constructs
the **left adjunction** `inductionForgetAdjunction k C : Center.induction k C ⊣ Center.forget C` —
making `Center.induction k C` a Frobenius functor without choosing a pivotal structure on `C`:
* the unit `X ⟶ inductionObj X` embeds `X` into the unit-class summand and splits
  `(forgetInductionAdjunction k C).counit.app X`;
* the counit `inductionCenterObj k Z.1 ⟶ Z` moves `Z.1` past `S.repr` via `(Z.2.β S.repr).inv` and
  contracts `S.repr ⊗ S.reprᘁ` via the opposite evaluation.

Simplicity of `𝟙_ C` is required for the single-unit-summand and `simpleOppositeExactPairing`
construction here (in `Vec_k × Vec_k`, `(k, 0)ᘁ ⊗ (k, 0)` does not surject onto `(k, k)`), and is
necessary for faithfulness of `Center.induction k C` and split-monomorphicity of the unit (which
fail in `M₂(Vec_k)`, where `inductionObj E₁₂ = 0`).

## Main declarations

* `CategoryTheory.Center.inductionForgetAdjunction` and
  `CategoryTheory.Center.instIsLeftAdjointInduction`, with unit/counit formulas
  `inductionForgetAdjunction_unit_app` and `ι_comp_inductionForgetAdjunction_counit_app_f`;
* `inductionForgetAdjunction_unit_app_comp_forgetInductionAdjunction_counit_app`,
  `instIsSplitMonoInductionForgetAdjunctionUnitApp`, and
  `instIsSplitEpiForgetInductionAdjunctionCounitApp`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §§2, 8
* M. Müger, *From subfactors to categories and topology II*, J. Pure Appl. Algebra **180** (2003)
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§7.13, 9.3
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory ExactPairing Module TauCeti

universe w v u

namespace CategoryTheory.Center

attribute [local instance] Abelian.hasFiniteBiproducts

section Helpers

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [RightRigidCategory C]
  [Fintype (SimpleClasses C)]

private theorem inductionObj_whiskerRight_hom_ext {X U W : C} {f₁ f₂ : inductionObj X ⊗ U ⟶ W}
    (h : ∀ S : SimpleClasses C,
      biproduct.ι (inductionSummand X) S ▷ U ≫ f₁ = biproduct.ι (inductionSummand X) S ▷ U ≫ f₂) :
    f₁ = f₂ := by
  apply (tensorRightHomEquiv (inductionObj X) U Uᘁ W).injective
  refine biproduct.hom_ext' _ _ fun S ↦ ?_
  rw [← tensorRightHomEquiv_whiskerRight_comp, ← tensorRightHomEquiv_whiskerRight_comp, h S]

end Helpers

section OppositeMate

variable (k : Type w) [Field k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

private abbrev oppEval (S : SimpleClasses C) : S.repr ⊗ S.reprᘁ ⟶ 𝟙_ C :=
  @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr)

private abbrev oppCoev (S : SimpleClasses C) : 𝟙_ C ⟶ S.reprᘁ ⊗ S.repr :=
  @ExactPairing.coevaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr)

/-- Component `S.repr ⊗ A ⊗ S.reprᘁ ⟶ A` of `(inductionForgetAdjunction k C).counit.app ⟨A, b⟩`. -/
private def counitComponent {A : C} (b : HalfBraiding A) (S : SimpleClasses C) :
    inductionSummand A S ⟶ A :=
  (α_ S.repr A S.reprᘁ).inv ≫ (b.β S.repr).inv ▷ S.reprᘁ ≫ (α_ A S.repr S.reprᘁ).hom ≫
    A ◁ oppEval S ≫ (ρ_ A).hom

private theorem inductionTerm_comp_inv_evaluation {A : C} (b : HalfBraiding A) (U : C)
    (S T : SimpleClasses C) (g : U ⊗ T.repr ⟶ S.repr) (f : S.repr ⟶ U ⊗ T.repr) :
    inductionTerm k A g f ≫ U ◁ counitComponent b T ≫ (b.β U).inv =
      ((α_ S.repr A S.reprᘁ).inv ▷ U ≫ (α_ (S.repr ⊗ A) S.reprᘁ U).hom ≫
        (b.β S.repr).inv ▷ (S.reprᘁ ⊗ U) ≫ (α_ A S.repr (S.reprᘁ ⊗ U)).hom) ≫
        A ◁ (𝟙 (S.repr ⊗ S.reprᘁ ⊗ U) ⊗≫ f ▷ (S.reprᘁ ⊗ U) ⊗≫
          U ◁ T.repr ◁ inductionMate k U g ⊗≫ U ◁ oppEval T ⊗≫ 𝟙 U) := by
  rw [inductionTerm_apply]
  have hmon : U ◁ ((b.β T.repr).inv ▷ T.reprᘁ) ⊗≫ U ◁ A ◁ oppEval T ⊗≫ (b.β U).inv =
      𝟙 (U ⊗ (T.repr ⊗ A) ⊗ T.reprᘁ) ⊗≫ (b.β (U ⊗ T.repr)).inv ▷ T.reprᘁ ⊗≫
        A ◁ U ◁ oppEval T ⊗≫ 𝟙 (A ⊗ U) := by
    calc _ = 𝟙 _ ⊗≫ U ◁ ((b.β T.repr).inv ▷ T.reprᘁ) ⊗≫
              ((U ⊗ A) ◁ oppEval T ≫ (b.β U).inv ▷ 𝟙_ C) ⊗≫ 𝟙 _ := by monoidal
      _ = 𝟙 _ ⊗≫ (U ◁ (b.β T.repr).inv ⊗≫ (b.β U).inv ▷ T.repr) ▷ T.reprᘁ ⊗≫
            A ◁ U ◁ oppEval T ⊗≫ 𝟙 _ := by rw [whisker_exchange]; monoidal
      _ = _ := by rw [b.monoidal_inv U T.repr]; simp only [comp_whiskerRight]; monoidal
  calc _ = 𝟙 _ ⊗≫ f ▷ A ▷ S.reprᘁ ▷ U ⊗≫ U ◁ T.repr ◁ A ◁ inductionMate k U g ⊗≫
            (U ◁ ((b.β T.repr).inv ▷ T.reprᘁ) ⊗≫ U ◁ A ◁ oppEval T ⊗≫ (b.β U).inv) := by
          simp only [counitComponent, whiskerLeft_comp]; monoidal
    _ = 𝟙 _ ⊗≫ f ▷ A ▷ (S.reprᘁ ⊗ U) ⊗≫
          (((U ⊗ T.repr) ⊗ A) ◁ inductionMate k U g ≫ (b.β (U ⊗ T.repr)).inv ▷ T.reprᘁ) ⊗≫
          A ◁ U ◁ oppEval T ⊗≫ 𝟙 _ := by rw [hmon]; monoidal
    _ = 𝟙 _ ⊗≫ ((f ▷ A ≫ (b.β (U ⊗ T.repr)).inv) ▷ (S.reprᘁ ⊗ U)) ⊗≫
          A ◁ U ◁ T.repr ◁ inductionMate k U g ⊗≫ A ◁ U ◁ oppEval T ⊗≫ 𝟙 _ := by
          rw [whisker_exchange]; simp only [comp_whiskerRight]; monoidal
    _ = _ := by rw [b.naturality_inv f]; simp only [comp_whiskerRight]; monoidal

/-- Frobenius reciprocity isomorphism `(S.repr ⟶ U ⊗ T.repr) ≃ₗ[k] (T.reprᘁ ⟶ S.reprᘁ ⊗ U)` built
from `simpleOppositeExactPairing S.repr` and `simpleOppositeExactPairing T.repr`. -/
private def oppositeMateEquiv (U : C) (S T : SimpleClasses C) :
    (S.repr ⟶ U ⊗ T.repr) ≃ₗ[k] (T.reprᘁ ⟶ S.reprᘁ ⊗ U) :=
  let _ := simpleOppositeExactPairing S.repr
  let _ := simpleOppositeExactPairing T.repr
  (tensorRightHomLinearEquiv k S.repr T.reprᘁ T.repr U).symm.trans
    (tensorLeftHomLinearEquiv k T.reprᘁ S.reprᘁ S.repr U)

private theorem oppositeMateEquiv_apply (U : C) (S T : SimpleClasses C)
    (f : S.repr ⟶ U ⊗ T.repr) :
    oppositeMateEquiv k U S T f =
      𝟙 (T.reprᘁ : C) ⊗≫ oppCoev S ▷ T.reprᘁ ⊗≫ S.reprᘁ ◁ f ▷ T.reprᘁ ⊗≫
        S.reprᘁ ◁ U ◁ oppEval T ⊗≫ 𝟙 ((S.reprᘁ : C) ⊗ U) := by
  let _ := simpleOppositeExactPairing S.repr
  let _ := simpleOppositeExactPairing T.repr
  rw [oppositeMateEquiv, LinearEquiv.trans_apply, tensorLeftHomLinearEquiv_apply,
    tensorRightHomLinearEquiv_symm_apply]
  dsimp only [tensorRightHomEquiv, tensorLeftHomEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  monoidal

private theorem tensorLeftHomEquiv_kernel (U : C) (S T : SimpleClasses C)
    (g : U ⊗ T.repr ⟶ S.repr) (f : S.repr ⟶ U ⊗ T.repr) :
    @tensorLeftHomEquiv C _ _ (S.reprᘁ ⊗ U) S.reprᘁ S.repr U (simpleOppositeExactPairing S.repr)
        (𝟙 (S.repr ⊗ S.reprᘁ ⊗ U) ⊗≫ f ▷ (S.reprᘁ ⊗ U) ⊗≫
          U ◁ T.repr ◁ inductionMate k U g ⊗≫ U ◁ oppEval T ⊗≫ 𝟙 U) =
      inductionMate k U g ≫ oppositeMateEquiv k U S T f := by
  rw [oppositeMateEquiv_apply]
  dsimp only [tensorLeftHomEquiv, Equiv.coe_fn_mk]
  calc _ = 𝟙 _ ⊗≫ oppCoev S ▷ ((S.reprᘁ : C) ⊗ U) ⊗≫
            S.reprᘁ ◁ (f ▷ ((S.reprᘁ : C) ⊗ U) ≫ (U ⊗ T.repr) ◁ inductionMate k U g) ⊗≫
            S.reprᘁ ◁ U ◁ oppEval T ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ (oppCoev S ▷ ((S.reprᘁ : C) ⊗ U) ≫
          ((S.reprᘁ : C) ⊗ S.repr) ◁ inductionMate k U g) ⊗≫
          ((S.reprᘁ : C) ◁ f) ▷ T.reprᘁ ⊗≫ S.reprᘁ ◁ U ◁ oppEval T ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange, whiskerLeft_comp]; monoidal
    _ = _ := by rw [← whisker_exchange]; monoidal

private theorem coevaluation_comp_oppositeMateEquiv_comp_inductionMate (U : C)
    (S T : SimpleClasses C) (f : S.repr ⟶ U ⊗ T.repr) (g : U ⊗ T.repr ⟶ S.repr) :
    oppCoev T ≫ (oppositeMateEquiv k U S T f ≫ inductionMate k U g) ▷ T.repr ≫ ε_ T.repr T.reprᘁ =
      oppCoev S ≫ S.reprᘁ ◁ (f ≫ g) ≫ ε_ S.repr S.reprᘁ := by
  rw [comp_whiskerRight_assoc, inductionMate_whiskerRight_evaluation]
  have hleft : oppCoev T ≫ oppositeMateEquiv k U S T f ▷ T.repr =
      oppCoev S ≫ S.reprᘁ ◁ f ≫ (α_ S.reprᘁ U T.repr).inv := by
    rw [oppositeMateEquiv_apply]
    calc _ = 𝟙 _ ⊗≫ (𝟙_ C ◁ oppCoev T ≫ (oppCoev S ≫ S.reprᘁ ◁ f) ▷ (T.reprᘁ ⊗ T.repr)) ⊗≫
              S.reprᘁ ◁ U ◁ (oppEval T ▷ T.repr) ⊗≫ 𝟙 _ := by
            simp only [comp_whiskerRight]; monoidal
      _ = 𝟙 _ ⊗≫ oppCoev S ≫ S.reprᘁ ◁ f ⊗≫
            S.reprᘁ ◁ U ◁ (T.repr ◁ oppCoev T ⊗≫ oppEval T ▷ T.repr) ⊗≫ 𝟙 _ := by
            rw [whisker_exchange]; monoidal
      _ = _ := by
            rw [@ExactPairing.coevaluation_evaluation'' C _ _ T.reprᘁ T.repr
              (simpleOppositeExactPairing T.repr)]
            monoidal
  rw [reassoc_of% hleft, Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc]

variable [IsAlgClosed k] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

private theorem inductionMate_homDual_eq (U : C) (S T : SimpleClasses C)
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι k (S.repr ⟶ U ⊗ T.repr)) (j : ι) :
    inductionMate k U (b.homDual j) = (b.map (oppositeMateEquiv k U S T)).homDual j := by
  refine ((b.map (oppositeMateEquiv k U S T)).eq_homDual_iff _ j).2 fun i ↦ ?_
  rw [Basis.map_apply]
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k
    (oppositeMateEquiv k U S T (b i) ≫ inductionMate k U (b.homDual j))
  have htr := coevaluation_comp_oppositeMateEquiv_comp_inductionMate k U S T (b i) (b.homDual j)
  rw [← hc, b.apply_comp_homDual i j, MonoidalLinear.smul_whiskerRight, Linear.smul_comp,
    Linear.comp_smul, id_whiskerRight, Category.id_comp,
    simpleOppositeExactPairing_coevaluation_comp_evaluation] at htr
  have hscalar : c = if i = j then 1 else 0 := by
    have h' := congrArg (endAlgEquivOfSimple k (𝟙_ C) ∘ End.of) htr
    split_ifs at h' ⊢ <;>
      simpa [simpleOppositeExactPairing_coevaluation_comp_evaluation] using h'
  rw [← hc, hscalar]; split_ifs <;> simp

private theorem left_triangle_of_ne (X : C) {S T : SimpleClasses C} (hST : S ≠ T) :
    inductionβComponent k X S.reprᘁ (SimpleClasses.classOf (𝟙_ C)) T = 0 := by
  let _ := simpleOppositeExactPairing S.repr
  have : Subsingleton (S.repr ⟶ T.repr) := SimpleClasses.homOrthogonal_repr hST
  have : Subsingleton ((SimpleClasses.classOf (𝟙_ C)).repr ⟶ S.reprᘁ ⊗ T.repr) :=
    ((Iso.homCongr (SimpleClasses.classOfReprIso (𝟙_ C)) (Iso.refl _)).trans
      ((tensorLeftHomEquiv (𝟙_ C) S.reprᘁ S.repr T.repr).symm.trans
        (Iso.homCongr (ρ_ S.repr) (Iso.refl T.repr)))).subsingleton
  rw [inductionβComponent_eq k X S.reprᘁ _ T (Module.finBasis k _)]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [Subsingleton.elim (Module.finBasis k _ i) 0, map_zero]

private def unitClassCoevaluationBasis (S : SimpleClasses C) :
    Basis (Fin 1) k ((SimpleClasses.classOf (𝟙_ C)).repr ⟶ S.reprᘁ ⊗ S.repr) :=
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  have hleft (c : k) :
      endAlgEquivOfSimple k (𝟙_ C)
        (End.of (u₀.inv ≫ (c • (u₀.hom ≫ oppCoev S)) ≫ ε_ S.repr S.reprᘁ)) = c :=
    (endAlgEquivOfSimple_apply_eq_iff _ c).2 <| by
      rw [Linear.smul_comp, Linear.comp_smul, Category.assoc, u₀.inv_hom_id_assoc,
        simpleOppositeExactPairing_coevaluation_comp_evaluation]
  let e : k ≃ₗ[k] ((SimpleClasses.classOf (𝟙_ C)).repr ⟶ S.reprᘁ ⊗ S.repr) :=
    { toFun c := c • (u₀.hom ≫ oppCoev S)
      map_add' c₁ c₂ := add_smul c₁ c₂ _
      map_smul' r c := by simp [mul_smul]
      invFun f := endAlgEquivOfSimple k (𝟙_ C) (End.of (u₀.inv ≫ f ≫ ε_ S.repr S.reprᘁ))
      left_inv := hleft
      right_inv f := by
        let _ := simpleOppositeExactPairing S.repr
        obtain ⟨c, hc⟩ := hom_from_tensorUnit_eq_smul_coevaluation_of_simple_right k (u₀.inv ≫ f)
        have hf : f = c • (u₀.hom ≫ oppCoev S) := by
          rw [← u₀.hom_inv_id_assoc f, hc, Linear.comp_smul]
        simp [hf] }
  (Module.Basis.singleton (Fin 1) k).map e

private theorem unitClassCoevaluationBasis_apply (S : SimpleClasses C) (i : Fin 1) :
    unitClassCoevaluationBasis k S i = (SimpleClasses.classOfReprIso (𝟙_ C)).hom ≫ oppCoev S := by
  simp [unitClassCoevaluationBasis]

private theorem unitClassCoevaluationBasis_homDual (S : SimpleClasses C) :
    (unitClassCoevaluationBasis k S).homDual 0 =
      ε_ S.repr S.reprᘁ ≫ (SimpleClasses.classOfReprIso (𝟙_ C)).inv := by
  refine (((unitClassCoevaluationBasis k S).eq_homDual_iff _ 0).2 fun i ↦ ?_).symm
  simp only [Fin.fin_one_eq_zero i, ↓reduceIte, unitClassCoevaluationBasis_apply, Category.assoc]
  rw [reassoc_of% (simpleOppositeExactPairing_coevaluation_comp_evaluation S.repr), Iso.hom_inv_id]

omit [IsAlgClosed k] [IsFiniteSemisimpleCategory C]
  [∀ (X Y : C), FiniteDimensional k (X ⟶ Y)] in
private theorem rightAdjointMate_whiskerRight_comp_inductionMate (S : SimpleClasses C) :
    ((SimpleClasses.classOfReprIso (𝟙_ C)).hom)ᘁ ▷ S.reprᘁ ≫
        inductionMate k S.reprᘁ (ε_ S.repr S.reprᘁ ≫ (SimpleClasses.classOfReprIso (𝟙_ C)).inv) =
      (λ_ S.reprᘁ).hom := by
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  refine ExactPairing.rightHom_ext (X := S.repr) ?_
  calc ((u₀.hom)ᘁ ▷ S.reprᘁ ≫ inductionMate k S.reprᘁ (ε_ S.repr S.reprᘁ ≫ u₀.inv)) ▷ S.repr ≫
          ε_ S.repr S.reprᘁ
      = (𝟙 _ ⊗≫ ((u₀.hom)ᘁ ▷ (S.reprᘁ ⊗ S.repr) ≫
          (SimpleClasses.classOf (𝟙_ C)).reprᘁ ◁ (ε_ S.repr S.reprᘁ ≫ u₀.inv))) ≫
          ε_ (SimpleClasses.classOf (𝟙_ C)).repr _ := by
        rw [comp_whiskerRight_assoc, inductionMate_whiskerRight_evaluation]; monoidal
    _ = (α_ (𝟙_ C) S.reprᘁ S.repr).hom ≫ 𝟙_ C ◁ (ε_ S.repr S.reprᘁ ≫ u₀.inv) ≫
          ((u₀.hom)ᘁ ▷ (SimpleClasses.classOf (𝟙_ C)).repr ≫
            ε_ (SimpleClasses.classOf (𝟙_ C)).repr _) := by
        rw [← whisker_exchange]; monoidal
    _ = (λ_ S.reprᘁ).hom ▷ S.repr ≫ ε_ S.repr S.reprᘁ := by
        rw [rightAdjointMate_whiskerRight_comp_evaluation_of_unit, leftUnitor_naturality_assoc,
          Category.assoc, u₀.inv_hom_id, Category.comp_id]
        monoidal

private theorem left_triangle_self (X : C) (S : SimpleClasses C) :
    S.repr ◁ (((λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫
        ((SimpleClasses.classOfReprIso (𝟙_ C)).inv ⊗ₘ
          (𝟙 X ⊗ₘ ((SimpleClasses.classOfReprIso (𝟙_ C)).hom)ᘁ))) ▷ S.reprᘁ ≫
      inductionβComponent k X S.reprᘁ (SimpleClasses.classOf (𝟙_ C)) S) ≫
      (α_ S.repr S.reprᘁ (S.repr ⊗ X ⊗ S.reprᘁ)).inv ≫ oppEval S ▷ (S.repr ⊗ X ⊗ S.reprᘁ) ≫
      (λ_ (S.repr ⊗ X ⊗ S.reprᘁ)).hom = 𝟙 (S.repr ⊗ X ⊗ S.reprᘁ) := by
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  have hinner : ((λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫ (u₀.inv ⊗ₘ (𝟙 X ⊗ₘ (u₀.hom)ᘁ))) ▷ S.reprᘁ ≫
        inductionTerm k X (ε_ S.repr S.reprᘁ ≫ u₀.inv) (u₀.hom ≫ oppCoev S) =
      (λ_ (X ⊗ S.reprᘁ)).inv ≫ oppCoev S ▷ (X ⊗ S.reprᘁ) ≫
        (α_ S.reprᘁ S.repr (X ⊗ S.reprᘁ)).hom := by
    rw [inductionTerm_apply]
    calc _ = 𝟙 _ ⊗≫ (u₀.inv ▷ (X ⊗ 𝟙_ C)) ▷ S.reprᘁ ⊗≫
              (((SimpleClasses.classOf (𝟙_ C)).repr ◁ (X ◁ (u₀.hom)ᘁ) ≫
                (u₀.hom ≫ oppCoev S) ▷ (X ⊗ _)) ▷ S.reprᘁ) ⊗≫
              S.reprᘁ ◁ S.repr ◁ X ◁ inductionMate k S.reprᘁ (ε_ S.repr S.reprᘁ ≫ u₀.inv) ⊗≫
              𝟙 _ := by simp only [tensorHom_def, comp_whiskerRight]; monoidal
      _ = 𝟙 _ ⊗≫ ((u₀.inv ≫ u₀.hom ≫ oppCoev S) ▷ (X ⊗ 𝟙_ C)) ▷ S.reprᘁ ⊗≫
            S.reprᘁ ◁ S.repr ◁ X ◁
              ((u₀.hom)ᘁ ▷ S.reprᘁ ≫ inductionMate k S.reprᘁ (ε_ S.repr S.reprᘁ ≫ u₀.inv)) ⊗≫
            𝟙 _ := by
            rw [whisker_exchange]; simp only [comp_whiskerRight, whiskerLeft_comp]; monoidal
      _ = _ := by
            rw [u₀.inv_hom_id_assoc, rightAdjointMate_whiskerRight_comp_inductionMate k S]; monoidal
  rw [inductionβComponent_eq k X S.reprᘁ _ S (unitClassCoevaluationBasis k S), Fin.sum_univ_one,
    unitClassCoevaluationBasis_homDual, unitClassCoevaluationBasis_apply, hinner]
  calc _ = 𝟙 _ ⊗≫ (S.repr ◁ oppCoev S ⊗≫ oppEval S ▷ S.repr) ▷ (X ⊗ S.reprᘁ) ⊗≫ 𝟙 _ := by
          simp only [whiskerLeft_comp]; monoidal
    _ = 𝟙 (S.repr ⊗ X ⊗ S.reprᘁ) := by
          rw [@ExactPairing.coevaluation_evaluation'' C _ _ S.reprᘁ S.repr
            (simpleOppositeExactPairing S.repr)]
          monoidal

end OppositeMate

section Fusion

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] [Fintype (SimpleClasses C)]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

private def unitL (X : C) : X ⟶ inductionObj X :=
  (λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫
    ((SimpleClasses.classOfReprIso (𝟙_ C)).inv ⊗ₘ
      (𝟙 X ⊗ₘ ((SimpleClasses.classOfReprIso (𝟙_ C)).hom)ᘁ)) ≫
    biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C))

omit [Field k] [IsAlgClosed k] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
private theorem unitL_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ unitL X' = unitL X ≫ inductionMap f := by
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  have h1 : (SimpleClasses.classOf (𝟙_ C)).repr ◁ f ▷ (SimpleClasses.classOf (𝟙_ C)).reprᘁ =
      𝟙 (SimpleClasses.classOf (𝟙_ C)).repr ⊗ₘ (f ⊗ₘ 𝟙 (SimpleClasses.classOf (𝟙_ C)).reprᘁ) := by
    simp [tensorHom_def]
  have hmid : (u₀.inv ⊗ₘ (𝟙 X ⊗ₘ (u₀.hom)ᘁ)) ≫ (SimpleClasses.classOf (𝟙_ C)).repr ◁ f ▷
        (SimpleClasses.classOf (𝟙_ C)).reprᘁ =
      (𝟙 (𝟙_ C) ⊗ₘ (f ⊗ₘ 𝟙 (𝟙_ C))) ≫ (u₀.inv ⊗ₘ (𝟙 X' ⊗ₘ (u₀.hom)ᘁ)) := by
    rw [h1, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]; simp
  have hunitor : f ≫ (λ_ X').inv ≫ 𝟙_ C ◁ (ρ_ X').inv =
      (λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ (f ⊗ₘ 𝟙 (𝟙_ C))) := by
    simp only [tensorHom_def]; monoidal
  dsimp only [unitL]
  simp only [Category.assoc, biproduct.ι_map]
  rw [reassoc_of% hunitor, ← reassoc_of% hmid]

private def counitLF {A : C} (b : HalfBraiding A) : inductionObj A ⟶ A :=
  biproduct.desc (counitComponent b)

omit [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
private theorem counitLF_naturality {A A' : C} {b : HalfBraiding A} {b' : HalfBraiding A'}
    (f : A ⟶ A') (hf : ∀ U : C, f ▷ U ≫ (b'.β U).hom = (b.β U).hom ≫ U ◁ f) :
    inductionMap f ≫ counitLF b' = counitLF b ≫ f := by
  refine biproduct.hom_ext' _ _ fun S ↦ ?_
  simp only [counitLF, biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc,
    counitComponent]
  have hβ : (S.repr ◁ f) ≫ (b'.β S.repr).inv = (b.β S.repr).inv ≫ (f ▷ S.repr) := by
    rw [Iso.comp_inv_eq, Category.assoc, hf S.repr, Iso.inv_hom_id_assoc]
  calc _ = (α_ S.repr A S.reprᘁ).inv ≫ ((S.repr ◁ f) ≫ (b'.β S.repr).inv) ▷ S.reprᘁ ≫
            (α_ A' S.repr S.reprᘁ).hom ≫ A' ◁ oppEval S ≫ (ρ_ A').hom := by
          rw [comp_whiskerRight_assoc]; monoidal
    _ = (α_ S.repr A S.reprᘁ).inv ≫ (b.β S.repr).inv ▷ S.reprᘁ ≫ (α_ A S.repr S.reprᘁ).hom ≫
          (f ▷ (S.repr ⊗ S.reprᘁ) ≫ A' ◁ oppEval S) ≫ (ρ_ A').hom := by
          rw [hβ]; simp only [comp_whiskerRight, Category.assoc]; monoidal
    _ = _ := by rw [← whisker_exchange, Category.assoc, rightUnitor_naturality]; simp

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [Simple (𝟙_ C)] [Fintype (SimpleClasses C)] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
private theorem homDual_map_homCongr {S S' X : C} [Simple S] [Simple S']
    [FiniteDimensional k (S ⟶ S)] [FiniteDimensional k (S' ⟶ S')]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι k (S ⟶ X)) (u : S' ≅ S) (i : ι) :
    (b.map (Linear.homCongr k u.symm (Iso.refl X))).homDual i = b.homDual i ≫ u.inv := by
  refine ((Basis.eq_homDual_iff _ _ i).2 fun l ↦ ?_).symm
  rw [Basis.map_apply, Linear.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id,
    Category.assoc, ← Category.assoc (b l), b.apply_comp_homDual l i]
  split_ifs <;> simp

private theorem sum_kernel_eq_evaluation (U : C) (S : SimpleClasses C) :
    (∑ T : SimpleClasses C, ∑ i,
      (𝟙 (S.repr ⊗ S.reprᘁ ⊗ U) ⊗≫ Module.finBasis k (S.repr ⟶ U ⊗ T.repr) i ▷ (S.reprᘁ ⊗ U) ⊗≫
        U ◁ T.repr ◁ inductionMate k U ((Module.finBasis k (S.repr ⟶ U ⊗ T.repr)).homDual i) ⊗≫
        U ◁ oppEval T ⊗≫ 𝟙 U)) =
      (α_ S.repr S.reprᘁ U).inv ≫ oppEval S ▷ U ≫ (λ_ U).hom := by
  let _ := simpleOppositeExactPairing S.repr
  apply (tensorLeftHomLinearEquiv k (S.reprᘁ ⊗ U) S.reprᘁ S.repr U).injective
  have hrhs : tensorLeftHomLinearEquiv k (S.reprᘁ ⊗ U) S.reprᘁ S.repr U
      ((α_ S.repr S.reprᘁ U).inv ≫ oppEval S ▷ U ≫ (λ_ U).hom) = 𝟙 (S.reprᘁ ⊗ U) := by
    rw [tensorLeftHomLinearEquiv_apply, ← Equiv.eq_symm_apply]; simp [tensorLeftHomEquiv]
  rw [hrhs, map_sum]
  simp_rw [map_sum, tensorLeftHomLinearEquiv_apply, tensorLeftHomEquiv_kernel,
    inductionMate_homDual_eq, ← Basis.map_apply]
  let c (R : SimpleClasses C) := Module.finBasis k (R.repr ⟶ S.reprᘁ ⊗ U)
  have hT (T : SimpleClasses C) :
      ∑ i, ((Module.finBasis k (S.repr ⟶ U ⊗ T.repr)).map (oppositeMateEquiv k U S T)).homDual i ≫
          ((Module.finBasis k (S.repr ⟶ U ⊗ T.repr)).map (oppositeMateEquiv k U S T)) i =
        ∑ j, (c T.dual).homDual j ≫ c T.dual j := by
    set d := (Module.finBasis k (S.repr ⟶ U ⊗ T.repr)).map (oppositeMateEquiv k U S T)
    let u := SimpleClasses.dualReprIso T
    let d' := d.map (Linear.homCongr k u.symm (Iso.refl (S.reprᘁ ⊗ U)))
    have hsum : ∑ i, d.homDual i ≫ d i = ∑ i, d'.homDual i ≫ d' i :=
      Finset.sum_congr rfl fun i _ ↦ by
        simp [d', homDual_map_homCongr, Linear.homCongr_apply, Category.assoc]
    rw [hsum]
    exact d'.sum_homDual_eq (c T.dual) (Linear.comp _ _ _)
  simp_rw [hT]
  exact (Fintype.sum_equiv (Function.Involutive.toPerm _ SimpleClasses.dual_involutive)
    (fun T ↦ ∑ j, (c T.dual).homDual j ≫ c T.dual j)
    (fun R ↦ ∑ j, (c R).homDual j ≫ c R j) (fun _ ↦ rfl)).trans
    (sum_sum_homDual_comp_eq_id (S.reprᘁ ⊗ U) c)

private theorem counitLF_comm {A : C} (b : HalfBraiding A) (U : C) :
    counitLF b ▷ U ≫ (b.β U).hom = inductionβHom k A U ≫ U ◁ counitLF b := by
  rw [← Iso.eq_comp_inv]
  refine inductionObj_whiskerRight_hom_ext fun S ↦ ?_
  have htot : U ◁ counitLF b =
      ∑ T : SimpleClasses C, U ◁ biproduct.π (inductionSummand A) T ≫ U ◁ counitComponent b T := by
    rw [← Category.id_comp (counitLF b), ← biproduct.total]
    simp only [Preadditive.sum_comp, Category.assoc, counitLF, biproduct.ι_desc, whiskerLeft_sum,
      whiskerLeft_comp]
  rw [Category.assoc, htot, ← comp_whiskerRight, counitLF, biproduct.ι_desc]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc,
    ι_whiskerRight_inductionβHom_whiskerLeft_π_assoc]
  simp_rw [inductionβComponent_eq k A U S _ (Module.finBasis k _)]
  simp only [Preadditive.sum_comp, inductionTerm_comp_inv_evaluation, ← Preadditive.comp_sum,
    ← whiskerLeft_sum]
  rw [sum_kernel_eq_evaluation]
  simp only [counitComponent, comp_whiskerRight, whiskerLeft_comp]; monoidal

omit [Field k] [IsAlgClosed k] [Linear k C] [MonoidalLinear k C]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
private theorem unitL_comp_counitLF {A : C} (b : HalfBraiding A) :
    unitL A ≫ counitLF b = 𝟙 A := by
  dsimp only [unitL, counitLF]
  rw [Category.assoc, Category.assoc, Category.assoc, biproduct.ι_desc]
  dsimp only [counitComponent, oppEval]
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  have hβ : u₀.inv ▷ A ≫ (b.β (SimpleClasses.classOf (𝟙_ C)).repr).inv =
      (λ_ A).hom ≫ (ρ_ A).inv ≫ A ◁ u₀.inv := by
    have hunit : (b.β (𝟙_ C)).inv = (λ_ A).hom ≫ (ρ_ A).inv := Iso.inv_ext (by simp)
    rw [b.naturality_inv u₀.inv, hunit, Category.assoc]
  have hex : ((SimpleClasses.classOf (𝟙_ C)).repr ◁ A ◁ (u₀.hom)ᘁ) ≫
        (α_ _ A _).inv ≫ (b.β _).inv ▷ _ =
      (α_ _ A (𝟙_ C)).inv ≫ (b.β _).inv ▷ 𝟙_ C ≫ (A ⊗ _) ◁ (u₀.hom)ᘁ := by
    calc _ = (α_ _ A (𝟙_ C)).inv ≫
              (((SimpleClasses.classOf (𝟙_ C)).repr ⊗ A) ◁ (u₀.hom)ᘁ ≫ (b.β _).inv ▷ _) := by
            monoidal
      _ = _ := by rw [whisker_exchange]
  have hmate_id : (u₀.hom)ᘁ ≫ (u₀.inv)ᘁ = 𝟙 ((𝟙_ C)ᘁ : C) := by
    rw [← comp_rightAdjointMate, u₀.inv_hom_id, rightAdjointMate_id]
  have hv : (u₀.inv ⊗ₘ (𝟙 A ⊗ₘ (u₀.hom)ᘁ)) =
      u₀.inv ▷ (A ⊗ 𝟙_ C) ≫ (SimpleClasses.classOf (𝟙_ C)).repr ◁ A ◁ (u₀.hom)ᘁ := by
    rw [tensorHom_def, id_tensorHom]; rfl
  rw [simpleOppositeExactPairing_evaluation_of_iso_unit u₀, hv, Category.assoc (u₀.inv ▷ _),
    reassoc_of% hex]
  calc _ = 𝟙 _ ⊗≫ (u₀.inv ▷ A ≫ (b.β _).inv) ▷ 𝟙_ C ⊗≫
            A ◁ ((SimpleClasses.classOf (𝟙_ C)).repr ◁ (u₀.hom)ᘁ ≫ (u₀.hom ⊗ₘ (u₀.inv)ᘁ)) ⊗≫
            𝟙 A := by simp only [whiskerLeft_comp]; monoidal
    _ = 𝟙 _ ⊗≫ A ◁ ((u₀.inv ⊗ₘ (u₀.hom)ᘁ) ≫ (u₀.hom ⊗ₘ (u₀.inv)ᘁ)) ⊗≫ 𝟙 A := by
          rw [hβ]; simp only [tensorHom_def, comp_whiskerRight]; monoidal
    _ = 𝟙 A := by
          rw [tensorHom_comp_tensorHom, u₀.inv_hom_id, hmate_id, id_tensorHom_id, whiskerLeft_id]
          monoidal

private theorem inductionMap_unitL_comp_counitLF (X : C) :
    inductionMap (unitL X) ≫ counitLF (inductionHalfBraiding k X) = 𝟙 (inductionObj X) := by
  refine biproduct.hom_ext' _ _ fun S ↦ biproduct.hom_ext _ _ fun T ↦ ?_
  simp only [Category.comp_id, Category.assoc, counitLF, biproduct.ι_map_assoc,
    biproduct.ι_desc_assoc]
  have hcounit : counitComponent (inductionHalfBraiding k X) S =
      S.repr ◁ inductionβHom k X S.reprᘁ ≫ (α_ S.repr S.reprᘁ (inductionObj X)).inv ≫
        oppEval S ▷ inductionObj X ≫ (λ_ (inductionObj X)).hom := by
    have hswap := (inductionHalfBraiding k X).inv_whiskerRight_comp_whiskerLeft (oppEval S)
    rw [inductionHalfBraiding_β_hom] at hswap
    calc _ = (α_ S.repr (inductionObj X) S.reprᘁ).inv ≫
              (((inductionHalfBraiding k X).β S.repr).inv ▷ S.reprᘁ ⊗≫
                inductionObj X ◁ oppEval S ⊗≫ 𝟙 _) := by dsimp [counitComponent]; monoidal
      _ = _ := by rw [hswap]; monoidal
  have hslide : (α_ S.repr S.reprᘁ (inductionObj X)).inv ≫ oppEval S ▷ inductionObj X ≫
        (λ_ (inductionObj X)).hom ≫ biproduct.π (inductionSummand X) T =
      S.repr ◁ S.reprᘁ ◁ biproduct.π (inductionSummand X) T ≫
        (α_ S.repr S.reprᘁ (inductionSummand X T)).inv ≫ oppEval S ▷ inductionSummand X T ≫
        (λ_ (inductionSummand X T)).hom := by
    rw [← leftUnitor_naturality, ← whisker_exchange_assoc, associator_inv_naturality_right_assoc]
  rw [reassoc_of% hcounit, hslide, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  dsimp only [unitL]
  simp only [comp_whiskerRight, Category.assoc, ι_whiskerRight_inductionβHom_whiskerLeft_π]
  by_cases hST : S = T
  · subst hST; rw [biproduct.ι_π_self]
    simpa only [inductionSummand, comp_whiskerRight, Category.assoc] using left_triangle_self k X S
  · rw [biproduct.ι_π_ne _ hST, left_triangle_of_ne k X hST, comp_zero, comp_zero, comp_zero,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp]

private theorem unitL_comp_counitF (X : C) :
    unitL X ≫ (forgetInductionAdjunction k C).counit.app X = 𝟙 X := by
  rw [forgetInductionAdjunction_counit_app]; dsimp only [unitL]
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  let r₀ : (SimpleClasses.classOf (𝟙_ C)).reprᘁ ⟶
      (RightRigidCategory.rightDual (𝟙_ C)).rightDual :=
    @rightAdjointMate C _ _ (𝟙_ C) _ (RightRigidCategory.rightDual (𝟙_ C)) _ u₀.inv
  have hend : biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) ≫
        inductionEndπ X (𝟙_ C) =
      (SimpleClasses.classOf (𝟙_ C)).repr ◁ X ◁ r₀ ≫
        u₀.hom ▷ (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual) := by
    have hdin := inductionEndπ_dinatural k X u₀.inv
    rw [inductionEndπ_repr k X (SimpleClasses.classOf (𝟙_ C))] at hdin
    have h1 := (biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) ≫= hdin) =≫
      u₀.hom ▷ (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual)
    simpa [Category.assoc, ← comp_whiskerRight] using h1
  have hmate_unit : (u₀.hom)ᘁ ≫ r₀ ≫ (rightDualUnitIso C).hom = 𝟙 (𝟙_ C) := by
    dsimp only [r₀]
    rw [rightAdjointMate_eq_rightMate,
      @rightAdjointMate_eq_rightMate C _ _ (𝟙_ C) _ (RightRigidCategory.rightDual (𝟙_ C)) _,
      rightDualUnitIso_hom, ExactPairing.rightDualIso_hom, ← ExactPairing.comp_rightMate,
      ← ExactPairing.comp_rightMate, Category.id_comp, u₀.inv_hom_id]
    exact ExactPairing.rightMate_id exactPairingUnit
  have hex : (SimpleClasses.classOf (𝟙_ C)).repr ◁ X ◁ ((u₀.hom)ᘁ ≫ r₀) ≫
        u₀.hom ▷ (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual) =
      u₀.hom ▷ (X ⊗ 𝟙_ C) ≫ 𝟙_ C ◁ X ◁ ((u₀.hom)ᘁ ≫ r₀) := whisker_exchange _ _
  simp only [Category.assoc]
  calc _ = (λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫ u₀.inv ▷ (X ⊗ 𝟙_ C) ≫
            ((SimpleClasses.classOf (𝟙_ C)).repr ◁ X ◁ ((u₀.hom)ᘁ ≫ r₀) ≫
              u₀.hom ▷ (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual)) ≫
            (λ_ (X ⊗ (RightRigidCategory.rightDual (𝟙_ C)).rightDual)).hom ≫
            X ◁ (rightDualUnitIso C).hom ≫ (ρ_ X).hom := by
          rw [reassoc_of% hend]; simp only [tensorHom_def, whiskerLeft_comp, Category.assoc]
          monoidal
    _ = 𝟙 X ⊗≫ (u₀.inv ≫ u₀.hom) ▷ (X ⊗ 𝟙_ C) ⊗≫
          𝟙_ C ◁ X ◁ ((u₀.hom)ᘁ ≫ r₀ ≫ (rightDualUnitIso C).hom) ⊗≫ 𝟙 X := by
          rw [hex]; simp only [comp_whiskerRight, whiskerLeft_comp]; monoidal
    _ = 𝟙 X := by rw [u₀.inv_hom_id, hmate_unit]; monoidal

/-! ### Public left adjunction API -/

variable (C)

/-- **Left adjunction for centre induction**: `Center.induction k C ⊣ Center.forget C`. This holds
for any fusion category `C` over an algebraically closed field `k` (in arbitrary characteristic
and without choosing a pivotal structure on `C`), making `Center.induction k C` a Frobenius
functor alongside `CategoryTheory.Center.forgetInductionAdjunction`. -/
def inductionForgetAdjunction : induction k C ⊣ forget C :=
  Adjunction.mkOfUnitCounit
    { unit := { app X := unitL X, naturality _ _ f := unitL_naturality f }
      counit :=
        { app Z :=
            { f := counitLF (A := (forget C).obj Z) Z.2
              comm U := (counitLF_comm k (A := (forget C).obj Z) Z.2 U).trans
                (congrArg (· ≫ U ◁ counitLF (A := (forget C).obj Z) Z.2)
                  (inductionHalfBraiding_β_hom k ((forget C).obj Z) U).symm) }
          naturality _ _ h := Center.ext _ _ <| by
            rw [comp_f, comp_f, Functor.comp_map, Functor.id_map, induction_map_f]
            exact counitLF_naturality h.f h.comm }
      left_triangle := NatTrans.ext <| funext fun X ↦ Center.ext _ _ <| by
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
          Functor.whiskerLeft_app, Functor.comp_obj, Functor.id_obj, Category.id_comp]
        dsimp only [NatTrans.id]
        rw [comp_f, id_f]
        exact inductionMap_unitL_comp_counitLF k X
      right_triangle := NatTrans.ext <| funext fun Z ↦
        (congrArg (unitL ((forget C).obj Z) ≫ ·)
          (Category.id_comp (counitLF (A := (forget C).obj Z) Z.2))).trans
          (unitL_comp_counitLF (A := (forget C).obj Z) Z.2) }

/-- `Center.induction k C` is a left adjoint (in particular, it preserves all colimits that exist in
`C`). -/
instance instIsLeftAdjointInduction : (induction k C).IsLeftAdjoint :=
  (inductionForgetAdjunction k C).isLeftAdjoint

/-- Explicit formula for the unit of `inductionForgetAdjunction` at `X`. -/
theorem inductionForgetAdjunction_unit_app (X : C) :
    (inductionForgetAdjunction k C).unit.app X =
      (λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫
        ((SimpleClasses.classOfReprIso (𝟙_ C)).inv ⊗ₘ
          (𝟙 X ⊗ₘ ((SimpleClasses.classOfReprIso (𝟙_ C)).hom)ᘁ)) ≫
        biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) := (rfl)

/-- Reassociated form of `inductionForgetAdjunction_unit_app`.

Stated explicitly because `@[reassoc]` does not unfold `induction` at `reducible` transparency and
would otherwise leave the right-hand side left-associated at `biproduct.ι`. -/
theorem inductionForgetAdjunction_unit_app_assoc (X : C) {W : C}
    (h : (forget C).obj ((induction k C).obj X) ⟶ W) :
    (inductionForgetAdjunction k C).unit.app X ≫ h =
      (λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫
        ((SimpleClasses.classOfReprIso (𝟙_ C)).inv ⊗ₘ
          (𝟙 X ⊗ₘ ((SimpleClasses.classOfReprIso (𝟙_ C)).hom)ᘁ)) ≫
        biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) ≫ h := by
  rw [inductionForgetAdjunction_unit_app]
  exact (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).trans
    (congrArg _ (Category.assoc _ _ _))))

private theorem inductionForgetAdjunction_counit_app_f (Z : Center C) :
    ((inductionForgetAdjunction k C).counit.app Z).f = counitLF Z.2 :=
  rfl

/-- Component of the counit of `inductionForgetAdjunction` on the `S`-summand of
`inductionObj Z.1`. -/
@[simp]
theorem ι_comp_inductionForgetAdjunction_counit_app_f (Z : Center C) (S : SimpleClasses C) :
    biproduct.ι (inductionSummand Z.1) S ≫ ((inductionForgetAdjunction k C).counit.app Z).f =
      (α_ S.repr Z.1 S.reprᘁ).inv ≫ (Z.2.β S.repr).inv ▷ S.reprᘁ ≫ (α_ Z.1 S.repr S.reprᘁ).hom ≫
        Z.1 ◁ @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr) ≫
        (ρ_ Z.1).hom := by
  rw [inductionForgetAdjunction_counit_app_f]
  simp [counitLF, counitComponent]

/-- Reassociated form of `ι_comp_inductionForgetAdjunction_counit_app_f`.

Stated explicitly because `@[reassoc (attr := simp)]` does not unfold `induction` at `reducible`
transparency and would otherwise produce a left-associated LHS rejected by `simpNF`. -/
@[simp]
theorem ι_comp_inductionForgetAdjunction_counit_app_f_assoc (Z : Center C) (S : SimpleClasses C)
    {W : C} (h : Z.1 ⟶ W) :
    biproduct.ι (inductionSummand Z.1) S ≫ ((inductionForgetAdjunction k C).counit.app Z).f ≫ h =
      (α_ S.repr Z.1 S.reprᘁ).inv ≫ (Z.2.β S.repr).inv ▷ S.reprᘁ ≫ (α_ Z.1 S.repr S.reprᘁ).hom ≫
        Z.1 ◁ @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr) ≫
        (ρ_ Z.1).hom ≫ h := by
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [ι_comp_inductionForgetAdjunction_counit_app_f]
  simp only [Category.assoc]

/-- The unit of `inductionForgetAdjunction` splits the counit of `forgetInductionAdjunction`. -/
@[reassoc]
theorem inductionForgetAdjunction_unit_app_comp_forgetInductionAdjunction_counit_app (X : C) :
    (inductionForgetAdjunction k C).unit.app X ≫ (forgetInductionAdjunction k C).counit.app X =
      𝟙 X :=
  unitL_comp_counitF k X

/-- Every component of `(inductionForgetAdjunction k C).unit` is a split monomorphism. -/
instance instIsSplitMonoInductionForgetAdjunctionUnitApp (X : C) :
    IsSplitMono ((inductionForgetAdjunction k C).unit.app X) :=
  IsSplitMono.mk'
    { retraction := (forgetInductionAdjunction k C).counit.app X
      id := inductionForgetAdjunction_unit_app_comp_forgetInductionAdjunction_counit_app k C X }

/-- Every component of `(forgetInductionAdjunction k C).counit` is a split epimorphism. -/
instance instIsSplitEpiForgetInductionAdjunctionCounitApp (X : C) :
    IsSplitEpi ((forgetInductionAdjunction k C).counit.app X) :=
  IsSplitEpi.mk'
    { section_ := (inductionForgetAdjunction k C).unit.app X
      id := inductionForgetAdjunction_unit_app_comp_forgetInductionAdjunction_counit_app k C X }

end Fusion

end CategoryTheory.Center
