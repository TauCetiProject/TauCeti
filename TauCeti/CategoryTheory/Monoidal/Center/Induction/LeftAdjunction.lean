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

Let `C` be a fusion category over an algebraically closed field `k`: a `k`-linear, finite
semisimple, rigid abelian monoidal category with simple tensor unit, finitely many isomorphism
classes of simple objects, and finite-dimensional morphism spaces. In
`TauCeti.CategoryTheory.Monoidal.Center.Induction.Adjunction`, the induction functor
`Center.induction k C : C ⥤ Center C` was shown to be right adjoint to `Center.forget C` without
requiring simplicity of `𝟙_ C` or a pivotal structure.

When `𝟙_ C` is simple, every simple representative `S.repr` carries its canonical opposite exact
pairing `TauCeti.simpleOppositeExactPairing S.repr : ExactPairing S.reprᘁ S.repr`
(`TauCeti.CategoryTheory.Semisimple.OppositePairing`), whose coevaluation `𝟙_ C ⟶ S.reprᘁ ⊗ S.repr`
is the unique section of `ε_ S.repr S.reprᘁ`. Using these pairings, this file constructs the **left
adjunction** `inductionForgetAdjunction k C : Center.induction k C ⊣ Center.forget C` — making
`Center.induction k C` a Frobenius (ambidextrous) functor — still without choosing a pivotal
structure on `C`:

* the unit `X ⟶ inductionObj X` embeds `X` into the unit-class summand `S₀.repr ⊗ X ⊗ S₀.reprᘁ`
  via `(classOfReprIso (𝟙_ C)).inv` and `(rightDualIsoUnitOfIso (classOfReprIso (𝟙_ C))).inv`, and
  splits `(forgetInductionAdjunction k C).counit.app X` (`Center.induction k C` is therefore
  faithful);
* the counit `inductionCenterObj k Z.1 ⟶ Z` acts on the `S`-summand `S.repr ⊗ Z.1 ⊗ S.reprᘁ` by
  moving `Z.1` to the left of `S.repr` via `(Z.2.β S.repr).inv` and contracting `S.repr ⊗ S.reprᘁ`
  via the evaluation of `simpleOppositeExactPairing S.repr`.

Simplicity of `𝟙_ C` is necessary here: in the multifusion category `Vec_k × Vec_k`, the tensor
unit `(k, k)` is not simple and `(k, 0) ⊗ (k, 0)ᘁ` cannot pair surjectively onto `(k, k)`.

## Main declarations

* `CategoryTheory.Center.inductionForgetAdjunction` and
  `CategoryTheory.Center.instIsLeftAdjointInduction`: the left adjunction
  `Center.induction k C ⊣ Center.forget C`, with unit and counit characterized by
  `CategoryTheory.Center.inductionForgetAdjunction_unit_app` and
  `CategoryTheory.Center.ι_comp_inductionForgetAdjunction_counit_app_f`;
* the unit of `inductionForgetAdjunction` splits the counit of `forgetInductionAdjunction`
  (`inductionForgetAdjunction_unit_app_comp_forgetInductionAdjunction_counit_app`);
* `CategoryTheory.Center.instIsSplitMonoInductionForgetAdjunctionUnitApp` and
  `CategoryTheory.Center.instFaithfulInduction`: components of the unit are split monomorphisms, so
  `Center.induction k C` is faithful.

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

section Helpers

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [RightRigidCategory C]
  [Fintype (SimpleClasses C)]

/-- Morphisms out of `inductionObj X ⊗ U` agree once they agree on every summand inclusion
`biproduct.ι (inductionSummand X) S ▷ U`. -/
private theorem inductionObj_whiskerRight_hom_ext {X U W : C}
    {f₁ f₂ : inductionObj X ⊗ U ⟶ W}
    (h : ∀ S : SimpleClasses C,
      biproduct.ι (inductionSummand X) S ▷ U ≫ f₁ =
        biproduct.ι (inductionSummand X) S ▷ U ≫ f₂) :
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

/-- Pulling `A` to the left through a single `inductionTerm` followed by a half-braiding inverse
and evaluation factors `(b.β S.repr).inv` to the front. -/
private theorem inductionTerm_comp_inv_evaluation {A : C} (b : HalfBraiding A) (U : C)
    (S T : SimpleClasses C) (g : U ⊗ T.repr ⟶ S.repr) (f : S.repr ⟶ U ⊗ T.repr) :
    inductionTerm k A g f ≫
        U ◁ ((α_ T.repr A T.reprᘁ).inv ≫ (b.β T.repr).inv ▷ T.reprᘁ ≫
          (α_ A T.repr T.reprᘁ).hom ≫
          A ◁ @ExactPairing.evaluation C _ _ T.reprᘁ T.repr
            (simpleOppositeExactPairing T.repr) ≫ (ρ_ A).hom) ≫
        (b.β U).inv =
      ((α_ S.repr A S.reprᘁ).inv ▷ U ≫ (α_ (S.repr ⊗ A) S.reprᘁ U).hom ≫
        (b.β S.repr).inv ▷ (S.reprᘁ ⊗ U) ≫ (α_ A S.repr (S.reprᘁ ⊗ U)).hom) ≫
        A ◁ (𝟙 (S.repr ⊗ S.reprᘁ ⊗ U) ⊗≫ f ▷ (S.reprᘁ ⊗ U) ⊗≫
          U ◁ T.repr ◁ inductionMate k U g ⊗≫
          U ◁ @ExactPairing.evaluation C _ _ T.reprᘁ T.repr
            (simpleOppositeExactPairing T.repr) ⊗≫ 𝟙 U) := by
  let εT := @ExactPairing.evaluation C _ _ T.reprᘁ T.repr (simpleOppositeExactPairing T.repr)
  rw [inductionTerm_apply]
  have hmon : U ◁ ((b.β T.repr).inv ▷ T.reprᘁ) ⊗≫ U ◁ A ◁ εT ⊗≫ (b.β U).inv =
      𝟙 (U ⊗ (T.repr ⊗ A) ⊗ T.reprᘁ) ⊗≫ (b.β (U ⊗ T.repr)).inv ▷ T.reprᘁ ⊗≫
        A ◁ U ◁ εT ⊗≫ 𝟙 (A ⊗ U) := by
    calc U ◁ ((b.β T.repr).inv ▷ T.reprᘁ) ⊗≫ U ◁ A ◁ εT ⊗≫ (b.β U).inv
        = 𝟙 (U ⊗ (T.repr ⊗ A) ⊗ T.reprᘁ) ⊗≫ U ◁ ((b.β T.repr).inv ▷ T.reprᘁ) ⊗≫
            ((U ⊗ A) ◁ εT ≫ (b.β U).inv ▷ 𝟙_ C) ⊗≫ 𝟙 (A ⊗ U) := by monoidal
      _ = 𝟙 (U ⊗ (T.repr ⊗ A) ⊗ T.reprᘁ) ⊗≫
            (U ◁ (b.β T.repr).inv ⊗≫ (b.β U).inv ▷ T.repr) ▷ T.reprᘁ ⊗≫
            A ◁ U ◁ εT ⊗≫ 𝟙 (A ⊗ U) := by
            rw [whisker_exchange]
            monoidal
      _ = _ := by
            rw [b.monoidal_inv U T.repr]
            simp only [comp_whiskerRight]
            monoidal
  calc _ = 𝟙 ((S.repr ⊗ A ⊗ S.reprᘁ) ⊗ U) ⊗≫ f ▷ A ▷ S.reprᘁ ▷ U ⊗≫
            U ◁ T.repr ◁ A ◁ inductionMate k U g ⊗≫
            (U ◁ ((b.β T.repr).inv ▷ T.reprᘁ) ⊗≫ U ◁ A ◁ εT ⊗≫ (b.β U).inv) := by
          simp only [whiskerLeft_comp, εT]
          monoidal
    _ = 𝟙 ((S.repr ⊗ A ⊗ S.reprᘁ) ⊗ U) ⊗≫ f ▷ A ▷ (S.reprᘁ ⊗ U) ⊗≫
          (((U ⊗ T.repr) ⊗ A) ◁ inductionMate k U g ≫
            (b.β (U ⊗ T.repr)).inv ▷ T.reprᘁ) ⊗≫
          A ◁ U ◁ εT ⊗≫ 𝟙 (A ⊗ U) := by
          rw [hmon]
          monoidal
    _ = 𝟙 ((S.repr ⊗ A ⊗ S.reprᘁ) ⊗ U) ⊗≫
          ((f ▷ A ≫ (b.β (U ⊗ T.repr)).inv) ▷ (S.reprᘁ ⊗ U)) ⊗≫
          A ◁ U ◁ T.repr ◁ inductionMate k U g ⊗≫ A ◁ U ◁ εT ⊗≫ 𝟙 (A ⊗ U) := by
          rw [whisker_exchange]
          simp only [comp_whiskerRight]
          monoidal
    _ = _ := by
          rw [b.naturality_inv f]
          simp only [comp_whiskerRight, εT]
          monoidal

/-- Frobenius reciprocity isomorphism `(S.repr ⟶ U ⊗ T.repr) ≃ₗ[k] (T.reprᘁ ⟶ S.reprᘁ ⊗ U)` built
from `simpleOppositeExactPairing S.repr` and `simpleOppositeExactPairing T.repr`. -/
private def oppositeMateEquiv (U : C) (S T : SimpleClasses C) :
    (S.repr ⟶ U ⊗ T.repr) ≃ₗ[k] (T.reprᘁ ⟶ S.reprᘁ ⊗ U) :=
  let _ : ExactPairing S.reprᘁ S.repr := simpleOppositeExactPairing S.repr
  let _ : ExactPairing T.reprᘁ T.repr := simpleOppositeExactPairing T.repr
  (tensorRightHomLinearEquiv k S.repr T.reprᘁ T.repr U).symm.trans
    (tensorLeftHomLinearEquiv k T.reprᘁ S.reprᘁ S.repr U)

private theorem oppositeMateEquiv_apply (U : C) (S T : SimpleClasses C)
    (f : S.repr ⟶ U ⊗ T.repr) :
    oppositeMateEquiv k U S T f =
      𝟙 (T.reprᘁ : C) ⊗≫ @ExactPairing.coevaluation C _ _ S.reprᘁ S.repr
          (simpleOppositeExactPairing S.repr) ▷ T.reprᘁ ⊗≫
        S.reprᘁ ◁ f ▷ T.reprᘁ ⊗≫
        S.reprᘁ ◁ U ◁ @ExactPairing.evaluation C _ _ T.reprᘁ T.repr
          (simpleOppositeExactPairing T.repr) ⊗≫ 𝟙 ((S.reprᘁ : C) ⊗ U) := by
  let _ : ExactPairing S.reprᘁ S.repr := simpleOppositeExactPairing S.repr
  let _ : ExactPairing T.reprᘁ T.repr := simpleOppositeExactPairing T.repr
  rw [oppositeMateEquiv, LinearEquiv.trans_apply, tensorLeftHomLinearEquiv_apply,
    tensorRightHomLinearEquiv_symm_apply]
  dsimp only [tensorRightHomEquiv, tensorLeftHomEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  monoidal

/-- Transposing the half-braiding kernel via `tensorLeftHomEquiv` factors it into
`inductionMate k U g` followed by `oppositeMateEquiv k U S T f`. -/
private theorem tensorLeftHomEquiv_kernel (U : C) (S T : SimpleClasses C)
    (g : U ⊗ T.repr ⟶ S.repr) (f : S.repr ⟶ U ⊗ T.repr) :
    @tensorLeftHomEquiv C _ _ (S.reprᘁ ⊗ U) S.reprᘁ S.repr U (simpleOppositeExactPairing S.repr)
        (𝟙 (S.repr ⊗ S.reprᘁ ⊗ U) ⊗≫ f ▷ (S.reprᘁ ⊗ U) ⊗≫
          U ◁ T.repr ◁ inductionMate k U g ⊗≫
          U ◁ @ExactPairing.evaluation C _ _ T.reprᘁ T.repr
            (simpleOppositeExactPairing T.repr) ⊗≫ 𝟙 U) =
      inductionMate k U g ≫ oppositeMateEquiv k U S T f := by
  let pS : ExactPairing S.reprᘁ S.repr := simpleOppositeExactPairing S.repr
  let εT := @ExactPairing.evaluation C _ _ T.reprᘁ T.repr (simpleOppositeExactPairing T.repr)
  rw [oppositeMateEquiv_apply]
  dsimp only [tensorLeftHomEquiv, Equiv.coe_fn_mk]
  have hex1 : (S.reprᘁ : C) ◁ (f ▷ ((S.reprᘁ : C) ⊗ U)) ⊗≫
        (S.reprᘁ : C) ◁ U ◁ T.repr ◁ inductionMate k U g =
      𝟙 ((S.reprᘁ : C) ⊗ S.repr ⊗ (S.reprᘁ : C) ⊗ U) ⊗≫
        ((S.reprᘁ : C) ⊗ S.repr) ◁ inductionMate k U g ⊗≫
        ((S.reprᘁ : C) ◁ f) ▷ T.reprᘁ ⊗≫
        𝟙 ((S.reprᘁ : C) ⊗ U ⊗ T.repr ⊗ T.reprᘁ) := by
    calc _ = 𝟙 ((S.reprᘁ : C) ⊗ S.repr ⊗ (S.reprᘁ : C) ⊗ U) ⊗≫
              (S.reprᘁ : C) ◁ (f ▷ ((S.reprᘁ : C) ⊗ U) ≫
              (U ⊗ T.repr) ◁ inductionMate k U g) ⊗≫
              𝟙 ((S.reprᘁ : C) ⊗ U ⊗ T.repr ⊗ T.reprᘁ) := by monoidal
      _ = _ := by rw [← whisker_exchange, whiskerLeft_comp]; monoidal
  have hex2 : @ExactPairing.coevaluation C _ _ S.reprᘁ S.repr pS ▷ ((S.reprᘁ : C) ⊗ U) ⊗≫
        ((S.reprᘁ : C) ⊗ S.repr) ◁ inductionMate k U g =
      𝟙 (𝟙_ C ⊗ (S.reprᘁ : C) ⊗ U) ⊗≫ (𝟙_ C ◁ inductionMate k U g ≫
        @ExactPairing.coevaluation C _ _ S.reprᘁ S.repr pS ▷ T.reprᘁ) ⊗≫
        𝟙 (((S.reprᘁ : C) ⊗ S.repr) ⊗ T.reprᘁ) := by
    calc _ = 𝟙 _ ⊗≫ (@ExactPairing.coevaluation C _ _ S.reprᘁ S.repr pS ▷ ((S.reprᘁ : C) ⊗ U) ≫
              ((S.reprᘁ : C) ⊗ S.repr) ◁ inductionMate k U g) ⊗≫ 𝟙 _ := by monoidal
      _ = _ := by rw [← whisker_exchange]
  calc _ = 𝟙 ((S.reprᘁ : C) ⊗ U) ⊗≫
            @ExactPairing.coevaluation C _ _ S.reprᘁ S.repr pS ▷ ((S.reprᘁ : C) ⊗ U) ⊗≫
            ((S.reprᘁ : C) ◁ (f ▷ ((S.reprᘁ : C) ⊗ U)) ⊗≫
              (S.reprᘁ : C) ◁ U ◁ T.repr ◁ inductionMate k U g) ⊗≫
            (S.reprᘁ : C) ◁ U ◁ εT ⊗≫ 𝟙 ((S.reprᘁ : C) ⊗ U) := by
          simp only [εT]
          monoidal
    _ = 𝟙 ((S.reprᘁ : C) ⊗ U) ⊗≫
          (@ExactPairing.coevaluation C _ _ S.reprᘁ S.repr pS ▷ ((S.reprᘁ : C) ⊗ U) ⊗≫
            ((S.reprᘁ : C) ⊗ S.repr) ◁ inductionMate k U g) ⊗≫
          ((S.reprᘁ : C) ◁ f) ▷ T.reprᘁ ⊗≫ (S.reprᘁ : C) ◁ U ◁ εT ⊗≫
          𝟙 ((S.reprᘁ : C) ⊗ U) := by
          rw [hex1]; monoidal
    _ = _ := by
          rw [hex2]
          simp only [εT]
          monoidal

/-- Pairing `oppositeMateEquiv k U S T f` with `inductionMate k U g` and tracing against `T.repr`
computes the trace of `f ≫ g` against `S.repr`. -/
private theorem coevaluation_comp_oppositeMateEquiv_comp_inductionMate (U : C)
    (S T : SimpleClasses C) (f : S.repr ⟶ U ⊗ T.repr) (g : U ⊗ T.repr ⟶ S.repr) :
    @ExactPairing.coevaluation C _ _ T.reprᘁ T.repr (simpleOppositeExactPairing T.repr) ≫
        (oppositeMateEquiv k U S T f ≫ inductionMate k U g) ▷ T.repr ≫ ε_ T.repr T.reprᘁ =
      @ExactPairing.coevaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr) ≫
        S.reprᘁ ◁ (f ≫ g) ≫ ε_ S.repr S.reprᘁ := by
  let pS : ExactPairing S.reprᘁ S.repr := simpleOppositeExactPairing S.repr
  let pT : ExactPairing T.reprᘁ T.repr := simpleOppositeExactPairing T.repr
  rw [comp_whiskerRight_assoc, inductionMate_whiskerRight_evaluation]
  have hleft : @ExactPairing.coevaluation C _ _ T.reprᘁ T.repr pT ≫
        oppositeMateEquiv k U S T f ▷ T.repr =
      @ExactPairing.coevaluation C _ _ S.reprᘁ S.repr pS ≫ S.reprᘁ ◁ f ≫
        (α_ S.reprᘁ U T.repr).inv := by
    rw [oppositeMateEquiv_apply]
    calc _ = 𝟙 (𝟙_ C) ⊗≫ (𝟙_ C ◁ @ExactPairing.coevaluation C _ _ T.reprᘁ T.repr pT ≫
              (@ExactPairing.coevaluation C _ _ S.reprᘁ S.repr pS ≫ S.reprᘁ ◁ f) ▷
                (T.reprᘁ ⊗ T.repr)) ⊗≫
              S.reprᘁ ◁ U ◁ (@ExactPairing.evaluation C _ _ T.reprᘁ T.repr pT ▷ T.repr) ⊗≫
              𝟙 (((S.reprᘁ : C) ⊗ U) ⊗ T.repr) := by
            simp only [comp_whiskerRight]
            monoidal
      _ = 𝟙 (𝟙_ C) ⊗≫ @ExactPairing.coevaluation C _ _ S.reprᘁ S.repr pS ≫ S.reprᘁ ◁ f ⊗≫
            S.reprᘁ ◁ U ◁ ((T.repr : C) ◁ @ExactPairing.coevaluation C _ _ T.reprᘁ T.repr pT ⊗≫
              @ExactPairing.evaluation C _ _ T.reprᘁ T.repr pT ▷ T.repr) ⊗≫
            𝟙 (((S.reprᘁ : C) ⊗ U) ⊗ T.repr) := by
            rw [whisker_exchange]
            monoidal
      _ = _ := by
            have hzig := @ExactPairing.coevaluation_evaluation'' C _ _ T.reprᘁ T.repr pT
            rw [hzig]
            monoidal
  rw [reassoc_of% hleft, Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc]

variable [IsAlgClosed k] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- Under `oppositeMateEquiv k U S T`, the composition-dual basis of `b` is `inductionMate k U`
applied to `b.homDual`. -/
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
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, whiskerLeft_id, Category.id_comp,
      simpleOppositeExactPairing_coevaluation_comp_evaluation] at htr
    have hc1 : c = 1 := by
      have hsub : (c - 1) • 𝟙 (𝟙_ C) = 0 := by rw [sub_smul, one_smul, htr, sub_self]
      exact sub_eq_zero.1 ((smul_eq_zero.1 hsub).resolve_right (CategoryTheory.id_ne_zero (𝟙_ C)))
    simp [← hc, hc1]
  · simp only [hij, ↓reduceIte, MonoidalPreadditive.whiskerLeft_zero, comp_zero, zero_comp] at htr
    have hc0 : c = 0 := (smul_eq_zero.1 htr).resolve_right (CategoryTheory.id_ne_zero (𝟙_ C))
    simp [← hc, hc0, hij]

/-- Off-diagonal vanishing for the left triangle identity of `inductionForgetAdjunction`. -/
private theorem left_triangle_of_ne (X : C) {S T : SimpleClasses C} (hST : S ≠ T) :
    inductionβComponent k X S.reprᘁ (SimpleClasses.classOf (𝟙_ C)) T = 0 := by
  let _ : ExactPairing S.reprᘁ S.repr := simpleOppositeExactPairing S.repr
  have : Subsingleton (S.repr ⟶ T.repr) := SimpleClasses.homOrthogonal_repr hST
  let e : ((SimpleClasses.classOf (𝟙_ C)).repr ⟶ S.reprᘁ ⊗ T.repr) ≃ (S.repr ⟶ T.repr) :=
    (Iso.homCongr (SimpleClasses.classOfReprIso (𝟙_ C)) (Iso.refl _)).trans
      ((tensorLeftHomEquiv (𝟙_ C) S.reprᘁ S.repr T.repr).symm.trans
        (Iso.homCongr (ρ_ S.repr) (Iso.refl T.repr)))
  have : Subsingleton ((SimpleClasses.classOf (𝟙_ C)).repr ⟶ S.reprᘁ ⊗ T.repr) := e.subsingleton
  rw [inductionβComponent_eq k X S.reprᘁ _ T (Module.finBasis k _)]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [Subsingleton.elim (Module.finBasis k _ i) 0, map_zero]

/-- One-element `k`-basis of `(classOf (𝟙_ C)).repr ⟶ S.reprᘁ ⊗ S.repr` spanned by the canonical
opposite coevaluation of `S.repr`. -/
private def unitClassCoevaluationBasis (S : SimpleClasses C) :
    Basis (Fin 1) k ((SimpleClasses.classOf (𝟙_ C)).repr ⟶ S.reprᘁ ⊗ S.repr) :=
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  let ηS := @ExactPairing.coevaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr)
  Basis.mk (v := fun _ ↦ u₀.hom ≫ ηS)
    (linearIndependent_unique_iff.2 fun h ↦ by
      have h1 := u₀.inv ≫= h =≫ ε_ S.repr S.reprᘁ
      rw [zero_comp, comp_zero, Category.assoc, u₀.inv_hom_id_assoc] at h1
      dsimp only [ηS] at h1
      rw [simpleOppositeExactPairing_coevaluation_comp_evaluation] at h1
      exact CategoryTheory.id_ne_zero (𝟙_ C) h1)
    (by
      rintro f -
      obtain ⟨c, hc⟩ := hom_from_tensorUnit_eq_smul_simpleOppositeExactPairing_coevaluation k
        (u₀.inv ≫ f)
      rw [Set.range_const, Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      have hf : f = u₀.hom ≫ (u₀.inv ≫ f) := by rw [Iso.hom_inv_id_assoc]
      dsimp only [ηS]
      rw [hf, hc, Linear.comp_smul])

private theorem unitClassCoevaluationBasis_homDual (S : SimpleClasses C) :
    (unitClassCoevaluationBasis k S).homDual 0 =
      ε_ S.repr S.reprᘁ ≫ (SimpleClasses.classOfReprIso (𝟙_ C)).inv := by
  refine (((unitClassCoevaluationBasis k S).eq_homDual_iff _ 0).2 fun i ↦ ?_).symm
  simp only [Fin.fin_one_eq_zero i, ↓reduceIte, unitClassCoevaluationBasis, Basis.mk_apply,
    Category.assoc]
  rw [reassoc_of% (simpleOppositeExactPairing_coevaluation_comp_evaluation S.repr),
    Iso.hom_inv_id]

omit [IsAlgClosed k] [IsFiniteSemisimpleCategory C]
  [∀ (X Y : C), FiniteDimensional k (X ⟶ Y)] in
private theorem rightDualIsoUnitOfIso_inv_whiskerRight_comp_inductionMate (S : SimpleClasses C) :
    (rightDualIsoUnitOfIso (SimpleClasses.classOfReprIso (𝟙_ C))).inv ▷ S.reprᘁ ≫
        inductionMate k S.reprᘁ
          (ε_ S.repr S.reprᘁ ≫ (SimpleClasses.classOfReprIso (𝟙_ C)).inv) =
      (λ_ S.reprᘁ).hom := by
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  let v₀ := rightDualIsoUnitOfIso u₀
  refine ExactPairing.rightHom_ext (X := S.repr) ?_
  have hex : (v₀.inv ▷ S.reprᘁ) ▷ S.repr ≫ (α_ _ S.reprᘁ S.repr).hom ≫
        (SimpleClasses.classOf (𝟙_ C)).reprᘁ ◁ (ε_ S.repr S.reprᘁ ≫ u₀.inv) =
      (α_ (𝟙_ C) S.reprᘁ S.repr).hom ≫ 𝟙_ C ◁ (ε_ S.repr S.reprᘁ ≫ u₀.inv) ≫
        v₀.inv ▷ (SimpleClasses.classOf (𝟙_ C)).repr := by
    calc _ = 𝟙 _ ⊗≫ (v₀.inv ▷ (S.reprᘁ ⊗ S.repr) ≫
              (SimpleClasses.classOf (𝟙_ C)).reprᘁ ◁ (ε_ S.repr S.reprᘁ ≫ u₀.inv)) := by monoidal
      _ = _ := by rw [whisker_exchange]; monoidal
  calc (v₀.inv ▷ S.reprᘁ ≫ inductionMate k S.reprᘁ (ε_ S.repr S.reprᘁ ≫ u₀.inv)) ▷ S.repr ≫
          ε_ S.repr S.reprᘁ
      = ((v₀.inv ▷ S.reprᘁ) ▷ S.repr ≫ (α_ _ S.reprᘁ S.repr).hom ≫
          (SimpleClasses.classOf (𝟙_ C)).reprᘁ ◁ (ε_ S.repr S.reprᘁ ≫ u₀.inv)) ≫
          ε_ (SimpleClasses.classOf (𝟙_ C)).repr _ := by
        rw [comp_whiskerRight_assoc, inductionMate_whiskerRight_evaluation]
        simp only [Category.assoc]
    _ = (α_ (𝟙_ C) S.reprᘁ S.repr).hom ≫ 𝟙_ C ◁ (ε_ S.repr S.reprᘁ ≫ u₀.inv) ≫
          (v₀.inv ▷ (SimpleClasses.classOf (𝟙_ C)).repr ≫
            ε_ (SimpleClasses.classOf (𝟙_ C)).repr _) := by
        rw [hex, Category.assoc, Category.assoc]
    _ = (λ_ S.reprᘁ).hom ▷ S.repr ≫ ε_ S.repr S.reprᘁ := by
        rw [rightDualIsoUnitOfIso_inv_whiskerRight_evaluation u₀,
          leftUnitor_naturality_assoc, Category.assoc, u₀.inv_hom_id, Category.comp_id]
        monoidal

/-- Diagonal evaluation for the left triangle identity of `inductionForgetAdjunction`. -/
private theorem left_triangle_self (X : C) (S : SimpleClasses C) :
    S.repr ◁ (((λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫
        ((SimpleClasses.classOfReprIso (𝟙_ C)).inv ⊗ₘ
          (𝟙 X ⊗ₘ (rightDualIsoUnitOfIso (SimpleClasses.classOfReprIso (𝟙_ C))).inv))) ▷
        S.reprᘁ ≫
      inductionβComponent k X S.reprᘁ (SimpleClasses.classOf (𝟙_ C)) S) ≫
      (α_ S.repr S.reprᘁ (S.repr ⊗ X ⊗ S.reprᘁ)).inv ≫
      @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr) ▷
        (S.repr ⊗ X ⊗ S.reprᘁ) ≫
      (λ_ (S.repr ⊗ X ⊗ S.reprᘁ)).hom = 𝟙 (S.repr ⊗ X ⊗ S.reprᘁ) := by
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  let v₀ := rightDualIsoUnitOfIso u₀
  let pS : ExactPairing S.reprᘁ S.repr := simpleOppositeExactPairing S.repr
  let ηS := @ExactPairing.coevaluation C _ _ S.reprᘁ S.repr pS
  let εS := @ExactPairing.evaluation C _ _ S.reprᘁ S.repr pS
  have hinner : ((λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫ (u₀.inv ⊗ₘ (𝟙 X ⊗ₘ v₀.inv))) ▷ S.reprᘁ ≫
        inductionTerm k X (ε_ S.repr S.reprᘁ ≫ u₀.inv) (u₀.hom ≫ ηS) =
      (λ_ (X ⊗ S.reprᘁ)).inv ≫ ηS ▷ (X ⊗ S.reprᘁ) ≫ (α_ S.reprᘁ S.repr (X ⊗ S.reprᘁ)).hom := by
    rw [inductionTerm_apply]
    have hex : (((SimpleClasses.classOf (𝟙_ C)).repr ◁ X ◁ v₀.inv) ▷ S.reprᘁ) ⊗≫
          (u₀.hom ≫ ηS) ▷ X ▷ (SimpleClasses.classOf (𝟙_ C)).reprᘁ ▷ S.reprᘁ =
        𝟙 _ ⊗≫ ((u₀.hom ≫ ηS) ▷ (X ⊗ 𝟙_ C)) ▷ S.reprᘁ ⊗≫
          (S.reprᘁ ⊗ S.repr) ◁ X ◁ (v₀.inv ▷ S.reprᘁ) ⊗≫ 𝟙 _ := by
      calc _ = (((SimpleClasses.classOf (𝟙_ C)).repr ◁ (X ◁ v₀.inv) ≫
                (u₀.hom ≫ ηS) ▷ (X ⊗ _)) ▷ S.reprᘁ) ⊗≫ 𝟙 _ := by monoidal
        _ = (((u₀.hom ≫ ηS) ▷ (X ⊗ 𝟙_ C) ≫ (S.reprᘁ ⊗ S.repr) ◁ (X ◁ v₀.inv)) ▷ S.reprᘁ) ⊗≫
              𝟙 _ := by rw [← whisker_exchange]
        _ = _ := by simp only [comp_whiskerRight]; monoidal
    calc _ = 𝟙 _ ⊗≫ (u₀.inv ▷ (X ⊗ 𝟙_ C)) ▷ S.reprᘁ ⊗≫
              ((((SimpleClasses.classOf (𝟙_ C)).repr ◁ X ◁ v₀.inv) ▷ S.reprᘁ) ⊗≫
                (u₀.hom ≫ ηS) ▷ X ▷ (SimpleClasses.classOf (𝟙_ C)).reprᘁ ▷ S.reprᘁ) ⊗≫
              S.reprᘁ ◁ S.repr ◁ X ◁
                inductionMate k S.reprᘁ (ε_ S.repr S.reprᘁ ≫ u₀.inv) ⊗≫ 𝟙 _ := by
            simp only [tensorHom_def, comp_whiskerRight]
            monoidal
      _ = 𝟙 _ ⊗≫ ((u₀.inv ≫ u₀.hom ≫ ηS) ▷ (X ⊗ 𝟙_ C)) ▷ S.reprᘁ ⊗≫
            S.reprᘁ ◁ S.repr ◁ X ◁
              (v₀.inv ▷ S.reprᘁ ≫ inductionMate k S.reprᘁ (ε_ S.repr S.reprᘁ ≫ u₀.inv)) ⊗≫
            𝟙 _ := by
            rw [hex]
            simp only [comp_whiskerRight, whiskerLeft_comp]
            monoidal
      _ = _ := by
            rw [u₀.inv_hom_id_assoc, rightDualIsoUnitOfIso_inv_whiskerRight_comp_inductionMate k S]
            monoidal
  rw [inductionβComponent_eq k X S.reprᘁ _ S (unitClassCoevaluationBasis k S), Fin.sum_univ_one,
    unitClassCoevaluationBasis_homDual, unitClassCoevaluationBasis, Basis.mk_apply]
  dsimp only [u₀, v₀, ηS, pS] at hinner
  rw [hinner]
  have hzig := @ExactPairing.coevaluation_evaluation'' C _ _ S.reprᘁ S.repr pS
  calc _ = 𝟙 _ ⊗≫ (S.repr ◁ ηS ⊗≫ εS ▷ S.repr) ▷ (X ⊗ S.reprᘁ) ⊗≫ 𝟙 _ := by
          simp only [ηS, εS, whiskerLeft_comp]
          monoidal
    _ = 𝟙 (S.repr ⊗ X ⊗ S.reprᘁ) := by
          dsimp only [ηS, εS]
          rw [hzig]
          monoidal

end OppositeMate

section Fusion

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)] [Fintype (SimpleClasses C)]
  [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]

/-- Underlying morphism `X ⟶ inductionObj X` of `(inductionForgetAdjunction k C).unit.app X`,
embedding `X` into the unit-class summand `S₀.repr ⊗ X ⊗ S₀.reprᘁ`. -/
private def unitL (X : C) : X ⟶ inductionObj X :=
  (λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫
    ((SimpleClasses.classOfReprIso (𝟙_ C)).inv ⊗ₘ
      (𝟙 X ⊗ₘ (rightDualIsoUnitOfIso (SimpleClasses.classOfReprIso (𝟙_ C))).inv)) ≫
    biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C))

omit [Field k] [IsAlgClosed k] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] in
private theorem unitL_naturality {X X' : C} (f : X ⟶ X') :
    f ≫ unitL X' = unitL X ≫ inductionMap f := by
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  let v₀ := rightDualIsoUnitOfIso u₀
  have hmid : (u₀.inv ⊗ₘ (𝟙 X ⊗ₘ v₀.inv)) ≫ (SimpleClasses.classOf (𝟙_ C)).repr ◁ f ▷
        (SimpleClasses.classOf (𝟙_ C)).reprᘁ =
      (𝟙 (𝟙_ C) ⊗ₘ (f ⊗ₘ 𝟙 (𝟙_ C))) ≫ (u₀.inv ⊗ₘ (𝟙 X' ⊗ₘ v₀.inv)) := by
    have h1 : (SimpleClasses.classOf (𝟙_ C)).repr ◁ f ▷ (SimpleClasses.classOf (𝟙_ C)).reprᘁ =
        𝟙 (SimpleClasses.classOf (𝟙_ C)).repr ⊗ₘ
          (f ⊗ₘ 𝟙 (SimpleClasses.classOf (𝟙_ C)).reprᘁ) := by
      simp [tensorHom_def]
    rw [h1, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, Category.id_comp, Category.comp_id,
      Category.id_comp, Category.comp_id]
  have hunitor : f ≫ (λ_ X').inv ≫ 𝟙_ C ◁ (ρ_ X').inv =
      (λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ (f ⊗ₘ 𝟙 (𝟙_ C))) := by
    simp only [tensorHom_def]
    monoidal
  have hpre : f ≫ (λ_ X').inv ≫ 𝟙_ C ◁ (ρ_ X').inv ≫ (u₀.inv ⊗ₘ (𝟙 X' ⊗ₘ v₀.inv)) =
      (λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫ (u₀.inv ⊗ₘ (𝟙 X ⊗ₘ v₀.inv)) ≫
        (SimpleClasses.classOf (𝟙_ C)).repr ◁ f ▷ (SimpleClasses.classOf (𝟙_ C)).reprᘁ := by
    rw [reassoc_of% hunitor, ← hmid]
  dsimp only [unitL]
  simp only [Category.assoc, biproduct.ι_map]
  exact (reassoc_of% hpre) _

/-- Component `S.repr ⊗ A ⊗ S.reprᘁ ⟶ A` of `(inductionForgetAdjunction k C).counit.app ⟨A, b⟩`. -/
private def counitComponent {A : C} (b : HalfBraiding A) (S : SimpleClasses C) :
    inductionSummand A S ⟶ A :=
  (α_ S.repr A S.reprᘁ).inv ≫ (b.β S.repr).inv ▷ S.reprᘁ ≫
    (α_ A S.repr S.reprᘁ).hom ≫
    A ◁ @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr) ≫
    (ρ_ A).hom

/-- Underlying morphism `inductionObj A ⟶ A` of
`(inductionForgetAdjunction k C).counit.app ⟨A, b⟩`. -/
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
  calc S.repr ◁ f ▷ S.reprᘁ ≫ (α_ S.repr A' S.reprᘁ).inv ≫ (b'.β S.repr).inv ▷ S.reprᘁ ≫
          (α_ A' S.repr S.reprᘁ).hom ≫
          A' ◁ @ExactPairing.evaluation C _ _ S.reprᘁ S.repr
            (simpleOppositeExactPairing S.repr) ≫ (ρ_ A').hom
      = (α_ S.repr A S.reprᘁ).inv ≫ ((S.repr ◁ f) ≫ (b'.β S.repr).inv) ▷ S.reprᘁ ≫
          (α_ A' S.repr S.reprᘁ).hom ≫
          A' ◁ @ExactPairing.evaluation C _ _ S.reprᘁ S.repr
            (simpleOppositeExactPairing S.repr) ≫ (ρ_ A').hom := by
          rw [comp_whiskerRight_assoc]
          monoidal
    _ = (α_ S.repr A S.reprᘁ).inv ≫ (b.β S.repr).inv ▷ S.reprᘁ ≫
          (α_ A S.repr S.reprᘁ).hom ≫
          (f ▷ (S.repr ⊗ S.reprᘁ) ≫
            A' ◁ @ExactPairing.evaluation C _ _ S.reprᘁ S.repr
              (simpleOppositeExactPairing S.repr)) ≫ (ρ_ A').hom := by
          rw [hβ]
          simp only [comp_whiskerRight, Category.assoc]
          monoidal
    _ = _ := by
          rw [← whisker_exchange, Category.assoc, rightUnitor_naturality]
          simp only [Category.assoc]

/-- Completeness identity for the kernel underlying half-braiding commutativity of `counitLF`. -/
private theorem sum_kernel_eq_evaluation (U : C) (S : SimpleClasses C) :
    (∑ T : SimpleClasses C, ∑ i,
      (𝟙 (S.repr ⊗ S.reprᘁ ⊗ U) ⊗≫ Module.finBasis k (S.repr ⟶ U ⊗ T.repr) i ▷ (S.reprᘁ ⊗ U) ⊗≫
        U ◁ T.repr ◁ inductionMate k U ((Module.finBasis k (S.repr ⟶ U ⊗ T.repr)).homDual i) ⊗≫
        U ◁ @ExactPairing.evaluation C _ _ T.reprᘁ T.repr
          (simpleOppositeExactPairing T.repr) ⊗≫ 𝟙 U)) =
      (α_ S.repr S.reprᘁ U).inv ≫
        @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr) ▷ U ≫
        (λ_ U).hom := by
  let _ : ExactPairing S.reprᘁ S.repr := simpleOppositeExactPairing S.repr
  apply (tensorLeftHomLinearEquiv k (S.reprᘁ ⊗ U) S.reprᘁ S.repr U).injective
  have hrhs : tensorLeftHomLinearEquiv k (S.reprᘁ ⊗ U) S.reprᘁ S.repr U
      ((α_ S.repr S.reprᘁ U).inv ≫
        @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr) ▷ U ≫
        (λ_ U).hom) = 𝟙 (S.reprᘁ ⊗ U) := by
    have hsymm : (tensorLeftHomEquiv (S.reprᘁ ⊗ U) S.reprᘁ S.repr U).symm (𝟙 (S.reprᘁ ⊗ U)) =
        (α_ S.repr S.reprᘁ U).inv ≫
          @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr) ▷ U ≫
          (λ_ U).hom := by
      simp [tensorLeftHomEquiv]
    rw [tensorLeftHomLinearEquiv_apply, ← hsymm, Equiv.apply_symm_apply]
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
    have hd' (i) : d'.homDual i = d.homDual i ≫ u.inv := by
      refine ((d'.eq_homDual_iff _ i).2 fun l ↦ ?_).symm
      have hl : d' l = u.hom ≫ d l := by simp [d', Linear.homCongr_apply]
      rw [hl, Category.assoc, ← Category.assoc (d l), d.apply_comp_homDual l i]
      split_ifs <;> simp
    have hsum : ∑ i, d.homDual i ≫ d i = ∑ i, d'.homDual i ≫ d' i := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi : d' i = u.hom ≫ d i := by simp [d', Linear.homCongr_apply]
      rw [hd' i, hi, Category.assoc, Iso.inv_hom_id_assoc]
    rw [hsum]
    exact d'.sum_homDual_eq (c T.dual)
      (LinearMap.mk₂ k (fun p q ↦ p ≫ q)
        (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
        (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp))
  simp_rw [hT]
  exact (Fintype.sum_equiv
    (Function.Involutive.toPerm SimpleClasses.dual SimpleClasses.dual_involutive)
    (fun T ↦ ∑ j, (c T.dual).homDual j ≫ c T.dual j)
    (fun R ↦ ∑ j, (c R).homDual j ≫ c R j) (fun _ ↦ rfl)).trans
    (sum_sum_homDual_comp_eq_id (S.reprᘁ ⊗ U) c)

private theorem counitLF_comm {A : C} (b : HalfBraiding A) (U : C) :
    counitLF b ▷ U ≫ (b.β U).hom = inductionβHom k A U ≫ U ◁ counitLF b := by
  rw [← Iso.eq_comp_inv]
  refine inductionObj_whiskerRight_hom_ext fun S ↦ ?_
  have htot : U ◁ counitLF b =
      ∑ T : SimpleClasses C,
        U ◁ biproduct.π (inductionSummand A) T ≫ U ◁ counitComponent b T := by
    calc U ◁ counitLF b
        = U ◁ ((∑ T, biproduct.π (inductionSummand A) T ≫
            biproduct.ι (inductionSummand A) T) ≫ counitLF b) := by
            rw [biproduct.total, Category.id_comp]
      _ = _ := by
            simp only [Preadditive.sum_comp, Category.assoc, counitLF, biproduct.ι_desc,
              whiskerLeft_sum, whiskerLeft_comp]
  rw [Category.assoc, htot, ← comp_whiskerRight, counitLF, biproduct.ι_desc]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc,
    ι_whiskerRight_inductionβHom_whiskerLeft_π_assoc]
  dsimp only [counitComponent]
  simp_rw [inductionβComponent_eq k A U S _ (Module.finBasis k _)]
  simp only [Preadditive.sum_comp, inductionTerm_comp_inv_evaluation,
    ← Preadditive.comp_sum, ← whiskerLeft_sum]
  rw [sum_kernel_eq_evaluation]
  simp only [comp_whiskerRight, whiskerLeft_comp]
  monoidal

include k in
/-- Right triangle identity for `inductionForgetAdjunction`: `unitL A ≫ counitLF b = 𝟙 A`. -/
private theorem unitL_comp_counitLF {A : C} (b : HalfBraiding A) :
    unitL A ≫ counitLF b = 𝟙 A := by
  dsimp only [unitL, counitLF]
  rw [Category.assoc, Category.assoc, Category.assoc, biproduct.ι_desc]
  dsimp only [counitComponent]
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  let v₀ := rightDualIsoUnitOfIso u₀
  have hε := simpleOppositeExactPairing_evaluation_of_iso_unit k u₀
  have hβ : u₀.inv ▷ A ≫ (b.β (SimpleClasses.classOf (𝟙_ C)).repr).inv =
      (λ_ A).hom ≫ (ρ_ A).inv ≫ A ◁ u₀.inv := by
    have hunit : (b.β (𝟙_ C)).inv = (λ_ A).hom ≫ (ρ_ A).inv := by
      apply Iso.inv_ext
      simp
    rw [b.naturality_inv u₀.inv, hunit, Category.assoc]
  have hex : ((SimpleClasses.classOf (𝟙_ C)).repr ◁ A ◁ v₀.inv) ≫
        (α_ _ A _).inv ≫ (b.β _).inv ▷ _ =
      (α_ _ A (𝟙_ C)).inv ≫ (b.β _).inv ▷ 𝟙_ C ≫ (A ⊗ _) ◁ v₀.inv := by
    calc _ = (α_ _ A (𝟙_ C)).inv ≫
              (((SimpleClasses.classOf (𝟙_ C)).repr ⊗ A) ◁ v₀.inv ≫ (b.β _).inv ▷ _) := by
            monoidal
      _ = _ := by rw [whisker_exchange]
  have hv : (u₀.inv ⊗ₘ (𝟙 A ⊗ₘ v₀.inv)) =
      u₀.inv ▷ (A ⊗ 𝟙_ C) ≫ (SimpleClasses.classOf (𝟙_ C)).repr ◁ A ◁ v₀.inv := by
    simp [tensorHom_def]
  rw [hε, hv, Category.assoc (u₀.inv ▷ _), reassoc_of% hex]
  calc (λ_ A).inv ≫ 𝟙_ C ◁ (ρ_ A).inv ≫ (u₀.inv ▷ (A ⊗ 𝟙_ C) ≫
          (α_ _ A (𝟙_ C)).inv ≫ (b.β _).inv ▷ 𝟙_ C ≫ (A ⊗ _) ◁ v₀.inv ≫
          (α_ A _ _).hom ≫ A ◁ ((u₀.hom ⊗ₘ v₀.hom) ≫ (λ_ (𝟙_ C)).hom) ≫ (ρ_ A).hom)
      = 𝟙 _ ⊗≫ (u₀.inv ▷ A ≫ (b.β _).inv) ▷ 𝟙_ C ⊗≫
          A ◁ ((SimpleClasses.classOf (𝟙_ C)).repr ◁ v₀.inv ≫ (u₀.hom ⊗ₘ v₀.hom)) ⊗≫ 𝟙 A := by
          simp only [whiskerLeft_comp]
          monoidal
    _ = 𝟙 _ ⊗≫ A ◁ ((u₀.inv ⊗ₘ v₀.inv) ≫ (u₀.hom ⊗ₘ v₀.hom)) ⊗≫ 𝟙 A := by
          rw [hβ]
          simp only [tensorHom_def, comp_whiskerRight]
          monoidal
    _ = 𝟙 A := by
          rw [tensorHom_comp_tensorHom, u₀.inv_hom_id, v₀.inv_hom_id, id_tensorHom_id,
            whiskerLeft_id]
          monoidal

/-- Left triangle identity for `inductionForgetAdjunction`:
`inductionMap (unitL X) ≫ counitLF (inductionHalfBraiding k X) = 𝟙 (inductionObj X)`. -/
private theorem inductionMap_unitL_comp_counitLF (X : C) :
    inductionMap (unitL X) ≫ counitLF (inductionHalfBraiding k X) = 𝟙 (inductionObj X) := by
  refine biproduct.hom_ext' _ _ fun S ↦ biproduct.hom_ext _ _ fun T ↦ ?_
  simp only [Category.comp_id, Category.assoc, counitLF, biproduct.ι_map_assoc,
    biproduct.ι_desc_assoc]
  let εS := @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr)
  have hcounit : counitComponent (inductionHalfBraiding k X) S =
      S.repr ◁ inductionβHom k X S.reprᘁ ≫ (α_ S.repr S.reprᘁ (inductionObj X)).inv ≫
        εS ▷ inductionObj X ≫ (λ_ (inductionObj X)).hom := by
    dsimp only [counitComponent, εS]
    have hswap := (inductionHalfBraiding k X).inv_whiskerRight_comp_whiskerLeft εS
    rw [inductionHalfBraiding_β_hom] at hswap
    calc _ = (α_ S.repr (inductionObj X) S.reprᘁ).inv ≫
              (((inductionHalfBraiding k X).β S.repr).inv ▷ S.reprᘁ ⊗≫
                inductionObj X ◁ εS ⊗≫ 𝟙 (inductionObj X)) := by monoidal
      _ = _ := by rw [hswap]; monoidal
  have hslide : (α_ S.repr S.reprᘁ (inductionObj X)).inv ≫ εS ▷ inductionObj X ≫
        (λ_ (inductionObj X)).hom ≫ biproduct.π (inductionSummand X) T =
      S.repr ◁ S.reprᘁ ◁ biproduct.π (inductionSummand X) T ≫
        (α_ S.repr S.reprᘁ (inductionSummand X T)).inv ≫ εS ▷ inductionSummand X T ≫
        (λ_ (inductionSummand X T)).hom := by
    rw [← leftUnitor_naturality, ← whisker_exchange_assoc, associator_inv_naturality_right_assoc]
  rw [reassoc_of% hcounit, hslide, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
  dsimp only [unitL]
  simp only [comp_whiskerRight, Category.assoc, ι_whiskerRight_inductionβHom_whiskerLeft_π]
  by_cases hST : S = T
  · subst hST
    rw [biproduct.ι_π_self]
    simpa only [inductionSummand, comp_whiskerRight, Category.assoc, εS] using
      left_triangle_self k X S
  · rw [biproduct.ι_π_ne _ hST, left_triangle_of_ne k X hST, comp_zero, comp_zero, comp_zero,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp]

private theorem unitL_comp_counitF (X : C) :
    unitL X ≫ (forgetInductionAdjunction k C).counit.app X = 𝟙 X := by
  rw [forgetInductionAdjunction_counit_app]
  dsimp only [unitL]
  let p₁ : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  let u₀ := SimpleClasses.classOfReprIso (𝟙_ C)
  let v₀ := rightDualIsoUnitOfIso u₀
  have hend : biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) ≫
        inductionEndπ X (𝟙_ C) =
      (SimpleClasses.classOf (𝟙_ C)).repr ◁ X ◁
        @rightAdjointMate C _ _ (𝟙_ C) _ p₁ _ u₀.inv ≫
        u₀.hom ▷ (X ⊗ p₁.rightDual) := by
    have hdin := inductionEndπ_dinatural k X u₀.inv
    rw [inductionEndπ_repr k X (SimpleClasses.classOf (𝟙_ C))] at hdin
    have h1 := biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) ≫= hdin
    rw [biproduct.ι_π_self_assoc, ← Category.assoc] at h1
    have h2 := h1 =≫ u₀.hom ▷ (X ⊗ p₁.rightDual)
    rw [Category.assoc, ← comp_whiskerRight, u₀.inv_hom_id, id_whiskerRight,
      Category.comp_id] at h2
    exact h2
  rw [Category.assoc, Category.assoc, Category.assoc, reassoc_of% hend]
  have hv : (u₀.inv ⊗ₘ (𝟙 X ⊗ₘ v₀.inv)) =
      u₀.inv ▷ (X ⊗ 𝟙_ C) ≫ (SimpleClasses.classOf (𝟙_ C)).repr ◁ X ◁ v₀.inv := by
    simp [tensorHom_def]
  rw [hv, Category.assoc (u₀.inv ▷ _), ← whiskerLeft_comp_assoc, ← whiskerLeft_comp,
    ← whisker_exchange_assoc, ← comp_whiskerRight_assoc, u₀.inv_hom_id, id_whiskerRight,
    Category.id_comp, leftUnitor_naturality_assoc, ← whiskerLeft_comp_assoc, Category.assoc v₀.inv,
    ← rightDualIsoUnitOfIso_hom u₀, v₀.inv_hom_id, whiskerLeft_id, Category.id_comp]
  monoidal

/-! ### Public left adjunction API -/

variable (C)

/-- **Left adjunction for centre induction**: `Center.induction k C ⊣ Center.forget C`. This holds
for any fusion category `C` over an algebraically closed field `k` (in arbitrary characteristic
and without choosing a pivotal structure on `C`), making `Center.induction k C` a Frobenius
functor alongside `CategoryTheory.Center.forgetInductionAdjunction`. -/
def inductionForgetAdjunction : induction k C ⊣ forget C :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app X := unitL X
          naturality _ _ f := unitL_naturality f }
      counit :=
        { app Z :=
            { f := counitLF (A := (forget C).obj Z) Z.2
              comm U :=
                (counitLF_comm k (A := (forget C).obj Z) Z.2 U).trans
                  (congrArg (· ≫ U ◁ counitLF (A := (forget C).obj Z) Z.2)
                    (inductionHalfBraiding_β_hom k ((forget C).obj Z) U).symm) }
          naturality _ _ h := Center.ext _ _ (counitLF_naturality h.f h.comm) }
      left_triangle := by
        refine NatTrans.ext (funext fun X ↦ ?_)
        dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
          Functor.whiskerLeft_app, NatTrans.id_app, Functor.comp_obj, Functor.id_obj]
        rw [Category.id_comp]
        exact Center.ext _ _ (inductionMap_unitL_comp_counitLF k X)
      right_triangle :=
        NatTrans.ext (funext fun Z ↦
          (congrArg (unitL ((forget C).obj Z) ≫ ·)
            (Category.id_comp (counitLF (A := (forget C).obj Z) Z.2))).trans
            (unitL_comp_counitLF k (A := (forget C).obj Z) Z.2)) }

/-- `Center.induction k C` is a left adjoint (in particular, it preserves all colimits that exist in
`C`). -/
instance instIsLeftAdjointInduction : (induction k C).IsLeftAdjoint :=
  (inductionForgetAdjunction k C).isLeftAdjoint

/-- Explicit formula for the unit of `inductionForgetAdjunction` at `X`. -/
theorem inductionForgetAdjunction_unit_app (X : C) :
    (inductionForgetAdjunction k C).unit.app X =
      (λ_ X).inv ≫ 𝟙_ C ◁ (ρ_ X).inv ≫
        ((SimpleClasses.classOfReprIso (𝟙_ C)).inv ⊗ₘ
          (𝟙 X ⊗ₘ (rightDualIsoUnitOfIso (SimpleClasses.classOfReprIso (𝟙_ C))).inv)) ≫
        biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) :=
  (rfl)

/-- Component of the counit of `inductionForgetAdjunction` on the `S`-summand of
`inductionObj Z.1`. -/
@[reassoc, simp]
theorem ι_comp_inductionForgetAdjunction_counit_app_f (Z : Center C) (S : SimpleClasses C) :
    biproduct.ι (inductionSummand Z.1) S ≫
        ((inductionForgetAdjunction k C).counit.app Z).f =
      (α_ S.repr Z.1 S.reprᘁ).inv ≫ (Z.2.β S.repr).inv ▷ S.reprᘁ ≫
        (α_ Z.1 S.repr S.reprᘁ).hom ≫
        Z.1 ◁ @ExactPairing.evaluation C _ _ S.reprᘁ S.repr (simpleOppositeExactPairing S.repr) ≫
        (ρ_ Z.1).hom := by
  -- Unfold the counit component of `inductionForgetAdjunction` to `biproduct.desc`.
  change biproduct.ι (inductionSummand Z.1) S ≫ counitLF Z.2 = _
  simp [counitLF, counitComponent]

/-- The unit of `inductionForgetAdjunction` splits the counit of `forgetInductionAdjunction`. -/
@[reassoc]
theorem inductionForgetAdjunction_unit_app_comp_forgetInductionAdjunction_counit_app (X : C) :
    (inductionForgetAdjunction k C).unit.app X ≫
      (forgetInductionAdjunction k C).counit.app X = 𝟙 X :=
  unitL_comp_counitF k X

/-- Every component of `(inductionForgetAdjunction k C).unit` is a split monomorphism. -/
instance instIsSplitMonoInductionForgetAdjunctionUnitApp (X : C) :
    IsSplitMono ((inductionForgetAdjunction k C).unit.app X) :=
  IsSplitMono.mk'
    { retraction := (forgetInductionAdjunction k C).counit.app X
      id := inductionForgetAdjunction_unit_app_comp_forgetInductionAdjunction_counit_app k C X }

/-- In a fusion category `C` over an algebraically closed field `k`, the induction functor
`Center.induction k C : C ⥤ Center C` is faithful. -/
instance instFaithfulInduction : (induction k C).Faithful where
  map_injective {X Y} {f g} h := by
    have hf := (inductionForgetAdjunction k C).unit.naturality f
    have hg := (inductionForgetAdjunction k C).unit.naturality g
    simp only [Functor.id_map, Functor.comp_map] at hf hg
    rw [h] at hf
    rw [← cancel_mono ((inductionForgetAdjunction k C).unit.app Y)]
    exact hf.trans hg.symm

end Fusion

end CategoryTheory.Center
