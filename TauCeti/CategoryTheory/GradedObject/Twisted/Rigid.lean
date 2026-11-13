/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GradedObject.FiniteSupport
public import TauCeti.CategoryTheory.GradedObject.Twisted.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Preadditive

/-!
# Duals of cocycle-twisted graded objects

Let `I` be an additive group, `C` an `R`-linear monoidal category and `c` a normalized
`3`-cocycle on `I` with values in `Rˣ`, so that `TwistedGradedObject c C` is the monoidal category
of `I`-graded objects of `C` with associator twisted by `c`. If `X` is finitely supported and each
component `X i` is exactly paired with `Y j` whenever `i + j = 0`, then `X` is exactly paired with
`Y` in `TwistedGradedObject c C`:

* the coevaluation `𝟙 ⟶ X ⊗ Y` is, in degree `0`, the sum over the support of `X` of the
  coevaluations `𝟙_ C ⟶ X i ⊗ Y (-i)`;
* the evaluation `Y ⊗ X ⟶ 𝟙` is, on the summand `Y (-i) ⊗ X i` of degree `0`, the evaluation of the
  pairing of `X i` with `Y (-i)` multiplied by `(c.ω i (-i) i)⁻¹`, and vanishes on the other
  summands.

The scalar is what the twisted associator requires: in the zigzag identity through
`(X ⊗ Y) ⊗ X` it meets `c.ω i (-i) i`, and in the one through `(Y ⊗ X) ⊗ Y` it meets
`(c.ω (-i) i (-i))⁻¹`, and `c.ω (-i) i (-i) * c.ω i (-i) i = 1` by the cocycle identity
(`TauCeti.GradedObject.TwistingCocycle.ω_neg_mul_ω`). For `I = Additive G` and `C = ModuleCat k`
this gives the duals of the pointed category `Vec^ω_G`, with `δ_g` dual to `δ_{g⁻¹}`.

## Main declarations

* `TauCeti.TwistedGradedObject.dualCoevaluation` and `TauCeti.TwistedGradedObject.dualEvaluation`:
  the coevaluation and the twisted evaluation, characterized by
  `TauCeti.TwistedGradedObject.tensorUnit₀_inv_dualCoevaluation` and
  `TauCeti.TwistedGradedObject.ιTensorObj_dualEvaluation`;
* `TauCeti.TwistedGradedObject.exactPairing`: the resulting exact pairing of `X` with `Y`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§2.3, 2.10
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Category CategoryTheory.GradedObject
  CategoryTheory.GradedObject.Monoidal

namespace TauCeti.GradedObject.TwistingCocycle

variable {I : Type*} [AddGroup I] {R : Type*} [Monoid R] (c : TwistingCocycle I R)

/-- The scalars met by the two zigzag identities of a graded dual pairing cancel: this is the
cocycle identity at `(i, -i, i, -i)`. -/
lemma ω_neg_mul_ω (i : I) : c.ω (-i) i (-i) * c.ω i (-i) i = 1 := by
  simpa using (c.cocycle i (-i) i (-i)).symm

end TauCeti.GradedObject.TwistingCocycle

namespace CategoryTheory.GradedObject.Monoidal

variable {I : Type*} [AddMonoid I] [DecidableEq I] {C : Type*} [Category* C]
  [MonoidalCategory C] [HasInitial C]

/-- The canonical isomorphism `tensorUnit n ≅ 𝟙_ C` in a degree `n` equal to `0`. -/
def tensorUnitIsoOfEq (n : I) (hn : n = 0) : (tensorUnit : GradedObject I C) n ≅ 𝟙_ C :=
  singleObjApplyIsoOfEq 0 (𝟙_ C) n hn

@[simp]
lemma tensorUnitIsoOfEq_zero : tensorUnitIsoOfEq (C := C) (0 : I) rfl = tensorUnit₀ :=
  (rfl)

/-- The inclusion of `X n ⊗ 𝟙_ C` into the degree `n` of `X ⊗ 𝟙` does not depend on how the
degree `0` of the unit is written. -/
@[reassoc]
lemma whiskerLeft_tensorUnitIsoOfEq_inv_ιTensorObj
    [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    (X : GradedObject I C) (n m : I) (hm : m = 0) (h : n + m = n) :
    X n ◁ (tensorUnitIsoOfEq m hm).inv ≫ ιTensorObj X tensorUnit n m n h =
      X n ◁ tensorUnit₀.inv ≫ ιTensorObj X tensorUnit n 0 n (add_zero n) := by
  subst hm
  rfl

/-- The inclusion of `𝟙_ C ⊗ Y n` into the degree `n` of `𝟙 ⊗ Y` does not depend on how the
degree `0` of the unit is written. -/
@[reassoc]
lemma tensorUnitIsoOfEq_inv_whiskerRight_ιTensorObj
    [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    (Y : GradedObject I C) (n m : I) (hm : m = 0) (h : m + n = n) :
    (tensorUnitIsoOfEq m hm).inv ▷ Y n ≫ ιTensorObj tensorUnit Y m n n h =
      tensorUnit₀.inv ▷ Y n ≫ ιTensorObj tensorUnit Y 0 n n (zero_add n) := by
  subst hm
  rfl

end CategoryTheory.GradedObject.Monoidal

namespace TauCeti.TwistedGradedObject

variable {I : Type*} [AddGroup I] [DecidableEq I] {R : Type*} [CommSemiring R]
  (c : GradedObject.TwistingCocycle I R) {C : Type*} [Category* C] [MonoidalCategory C]
  [Preadditive C] [Linear R C] [HasInitial C] [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  {X Y : GradedObject I C} (hX : X.HasFiniteSupport)
  (p : ∀ i j : I, i + j = 0 → ExactPairing (X i) (Y j))

/-- The coevaluation of the graded dual pairing: in degree `0` it is the sum of the coevaluations
`𝟙_ C ⟶ X i ⊗ Y (-i)` over the finitely many degrees `i` in the support of `X`. -/
def dualCoevaluation : (tensorUnit : GradedObject I C) ⟶ tensorObj X Y := fun n ↦
  if hn : n = 0 then
    (tensorUnitIsoOfEq n hn).hom ≫ ∑ i ∈ hX.toFinset,
      letI := p i (-i) (add_neg_cancel i)
      η_ (X i) (Y (-i)) ≫ ιTensorObj X Y i (-i) n (by rw [hn, add_neg_cancel])
  else 0

/-- The degree `0` component of `TwistedGradedObject.dualCoevaluation`: the sum of the
coevaluations of the components over the support of `X`. -/
lemma tensorUnit₀_inv_dualCoevaluation :
    tensorUnit₀.inv ≫ dualCoevaluation hX p 0 = ∑ i ∈ hX.toFinset,
      letI := p i (-i) (add_neg_cancel i)
      η_ (X i) (Y (-i)) ≫ ιTensorObj X Y i (-i) 0 (add_neg_cancel i) := by
  rw [dualCoevaluation, dite_eq_left rfl]
  exact Iso.inv_hom_id_assoc _ _

/-- The evaluation of the graded dual pairing: on the summand `Y j ⊗ X i` with `i + j = 0` it is
`(c.ω i j i)⁻¹` times the evaluation of the pairing of `X i` with `Y j`, and it vanishes on the
other summands. -/
def dualEvaluation : tensorObj Y X ⟶ (tensorUnit : GradedObject I C) := fun n ↦
  tensorObjDesc fun j i h ↦
    if h' : i + j = 0 then
      letI := p i j h'
      (((c.ω i j i)⁻¹ : Rˣ) : R) • (ε_ (X i) (Y j) ≫
        (tensorUnitIsoOfEq n
          (by rw [← h, eq_neg_of_add_eq_zero_right h', neg_add_cancel])).inv)
    else 0

/-- The components of `TwistedGradedObject.dualEvaluation` on the summands `Y j ⊗ X i`. -/
@[reassoc]
lemma ιTensorObj_dualEvaluation (i j n : I) (h : j + i = n) :
    ιTensorObj Y X j i n h ≫ dualEvaluation c p n =
      if h' : i + j = 0 then
        letI := p i j h'
        (((c.ω i j i)⁻¹ : Rˣ) : R) • (ε_ (X i) (Y j) ≫
          (tensorUnitIsoOfEq n
            (by rw [← h, eq_neg_of_add_eq_zero_right h', neg_add_cancel])).inv)
      else 0 :=
  ι_tensorObjDesc _ _ _ _

variable [MonoidalPreadditive C] [MonoidalLinear R C]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

/-- The zigzag identity `(η ▷ X) ≫ α ≫ (X ◁ ε) = λ ≫ ρ⁻¹` of the graded dual pairing, composed
with `λ⁻¹`. In degree `n` only the summand of the coevaluation indexed by `n` survives the
evaluation, and there the scalar `c.ω n (-n) n` of the twisted associator cancels that of the
evaluation. -/
private lemma leftUnitor_inv_comp_evaluation_coevaluation :
    (leftUnitor X).inv ≫ tensorHom (dualCoevaluation hX p) (𝟙 X) ≫
      (twistedAssociator c.ω X Y X).hom ≫ tensorHom (𝟙 X) (dualEvaluation c p) =
    (rightUnitor X).inv := by
  ext n
  simp only [categoryOfGradedObjects_comp]
  rw [Monoidal.leftUnitor_inv_apply, Monoidal.rightUnitor_inv_apply]
  simp only [assoc]
  rw [ι_tensorHom_assoc]
  dsimp only [categoryOfGradedObjects_id]
  rw [tensorHom_id, ← comp_whiskerRight_assoc,
    tensorUnit₀_inv_dualCoevaluation, sum_whiskerRight, Preadditive.sum_comp]
  simp only [comp_whiskerRight, assoc, Preadditive.comp_sum]
  rw [Finset.sum_congr rfl (fun i _ ↦ by
    rw [← ιTensorObj₃'_eq_assoc X Y X i (-i) n n (by rw [add_neg_cancel, zero_add]) 0
      (add_neg_cancel i), ιTensorObj₃'_twistedAssociator_hom_assoc,
      Linear.smul_comp, assoc, ιTensorObj₃_eq X Y X i (-i) n n _ (-i + n) rfl, assoc,
      ι_tensorHom])]
  dsimp only [categoryOfGradedObjects_id]
  simp only [id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc, ιTensorObj_dualEvaluation]
  by_cases hn : n ∈ hX.toFinset
  · rw [Finset.sum_eq_single_of_mem n hn (fun i _ hi ↦ by
      rw [dite_eq_right (by rwa [add_neg_eq_zero, eq_comm])]
      simp)]
    rw [dite_eq_left (add_neg_cancel n)]
    let := p n (-n) (add_neg_cancel n)
    simp only [MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul, smul_smul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul, MonoidalCategory.whiskerLeft_comp,
      assoc]
    rw [whiskerLeft_tensorUnitIsoOfEq_inv_ιTensorObj,
      ExactPairing.evaluation_coevaluation_assoc, Iso.inv_hom_id_assoc]
  · exact (by simpa using hn : IsZero (X n)).eq_of_src _ _

/-- The zigzag identity `(Y ◁ η) ≫ α⁻¹ ≫ (ε ▷ Y) = ρ ≫ λ⁻¹` of the graded dual pairing,
composed with `ρ⁻¹`. In degree `-i` only the summand of the coevaluation indexed by `i` survives
the evaluation, and there the two scalars cancel by `TwistingCocycle.ω_neg_mul_ω`. -/
private lemma rightUnitor_inv_comp_coevaluation_evaluation :
    (rightUnitor Y).inv ≫ tensorHom (𝟙 Y) (dualCoevaluation hX p) ≫
      (twistedAssociator c.ω Y X Y).inv ≫ tensorHom (dualEvaluation c p) (𝟙 Y) =
    (leftUnitor Y).inv := by
  ext n
  obtain ⟨i, rfl⟩ : ∃ i, -i = n := ⟨-n, neg_neg n⟩
  simp only [categoryOfGradedObjects_comp]
  rw [Monoidal.leftUnitor_inv_apply, Monoidal.rightUnitor_inv_apply]
  simp only [assoc]
  rw [ι_tensorHom_assoc]
  dsimp only [categoryOfGradedObjects_id]
  rw [id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc,
    tensorUnit₀_inv_dualCoevaluation, whiskerLeft_sum, Preadditive.sum_comp]
  simp only [MonoidalCategory.whiskerLeft_comp, assoc, Preadditive.comp_sum]
  rw [Finset.sum_congr rfl (fun k _ ↦ by
    rw [← ιTensorObj₃_eq_assoc Y X Y (-i) k (-k) (-i)
      (by rw [add_assoc, add_neg_cancel, add_zero]) 0 (add_neg_cancel k),
      ιTensorObj₃_twistedAssociator_inv_assoc,
      Linear.smul_comp, assoc, ιTensorObj₃'_eq Y X Y (-i) k (-k) (-i) _ (-i + k) rfl, assoc,
      ι_tensorHom])]
  dsimp only [categoryOfGradedObjects_id]
  simp only [tensorHom_id, ← comp_whiskerRight_assoc, ιTensorObj_dualEvaluation]
  by_cases hi : i ∈ hX.toFinset
  · rw [Finset.sum_eq_single_of_mem i hi (fun k _ hk ↦ by
      rw [dite_eq_right (by rwa [add_neg_eq_zero])]
      simp)]
    rw [dite_eq_left (add_neg_cancel i)]
    let := p i (-i) (add_neg_cancel i)
    simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul, smul_smul,
      ← Units.val_mul, ← mul_inv, c.ω_neg_mul_ω, inv_one, Units.val_one, one_smul,
      MonoidalCategory.comp_whiskerRight, assoc]
    rw [tensorUnitIsoOfEq_inv_whiskerRight_ιTensorObj,
      ExactPairing.coevaluation_evaluation_assoc, Iso.inv_hom_id_assoc]
  · let := p i (-i) (add_neg_cancel i)
    exact ((by simpa using hi : IsZero (X i)).of_exactPairing (Y (-i))).eq_of_src _ _

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- A finitely supported graded object `X` whose component `X i` is exactly paired with the
component `Y j` whenever `i + j = 0` is exactly paired with `Y` in the category of graded objects
with associator twisted by `c`. The coevaluation is `TwistedGradedObject.dualCoevaluation` and the
evaluation `TwistedGradedObject.dualEvaluation`, whose scalars `(c.ω i (-i) i)⁻¹` compensate the
twisted associator in the zigzag identities. -/
@[instance_reducible]
def exactPairing (X Y : TwistedGradedObject c C) (hX : HasFiniteSupport X)
    (p : ∀ i j : I, i + j = 0 → ExactPairing (X i) (Y j)) : ExactPairing X Y where
  coevaluation' := dualCoevaluation hX p
  evaluation' := dualEvaluation c p
  coevaluation_evaluation' := by
    rw [← cancel_epi (ρ_ Y).inv, Iso.inv_hom_id_assoc]
    exact rightUnitor_inv_comp_coevaluation_evaluation c hX p
  evaluation_coevaluation' := by
    rw [← cancel_epi (λ_ X).inv, Iso.inv_hom_id_assoc]
    exact leftUnitor_inv_comp_evaluation_coevaluation c hX p

/-- The coevaluation of `TwistedGradedObject.exactPairing` is
`TwistedGradedObject.dualCoevaluation`. -/
@[simp]
lemma exactPairing_coevaluation (X Y : TwistedGradedObject c C) (hX : HasFiniteSupport X)
    (p : ∀ i j : I, i + j = 0 → ExactPairing (X i) (Y j)) :
    @ExactPairing.coevaluation _ _ _ X Y (exactPairing c X Y hX p) = dualCoevaluation hX p :=
  (rfl)

/-- The evaluation of `TwistedGradedObject.exactPairing` is `TwistedGradedObject.dualEvaluation`. -/
@[simp]
lemma exactPairing_evaluation (X Y : TwistedGradedObject c C) (hX : HasFiniteSupport X)
    (p : ∀ i j : I, i + j = 0 → ExactPairing (X i) (Y j)) :
    @ExactPairing.evaluation _ _ _ X Y (exactPairing c X Y hX p) = dualEvaluation c p :=
  (rfl)

end TauCeti.TwistedGradedObject
