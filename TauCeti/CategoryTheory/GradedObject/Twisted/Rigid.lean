/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.CategoryTheory.GradedObject.FiniteSupport
public import TauCeti.CategoryTheory.GradedObject.MonObj
public import TauCeti.CategoryTheory.GradedObject.Twisted.Basic

/-!
# Duals of cocycle-twisted graded objects

Let `I` be an additive group and `c` a normalized `3`-cocycle on `I` with values in `Rˣ`. In the
category `TwistedGradedObject c C` of `I`-graded objects of an `R`-linear monoidal category `C`,
with associator twisted by `c`, a graded object `X` of finite support has a right dual `Y` as soon
as every component `X i` has a right dual `Y (-i)` in `C`: the dual of the degree `i` component
sits in degree `-i`.

The evaluation `Y ⊗ X ⟶ 𝟙_` is the evaluation of `C` on each summand `Y (-i) ⊗ X i` of degree
zero, and the coevaluation `𝟙_ ⟶ X ⊗ Y` is the sum over the support of `X` of the coevaluations
`𝟙_ C ⟶ X i ⊗ Y (-i)`, each scaled by `(c.ω i (-i) i)⁻¹`. This scalar cancels the twisted
associator in the zigzag identity on `X`, and in the zigzag identity on `Y` it cancels against
`c.ω (-i) i (-i)`, by the cocycle identity
(`TauCeti.GradedObject.TwistingCocycle.ω_mul_ω_neg_eq_one`). For the one-dimensional objects
`δ_g` of `Vec^ω_G` this is the standard duality: the dual of `δ_g` sits in degree `g⁻¹`, the
evaluation is that of the underlying vector spaces, and the coevaluation carries the scalar
`ω(g, g⁻¹, g)⁻¹`.

## Main definitions

* `TauCeti.TwistedGradedObject.evaluation` and `TauCeti.TwistedGradedObject.coevaluation`: the
  evaluation `Y ⊗ X ⟶ 𝟙_` and the coevaluation `𝟙_ ⟶ X ⊗ Y`.
* `TauCeti.TwistedGradedObject.exactPairing`: the exact pairing of a finitely supported graded
  object `X` with a graded object `Y` whose components `Y (-i)` are right duals of the `X i`.

## Main statements

* `TauCeti.TwistedGradedObject.ιTensorObj_evaluation_zero` and
  `TauCeti.TwistedGradedObject.evaluation_of_ne_zero`: the evaluation on the summands of
  `Y ⊗ X`.
* `TauCeti.TwistedGradedObject.coevaluation_zero`: its coevaluation in degree zero, as a sum
  over any finite set of degrees outside of which `X` vanishes.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], Example 2.3.8 and
  §2.10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Category

namespace TauCeti.TwistedGradedObject

open CategoryTheory.GradedObject CategoryTheory.GradedObject.Monoidal

variable {I : Type*} [AddGroup I] {R : Type*} [CommSemiring R]
  {c : GradedObject.TwistingCocycle I R} {C : Type*} [Category* C]
  [MonoidalCategory C] [Preadditive C] [Linear R C]
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂] [DecidableEq I] [HasInitial C]

section ExactPairing

variable (X Y : GradedObject I C) [∀ i, ExactPairing (X i) (Y (-i))]

/-- The evaluation `Y ⊗ X ⟶ 𝟙_` of graded objects: on the summand `Y j ⊗ X i` of degree zero
it is the evaluation of `C` for the pairing of `X i` with `Y (-i) = Y j`. -/
def evaluation : Monoidal.tensorObj Y X ⟶ Monoidal.tensorUnit :=
  toTensorUnitOfDegreeZero (Monoidal.tensorObj Y X) <| tensorObjDesc fun _ i h ↦
    eqToHom (congrArg Y (eq_neg_of_add_eq_zero_left h)) ▷ X i ≫ ε_ (X i) (Y (-i))

variable (c) {X} in
/-- The coevaluation `𝟙_ ⟶ X ⊗ Y` of graded objects, for `X` of finite support: in degree zero it
is the sum over the support of the coevaluations `𝟙_ C ⟶ X i ⊗ Y (-i)`, each scaled by
`(c.ω i (-i) i)⁻¹`. -/
def coevaluation (hX : X.HasFiniteSupport) : Monoidal.tensorUnit ⟶ Monoidal.tensorObj X Y :=
  oneOfDegreeZero (Monoidal.tensorObj X Y) <| ∑ i ∈ (X.hasFiniteSupport_iff_finite.mp hX).toFinset,
    (((c.ω i (-i) i)⁻¹ : Rˣ) : R) • (η_ (X i) (Y (-i)) ≫ ιTensorObj X Y i (-i) 0 (add_neg_cancel i))

variable {X} in
/-- The coevaluation in degree zero is the sum, over any finite set of degrees outside of which `X`
vanishes, of the coevaluations of `C` scaled by `(c.ω i (-i) i)⁻¹`. -/
lemma coevaluation_zero (hX : X.HasFiniteSupport) (s : Finset I) (hs : ∀ i ∉ s, IsZero (X i)) :
    coevaluation c Y hX 0 = tensorUnit₀.hom ≫ ∑ i ∈ s,
      (((c.ω i (-i) i)⁻¹ : Rˣ) : R) •
        (η_ (X i) (Y (-i)) ≫ ιTensorObj X Y i (-i) 0 (add_neg_cancel i)) := by
  rw [coevaluation, oneOfDegreeZero_zero]
  congr 1
  refine Finset.sum_subset (fun i hi ↦ ?_) fun i _ hi ↦ ?_
  · by_contra h
    exact (by simpa using hi : ¬IsZero (X i)) (hs i h)
  · rw [coevaluation_eq_zero_of_isZero_left (by simpa using hi), zero_comp, smul_zero]

/-- The evaluation on a summand `Y j ⊗ X i` of degree zero. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_evaluation_zero (j i : I) (h : j + i = 0) :
    ιTensorObj Y X j i 0 h ≫ evaluation X Y 0 =
      (eqToHom (congrArg Y (eq_neg_of_add_eq_zero_left h)) ▷ X i ≫ ε_ (X i) (Y (-i))) ≫
        tensorUnit₀.inv := by
  simp [evaluation]

/-- The evaluation vanishes away from degree zero. -/
lemma evaluation_of_ne_zero {n : I} (hn : n ≠ 0) : evaluation X Y n = 0 :=
  toTensorUnitOfDegreeZero_of_ne _ _ hn

variable [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- The summand of the same degree in the zigzag identity on `X`: the twisted associator
contributes `c.ω n (-n) n`. -/
private lemma ι_whiskerRight_associator_whiskerLeft_evaluation_self (n : I) :
    ιTensorObj X Y n (-n) 0 (add_neg_cancel n) ▷ X n ≫
        ιTensorObj (Monoidal.tensorObj X Y) X 0 n n (zero_add n) ≫
          (twistedAssociator c.ω X Y X).hom n ≫ Monoidal.whiskerLeft X (evaluation X Y) n =
      (c.ω n (-n) n : R) • ((α_ _ _ _).hom ≫ X n ◁ ε_ (X n) (Y (-n)) ≫ X n ◁ tensorUnit₀.inv ≫
        ιTensorObj X Monoidal.tensorUnit n 0 n (add_zero n)) := by
  rw [← ιTensorObj₃'_eq_assoc X Y X n (-n) n n (by simp) 0 (add_neg_cancel n),
    ιTensorObj₃'_twistedAssociator_hom_assoc,
    ιTensorObj₃_eq X Y X n (-n) n n (by simp) 0 (neg_add_cancel n)]
  simp only [Monoidal.whiskerLeft, Linear.smul_comp, assoc, Monoidal.ι_tensorHom,
    categoryOfGradedObjects_id, id_tensorHom]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ιTensorObj_evaluation_zero]
  simp

/-- The summand of opposite degree in the zigzag identity on `Y`: the scalars
`(c.ω i (-i) i)⁻¹` of the coevaluation and `(c.ω (-i) i (-i))⁻¹` of the inverse twisted associator
cancel, and what remains is the zigzag identity of `C`. -/
private lemma whiskerLeft_ι_associator_inv_whiskerRight_evaluation_of_eq {m i : I}
    (h : m + i = 0) :
    (((c.ω i (-i) i)⁻¹ : Rˣ) : R) • ((ρ_ (Y m)).inv ≫ Y m ◁ η_ (X i) (Y (-i)) ≫
      Y m ◁ ιTensorObj X Y i (-i) 0 (add_neg_cancel i) ≫
        ιTensorObj Y (Monoidal.tensorObj X Y) m 0 m (add_zero m) ≫
          (twistedAssociator c.ω Y X Y).inv m ≫ Monoidal.whiskerRight (evaluation X Y) Y m) =
      (λ_ (Y m)).inv ≫ tensorUnit₀.inv ▷ Y m ≫
        ιTensorObj Monoidal.tensorUnit Y 0 m m (zero_add m) := by
  obtain rfl : m = -i := eq_neg_of_add_eq_zero_left h
  rw [← ιTensorObj₃_eq_assoc Y X Y (-i) i (-i) (-i) (by simp) 0 (add_neg_cancel i),
    ιTensorObj₃_twistedAssociator_inv_assoc,
    ιTensorObj₃'_eq Y X Y (-i) i (-i) (-i) (by simp) 0 (neg_add_cancel i)]
  simp only [Monoidal.whiskerRight, Linear.smul_comp, Linear.comp_smul, assoc,
    Monoidal.ι_tensorHom, categoryOfGradedObjects_id, tensorHom_id]
  rw [← comp_whiskerRight_assoc, ιTensorObj_evaluation_zero]
  simp [smul_smul, c.inv_ω_mul_inv_ω_neg]

variable [MonoidalPreadditive C]

/-- A summand of the coevaluation, followed by the twisted associator and the evaluation, in the
zigzag identity on `X`: it vanishes unless its degree is that of the component of `X`. -/
private lemma ι_whiskerRight_associator_whiskerLeft_evaluation_of_ne {i n : I} (hin : i ≠ n) :
    ιTensorObj X Y i (-i) 0 (add_neg_cancel i) ▷ X n ≫
        ιTensorObj (Monoidal.tensorObj X Y) X 0 n n (zero_add n) ≫
          (twistedAssociator c.ω X Y X).hom n ≫ Monoidal.whiskerLeft X (evaluation X Y) n = 0 := by
  rw [← ιTensorObj₃'_eq_assoc X Y X i (-i) n n (by simp) 0 (add_neg_cancel i),
    ιTensorObj₃'_twistedAssociator_hom_assoc,
    ιTensorObj₃_eq X Y X i (-i) n n (by simp) (-i + n) rfl]
  simp [Monoidal.ι_tensorHom, evaluation_of_ne_zero X Y
    (show -i + n ≠ 0 from fun h ↦ hin (neg_add_eq_zero.mp h))]

/-- A summand of the coevaluation, followed by the inverse twisted associator and the evaluation,
in the zigzag identity on `Y`: it vanishes unless its degree is opposite to that of the component
of `Y`. -/
private lemma whiskerLeft_ι_associator_inv_whiskerRight_evaluation_of_ne {m i : I}
    (h : m + i ≠ 0) :
    Y m ◁ ιTensorObj X Y i (-i) 0 (add_neg_cancel i) ≫
        ιTensorObj Y (Monoidal.tensorObj X Y) m 0 m (add_zero m) ≫
          (twistedAssociator c.ω Y X Y).inv m ≫ Monoidal.whiskerRight (evaluation X Y) Y m = 0 := by
  rw [← ιTensorObj₃_eq_assoc Y X Y m i (-i) m (by simp [add_assoc]) 0 (add_neg_cancel i),
    ιTensorObj₃_twistedAssociator_inv_assoc,
    ιTensorObj₃'_eq Y X Y m i (-i) m (by simp [add_assoc]) (m + i) rfl]
  simp [Monoidal.ι_tensorHom, evaluation_of_ne_zero X Y h]

variable [MonoidalLinear R C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

/-- The zigzag identity on `X` for `TwistedGradedObject.exactPairing`. -/
private lemma whiskerRight_coevaluation_associator_whiskerLeft_evaluation
    (hX : X.HasFiniteSupport) :
    Monoidal.whiskerRight (coevaluation c Y hX) X ≫ (twistedAssociator c.ω X Y X).hom ≫
      Monoidal.whiskerLeft X (evaluation X Y) =
        (Monoidal.leftUnitor X).hom ≫ (Monoidal.rightUnitor X).inv := by
  refine (Iso.inv_comp_eq _).mp (GradedObject.hom_ext _ _ fun n ↦ ?_)
  by_cases hn : IsZero (X n)
  · exact hn.eq_of_src _ _
  simp only [categoryOfGradedObjects_comp, Monoidal.leftUnitor_inv_apply,
    Monoidal.rightUnitor_inv_apply, assoc, Monoidal.ι_tensorHom_assoc, coevaluation,
    oneOfDegreeZero_zero, categoryOfGradedObjects_id, tensorHom_id, comp_whiskerRight,
    inv_hom_whiskerRight_assoc, sum_whiskerRight, MonoidalLinear.smul_whiskerRight,
    MonoidalCategory.comp_whiskerRight, Preadditive.sum_comp,
    Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul]
  have hn' : n ∈ (X.hasFiniteSupport_iff_finite.mp hX).toFinset := by simpa using hn
  rw [Finset.sum_eq_single_of_mem n hn' fun i _ hin ↦ by
    simp [ι_whiskerRight_associator_whiskerLeft_evaluation_of_ne X Y hin]]
  simp [ι_whiskerRight_associator_whiskerLeft_evaluation_self, smul_smul]

/-- The zigzag identity on `Y` for `TwistedGradedObject.exactPairing`. -/
private lemma whiskerLeft_coevaluation_associator_inv_whiskerRight_evaluation
    (hX : X.HasFiniteSupport) :
    Monoidal.whiskerLeft Y (coevaluation c Y hX) ≫ (twistedAssociator c.ω Y X Y).inv ≫
      Monoidal.whiskerRight (evaluation X Y) Y =
        (Monoidal.rightUnitor Y).hom ≫ (Monoidal.leftUnitor Y).inv := by
  refine (Iso.inv_comp_eq _).mp (GradedObject.hom_ext _ _ fun m ↦ ?_)
  by_cases hm : IsZero (Y m)
  · exact hm.eq_of_src _ _
  simp only [categoryOfGradedObjects_comp, Monoidal.leftUnitor_inv_apply,
    Monoidal.rightUnitor_inv_apply, assoc, Monoidal.ι_tensorHom_assoc, coevaluation,
    oneOfDegreeZero_zero, categoryOfGradedObjects_id, id_tensorHom, whiskerLeft_comp,
    whiskerLeft_inv_hom_assoc, whiskerLeft_sum, MonoidalLinear.whiskerLeft_smul,
    Preadditive.sum_comp, Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul]
  have hm' : -m ∈ (X.hasFiniteSupport_iff_finite.mp hX).toFinset := by
    simpa using fun hz ↦
      hm ((isZero_right_of_isZero_left hz).of_iso (eqToIso (congrArg Y (neg_neg m)).symm))
  rw [Finset.sum_eq_single_of_mem (-m) hm' fun i _ him ↦ by
      simp [whiskerLeft_ι_associator_inv_whiskerRight_evaluation_of_ne X Y
        (show m + i ≠ 0 from fun h ↦ him (eq_neg_of_add_eq_zero_right h))]]
  exact whiskerLeft_ι_associator_inv_whiskerRight_evaluation_of_eq X Y (add_neg_cancel m)

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

variable {X} in
/-- A graded object `X` of finite support is paired with a graded object `Y` whose components
`Y (-i)` are right duals of the components `X i`: the evaluation is that of `C` on the summands
`Y (-i) ⊗ X i` of degree zero, and the coevaluation is the sum of the coevaluations of `C`, scaled
by `(c.ω i (-i) i)⁻¹`. -/
@[instance_reducible]
def exactPairing (hX : X.HasFiniteSupport) : ExactPairing (C := TwistedGradedObject c C) X Y where
  coevaluation' := coevaluation c Y hX
  evaluation' := evaluation X Y
  coevaluation_evaluation' :=
    whiskerLeft_coevaluation_associator_inv_whiskerRight_evaluation X Y hX
  evaluation_coevaluation' :=
    whiskerRight_coevaluation_associator_whiskerLeft_evaluation X Y hX

variable {X} (hX : X.HasFiniteSupport)

/-- The evaluation of `TwistedGradedObject.exactPairing` is `TwistedGradedObject.evaluation`. -/
lemma exactPairing_evaluation :
    @ExactPairing.evaluation (TwistedGradedObject c C) _ _ X Y (exactPairing Y hX) =
      evaluation X Y :=
  (rfl)

/-- The coevaluation of `TwistedGradedObject.exactPairing` is
`TwistedGradedObject.coevaluation`. -/
lemma exactPairing_coevaluation :
    @ExactPairing.coevaluation (TwistedGradedObject c C) _ _ X Y (exactPairing Y hX) =
      coevaluation c Y hX :=
  (rfl)

end ExactPairing

end TauCeti.TwistedGradedObject
