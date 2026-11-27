/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Braiding
public import TauCeti.CategoryTheory.Monoidal.Rigid.Twisted

/-!
# The Koszul sign of a swapped twisted pairing of cochain complexes

For cochain complexes with the Koszul braiding (`TauCeti.koszulBraidedCategory`), the swap
`TauCeti.TwistedPairing.swap` of a pairing of `X` and `Y` twisted by `V` interchanges the two
factors with the Koszul sign. On the summand `X^p ⊗ Y^q` of degree `j = p + q`, the evaluation of
the swap is `(-1)^(p q)` times the coefficient braiding into `Y^q ⊗ X^p` followed by the
evaluation of the original pairing (`TauCeti.TwistedPairing.ιTensorObj_swap_evaluation_f`).
Over symmetric coefficients, when the coevaluation of the original pairing lands in the summand
`X^p ⊗ Y^q` in degree `j`, the coevaluation of the swap lands in `Y^q ⊗ X^p`, again with the
coefficient braiding and the sign `(-1)^(p q)`
(`TauCeti.TwistedPairing.swap_coevaluation_f_of_coevaluation_f_eq`).

## Main results

* `TauCeti.TwistedPairing.ιTensorObj_swap_evaluation_f`: the Koszul sign of the evaluation of a
  swapped twisted pairing.
* `TauCeti.TwistedPairing.swap_coevaluation_f_of_coevaluation_f_eq`: the Koszul sign of the
  coevaluation of a swapped twisted pairing.
-/

public section

open CategoryTheory Limits MonoidalCategory BraidedCategory

namespace TauCeti

namespace TwistedPairing

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ (X Y : GradedObject ℤ C), GradedObject.HasTensor X Y]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
  [∀ (W X Y Z : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt W X Y Z]

section Braided

variable [BraidedCategory C] {X Y V : CochainComplex C ℤ} (P : TwistedPairing X Y V)

/-- **The Koszul sign of a swapped evaluation.** On the summand `X^p ⊗ Y^q` of degree `j = p + q`,
the evaluation of the swap of `P` is `(-1)^(p q)` times the coefficient braiding into
`Y^q ⊗ X^p` followed by the evaluation of `P`. -/
@[reassoc]
theorem ιTensorObj_swap_evaluation_f (p q j : ℤ) (h : p + q = j) :
    HomologicalComplex.ιTensorObj X Y p q j h ≫ P.swap.evaluation.f j =
      (p * q).negOnePow • ((β_ (X.X p) (Y.X q)).hom ≫
        HomologicalComplex.ιTensorObj Y X q p j (by omega) ≫ P.evaluation.f j) := by
  rw [swap_evaluation, HomologicalComplex.comp_f, ← Category.assoc,
    braiding_eq_tensorBraiding, HomologicalComplex.ιTensorObj_tensorBraiding_hom_f,
    ComplexShape.σ_up_ℤ, Linear.units_smul_comp, Category.assoc]

end Braided

section Symmetric

variable [SymmetricCategory C] {X Y V : CochainComplex C ℤ} (P : TwistedPairing X Y V)

/-- **The Koszul sign of a swapped coevaluation.** Over symmetric coefficients, if the
coevaluation of `P` in degree `j` is `g` followed by the inclusion of the summand `X^p ⊗ Y^q`, then
the coevaluation of the swap of `P` in degree `j` is `(-1)^(p q)` times `g` followed by the
coefficient braiding and the inclusion of the summand `Y^q ⊗ X^p`. -/
theorem swap_coevaluation_f_of_coevaluation_f_eq (p q j : ℤ) (h : p + q = j)
    (g : V.X j ⟶ X.X p ⊗ Y.X q)
    (hg : P.coevaluation.f j = g ≫ HomologicalComplex.ιTensorObj X Y p q j h) :
    P.swap.coevaluation.f j =
      (p * q).negOnePow • (g ≫ (β_ (X.X p) (Y.X q)).hom ≫
        HomologicalComplex.ιTensorObj Y X q p j (by omega)) := by
  rw [swap_coevaluation, ← SymmetricCategory.braiding_swap_eq_inv_braiding,
    HomologicalComplex.comp_f, hg, Category.assoc, braiding_eq_tensorBraiding,
    HomologicalComplex.ιTensorObj_tensorBraiding_hom_f, ComplexShape.σ_up_ℤ,
    Linear.comp_units_smul]

end Symmetric

end TwistedPairing

end TauCeti
