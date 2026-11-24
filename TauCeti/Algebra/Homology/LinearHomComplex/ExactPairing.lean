/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.Algebra.Homology.LinearHomComplex.DualTensor

/-!
# The dual of a finite complex of finite projective modules is a right dual

Let `A` be a cochain complex of modules over a commutative ring `R` and `A∨ = Hom(A, R[0])` its dual
complex, the `R`-linear Hom complex into the tensor unit. This file constructs the evaluation and
coevaluation of `A` and `A∨` in the monoidal category `CochainComplex (ModuleCat R) ℤ`, with the
Koszul sign conventions of Mathlib's totalized tensor product, and proves the two snake (zigzag)
identities. So `A∨` is a right dual of `A` in the sense of Mathlib's `CategoryTheory.ExactPairing`
whenever the dual-tensor comparison `A ⊗ A∨ ⟶ Hom(A, A)` is an isomorphism, for instance when `A`
has finitely many nonzero terms, all finitely generated projective
(`TauCeti.isIso_linearHomComplexDualTensor`). Determinant lines and orientation lines of Fredholm
operators are such complexes, and the evaluation and coevaluation are the pairing and the sewing
map by which count functionals on tensor products of these lines are composed.

* **Evaluation** `TauCeti.linearHomComplexEvaluation R A : A∨ ⊗ A ⟶ R[0]` sends `φ ⊗ a` to `φ(a)`,
  with no sign (`TauCeti.linearHomComplexEvaluation_ιTensorObj_tmul`). It is composition of
  cochains `Hom(A, R[0]) ⊗ Hom(R[0], A) ⟶ Hom(R[0], R[0])` after identifying `A` with
  `Hom(R[0], A)` and `Hom(R[0], R[0])` with `R[0]` by evaluation at `1`, so it is a morphism of
  complexes for every `A`.
* **Coevaluation** `TauCeti.linearHomComplexCoevaluation R A : R[0] ⟶ A ⊗ A∨` is the identity
  cochain of `A` read back through the inverse of the dual-tensor comparison: it is the unique
  morphism whose image under the comparison is the identity
  (`TauCeti.linearHomComplexCoevaluation_comp_linearHomComplexDualTensor`). On a basis `(eᵢ)` of
  `A` with dual basis `(eᵢ*)` it is `1 ↦ ∑ᵢ eᵢ ⊗ eᵢ*`.
* **Snake identities.** Both zigzags are identities, so `A` and `A∨` form an exact pairing and
  `A∨` is a right dual of `A`; the identities are Mathlib's `ExactPairing.evaluation_coevaluation`
  and `ExactPairing.coevaluation_evaluation` for this instance. The proof is formal: applying the
  dual-tensor image of `b ⊗ φ` to `a` is `b ⊗ φ(a)`
  (`TauCeti.linearHomComplexDualTensor_whiskerRight_comp`), and precomposing a linear form `ψ`
  with it is `ψ(b) φ` (`TauCeti.whiskerLeft_linearHomComplexDualTensor_comp`). Both follow from
  associativity and the unit laws of composition of cochains, and the snake identities then reduce
  to the unit laws.

## Main definitions

* `TauCeti.linearHomComplexEvaluation`: the evaluation `A∨ ⊗ A ⟶ R[0]`.
* `TauCeti.linearHomComplexCoevaluation`: the coevaluation `R[0] ⟶ A ⊗ A∨`.
* The instances `ExactPairing A A∨` and `HasRightDual A`, given that the dual-tensor comparison of
  `A` with itself is an isomorphism.

## References

* C. A. Weibel, *An introduction to homological algebra*, Section 2.7, on the Hom and tensor
  complexes and their sign conventions.
* P. Etingof, S. Gelaki, D. Nikshych and V. Ostrik, *Tensor categories*, Mathematical Surveys and
  Monographs 205, AMS, 2015, Section 2.10, on exact pairings, duals and the snake identities.
-/

public section

open CategoryTheory Limits MonoidalCategory CochainComplex CochainComplex.HomComplex
open scoped TensorProduct

namespace TauCeti

universe v

variable {R : Type v} [CommRing R]

section Evaluation

variable (R) in
/-- The **evaluation** `A∨ ⊗ A ⟶ R[0]` of a cochain complex of `R`-modules and its dual complex
`A∨ = Hom(A, R[0])`. It sends `φ ⊗ a` to `φ(a)`, with no sign
(`TauCeti.linearHomComplexEvaluation_ιTensorObj_tmul`): it is composition of cochains
`Hom(A, R[0]) ⊗ Hom(R[0], A) ⟶ Hom(R[0], R[0])`, after identifying `A` with `Hom(R[0], A)` and
`Hom(R[0], R[0])` with `R[0]` by evaluation at `1`. -/
noncomputable def linearHomComplexEvaluation (A : CochainComplex (ModuleCat.{v} R) ℤ) :
    linearHomComplex R A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) ⊗ A ⟶
      𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) :=
  _ ◁ (linearHomComplexFromTensorUnitIso R A).inv ≫
    linearHomComplexComp R (𝟙_ _) A (𝟙_ _) ≫
      (linearHomComplexFromTensorUnitIso R (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))).hom

/-- The evaluation is composition of cochains after identifying `A` with `Hom(R[0], A)` and
`Hom(R[0], R[0])` with `R[0]`. -/
lemma linearHomComplexEvaluation_def (A : CochainComplex (ModuleCat.{v} R) ℤ) :
    linearHomComplexEvaluation R A =
      _ ◁ (linearHomComplexFromTensorUnitIso R A).inv ≫
        linearHomComplexComp R (𝟙_ _) A (𝟙_ _) ≫
          (linearHomComplexFromTensorUnitIso R (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))).hom :=
  (rfl)

/-- On the summand `(A∨)^q ⊗ Aᵖ` with `q + p = 0`, the evaluation sends `φ ⊗ a` to `φ(a)`, where
`φ` is read as a linear form on `Aᵖ` and its value as an element of the degree-zero term `R` of
the tensor unit. -/
@[simp]
lemma linearHomComplexEvaluation_ιTensorObj_tmul (A : CochainComplex (ModuleCat.{v} R) ℤ)
    {p q : ℤ} (h : q + p = 0)
    (φ : ModuleCat.of R (Cochain A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) q)) (a : A.X p) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexEvaluation R A).f 0)
        ((HomologicalComplex.ιTensorObj (linearHomComplex R A _) A q p 0 h).hom (φ ⊗ₜ a))) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv
        (cochainToTensorUnitLinearEquiv R A (by omega : p + q = 0) φ a) := by
  rw [linearHomComplexEvaluation_def, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.ι_whiskerLeft_assoc]
  have hι := ι_linearHomComplexComp R (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) A
    (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) q p 0 h
  rw [HomologicalComplex.ιTensorObj, reassoc_of% hι, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply]
  simp only [linearHomComplex_X, linearHomComplexFromTensorUnitIso_inv_f_apply,
    cochainFromTensorUnitLinearEquiv_symm_apply, cochainCompTensor_tmul,
    linearHomComplexFromTensorUnitIso_hom_f_apply, cochainFromTensorUnitLinearEquiv_apply,
    Cochain.comp_v _ _ _ 0 p 0 (zero_add p) (by omega : p + q = 0),
    cochainToTensorUnitLinearEquiv_apply, Cochain.toSingleEquiv_apply, Cochain.fromSingleMk_v,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, Iso.hom_inv_id_apply]
  -- The tensor unit `𝟙_ (ModuleCat R)` and `ModuleCat.of R R` index the same single complex but
  -- are presented differently in the two isomorphisms `singleObjXSelf`.
  rw [singleObjXSelf_hom_singleObjXSelf_inv_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul]

/-- **Applying the dual-tensor comparison is evaluation.** The cochain that the dual-tensor
comparison assigns to `b ⊗ φ`, applied to `a ∈ A ≅ Hom(R[0], A)`, is `b ⊗ φ(a) ≅ b • φ(a)` in
`B ≅ Hom(R[0], B)`. -/
lemma linearHomComplexDualTensor_whiskerRight_comp (A B : CochainComplex (ModuleCat.{v} R) ℤ) :
    linearHomComplexDualTensor R A B ▷ A ≫
        linearHomComplex R A B ◁ (linearHomComplexFromTensorUnitIso R A).inv ≫
          linearHomComplexComp R (𝟙_ _) A B =
      (α_ _ _ _).hom ≫ B ◁ linearHomComplexEvaluation R A ≫ (ρ_ B).hom ≫
        (linearHomComplexFromTensorUnitIso R B).inv := by
  rw [linearHomComplexDualTensor_def, comp_whiskerRight_assoc, ← whisker_exchange_assoc,
    linearHomComplexComp_assoc, linearHomComplexComp_eq_rightUnitor,
    linearHomComplexEvaluation_def]
  simp [associator_naturality_left_assoc, ← whisker_exchange_assoc, -whiskerRight_tensor]

/-- **Precomposing with the dual-tensor comparison is evaluation.** Composing a linear form
`ψ ∈ B∨` with the cochain that the dual-tensor comparison assigns to `b ⊗ φ` gives `ψ(b) φ`. -/
lemma whiskerLeft_linearHomComplexDualTensor_comp (A B : CochainComplex (ModuleCat.{v} R) ℤ) :
    linearHomComplex R B (𝟙_ _) ◁ linearHomComplexDualTensor R A B ≫
        linearHomComplexComp R A B (𝟙_ _) =
      (α_ _ _ _).inv ≫ linearHomComplexEvaluation R B ▷ _ ≫ (λ_ _).hom := by
  have h := (Iso.inv_comp_eq _).2 (linearHomComplexComp_assoc (R := R) (F := A)
    (G := 𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) (K := B)
    (L := 𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)))
  rw [linearHomComplexDualTensor_def, whiskerLeft_comp_assoc, ← h,
    linearHomComplexComp_eq_leftUnitor, linearHomComplexEvaluation_def]
  simp

end Evaluation

section Coevaluation

variable (A : CochainComplex (ModuleCat.{v} R) ℤ) [IsIso (linearHomComplexDualTensor R A A)]

variable (R) in
/-- The **coevaluation** `R[0] ⟶ A ⊗ A∨` of a cochain complex of `R`-modules whose dual-tensor
comparison `A ⊗ A∨ ⟶ Hom(A, A)` is an isomorphism, such as a finite complex of finitely generated
projective modules: the identity cochain of `A`, read back through the inverse of the comparison.
On a basis `(eᵢ)` of `A` with dual basis `(eᵢ*)` it is `1 ↦ ∑ᵢ eᵢ ⊗ eᵢ*`. -/
noncomputable def linearHomComplexCoevaluation :
    𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) ⟶
      A ⊗ linearHomComplex R A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) :=
  linearHomComplexUnit R A ≫ inv (linearHomComplexDualTensor R A A)

/-- The dual-tensor comparison sends the coevaluation to the identity cochain; since the comparison
is an isomorphism, this characterizes the coevaluation. -/
@[reassoc (attr := simp)]
lemma linearHomComplexCoevaluation_comp_linearHomComplexDualTensor :
    linearHomComplexCoevaluation R A ≫ linearHomComplexDualTensor R A A =
      linearHomComplexUnit R A := by
  rw [linearHomComplexCoevaluation, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- A cochain complex of modules whose dual-tensor comparison with itself is an isomorphism forms
an exact pairing with its dual complex `A∨ = Hom(A, R[0])`, through the evaluation and the
coevaluation. -/
noncomputable instance exactPairingLinearHomComplex :
    ExactPairing A (linearHomComplex R A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))) where
  coevaluation' := linearHomComplexCoevaluation R A
  evaluation' := linearHomComplexEvaluation R A
  coevaluation_evaluation' := by
    rw [← cancel_mono (λ_ _).hom]
    simp [← whiskerLeft_linearHomComplexDualTensor_comp, ← whiskerLeft_comp_assoc,
      linearHomComplexComp_unit]
  evaluation_coevaluation' := by
    rw [← cancel_mono ((ρ_ A).hom ≫ (linearHomComplexFromTensorUnitIso R A).inv)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← linearHomComplexDualTensor_whiskerRight_comp, ← comp_whiskerRight_assoc,
      linearHomComplexCoevaluation_comp_linearHomComplexDualTensor]
    simp [← whisker_exchange_assoc, linearHomComplexUnit_comp]

/-- The coevaluation of the exact pairing of `A` with its dual complex. -/
@[simp]
lemma exactPairing_coevaluation_eq_linearHomComplexCoevaluation :
    ExactPairing.coevaluation A (linearHomComplex R A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))) =
      linearHomComplexCoevaluation R A :=
  (rfl)

/-- The evaluation of the exact pairing of `A` with its dual complex. -/
@[simp]
lemma exactPairing_evaluation_eq_linearHomComplexEvaluation :
    ExactPairing.evaluation A (linearHomComplex R A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))) =
      linearHomComplexEvaluation R A :=
  (rfl)

/-- The dual complex `A∨ = Hom(A, R[0])` is a right dual of `A` whenever the dual-tensor
comparison of `A` with itself is an isomorphism. -/
noncomputable instance hasRightDualCochainComplex : HasRightDual A where
  rightDual := linearHomComplex R A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ))

/-- The right dual of `A` is its dual complex `Hom(A, R[0])`. -/
lemma rightDual_eq_linearHomComplex :
    Aᘁ = linearHomComplex R A (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)) :=
  (rfl)

end Coevaluation

end TauCeti
