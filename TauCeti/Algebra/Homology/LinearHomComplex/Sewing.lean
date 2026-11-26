/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import TauCeti.Algebra.Homology.LinearHomComplex.ExactPairing
public import TauCeti.Algebra.Homology.LinearHomComplex.Functional
public import TauCeti.Algebra.Homology.Monoidal.Braiding
public import TauCeti.CategoryTheory.Monoidal.Rigid.Sewing

/-!
# Right evaluation, the identity functional and sewing of functionals

Let `A` and `B` be cochain complexes of modules over a commutative ring `R`, with dual complexes
`A∨ = Hom(A, R[0])` and `B∨`. An operation from `A` to `B` is recorded as a functional on the
input-first external kernel `A ⊗ B∨`, and a chain map `F : A ⊗ B∨ ⟶ R[0]` is read as a chain map
`A ⟶ B` (`TauCeti.linearHomComplexTensorDualHomEquiv`), with the sign
`φ (T a) = (-1)^p F (a ⊗ φ)` for `a` in `Aᵖ`. This file identifies the functionals of chain maps
and the composition of operators in terms of the symmetric monoidal structure of complexes.

**Right evaluation.** The evaluation `A∨ ⊗ A ⟶ R[0]`, `φ ⊗ a ↦ φ(a)`
(`TauCeti.linearHomComplexEvaluation`), has no sign. The **right evaluation**
`A ⊗ A∨ ⟶ R[0]` (`TauCeti.linearHomComplexRightEvaluation`) is the Koszul interchange of the two
factors followed by the evaluation. On `a ⊗ φ` with `a` in `Aᵖ` it is `(-1)^p φ(a)`
(`TauCeti.singleObjXSelf_hom_linearHomComplexRightEvaluation_f_apply`): the Koszul sign of
interchanging degrees `p` and `-p` is `(-1)^(p (-p)) = (-1)^p`. So on a line spanned by `e` in
degree `p`, with dual basis `e*`, the right evaluation has coefficient `(-1)^p` on `e ⊗ e*`, while
the evaluation has coefficient `1` on `e* ⊗ e`; the two differ exactly in odd degree.

**The functional of an operator.** The functional of a chain map `T : A ⟶ B` is the right
evaluation of `B` after `T` on the first factor
(`TauCeti.linearHomComplexTensorDualHomEquiv_symm_apply_eq_whiskerRight_comp`). In particular
the **identity functional**, the functional on `A ⊗ A∨` whose operator is the identity of `A`, is
the right evaluation (`TauCeti.linearHomComplexTensorDualHomEquiv_linearHomComplexRightEvaluation`),
with coefficient `(-1)^|a|` on `a ⊗ a*`, and not the evaluation.

**Sewing.** When `B` has a coevaluation `R[0] ⟶ B ⊗ B∨`
(`TauCeti.linearHomComplexCoevaluation`), for instance when `B` is a finite complex of finitely
generated projective modules, the right evaluation is the evaluation of the exact pairing
`(B∨, B)` obtained from `(B, B∨)` by the braiding
(`CategoryTheory.BraidedCategory.exactPairing_swap`,
`TauCeti.exactPairing_swap_evaluation_eq_linearHomComplexRightEvaluation`). Its coevaluation
`R[0] ⟶ B∨ ⊗ B` is the coevaluation of `B` followed by the interchange
(`TauCeti.exactPairing_swap_coevaluation_eq_linearHomComplexCoevaluation_comp`), so on a line
spanned by `e` in degree `p` it is
`1 ↦ (-1)^p e* ⊗ e`, with the dual factor first. The **sewing** of functionals `F` on `A ⊗ B∨`
and `G` on `B ⊗ C∨` (`TauCeti.linearHomComplexSewing`) inserts this coevaluation between `A` and
`C∨`,

`A ⊗ C∨ ⟶ A ⊗ (B∨ ⊗ B) ⊗ C∨ ≅ (A ⊗ B∨) ⊗ (B ⊗ C∨) ⟶ R[0]`.

This is the sewing `TauCeti.ExactPairing.sewing` along the braided pairing `(B∨, B)`, so it is
associative with the right evaluations as units, by the snake identities and the interchange law
alone. Sewing the functional of a chain map `T : A ⟶ B` with `G` is `T` followed by `G`
(`TauCeti.linearHomComplexSewing_whiskerRight_comp_linearHomComplexRightEvaluation`), so the
operator of a sewing is the composite of the operators of `F` and `G`
(`TauCeti.linearHomComplexTensorDualHomEquiv_linearHomComplexSewing`). This is how counts of
moduli spaces are composed when broken configurations are glued along an intermediate end: the
functional of the composite operation is the sewing of the functionals of its pieces.

## Main definitions

* `TauCeti.linearHomComplexRightEvaluation`: the right evaluation `A ⊗ A∨ ⟶ R[0]`.
* `TauCeti.linearHomComplexSewing`: the sewing of functionals on `A ⊗ B∨` and `B ⊗ C∨` into a
  functional on `A ⊗ C∨`.

## Main results

* `TauCeti.singleObjXSelf_hom_linearHomComplexRightEvaluation_f_apply`: the value `(-1)^p φ(a)`
  of the right evaluation.
* `TauCeti.linearHomComplexTensorDualHomEquiv_symm_apply_eq_whiskerRight_comp`: the functional of
  a chain map.
* `TauCeti.linearHomComplexTensorDualHomEquiv_linearHomComplexRightEvaluation`: the identity
  functional is the right evaluation.
* `TauCeti.linearHomComplexSewing_whiskerRight_comp_linearHomComplexRightEvaluation`: sewing the
  functional of a chain map composes with it.
* `TauCeti.linearHomComplexTensorDualHomEquiv_linearHomComplexSewing`: the operator of a sewing is
  the composite of the operators.
* `TauCeti.linearHomComplexSewing_assoc`,
  `TauCeti.linearHomComplexSewing_linearHomComplexRightEvaluation_left` and
  `TauCeti.linearHomComplexSewing_linearHomComplexRightEvaluation_right`: sewing is associative,
  with the right evaluations as units.

## References

* C. A. Weibel, *An introduction to homological algebra*, Section 2.7, on the Hom and tensor
  complexes and their sign conventions.
* P. Etingof, S. Gelaki, D. Nikshych and V. Ostrik, *Tensor categories*, Mathematical Surveys and
  Monographs 205, AMS, 2015, Section 2.10, on exact pairings and the snake identities.
-/

public section

open CategoryTheory Limits MonoidalCategory BraidedCategory CochainComplex
  CochainComplex.HomComplex
open scoped TensorProduct

namespace TauCeti

universe v

variable {R : Type v} [CommRing R]

section RightEvaluation

variable (R) in
/-- The **right evaluation** `A ⊗ A∨ ⟶ R[0]` of a cochain complex of `R`-modules and its dual
complex: the Koszul interchange of the two factors followed by the evaluation `A∨ ⊗ A ⟶ R[0]`.
It sends `a ⊗ φ` to `(-1)^p φ(a)` for `a` in `Aᵖ`
(`TauCeti.singleObjXSelf_hom_linearHomComplexRightEvaluation_f_apply`). -/
noncomputable def linearHomComplexRightEvaluation (A : CochainComplex (ModuleCat.{v} R) ℤ) :
    A ⊗ linearDual R A ⟶ 𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ) :=
  (β_ A (linearDual R A)).hom ≫ linearHomComplexEvaluation R A

/-- The right evaluation is the interchange of the factors followed by the evaluation. -/
lemma linearHomComplexRightEvaluation_def (A : CochainComplex (ModuleCat.{v} R) ℤ) :
    linearHomComplexRightEvaluation R A =
      (β_ A (linearDual R A)).hom ≫ linearHomComplexEvaluation R A :=
  (rfl)

/-- **The value of the right evaluation.** On `a ⊗ φ`, for `a` in `Aᵖ` and a form `φ` on `Aᵖ`, of
degree `-p`, the right evaluation is `(-1)^p φ(a)`: the evaluation has no sign, and the Koszul sign
of interchanging the factors is `(-1)^(p (-p)) = (-1)^p`. -/
@[simp]
theorem singleObjXSelf_hom_linearHomComplexRightEvaluation_f_apply
    (A : CochainComplex (ModuleCat.{v} R) ℤ) {p : ℤ} (a : A.X p) (φ : (linearDual R A).X (-p)) :
    (dsimp% only [linearHomComplex_X]
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).hom.hom
        (((linearHomComplexRightEvaluation R A).f 0).hom
          ((HomologicalComplex.ιTensorObj A (linearDual R A) p (-p) 0
            (add_neg_cancel p)).hom (a ⊗ₜ φ)))) =
      p.negOnePow • linearDualXEquiv A (add_neg_cancel p) φ a := by
  have hβ := congrArg (fun f => f.hom (a ⊗ₜ φ))
    (HomologicalComplex.ιTensorObj_tensorBraiding_hom_f A (linearDual R A) p (-p) 0
      (add_neg_cancel p))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ComplexShape.σ_up_ℤ, mul_neg,
    Int.negOnePow_neg, Int.negOnePow_mul_self, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.smul_apply, ModuleCat.MonoidalCategory.braiding_hom_apply] at hβ
  rw [linearHomComplexRightEvaluation_def, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, braiding_eq_tensorBraiding, hβ, Units.smul_def, map_zsmul,
    map_zsmul, singleObjXSelf_hom_linearHomComplexEvaluation_f_apply]

end RightEvaluation

section Functional

variable {A B : CochainComplex (ModuleCat.{v} R) ℤ} [∀ p, Module.IsReflexive R (B.X p)]

/-- **The functional of an operator.** The functional on `A ⊗ B∨` of a chain map `T : A ⟶ B` is
`T` on the first factor followed by the right evaluation of `B`. -/
theorem linearHomComplexTensorDualHomEquiv_symm_apply_eq_whiskerRight_comp (T : A ⟶ B) :
    (linearHomComplexTensorDualHomEquiv R A B).symm T =
      T ▷ linearDual R B ≫ linearHomComplexRightEvaluation R B := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  replace hpq : p + q = j := hpq
  -- Both sides lie in the degree-`j` term of `R[0]`, which vanishes unless `j = 0`.
  by_cases hj : j = 0
  swap
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hj).eq_of_tgt _ _
  subst hj
  obtain rfl : q = -p := by omega
  refine (cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).hom).1 ?_
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a φ
  simp only [Category.assoc, ModuleCat.hom_comp, LinearMap.comp_apply]
  have h := singleObjXSelf_hom_linearHomComplexTensorDualHomEquiv_symm_f_apply T a φ
  have h' := singleObjXSelf_hom_linearHomComplexRightEvaluation_f_apply B ((T.f p).hom a) φ
  have hw := congrArg (fun f => f.hom (a ⊗ₜ φ))
    (HomologicalComplex.ι_whiskerRight T (linearDual R B) p (-p) 0 (add_neg_cancel p))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply] at hw
  refine h.trans ?_
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact h'.symm.trans (congrArg (fun x => (HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (𝟙_ (ModuleCat.{v} R))).hom.hom (((linearHomComplexRightEvaluation R B).f 0).hom x)) hw.symm)

/-- The operator of the functional `T ▷ B∨ ≫ ε'`, for the right evaluation `ε'` of `B`, is `T`. -/
@[simp]
theorem linearHomComplexTensorDualHomEquiv_whiskerRight_comp_linearHomComplexRightEvaluation
    (T : A ⟶ B) :
    linearHomComplexTensorDualHomEquiv R A B
        (T ▷ linearDual R B ≫ linearHomComplexRightEvaluation R B) = T := by
  rw [← linearHomComplexTensorDualHomEquiv_symm_apply_eq_whiskerRight_comp,
    Equiv.apply_symm_apply]

/-- **The identity functional is the right evaluation.** The functional on `A ⊗ A∨` whose operator
is the identity of `A` is the right evaluation `a ⊗ φ ↦ (-1)^p φ(a)`, not the evaluation. -/
@[simp]
theorem linearHomComplexTensorDualHomEquiv_linearHomComplexRightEvaluation
    [∀ p, Module.IsReflexive R (A.X p)] :
    linearHomComplexTensorDualHomEquiv R A A (linearHomComplexRightEvaluation R A) = 𝟙 A := by
  simpa using
    linearHomComplexTensorDualHomEquiv_whiskerRight_comp_linearHomComplexRightEvaluation (𝟙 A)

end Functional

section Sewing

variable {A B C : CochainComplex (ModuleCat.{v} R) ℤ} [IsIso (linearHomComplexDualTensor R B B)]

/-- The **sewing** of a functional `F` on `A ⊗ B∨` and a functional `G` on `B ⊗ C∨`: the functional
on `A ⊗ C∨` that inserts the coevaluation `R[0] ⟶ B∨ ⊗ B` of the braided pairing `(B∨, B)`, the
coevaluation of `B` followed by the interchange, between `A` and `C∨`, and applies `F ⊗ G`:
`A ⊗ C∨ ⟶ A ⊗ (B∨ ⊗ B) ⊗ C∨ ≅ (A ⊗ B∨) ⊗ (B ⊗ C∨) ⟶ R[0]`. This is `TauCeti.ExactPairing.sewing`
along that pairing. Its operator is the composite of the operators of `F` and `G`
(`TauCeti.linearHomComplexTensorDualHomEquiv_linearHomComplexSewing`). -/
noncomputable def linearHomComplexSewing (F : A ⊗ linearDual R B ⟶ 𝟙_ _)
    (G : B ⊗ linearDual R C ⟶ 𝟙_ _) : A ⊗ linearDual R C ⟶ 𝟙_ _ :=
  @ExactPairing.sewing _ _ _ A (linearDual R B) B (linearDual R C)
    (@exactPairing_swap _ _ _ _ B (linearDual R B) (exactPairingLinearHomComplex B)) F G

/-- The evaluation of the braided exact pairing `(B∨, B)`, obtained from `(B, B∨)` by
`CategoryTheory.BraidedCategory.exactPairing_swap`, is the right evaluation of `B`. -/
lemma exactPairing_swap_evaluation_eq_linearHomComplexRightEvaluation :
    @ExactPairing.evaluation _ _ _ (linearDual R B) B
        (@exactPairing_swap _ _ _ _ B (linearDual R B) (exactPairingLinearHomComplex B)) =
      linearHomComplexRightEvaluation R B :=
  (rfl)

/-- The coevaluation of the braided exact pairing `(B∨, B)`, obtained from `(B, B∨)` by
`CategoryTheory.BraidedCategory.exactPairing_swap`, is the coevaluation of `B` followed by the
interchange of the factors. -/
lemma exactPairing_swap_coevaluation_eq_linearHomComplexCoevaluation_comp :
    @ExactPairing.coevaluation _ _ _ (linearDual R B) B
        (@exactPairing_swap _ _ _ _ B (linearDual R B) (exactPairingLinearHomComplex B)) =
      linearHomComplexCoevaluation R B ≫ (β_ (linearDual R B) B).inv :=
  (rfl)

/-- The sewing of functionals on `A ⊗ B∨` and `B ⊗ C∨` is the sewing along the braided exact
pairing `(B∨, B)`. -/
lemma linearHomComplexSewing_def (F : A ⊗ linearDual R B ⟶ 𝟙_ _)
    (G : B ⊗ linearDual R C ⟶ 𝟙_ _) :
    linearHomComplexSewing F G =
      @ExactPairing.sewing _ _ _ A (linearDual R B) B (linearDual R C)
        (@exactPairing_swap _ _ _ _ B (linearDual R B) (exactPairingLinearHomComplex B)) F G :=
  (rfl)

/-- **Sewing with the functional of an operator on the left.** Sewing the functional
`T ▷ B∨ ≫ ε'` of a chain map `T : A ⟶ B`, for the right evaluation `ε'` of `B`, with a functional
`G` on `B ⊗ C∨` is `T ▷ C∨ ≫ G`. -/
@[simp]
theorem linearHomComplexSewing_whiskerRight_comp_linearHomComplexRightEvaluation (T : A ⟶ B)
    (G : B ⊗ linearDual R C ⟶ 𝟙_ _) :
    linearHomComplexSewing (T ▷ linearDual R B ≫ linearHomComplexRightEvaluation R B) G =
      T ▷ linearDual R C ≫ G := by
  let := @exactPairing_swap _ _ _ _ B (linearDual R B) (exactPairingLinearHomComplex B)
  rw [linearHomComplexSewing_def, ← exactPairing_swap_evaluation_eq_linearHomComplexRightEvaluation,
    ExactPairing.sewing_whiskerRight_comp_evaluation]

/-- **The operator of a sewing is the composite of the operators.** Sewing a functional on
`A ⊗ B∨` with a functional on `B ⊗ C∨` along the braided coevaluation of `B` gives the functional
on `A ⊗ C∨` of the composite of their operators. -/
@[simp]
theorem linearHomComplexTensorDualHomEquiv_linearHomComplexSewing
    [∀ p, Module.IsReflexive R (B.X p)] [∀ p, Module.IsReflexive R (C.X p)]
    (F : A ⊗ linearDual R B ⟶ 𝟙_ _) (G : B ⊗ linearDual R C ⟶ 𝟙_ _) :
    linearHomComplexTensorDualHomEquiv R A C (linearHomComplexSewing F G) =
      linearHomComplexTensorDualHomEquiv R A B F ≫ linearHomComplexTensorDualHomEquiv R B C G := by
  obtain ⟨T, rfl⟩ := (linearHomComplexTensorDualHomEquiv R A B).symm.surjective F
  obtain ⟨S, rfl⟩ := (linearHomComplexTensorDualHomEquiv R B C).symm.surjective G
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    linearHomComplexTensorDualHomEquiv_symm_apply_eq_whiskerRight_comp T,
    linearHomComplexSewing_whiskerRight_comp_linearHomComplexRightEvaluation,
    linearHomComplexTensorDualHomEquiv_symm_apply_eq_whiskerRight_comp, ← Category.assoc,
    ← comp_whiskerRight,
    linearHomComplexTensorDualHomEquiv_whiskerRight_comp_linearHomComplexRightEvaluation]

/-- **Sewing with the identity functional on the left.** Sewing the right evaluation of `B`, the
identity functional on `B ⊗ B∨`, with a functional `G` on `B ⊗ C∨` gives `G`. -/
@[simp]
theorem linearHomComplexSewing_linearHomComplexRightEvaluation_left
    (G : B ⊗ linearDual R C ⟶ 𝟙_ _) :
    linearHomComplexSewing (linearHomComplexRightEvaluation R B) G = G := by
  let := @exactPairing_swap _ _ _ _ B (linearDual R B) (exactPairingLinearHomComplex B)
  rw [linearHomComplexSewing_def, ← exactPairing_swap_evaluation_eq_linearHomComplexRightEvaluation,
    ExactPairing.sewing_evaluation_left]

/-- **Sewing with the identity functional on the right.** Sewing a functional `F` on `A ⊗ B∨` with
the right evaluation of `B`, the identity functional on `B ⊗ B∨`, gives `F`. -/
@[simp]
theorem linearHomComplexSewing_linearHomComplexRightEvaluation_right
    (F : A ⊗ linearDual R B ⟶ 𝟙_ _) :
    linearHomComplexSewing F (linearHomComplexRightEvaluation R B) = F := by
  let := @exactPairing_swap _ _ _ _ B (linearDual R B) (exactPairingLinearHomComplex B)
  rw [linearHomComplexSewing_def, ← exactPairing_swap_evaluation_eq_linearHomComplexRightEvaluation,
    ExactPairing.sewing_evaluation_right]

/-- **Sewing is associative.** For functionals on `A ⊗ B∨`, `B ⊗ C∨` and `C ⊗ D∨`, sewing along
`B` and then along `C` gives the same functional on `A ⊗ D∨` as sewing along `C` and then along
`B`. -/
theorem linearHomComplexSewing_assoc {D : CochainComplex (ModuleCat.{v} R) ℤ}
    [IsIso (linearHomComplexDualTensor R C C)]
    (F : A ⊗ linearDual R B ⟶ 𝟙_ _) (G : B ⊗ linearDual R C ⟶ 𝟙_ _)
    (H : C ⊗ linearDual R D ⟶ 𝟙_ _) :
    linearHomComplexSewing (linearHomComplexSewing F G) H =
      linearHomComplexSewing F (linearHomComplexSewing G H) :=
  let := @exactPairing_swap _ _ _ _ B (linearDual R B) (exactPairingLinearHomComplex B)
  let := @exactPairing_swap _ _ _ _ C (linearDual R C) (exactPairingLinearHomComplex C)
  ExactPairing.sewing_assoc F G H

end Sewing

end TauCeti
