/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Total.Augmentation
public import Mathlib.CategoryTheory.Abelian.Basic

import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients
import TauCeti.Algebra.Homology.Embedding.MapExtend
import TauCeti.Algebra.Homology.TotalComplex.UpInt
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Data.Int.Interval

/-!
# Bounded-below Čech totalization

A common strict lower bound on the coefficient complexes makes each total degree contain
only finitely many nonzero Čech summands. Termwise acyclic augmented Čech complexes then
make the canonical total augmentation a quasi-isomorphism.

## References

* The Stacks Project, Cohomology of Sheaves, Lemma 20.25.1 (tag 08BN): the bounded-below
  total Čech comparison.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite HomologicalComplex₂

universe w v u v' u'

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] {ι : Type w} (U : ι → C)

section

variable [Preadditive A] [HasZeroObject A] [HasProducts.{w} A]
  (P : Cᵒᵖ ⥤ CochainComplex A ℤ)

private abbrev cechEvalXIso (q : ℤ) (p : ℕ) :
    (((cechComplexFunctor U).obj P).X p).X q ≅
      ((cechComplexFunctor U).obj (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q)).X p :=
  (HomologicalComplex.eval A (ComplexShape.up ℕ) p).mapIso
    ((cechComplexFunctorMapIso U (HomologicalComplex.eval A (ComplexShape.up ℤ) q)).app P)

omit [HasZeroObject A] in
private lemma isZero_cechEvalX (b : ℤ)
    (hP : ∀ X q, q < b → IsZero ((P.obj X).X q)) (p : ℕ) (q : ℤ) (hq : q < b) :
    IsZero ((((cechComplexFunctor U).obj P).X p).X q) := by
  apply IsZero.of_iso _ (cechEvalXIso U P q p)
  apply IsZero.of_iso _ (cechXIso U
    (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q) p)
  refine (IsZero.iff_id_eq_zero _).2 (Pi.hom_ext _ _ fun a ↦ ?_)
  exact (hP _ q hq).eq_of_tgt _ _

private lemma isZero_extendedCechX (b : ℤ)
    (hP : ∀ X q, q < b → IsZero ((P.obj X).X q)) (p q : ℤ)
    (h : p < 0 ∨ q < b) :
    IsZero (((((cechComplexFunctor U).obj P).extend
      ComplexShape.embeddingUpNat).X p).X q) := by
  have hz (hp : p < 0) : IsZero (((((cechComplexFunctor U).obj P).extend
      ComplexShape.embeddingUpNat).X p).X q) := by
    apply (HomologicalComplex.eval A (ComplexShape.up ℤ) q).map_isZero
    apply ((cechComplexFunctor U).obj P).isZero_extend_X ComplexShape.embeddingUpNat p
    intro n hn
    -- The nonnegative-grading embedding sends a natural number to its integer cast.
    change (n : ℤ) = p at hn
    omega
  rcases h with hp | hq
  · exact hz hp
  · by_cases hp : 0 ≤ p
    · exact IsZero.of_iso (isZero_cechEvalX U P b hP p.toNat q hq)
        ((HomologicalComplex.eval A (ComplexShape.up ℤ) q).mapIso
          (((cechComplexFunctor U).obj P).extendXIso ComplexShape.embeddingUpNat
            (i := p.toNat) (by simpa using Int.toNat_of_nonneg hp)))
    · exact hz (by omega)

private def extendedCechRowIso (q : ℤ) :
    (HomologicalComplex₂.flip
      (((cechComplexFunctor U).obj P).extend ComplexShape.embeddingUpNat)).X q ≅
      ((cechComplexFunctor U).obj
        (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q)).extend
          ComplexShape.embeddingUpNat :=
  HomologicalComplex.mapExtendIso (HomologicalComplex.eval A (ComplexShape.up ℤ) q)
    ((cechComplexFunctor U).obj P) ComplexShape.embeddingUpNat ≪≫
      (ComplexShape.embeddingUpNat.extendFunctor A).mapIso
        ((cechComplexFunctorMapIso U (HomologicalComplex.eval A (ComplexShape.up ℤ) q)).app P)

variable {T : C} (hT : IsTerminal T)

private lemma cechAugmentation_eval_f_zero (q : ℤ) :
    ((cechAugmentation U hT P).f 0).f q ≫
        ((cechComplexFunctorMapIso U
          (HomologicalComplex.eval A (ComplexShape.up ℤ) q)).hom.app P).f 0 =
      (cechAugmentation U hT (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q)).f 0 := by
  refine Pi.hom_ext _ _ fun a ↦ ?_
  have h₁ := cechComplexFunctorMapIso_hom_app_f_π U
    (HomologicalComplex.eval A (ComplexShape.up ℤ) q) P 0 a
  have h₂ := congrArg (fun f ↦ f.f q) (cechAugmentation_f_zero_comp_π U hT P a)
  have h₃ := cechAugmentation_f_zero_comp_π U hT
    (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q) a
  exact (Category.assoc _ _ _).trans <| (_ ≫= h₁).trans <|
    ((HomologicalComplex.eval A (ComplexShape.up ℤ) q).map_comp _ _).symm.trans <|
      h₂.trans h₃.symm

private lemma rowCoaugmentationUpInt_comp_extendedCechRowIso (q : ℤ) :
    rowCoaugmentationUpInt _ (cechTotalComplexAugmentationColumn U hT P)
        (cechTotalComplexAugmentationColumn_comp_d U hT P) q ≫
      (extendedCechRowIso U P q).hom =
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      ((P.obj (op T)).X q) 0 0 rfl).inv ≫
        HomologicalComplex.extendMap
          (cechAugmentation U hT (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q))
            ComplexShape.embeddingUpNat := by
  apply HomologicalComplex.from_single_hom_ext
  apply (cancel_epi (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    ((P.obj (op T)).X q)).inv).mp
  simp only [HomologicalComplex.comp_f]
  rw [rowCoaugmentationUpInt_f_zero_assoc]
  rw [cechTotalComplexAugmentationColumn_def]
  simp only [extendedCechRowIso, Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom]
  dsimp only [ComplexShape.Embedding.extendFunctor]
  rw [HomologicalComplex.mapExtendIso_hom_f _ _ _ (j := 0) (j' := (0 : ℤ)) rfl,
    HomologicalComplex.extendMap_f _ _ (i := 0) (i' := (0 : ℤ)) rfl,
    HomologicalComplex.extendMap_f _ _ (i := 0) (i' := (0 : ℤ)) rfl,
    HomologicalComplex.extendSingleIso_inv_f ComplexShape.embeddingUpNat
      ((P.obj (op T)).X q) (0 : ℕ) (0 : ℤ) rfl]
  simp only [HomologicalComplex.eval_map, Category.assoc,
    Iso.inv_hom_id_assoc]
  simp only [← HomologicalComplex.comp_f_assoc, Iso.inv_hom_id,
    HomologicalComplex.id_f, Category.id_comp]
  simp only [CochainComplex.single₀ObjXSelf, Iso.refl_inv]
  dsimp only [Functor.comp_obj, HomologicalComplex.eval_obj, CochainComplex.single₀]
  simp only [Iso.inv_hom_id_assoc]
  exact (congrArg (fun f ↦ f.f q) (Category.id_comp ((cechAugmentation U hT P).f 0)) =≫ _).trans
    ((Category.assoc _ _ _).symm.trans <|
      (cechAugmentation_eval_f_zero U P hT q =≫ _).trans (Category.id_comp _).symm)

end

section

variable [Abelian A] [HasProducts.{w} A] [HasCoproducts.{0} A]
  (P : Cᵒᵖ ⥤ CochainComplex A ℤ) {T : C} (hT : IsTerminal T)

/-- A presheaf of complexes with a common strict lower bound is computed by the total Čech
complex whenever every term has a quasi-isomorphic augmented Čech complex. -/
theorem quasiIso_cechTotalComplexAugmentation (b : ℤ)
    (hP : ∀ X q, q < b → IsZero ((P.obj X).X q))
    (hrows : ∀ q : ℤ, QuasiIso
      (cechAugmentation U hT (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q))) :
    QuasiIso (cechTotalComplexAugmentation U hT P) := by
  have hfin (n : ℤ) : {p : ℤ | ¬ IsZero
      (((((cechComplexFunctor U).obj P).extend
        ComplexShape.embeddingUpNat).X p).X (n - p))}.Finite := by
    apply (Set.finite_Icc (0 : ℤ) (n - b)).subset
    intro p hp
    constructor
    · by_contra h
      exact hp (isZero_extendedCechX U P b hP p (n - p) (Or.inl (by omega)))
    · by_contra h
      exact hp (isZero_extendedCechX U P b hP p (n - p) (Or.inr (by omega)))
  have hr (q : ℤ) : QuasiIso
      (rowCoaugmentationUpInt _ (cechTotalComplexAugmentationColumn U hT P)
        (cechTotalComplexAugmentationColumn_comp_d U hT P) q) := by
    have := hrows q
    have he : QuasiIso
        ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
          ((P.obj (op T)).X q) 0 0 rfl).inv ≫
            HomologicalComplex.extendMap
              (cechAugmentation U hT (P ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q))
                ComplexShape.embeddingUpNat) := by infer_instance
    rw [← rowCoaugmentationUpInt_comp_extendedCechRowIso] at he
    exact (quasiIso_iff_comp_right _ (extendedCechRowIso U P q).hom).1 he
  have he : cechTotalComplexAugmentation U hT P =
      totalCoaugmentationUpInt _ (cechTotalComplexAugmentationColumn U hT P)
        (cechTotalComplexAugmentationColumn_comp_d U hT P) := by
    ext n
    simp only [cechTotalComplexAugmentation_f, totalCoaugmentationUpInt_f,
      cechTotalComplexAugmentationColumn_def]
  rw [he]
  exact quasiIso_totalCoaugmentationUpInt _ _ _ hfin hr

end

end TauCeti.CategoryTheory
