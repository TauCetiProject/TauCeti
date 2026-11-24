/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.Zero
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import TauCeti.Algebra.Homology.Homotopy

/-!
# Category homology of a category with a terminal object

When `C` has a terminal object `t`, appending `ht.from σ.right` via
`CategoryTheory.ComposableArrows.postcomp` gives an extra degeneracy on `nerve C` fixing vertex `0`,
contracting `categoryChainComplex M` to `(ChainComplex.single₀ A).obj (M.obj t)`
(`TauCeti.categoryChainComplexToSingle₀OfIsTerminal`, `TauCeti.categoryChainComplexFromSingle₀`,
`TauCeti.categoryChainComplexContractingHomotopy`, `TauCeti.categoryHomology₀IsoOfIsTerminal`,
`TauCeti.categoryChainComplexHomotopyEquivSingle₀OfIsTerminal`, and
`TauCeti.isZero_categoryHomology_succ_of_isTerminal`).

## References

* P. Gabriel and M. Zisman, *Calculus of Fractions and Homotopy Theory* (1967), Appendix II, §3.
* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 91
  (see also §1, Prop. 2, Cor. 2, p. 92).
* C. A. Weibel, *The K-book*, Grad. Stud. Math. 145 (2013), Chapter IV, §3.5.
-/

public section

noncomputable section

open CategoryTheory Category Limits Simplicial

universe u v u' v'

namespace TauCeti

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Preadditive A]

private def ιPostcompTerminal (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) {t : C}
    (ht : IsTerminal t) : M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X (n + 1) :=
  eqToHom (congrArg M.obj (σ.postcomp_obj_zero (ht.from σ.right)).symm) ≫
    ιCategoryChainComplex M (σ.postcomp (ht.from σ.right))

private lemma eqToHom_ιCategoryChainComplex_postcomp (M : C ⥤ A) {n : ℕ}
    {σ : ComposableArrows C (n + 1)} {τ : ComposableArrows C n} {t : C} (ht : IsTerminal t)
    (h : σ = τ.postcomp (ht.from τ.right)) (h0 : σ.obj 0 = τ.obj 0) :
    eqToHom (congrArg M.obj h0.symm) ≫ ιCategoryChainComplex M σ = ιPostcompTerminal M τ ht := by
  rw [ιCategoryChainComplex_congr M h, eqToHom_trans_assoc]; rfl

private lemma ιPostcompTerminal_mk₀ (M : C ⥤ A) (X : C) {t : C} (ht : IsTerminal t) :
    ιPostcompTerminal M (.mk₀ X) ht = ιCategoryChainComplex₁ M (ht.from X) :=
  (ιCategoryChainComplex_congr M (ComposableArrows.mk₀_postcomp (ht.from X)).symm
    ((ComposableArrows.mk₀ X).postcomp_obj_zero (ht.from X)).symm).symm

private lemma ιPostcompTerminal_d_succ (M : C ⥤ A) {m : ℕ} (σ : ComposableArrows C (m + 1))
    {t : C} (ht : IsTerminal t) :
    ιPostcompTerminal M σ ht ≫ (categoryChainComplex M).d (m + 2) (m + 1) =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
          ιPostcompTerminal M ((nerve C).δ 0 σ) ht +
        (∑ j : Fin (m + 1),
          (-1 : ℤ) ^ (j.val + 1) • ιPostcompTerminal M ((nerve C).δ j.succ σ) ht) +
        (-1 : ℤ) ^ (m + 2) • ιCategoryChainComplex M σ := by
  have h0 := ((reassoc_of% (σ.eqToHom_postcomp_map_zero_one M (ht.from σ.right))) _).trans <|
    congrArg (M.map _ ≫ ·) <| eqToHom_ιCategoryChainComplex_postcomp M ht
      (nerve.δ_zero_postcomp σ (ht.from σ.right)) (σ.postcomp_obj_succ_zero (ht.from σ.right))
  have hj (j : Fin (m + 1)) := eqToHom_ιCategoryChainComplex_postcomp M ht
    ((nerve.δ_castSucc_postcomp j.succ σ (ht.from σ.right)).trans
      (congrArg (((nerve C).δ j.succ σ).postcomp) (ht.hom_ext _ (ht.from _))))
    (σ.postcomp_obj_zero (ht.from σ.right))
  have hlast : eqToHom (congrArg M.obj (σ.postcomp_obj_zero (ht.from σ.right)).symm) ≫
      ιCategoryChainComplex M ((nerve C).δ (Fin.last (m + 2)) (σ.postcomp (ht.from σ.right))) =
      ιCategoryChainComplex M σ :=
    (ιCategoryChainComplex_congr M (nerve.δ_last_postcomp σ (ht.from σ.right)).symm
      (σ.postcomp_obj_zero (ht.from σ.right)).symm).symm
  have hsum : eqToHom (congrArg M.obj (σ.postcomp_obj_zero (ht.from σ.right)).symm) ≫
      (∑ j : Fin (m + 2), (-1 : ℤ) ^ (j.val + 1) •
        (ιCategoryChainComplex M ((nerve C).δ j.succ (σ.postcomp (ht.from σ.right))) :
          M.obj ((σ.postcomp (ht.from σ.right)).obj 0) ⟶ (categoryChainComplex M).X (m + 1))) =
      (∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) • ιPostcompTerminal M ((nerve C).δ j.succ σ) ht) +
        (-1 : ℤ) ^ (m + 2) • ιCategoryChainComplex M σ :=
    (Preadditive.comp_sum _ _ _).trans <| (Fin.sum_univ_castSucc _).trans <| congrArg₂ (· + ·)
      (Finset.sum_congr rfl fun j _ ↦
        (Preadditive.comp_zsmul _ _ _).trans (congrArg (_ • ·) (hj j)))
      ((Preadditive.comp_zsmul _ _ _).trans (congrArg (_ • ·) hlast))
  exact (assoc _ _ _).trans <| (congrArg _ (ιCategoryChainComplex_d M _)).trans <|
    (Preadditive.comp_add _ _ _ _ _ _).trans <|
      (congrArg₂ (· + ·) h0 hsum).trans (add_assoc _ _ _).symm

private def contractingHomotopyStep (M : C ⥤ A) {t : C} (ht : IsTerminal t) (n : ℕ) :
    (categoryChainComplex M).X n ⟶ (categoryChainComplex M).X (n + 1) :=
  descCategoryChainComplex M fun σ ↦ (-1 : ℤ) ^ (n + 1) • ιPostcompTerminal M σ ht

@[reassoc (attr := simp)] private lemma ι_contractingHomotopyStep (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ ≫ contractingHomotopyStep M ht n =
      (-1 : ℤ) ^ (n + 1) • ιPostcompTerminal M σ ht := ιCategoryChainComplex_desc M _ σ

@[reassoc] private lemma ι₀_contractingHomotopyStep (M : C ⥤ A) {t : C} (ht : IsTerminal t)
    (X : C) : ιCategoryChainComplex₀ M X ≫ contractingHomotopyStep M ht 0 =
      -ιCategoryChainComplex₁ M (ht.from X) :=
  (ι_contractingHomotopyStep M ht (.mk₀ X)).trans (by simp [ιPostcompTerminal_mk₀]; abel)

private lemma ιCategoryChainComplex_d_contractingHomotopyStep (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) {m : ℕ} (σ : ComposableArrows C (m + 1)) :
    ιCategoryChainComplex M σ ≫
        (categoryChainComplex M).d (m + 1) m ≫ contractingHomotopyStep M ht m =
      (-1 : ℤ) ^ (m + 1) • ((M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
        ιPostcompTerminal M ((nerve C).δ 0 σ) ht) + ∑ j : Fin (m + 1),
          (-1 : ℤ) ^ (j.val + 1) • ιPostcompTerminal M ((nerve C).δ j.succ σ) ht) := by
  have h0 := (assoc (M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))))
    (ιCategoryChainComplex M ((nerve C).δ 0 σ)) (contractingHomotopyStep M ht m)).trans <|
      (congrArg _ (ι_contractingHomotopyStep M ht _)).trans (Preadditive.comp_zsmul _ _ _)
  have hsum : (∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) •
      (ιCategoryChainComplex M ((nerve C).δ j.succ σ) :
        M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X m)) ≫ contractingHomotopyStep M ht m =
      (-1 : ℤ) ^ (m + 1) • (∑ j : Fin (m + 1),
        (-1 : ℤ) ^ (j.val + 1) • ιPostcompTerminal M ((nerve C).δ j.succ σ) ht :
          M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X (m + 1)) := by
    refine (Preadditive.sum_comp _ _ _).trans ((Finset.sum_congr rfl fun j _ ↦ ?_).trans
      Finset.smul_sum.symm)
    exact (Preadditive.zsmul_comp _ _ _).trans <|
      (congrArg _ (ι_contractingHomotopyStep M ht _)).trans <|
        (mul_zsmul _ _ _).symm.trans ((congrArg (· • _) (mul_comm _ _)).trans (mul_zsmul _ _ _))
  exact (ιCategoryChainComplex_d_assoc M σ _).trans <| (Preadditive.add_comp _ _ _ _ _ _).trans <|
    (congrArg₂ (· + ·) h0 hsum).trans (smul_add ((-1 : ℤ) ^ (m + 1)) _ _).symm

private lemma contractingHomotopyStep_comm_succ (M : C ⥤ A) {t : C} (ht : IsTerminal t) (m : ℕ) :
    (categoryChainComplex M).d (m + 1) m ≫ contractingHomotopyStep M ht m +
        contractingHomotopyStep M ht (m + 1) ≫ (categoryChainComplex M).d (m + 2) (m + 1) =
      𝟙 ((categoryChainComplex M).X (m + 1)) := by
  ext σ
  have hcancel (a w : M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X (m + 1)) :
      (-1 : ℤ) ^ (m + 1) • a + (-1 : ℤ) ^ (m + 2) • (a + (-1 : ℤ) ^ (m + 2) • w) = w := by
    simp [← mul_zsmul, ← mul_pow, pow_succ (-1 : ℤ) (m + 1)]
  rw [Preadditive.comp_add, comp_id, ιCategoryChainComplex_d_contractingHomotopyStep,
    ι_contractingHomotopyStep_assoc, Preadditive.zsmul_comp, ιPostcompTerminal_d_succ]
  exact hcancel _ _

section WithZeroObject

variable [HasZeroObject A]

/-- Augmentation chain map `categoryChainComplex M ⟶ (ChainComplex.single₀ A).obj (M.obj t)`. -/
def categoryChainComplexToSingle₀OfIsTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    categoryChainComplex M ⟶ (ChainComplex.single₀ A).obj (M.obj t) :=
  (ChainComplex.toSingle₀Equiv (categoryChainComplex M) (M.obj t)).symm
    ⟨descCategoryChainComplex₀ M (coconeOfDiagramTerminal ht M).ι.app,
      d_descCategoryChainComplex₀_cocone M (coconeOfDiagramTerminal ht M)⟩

@[simp] lemma categoryChainComplexToSingle₀OfIsTerminal_f_zero (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) : (categoryChainComplexToSingle₀OfIsTerminal M ht).f 0 =
      descCategoryChainComplex₀ M (fun X ↦ M.map (ht.from X)) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- Inclusion chain map `(ChainComplex.single₀ A).obj (M.obj X) ⟶ categoryChainComplex M`. -/
def categoryChainComplexFromSingle₀ (M : C ⥤ A) (X : C) :
    (ChainComplex.single₀ A).obj (M.obj X) ⟶ categoryChainComplex M :=
  (ChainComplex.fromSingle₀Equiv _ _).symm (ιCategoryChainComplex₀ M X)

@[simp] lemma categoryChainComplexFromSingle₀_f_zero (M : C ⥤ A) (X : C) :
    dsimp% (categoryChainComplexFromSingle₀ M X).f 0 = ιCategoryChainComplex₀ M X :=
  ChainComplex.fromSingle₀Equiv_symm_apply_f_zero _

@[simp] lemma categoryChainComplexFromSingle₀_f_succ (M : C ⥤ A) (X : C) (n : ℕ) :
    (categoryChainComplexFromSingle₀ M X).f (n + 1) = 0 :=
  ChainComplex.fromSingle₀Equiv_symm_apply_f_succ _ n

@[reassoc (attr := simp)]
lemma categoryChainComplexFromSingle₀_comp_categoryChainComplexToSingle₀OfIsTerminal (M : C ⥤ A)
    {t : C} (ht : IsTerminal t) :
    categoryChainComplexFromSingle₀ M t ≫ categoryChainComplexToSingle₀OfIsTerminal M ht = 𝟙 _ := by
  ext; rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]; dsimp; simp

private lemma contractingHomotopyStep_comm_zero (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    contractingHomotopyStep M ht 0 ≫ (categoryChainComplex M).d 1 0 +
        (categoryChainComplexToSingle₀OfIsTerminal M ht ≫
          categoryChainComplexFromSingle₀ M t).f 0 = 𝟙 ((categoryChainComplex M).X 0) := by
  rw [HomologicalComplex.comp_f]; refine categoryChainComplex₀_hom_ext fun X ↦ ?_
  dsimp; simp [ι₀_contractingHomotopyStep_assoc]

/-- Contracting homotopy from `𝟙 (categoryChainComplex M)` to the projection through `M.obj t`. -/
def categoryChainComplexContractingHomotopy (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    Homotopy (𝟙 (categoryChainComplex M))
      (categoryChainComplexToSingle₀OfIsTerminal M ht ≫ categoryChainComplexFromSingle₀ M t) :=
  Homotopy.equivSubZero.symm <| Homotopy.mkChainComplex _ (contractingHomotopyStep M ht)
    (by simpa using sub_eq_of_eq_add (contractingHomotopyStep_comm_zero M ht).symm)
    (fun m ↦ by simp [contractingHomotopyStep_comm_succ])

@[reassoc (attr := simp)] lemma ιCategoryChainComplex_contractingHomotopy_hom (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) (n : ℕ) (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplexContractingHomotopy M ht).hom n (n + 1) =
      (-1 : ℤ) ^ (n + 1) • (eqToHom (congrArg M.obj (σ.postcomp_obj_zero (ht.from σ.right)).symm) ≫
        ιCategoryChainComplex M (σ.postcomp (ht.from σ.right))) := by
  dsimp [categoryChainComplexContractingHomotopy, Homotopy.equivSubZero]
  rw [Homotopy.mkChainComplex_hom_succ, ι_contractingHomotopyStep, ιPostcompTerminal]

/-- Chain homotopy equivalence `categoryChainComplex M ≃ (ChainComplex.single₀ A).obj (M.obj t)`
when `t` is terminal in `C`. -/
def categoryChainComplexHomotopyEquivSingle₀OfIsTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    HomotopyEquiv (categoryChainComplex M) ((ChainComplex.single₀ A).obj (M.obj t)) where
  hom := categoryChainComplexToSingle₀OfIsTerminal M ht
  inv := categoryChainComplexFromSingle₀ M t
  homotopyHomInvId := (categoryChainComplexContractingHomotopy M ht).symm
  homotopyInvHomId := Homotopy.ofEq
    (categoryChainComplexFromSingle₀_comp_categoryChainComplexToSingle₀OfIsTerminal M ht)

@[simp] lemma categoryChainComplexHomotopyEquivSingle₀OfIsTerminal_hom (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) : (categoryChainComplexHomotopyEquivSingle₀OfIsTerminal M ht).hom =
      categoryChainComplexToSingle₀OfIsTerminal M ht := (rfl)

@[simp] lemma categoryChainComplexHomotopyEquivSingle₀OfIsTerminal_inv (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) : (categoryChainComplexHomotopyEquivSingle₀OfIsTerminal M ht).inv =
      categoryChainComplexFromSingle₀ M t := (rfl)

end WithZeroObject

section Homology

variable [CategoryWithHomology A]

/-- When `t` is terminal in `C`, `categoryHomology M 0` is canonically isomorphic to `M.obj t`. -/
def categoryHomology₀IsoOfIsTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    categoryHomology M 0 ≅ M.obj t :=
  (isColimitCategoryHomology₀Cocone M).coconePointUniqueUpToIso (colimitOfDiagramTerminal ht M)

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_isoOfIsTerminal_hom (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) (X : C) :
    ιCategoryHomology₀ M X ≫ (categoryHomology₀IsoOfIsTerminal M ht).hom = M.map (ht.from X) :=
  (isColimitCategoryHomology₀Cocone M).comp_coconePointUniqueUpToIso_hom _ X

@[simp] lemma categoryHomology₀IsoOfIsTerminal_inv (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    (categoryHomology₀IsoOfIsTerminal M ht).inv = ιCategoryHomology₀ M t := by
  rw [← cancel_mono (categoryHomology₀IsoOfIsTerminal M ht).hom, Iso.inv_hom_id,
    ιCategoryHomology₀_isoOfIsTerminal_hom, ht.hom_ext (ht.from t) (𝟙 t), M.map_id]

/-- Higher category homology `categoryHomology M (n + 1)` vanishes when `t` is terminal in `C`. -/
lemma isZero_categoryHomology_succ_of_isTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) (n : ℕ) :
    IsZero (categoryHomology M (n + 1)) := by
  have : HasZeroObject A := Preadditive.hasZeroObject_of_hasCoproduct.{max u v} A
  exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0 (M.obj t)
    (n + 1) (Nat.succ_ne_zero n)).of_iso
      ((categoryChainComplexHomotopyEquivSingle₀OfIsTerminal M ht).toHomologyIso (n + 1))

lemma isZero_categoryHomology_of_isTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) {n : ℕ}
    (hn : n ≠ 0) : IsZero (categoryHomology M n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact isZero_categoryHomology_succ_of_isTerminal M ht m

/-- Canonical isomorphism `categoryHomology M 0 ≅ M.obj (⊤_ C)` when `C` has a terminal object. -/
def categoryHomology₀IsoTerminal (M : C ⥤ A) [HasTerminal C] :
    categoryHomology M 0 ≅ M.obj (⊤_ C) := categoryHomology₀IsoOfIsTerminal M terminalIsTerminal

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_isoTerminal_hom (M : C ⥤ A) [HasTerminal C]
    (X : C) :
    ιCategoryHomology₀ M X ≫ (categoryHomology₀IsoTerminal M).hom = M.map (terminal.from X) :=
  (ιCategoryHomology₀_isoOfIsTerminal_hom M terminalIsTerminal X).trans
    (congrArg M.map (terminal.hom_ext _ _))

@[simp] lemma categoryHomology₀IsoTerminal_inv (M : C ⥤ A) [HasTerminal C] :
    (categoryHomology₀IsoTerminal M).inv = ιCategoryHomology₀ M (⊤_ C) :=
  categoryHomology₀IsoOfIsTerminal_inv M terminalIsTerminal

lemma isZero_categoryHomology_succ_of_hasTerminal (M : C ⥤ A) [HasTerminal C] (n : ℕ) :
    IsZero (categoryHomology M (n + 1)) :=
  isZero_categoryHomology_succ_of_isTerminal M terminalIsTerminal n

lemma isZero_categoryHomology_of_hasTerminal (M : C ⥤ A) [HasTerminal C] {n : ℕ} (hn : n ≠ 0) :
    IsZero (categoryHomology M n) := isZero_categoryHomology_of_isTerminal M terminalIsTerminal hn

end Homology

end TauCeti
