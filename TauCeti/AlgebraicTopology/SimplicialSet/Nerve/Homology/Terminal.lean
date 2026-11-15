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

/-!
# Category homology of a category with a terminal object

When `C` has a terminal object `t`, appending `t` (`CategoryTheory.ComposableArrows.snocTerminal`)
defines an extra degeneracy on `nerve C` fixing vertex `0` and preserving `M : C ⥤ A`, yielding a
contracting homotopy to `(ChainComplex.single₀ A).obj (M.obj t)`:
* `snocTerminal` satisfies `δ (Fin.last (n + 1)) (σ.snocTerminal ht) = σ` and commutes with earlier
  faces;
* `TauCeti.categoryChainComplexHomotopyEquivSingle₀OfIsTerminal` constructs
  `HomotopyEquiv (categoryChainComplex M) ((ChainComplex.single₀ A).obj (M.obj t))`;
* `TauCeti.categoryHomology₀IsoOfIsTerminal` identifies `categoryHomology M 0 ≅ M.obj t`, and
  `TauCeti.isZero_categoryHomology_succ_of_isTerminal` /
  `TauCeti.isZero_categoryHomology_of_isTerminal` prove vanishing for `n ≠ 0` (plus `⊤_ C` forms).

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, Cor. 1, p. 90.
* C. A. Weibel, *The K-book*, Grad. Stud. Math. 145 (2013), Chapter IV, Example 3.5.1, p. IV.28.
-/

public section

noncomputable section

open CategoryTheory Category Limits Simplicial

universe u v u' v'

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C]

private def snocTerminalObj {n : ℕ} (σ : ComposableArrows C n) (t : C) (i : Fin (n + 2)) : C :=
  if hi : i.val < n + 1 then σ.obj ⟨i.val, hi⟩ else t

private lemma snocTerminalObj_pos {n : ℕ} (σ : ComposableArrows C n) (t : C) {i : Fin (n + 2)}
    (hi : i.val < n + 1) : snocTerminalObj σ t i = σ.obj ⟨i.val, hi⟩ := dite_eq_left hi

private lemma snocTerminalObj_neg {n : ℕ} (σ : ComposableArrows C n) (t : C) {i : Fin (n + 2)}
    (hi : ¬ i.val < n + 1) : snocTerminalObj σ t i = t := dite_eq_right hi

/-- Append a terminal object `t` of `C` at the end of `σ : ComposableArrows C n`. -/
def snocTerminal {n : ℕ} (σ : ComposableArrows C n) {t : C} (ht : IsTerminal t) :
    ComposableArrows C (n + 1) where
  obj := snocTerminalObj σ t
  map {i j} f :=
    if hj : j.val < n + 1 then
      have hi : i.val < n + 1 := Nat.lt_of_le_of_lt f.le hj
      eqToHom (snocTerminalObj_pos σ t hi) ≫
        σ.map (homOfLE (show (⟨i.val, hi⟩ : Fin (n + 1)) ≤ ⟨j.val, hj⟩ from f.le)) ≫
          eqToHom (snocTerminalObj_pos σ t hj).symm
    else ht.from (snocTerminalObj σ t i) ≫ eqToHom (snocTerminalObj_neg σ t hj).symm
  map_id i := by
    by_cases hi : i.val < n + 1
    · rw [dite_eq_left hi]; simp
    · rw [dite_eq_right hi, ← cancel_mono (eqToHom (snocTerminalObj_neg σ t hi)),
        assoc, eqToHom_trans, eqToHom_refl, comp_id]
      exact ht.hom_ext _ _
  map_comp {i j k} f g := by
    by_cases hk : k.val < n + 1
    · have hj : j.val < n + 1 := Nat.lt_of_le_of_lt g.le hk
      have hi : i.val < n + 1 := Nat.lt_of_le_of_lt f.le hj
      rw [dite_eq_left hk, dite_eq_left hj, dite_eq_left hk]
      simp only [assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp, ← σ.map_comp_assoc]
      exact congrArg (fun u ↦ eqToHom (snocTerminalObj_pos σ t hi) ≫ σ.map u ≫
        eqToHom (snocTerminalObj_pos σ t hk).symm) (Subsingleton.elim _ _)
    · rw [dite_eq_right hk, ← cancel_mono (eqToHom (snocTerminalObj_neg σ t hk))]
      exact ht.hom_ext _ _

@[simp]
lemma snocTerminal_obj_castSucc {n : ℕ} (σ : ComposableArrows C n) {t : C} (ht : IsTerminal t)
    (j : Fin (n + 1)) : (σ.snocTerminal ht).obj j.castSucc = σ.obj j :=
  snocTerminalObj_pos σ t j.isLt

@[simp]
lemma snocTerminal_obj_zero {n : ℕ} (σ : ComposableArrows C n) {t : C} (ht : IsTerminal t) :
    (σ.snocTerminal ht).obj 0 = σ.obj 0 := by
  rw [← Fin.castSucc_zero]; exact σ.snocTerminal_obj_castSucc ht 0

@[simp]
lemma snocTerminal_obj_last {n : ℕ} (σ : ComposableArrows C n) {t : C} (ht : IsTerminal t) :
    (σ.snocTerminal ht).obj (Fin.last (n + 1)) = t :=
  snocTerminalObj_neg σ t (Nat.lt_irrefl (n + 1))

@[simp]
lemma totalArrow_snocTerminal_castSucc {n : ℕ} (σ : ComposableArrows C n) {t : C}
    (ht : IsTerminal t) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (σ.snocTerminal ht).totalArrow i.castSucc j.castSucc (Fin.castSucc_le_castSucc_iff.mpr hij) =
      σ.totalArrow i j hij := by
  rw [totalArrow_def, totalArrow_def]
  refine Quiver.Total.ext (σ.snocTerminal_obj_castSucc ht i) (σ.snocTerminal_obj_castSucc ht j)
    ((conj_eqToHom_iff_heq _ _ (σ.snocTerminal_obj_castSucc ht i)
      (σ.snocTerminal_obj_castSucc ht j)).mp ?_)
  dsimp [snocTerminal]; rw [dite_eq_left j.isLt]

@[simp]
lemma totalArrow_snocTerminal_last {n : ℕ} (σ : ComposableArrows C n) {t : C}
    (ht : IsTerminal t) (i : Fin (n + 2)) :
    (σ.snocTerminal ht).totalArrow i (Fin.last (n + 1)) (Fin.le_last i) =
      ⟨(σ.snocTerminal ht).obj i, t, ht.from ((σ.snocTerminal ht).obj i)⟩ := by
  rw [totalArrow_def]
  refine Quiver.Total.ext rfl (σ.snocTerminal_obj_last ht)
    ((conj_eqToHom_iff_heq _ _ rfl (σ.snocTerminal_obj_last ht)).mp ?_)
  rw [eqToHom_refl, id_comp, ← cancel_mono (eqToHom (σ.snocTerminal_obj_last ht))]
  exact ht.hom_ext _ _

/-- Appending `t` to the `0`-simplex at `X` yields the `1`-simplex of `ht.from X : X ⟶ t`. -/
@[simp]
lemma mk₀_snocTerminal (X : C) {t : C} (ht : IsTerminal t) :
    (mk₀ X).snocTerminal ht = mk₁ (ht.from X) :=
  ext₁ ((mk₀ X).snocTerminal_obj_zero ht) ((mk₀ X).snocTerminal_obj_last ht) (by
    rw [← cancel_mono (eqToHom ((mk₀ X).snocTerminal_obj_last ht))]; exact ht.hom_ext _ _)

end CategoryTheory.ComposableArrows

namespace CategoryTheory.nerve

variable {C : Type u} [Category.{v} C]

/-- Deleting the last vertex of `σ.snocTerminal ht` recovers `σ`. -/
@[simp]
lemma δ_last_snocTerminal {n : ℕ} (σ : ComposableArrows C n) {t : C} (ht : IsTerminal t) :
    (nerve C).δ (Fin.last (n + 1)) (σ.snocTerminal ht) = σ := by
  refine ComposableArrows.ext_of_totalArrow fun i j hij ↦ ?_
  refine ((σ.snocTerminal ht).totalArrow_whiskerLeft _ i j hij).trans ?_
  change (σ.snocTerminal ht).totalArrow
    ((Fin.last (n + 1)).succAbove i) ((Fin.last (n + 1)).succAbove j) _ = _
  simp only [Fin.succAbove_last]; exact σ.totalArrow_snocTerminal_castSucc ht i j hij

/-- Any face map other than the last commutes with `snocTerminal`. -/
@[simp]
lemma δ_castSucc_snocTerminal {n : ℕ} (k : Fin (n + 2)) (σ : ComposableArrows C (n + 1))
    {t : C} (ht : IsTerminal t) :
    (nerve C).δ k.castSucc (σ.snocTerminal ht) = ((nerve C).δ k σ).snocTerminal ht := by
  let τ : ComposableArrows C n := (nerve C).δ k σ
  change (nerve C).δ k.castSucc (σ.snocTerminal ht) = τ.snocTerminal ht
  refine ComposableArrows.ext_of_totalArrow (n := n + 1) fun i j hij ↦ ?_
  refine ((σ.snocTerminal ht).totalArrow_whiskerLeft _ i j hij).trans ?_
  change (σ.snocTerminal ht).totalArrow (k.castSucc.succAbove i) (k.castSucc.succAbove j) _ =
    (τ.snocTerminal ht).totalArrow i j hij
  cases j using Fin.lastCases with
  | cast j₀ =>
    cases i using Fin.lastCases with
    | last => exact absurd hij (not_le_of_gt (Fin.castSucc_lt_last j₀))
    | cast i₀ =>
      have hij₀ : i₀ ≤ j₀ := Fin.castSucc_le_castSucc_iff.mp hij
      simp only [Fin.castSucc_succAbove_castSucc]
      rw [σ.totalArrow_snocTerminal_castSucc ht (k.succAbove i₀) (k.succAbove j₀)
        ((Fin.strictMono_succAbove k).monotone hij₀),
        τ.totalArrow_snocTerminal_castSucc ht i₀ j₀ hij₀]
      exact (σ.totalArrow_whiskerLeft
        (SimplexCategory.toCat.map (SimplexCategory.δ k)).toFunctor i₀ j₀ hij₀).symm
  | last =>
    have hkl : k.castSucc.succAbove (Fin.last (n + 1)) = Fin.last (n + 2) := by
      ext; simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_last]
      split_ifs with h
      · exact absurd h (Nat.not_lt_of_ge (Nat.le_of_lt_succ k.isLt))
      · rfl
    have hobj : (σ.snocTerminal ht).obj (k.castSucc.succAbove i) = (τ.snocTerminal ht).obj i := by
      cases i using Fin.lastCases with
      | last => rw [hkl, σ.snocTerminal_obj_last, τ.snocTerminal_obj_last]
      | cast _ =>
        rw [Fin.castSucc_succAbove_castSucc, σ.snocTerminal_obj_castSucc,
          τ.snocTerminal_obj_castSucc]; rfl
    have hr : (σ.snocTerminal ht).obj (k.castSucc.succAbove (Fin.last (n + 1))) = t := by
      rw [hkl, σ.snocTerminal_obj_last]
    refine (ComposableArrows.totalArrow_def _ _ _ _).trans
      (Eq.trans ?_ (τ.totalArrow_snocTerminal_last ht i).symm)
    refine Quiver.Total.ext hobj hr ((conj_eqToHom_iff_heq _ _ hobj hr).mp ?_)
    rw [← cancel_mono (eqToHom hr)]; exact ht.hom_ext _ _

end CategoryTheory.nerve

namespace TauCeti

section ChainHomotopy

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Preadditive A]

/-- Summand inclusion of `σ.snocTerminal ht` transported along `(σ.snocTerminal ht).obj 0 = σ.obj 0`
so that its domain is `M.obj (σ.obj 0)`. -/
private def ιSnocTerminal (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) {t : C}
    (ht : IsTerminal t) : M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X (n + 1) :=
  eqToHom (congrArg M.obj (σ.snocTerminal_obj_zero ht).symm) ≫
    ιCategoryChainComplex M (σ.snocTerminal ht)

private lemma ιSnocTerminal_mk₀ (M : C ⥤ A) (X : C) {t : C} (ht : IsTerminal t) :
    ιSnocTerminal M (ComposableArrows.mk₀ X) ht = ιCategoryChainComplex₁ M (ht.from X) :=
  (congrArg (_ ≫ ·) (ιCategoryChainComplex_congr M (ComposableArrows.mk₀_snocTerminal X ht)
    (congrArg (fun τ ↦ τ.obj 0) (ComposableArrows.mk₀_snocTerminal X ht)))).trans
    ((eqToHom_trans_assoc _ _ _).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (id_comp _)))

private lemma ιSnocTerminal_d_succ (M : C ⥤ A) {m : ℕ} (σ : ComposableArrows C (m + 1))
    {t : C} (ht : IsTerminal t) :
    ιSnocTerminal M σ ht ≫ (categoryChainComplex M).d (m + 2) (m + 1) =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
          ιSnocTerminal M ((nerve C).δ 0 σ) ht +
        (∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) •
          ιSnocTerminal M ((nerve C).δ j.succ σ) ht) +
        (-1 : ℤ) ^ (m + 2) • ιCategoryChainComplex M σ := by
  have hmap : eqToHom (congrArg M.obj (σ.snocTerminal_obj_zero ht).symm) ≫
      M.map ((σ.snocTerminal ht).map (homOfLE (Fin.zero_le (Fin.succ 0)))) =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
        eqToHom (congrArg M.obj (σ.snocTerminal_obj_castSucc ht (Fin.succ 0)).symm) := by
    have htot := σ.totalArrow_snocTerminal_castSucc ht 0 (Fin.succ 0) (Fin.zero_le _)
    rw [ComposableArrows.totalArrow_def, ComposableArrows.totalArrow_def] at htot
    obtain ⟨h0, h1, hm⟩ := Quiver.Total.mk.inj htot
    have hc : (σ.snocTerminal ht).map (homOfLE (Fin.zero_le (Fin.succ 0))) =
        eqToHom h0 ≫ σ.map (homOfLE (Fin.zero_le (Fin.succ 0))) ≫ eqToHom h1.symm :=
      (conj_eqToHom_iff_heq _ _ h0 h1).mpr hm
    exact (congrArg (_ ≫ M.map ·) hc).trans ((congrArg (_ ≫ ·) ((M.map_comp _ _).trans
      (congrArg₂ (· ≫ ·) (eqToHom_map M h0)
        ((M.map_comp _ _).trans (congrArg (_ ≫ ·) (eqToHom_map M h1.symm)))))).trans
      ((eqToHom_trans_assoc _ _ _).trans
        ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (id_comp _))))
  have heq0 : (nerve C).δ 0 (σ.snocTerminal ht) = ((nerve C).δ 0 σ).snocTerminal ht :=
    (congrArg (fun k ↦ (nerve C).δ k (σ.snocTerminal ht))
      (Fin.castSucc_zero (n := m + 2)).symm).trans
      (nerve.δ_castSucc_snocTerminal (0 : Fin (m + 2)) σ ht)
  have h0_term : eqToHom (congrArg M.obj (σ.snocTerminal_obj_zero ht).symm) ≫
      M.map ((σ.snocTerminal ht).map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
        ιCategoryChainComplex M ((nerve C).δ 0 (σ.snocTerminal ht)) =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
        ιSnocTerminal M ((nerve C).δ 0 σ) ht :=
    (assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hmap).trans <| (assoc _ _ _).trans <|
      congrArg (M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫ ·) <|
        (congrArg (_ ≫ ·) (ιCategoryChainComplex_congr M heq0
          (congrArg (fun τ ↦ τ.obj 0) heq0))).trans (eqToHom_trans_assoc _ _ _)
  let L := Preadditive.leftComp ((categoryChainComplex M).X (m + 1))
    (eqToHom (congrArg M.obj (σ.snocTerminal_obj_zero ht).symm))
  have hsum : eqToHom (congrArg M.obj (σ.snocTerminal_obj_zero ht).symm) ≫
      (∑ k : Fin (m + 2), (-1 : ℤ) ^ (k.val + 1) •
        (ιCategoryChainComplex M ((nerve C).δ k.succ (σ.snocTerminal ht)) :
          M.obj ((σ.snocTerminal ht).obj 0) ⟶ (categoryChainComplex M).X (m + 1))) =
      (∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) •
        ιSnocTerminal M ((nerve C).δ j.succ σ) ht) +
      (-1 : ℤ) ^ (m + 2) • ιCategoryChainComplex M σ :=
    (map_sum L _ _).trans <| (Fin.sum_univ_castSucc _).trans <| congrArg₂ (· + ·)
      (Finset.sum_congr rfl fun j _ ↦ (L.map_zsmul _ _).trans <|
        congrArg ((-1 : ℤ) ^ (j.val + 1) • ·) (by
          have heqj : (nerve C).δ (j.castSucc : Fin (m + 2)).succ (σ.snocTerminal ht) =
              ((nerve C).δ j.succ σ).snocTerminal ht :=
            (congrArg (fun k ↦ (nerve C).δ k (σ.snocTerminal ht)) (Fin.succ_castSucc j)).trans
              (nerve.δ_castSucc_snocTerminal j.succ σ ht)
          exact (congrArg (_ ≫ ·) (ιCategoryChainComplex_congr M heqj
            (congrArg (fun τ ↦ τ.obj 0) heqj))).trans (eqToHom_trans_assoc _ _ _)))
      ((L.map_zsmul _ _).trans <| congrArg ((-1 : ℤ) ^ (m + 2) • ·) (by
        have heql : (nerve C).δ (Fin.last (m + 1)).succ (σ.snocTerminal ht) = σ :=
          (congrArg (fun k ↦ (nerve C).δ k (σ.snocTerminal ht)) (Fin.succ_last (m + 1))).trans
            (nerve.δ_last_snocTerminal σ ht)
        exact (congrArg (_ ≫ ·) (ιCategoryChainComplex_congr M heql
          (congrArg (fun τ ↦ τ.obj 0) heql))).trans ((eqToHom_trans_assoc _ _ _).trans
            ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (id_comp _)))))
  exact (assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (ιCategoryChainComplex_d M (σ.snocTerminal ht))).trans <|
      (Preadditive.comp_add _ _ _ _ _ _).trans
        ((congrArg₂ (· + ·) h0_term hsum).trans (add_assoc _ _ _).symm)

/-- Degree-`n` component of the contracting homotopy on `categoryChainComplex M` associated to a
terminal object `t` of `C`. -/
private def contractingHomotopyStep (M : C ⥤ A) {t : C} (ht : IsTerminal t) (n : ℕ) :
    (categoryChainComplex M).X n ⟶ (categoryChainComplex M).X (n + 1) :=
  descCategoryChainComplex M fun σ ↦ (-1 : ℤ) ^ (n + 1) • ιSnocTerminal M σ ht

private lemma ι_contractingHomotopyStep (M : C ⥤ A) {t : C} (ht : IsTerminal t) {n : ℕ}
    (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ ≫ contractingHomotopyStep M ht n =
      (-1 : ℤ) ^ (n + 1) • ιSnocTerminal M σ ht :=
  ιCategoryChainComplex_desc M _ σ

private lemma ι₀_contractingHomotopyStep (M : C ⥤ A) {t : C} (ht : IsTerminal t) (X : C) :
    ιCategoryChainComplex₀ M X ≫ contractingHomotopyStep M ht 0 =
      -ιCategoryChainComplex₁ M (ht.from X) := by
  refine (ι_contractingHomotopyStep M ht (ComposableArrows.mk₀ X)).trans ?_
  rw [pow_one, neg_one_zsmul, ιSnocTerminal_mk₀]; rfl

section WithZeroObject

variable [HasZeroObject A]

/-- Augmentation chain map `categoryChainComplex M ⟶ (ChainComplex.single₀ A).obj (M.obj t)`
evaluated at a terminal object `t` of `C`. -/
def toSingle₀OfIsTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    categoryChainComplex M ⟶ (ChainComplex.single₀ A).obj (M.obj t) :=
  HomologicalComplex.mkHomToSingle
    (descCategoryChainComplex₀ M (fun X ↦ M.map (ht.from X)))
    (fun i hi ↦ by
      obtain rfl : i = 1 := by simpa using hi.symm
      ext σ; obtain ⟨X, Y, f, rfl⟩ := ComposableArrows.mk₁_surjective σ
      rw [ιCategoryChainComplex₁_d_assoc, Preadditive.sub_comp, assoc,
        ιCategoryChainComplex₀_desc₀, ιCategoryChainComplex₀_desc₀, ← M.map_comp,
        ht.hom_ext (f ≫ ht.from Y) (ht.from X), sub_self, comp_zero])

@[simp]
lemma toSingle₀OfIsTerminal_f_zero (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    (toSingle₀OfIsTerminal M ht).f 0 =
      descCategoryChainComplex₀ M (fun X ↦ M.map (ht.from X)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (M.obj t)).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- Inclusion chain map `(ChainComplex.single₀ A).obj (M.obj X) ⟶ categoryChainComplex M` at an
object `X` of `C`. -/
def fromSingle₀CategoryChainComplex (M : C ⥤ A) (X : C) :
    (ChainComplex.single₀ A).obj (M.obj X) ⟶ categoryChainComplex M :=
  HomologicalComplex.mkHomFromSingle (ιCategoryChainComplex₀ M X) (fun _ hk ↦ by simp at hk)

@[simp]
lemma fromSingle₀CategoryChainComplex_f_zero (M : C ⥤ A) (X : C) :
    (fromSingle₀CategoryChainComplex M X).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (M.obj X)).hom ≫
        ιCategoryChainComplex₀ M X :=
  HomologicalComplex.mkHomFromSingle_f _ _

@[reassoc (attr := simp)]
lemma fromSingle₀_comp_toSingle₀_of_isTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    fromSingle₀CategoryChainComplex M t ≫ toSingle₀OfIsTerminal M ht = 𝟙 _ := by
  ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    fromSingle₀CategoryChainComplex_f_zero, toSingle₀OfIsTerminal_f_zero, assoc,
    ιCategoryChainComplex₀_desc₀_assoc, ht.hom_ext (ht.from t) (𝟙 t), M.map_id, id_comp,
    Iso.hom_inv_id]

/-- Contracting homotopy from `𝟙 (categoryChainComplex M)` to the projection through `M.obj t` in
degree `0` when `t` is terminal in `C`. -/
def categoryChainComplexContractingHomotopy (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    Homotopy (𝟙 (categoryChainComplex M))
      (toSingle₀OfIsTerminal M ht ≫ fromSingle₀CategoryChainComplex M t) where
  hom i j := if h : j = i + 1 then
      contractingHomotopyStep M ht i ≫ eqToHom (congrArg (categoryChainComplex M).X h.symm) else 0
  zero i j hij := dite_eq_right (by intro h; exact hij h.symm)
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq_zero _ 0 (by simp), prevD_eq _ (j' := 1) rfl, dite_eq_left rfl, eqToHom_refl,
        comp_id, zero_add, HomologicalComplex.comp_f, toSingle₀OfIsTerminal_f_zero,
        fromSingle₀CategoryChainComplex_f_zero, assoc, Iso.inv_hom_id_assoc]
      refine categoryChainComplex₀_hom_ext fun X ↦ ?_
      rw [HomologicalComplex.id_f, comp_id, Preadditive.comp_add,
        ιCategoryChainComplex₀_desc₀_assoc,
        (assoc (ιCategoryChainComplex₀ M X) (contractingHomotopyStep M ht 0) _).symm,
        ι₀_contractingHomotopyStep, Preadditive.neg_comp, ιCategoryChainComplex₁_d]
      abel
    | succ m =>
      have hzero :
          (toSingle₀OfIsTerminal M ht ≫ fromSingle₀CategoryChainComplex M t).f (m + 1) = 0 := by
        rw [HomologicalComplex.comp_f, (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) 0 (M.obj t) (m + 1) (Nat.succ_ne_zero m)).eq_of_tgt
          ((toSingle₀OfIsTerminal M ht).f (m + 1)) 0, zero_comp]
      rw [dNext_eq _ (rfl : (ComplexShape.down ℕ).Rel (m + 1) m),
        prevD_eq _ (rfl : (ComplexShape.down ℕ).Rel (m + 2) (m + 1)), dite_eq_left rfl,
        dite_eq_left rfl, eqToHom_refl, eqToHom_refl, comp_id, comp_id, hzero, add_zero]
      ext σ; rw [HomologicalComplex.id_f, comp_id, Preadditive.comp_add]
      let L₀ := Preadditive.leftComp ((categoryChainComplex M).X (m + 1))
        (M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))))
      let Rₘ := Preadditive.rightComp (M.obj (σ.obj 0)) (contractingHomotopyStep M ht m)
      let Rₘ₁ :=
        Preadditive.rightComp (M.obj (σ.obj 0)) ((categoryChainComplex M).d (m + 2) (m + 1))
      let Z : (M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X (m + 1)) →+
          (M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X (m + 1)) :=
        zsmulAddGroupHom ((-1 : ℤ) ^ (m + 1))
      have h1 : ιCategoryChainComplex M σ ≫
          (categoryChainComplex M).d (m + 1) m ≫ contractingHomotopyStep M ht m =
          (-1 : ℤ) ^ (m + 1) • ((M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
            ιSnocTerminal M ((nerve C).δ 0 σ) ht) + ∑ j : Fin (m + 1),
              (-1 : ℤ) ^ (j.val + 1) • ιSnocTerminal M ((nerve C).δ j.succ σ) ht) :=
        (ιCategoryChainComplex_d_assoc M σ _).trans <| (Preadditive.add_comp _ _ _ _ _ _).trans <|
          (congrArg₂ (· + ·)
            ((assoc _ _ _).trans <| (congrArg (_ ≫ ·)
              (ι_contractingHomotopyStep M ht ((nerve C).δ 0 σ))).trans (L₀.map_zsmul _ _))
            ((map_sum Rₘ _ _).trans <| (Finset.sum_congr rfl fun j _ ↦
              (Rₘ.map_zsmul _ _).trans <| (congrArg (_ • ·)
                (ι_contractingHomotopyStep M ht ((nerve C).δ j.succ σ))).trans <|
                (mul_zsmul _ _ _).symm.trans <| (congrArg (· • _) (mul_comm _ _)).trans
                  (mul_zsmul _ _ _)).trans (map_sum Z _ _).symm)).trans
            (zsmul_add _ _ ((-1 : ℤ) ^ (m + 1))).symm
      have h2 : ιCategoryChainComplex M σ ≫
          contractingHomotopyStep M ht (m + 1) ≫ (categoryChainComplex M).d (m + 2) (m + 1) =
          (-1 : ℤ) ^ (m + 2) • (((M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
              ιSnocTerminal M ((nerve C).δ 0 σ) ht) + ∑ j : Fin (m + 1),
                (-1 : ℤ) ^ (j.val + 1) • ιSnocTerminal M ((nerve C).δ j.succ σ) ht) +
              (-1 : ℤ) ^ (m + 2) • ιCategoryChainComplex M σ) :=
        (assoc _ _ _).symm.trans <| (congrArg (· ≫ _) (ι_contractingHomotopyStep M ht σ)).trans <|
          (Rₘ₁.map_zsmul _ _).trans
            (congrArg ((-1 : ℤ) ^ (m + 2) • ·) (ιSnocTerminal_d_succ M σ ht))
      have hcancel (a w : M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X (m + 1)) :
          (-1 : ℤ) ^ (m + 1) • a + (-1 : ℤ) ^ (m + 2) • (a + (-1 : ℤ) ^ (m + 2) • w) = w := by
        have hp1 : (-1 : ℤ) ^ (m + 2) = -((-1 : ℤ) ^ (m + 1)) := by rw [pow_succ, mul_neg_one]
        have hp2 : (-1 : ℤ) ^ (m + 2) * (-1 : ℤ) ^ (m + 2) = 1 := by
          rw [← mul_pow, show (-1 : ℤ) * (-1 : ℤ) = 1 from rfl, one_pow]
        rw [zsmul_add, ← mul_zsmul, hp2, one_zsmul, hp1, neg_zsmul]; abel
      exact ((congrArg₂ (· + ·) h1 h2).trans (hcancel _ _)).symm

/-- When `t` is terminal in `C`, `categoryChainComplex M` is chain homotopy equivalent to the
complex `(ChainComplex.single₀ A).obj (M.obj t)` concentrated in degree `0`. -/
def categoryChainComplexHomotopyEquivSingle₀OfIsTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    HomotopyEquiv (categoryChainComplex M) ((ChainComplex.single₀ A).obj (M.obj t)) where
  hom := toSingle₀OfIsTerminal M ht
  inv := fromSingle₀CategoryChainComplex M t
  homotopyHomInvId := (categoryChainComplexContractingHomotopy M ht).symm
  homotopyInvHomId := Homotopy.ofEq (fromSingle₀_comp_toSingle₀_of_isTerminal M ht)

@[simp]
lemma categoryChainComplexHomotopyEquivSingle₀OfIsTerminal_hom (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) : (categoryChainComplexHomotopyEquivSingle₀OfIsTerminal M ht).hom =
      toSingle₀OfIsTerminal M ht := (rfl)

@[simp]
lemma categoryChainComplexHomotopyEquivSingle₀OfIsTerminal_inv (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) : (categoryChainComplexHomotopyEquivSingle₀OfIsTerminal M ht).inv =
      fromSingle₀CategoryChainComplex M t := (rfl)

end WithZeroObject

end ChainHomotopy

section Homology

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Preadditive A] [CategoryWithHomology A]

/-- When `t` is terminal in `C`, `categoryHomology M 0` is canonically isomorphic to `M.obj t`. -/
def categoryHomology₀IsoOfIsTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    categoryHomology M 0 ≅ M.obj t :=
  (isColimitCategoryHomology₀Cocone M).coconePointUniqueUpToIso (colimitOfDiagramTerminal ht M)

@[reassoc (attr := simp)]
lemma ιCategoryHomology₀_isoOfIsTerminal_hom (M : C ⥤ A) {t : C} (ht : IsTerminal t) (X : C) :
    ιCategoryHomology₀ M X ≫ (categoryHomology₀IsoOfIsTerminal M ht).hom = M.map (ht.from X) :=
  (isColimitCategoryHomology₀Cocone M).comp_coconePointUniqueUpToIso_hom
    (colimitOfDiagramTerminal ht M) X

@[simp]
lemma categoryHomology₀IsoOfIsTerminal_inv (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
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

/-- Category homology `categoryHomology M n` vanishes for `n ≠ 0` when `t` is terminal in `C`. -/
lemma isZero_categoryHomology_of_isTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) {n : ℕ}
    (hn : n ≠ 0) : IsZero (categoryHomology M n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact isZero_categoryHomology_succ_of_isTerminal M ht m

/-- Canonical isomorphism `categoryHomology M 0 ≅ M.obj (⊤_ C)` when `C` has a terminal object. -/
def categoryHomology₀IsoTerminal (M : C ⥤ A) [HasTerminal C] :
    categoryHomology M 0 ≅ M.obj (⊤_ C) := categoryHomology₀IsoOfIsTerminal M terminalIsTerminal

@[reassoc (attr := simp)]
lemma ιCategoryHomology₀_isoTerminal_hom (M : C ⥤ A) [HasTerminal C] (X : C) :
    ιCategoryHomology₀ M X ≫ (categoryHomology₀IsoTerminal M).hom = M.map (terminal.from X) :=
  (ιCategoryHomology₀_isoOfIsTerminal_hom M terminalIsTerminal X).trans
    (congrArg M.map (terminal.hom_ext _ _))

@[simp]
lemma categoryHomology₀IsoTerminal_inv (M : C ⥤ A) [HasTerminal C] :
    (categoryHomology₀IsoTerminal M).inv = ιCategoryHomology₀ M (⊤_ C) :=
  categoryHomology₀IsoOfIsTerminal_inv M terminalIsTerminal

/-- Higher category homology `categoryHomology M (n + 1)` vanishes when `[HasTerminal C]`. -/
lemma isZero_categoryHomology_succ_of_hasTerminal (M : C ⥤ A) [HasTerminal C] (n : ℕ) :
    IsZero (categoryHomology M (n + 1)) :=
  isZero_categoryHomology_succ_of_isTerminal M terminalIsTerminal n

/-- Category homology `categoryHomology M n` vanishes for `n ≠ 0` when `[HasTerminal C]`. -/
lemma isZero_categoryHomology_of_hasTerminal (M : C ⥤ A) [HasTerminal C] {n : ℕ} (hn : n ≠ 0) :
    IsZero (categoryHomology M n) :=
  isZero_categoryHomology_of_isTerminal M terminalIsTerminal hn

end Homology

end TauCeti
