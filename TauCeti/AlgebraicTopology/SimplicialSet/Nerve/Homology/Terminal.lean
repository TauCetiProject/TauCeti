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

/-!
# Category homology of a category with a terminal object

When `C` has a terminal object `t`, `CategoryTheory.ComposableArrows.snocTerminal` (with
`CategoryTheory.nerve.δ_last_snocTerminal` and `CategoryTheory.nerve.δ_castSucc_snocTerminal`) is
an extra degeneracy on `nerve C` fixing vertex `0`, contracting `categoryChainComplex M` to
`(ChainComplex.single₀ A).obj (M.obj t)`:
* `TauCeti.categoryChainComplexToSingle₀OfIsTerminal`, `TauCeti.categoryChainComplexFromSingle₀`,
  and `TauCeti.categoryChainComplexContractingHomotopy` assemble into
  `TauCeti.categoryChainComplexHomotopyEquivSingle₀OfIsTerminal`;
* `TauCeti.categoryHomology₀IsoOfIsTerminal` gives `categoryHomology M 0 ≅ M.obj t`, and
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

namespace TauCeti

section ChainHomotopy

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Preadditive A]

/-- Summand inclusion of `σ.snocTerminal ht` transported to domain `M.obj (σ.obj 0)`. -/
private def ιSnocTerminal (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) {t : C}
    (ht : IsTerminal t) : M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X (n + 1) :=
  eqToHom (congrArg M.obj (σ.snocTerminal_obj_zero ht).symm) ≫
    ιCategoryChainComplex M (σ.snocTerminal ht)

private lemma eqToHom_ιCategoryChainComplex_snocTerminal (M : C ⥤ A) {n : ℕ}
    {σ : ComposableArrows C (n + 1)} {τ : ComposableArrows C n} {t : C} {ht : IsTerminal t}
    (h : σ = τ.snocTerminal ht) (h0 : σ.obj 0 = τ.obj 0) :
    eqToHom (congrArg M.obj h0.symm) ≫ ιCategoryChainComplex M σ = ιSnocTerminal M τ ht := by
  subst h; rfl

private lemma ιSnocTerminal_mk₀ (M : C ⥤ A) (X : C) {t : C} (ht : IsTerminal t) :
    ιSnocTerminal M (.mk₀ X) ht = ιCategoryChainComplex₁ M (ht.from X) :=
  eqToHom_ιCategoryChainComplex_eq M (ComposableArrows.mk₀_snocTerminal X ht)
    ((ComposableArrows.mk₀ X).snocTerminal_obj_zero ht)

private lemma snocTerminal_obj_succ_zero {m : ℕ} (σ : ComposableArrows C (m + 1)) {t : C}
    (ht : IsTerminal t) : (σ.snocTerminal ht).obj (Fin.succ 0) = σ.obj (Fin.succ 0) := by
  rw [← Fin.castSucc_zero, Fin.succ_castSucc, σ.snocTerminal_obj_castSucc]

omit [HasCoproducts.{max u v} A] [Preadditive A] in
private lemma eqToHom_snocTerminal_map_zero_one (M : C ⥤ A) {m : ℕ}
    (σ : ComposableArrows C (m + 1)) {t : C} (ht : IsTerminal t) :
    eqToHom (congrArg M.obj (σ.snocTerminal_obj_zero ht).symm) ≫
        M.map ((σ.snocTerminal ht).map (homOfLE (Fin.zero_le (Fin.succ 0)))) =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
        eqToHom (congrArg M.obj (snocTerminal_obj_succ_zero σ ht).symm) := by
  have htot := σ.totalArrow_snocTerminal_castSucc ht 0 (Fin.succ 0) (Fin.zero_le _)
  rw [ComposableArrows.totalArrow_def, ComposableArrows.totalArrow_def] at htot
  obtain ⟨h0, h1, hm⟩ := Quiver.Total.mk.inj htot
  dsimp only [← Fin.succ_castSucc, Fin.castSucc_zero] at h0 h1 hm
  rw [(conj_eqToHom_iff_heq _ _ h0 h1).mpr hm, M.map_comp, M.map_comp, eqToHom_map,
    eqToHom_map, eqToHom_trans_assoc, eqToHom_refl, id_comp]

/-- Differential of `σ.snocTerminal ht` on an `(m + 1)`-simplex `σ`, split into face `0`,
intermediate faces `1, …, m + 1`, and the final `(m + 2)`-nd face recovering `σ`. -/
private lemma ιSnocTerminal_d_succ (M : C ⥤ A) {m : ℕ} (σ : ComposableArrows C (m + 1))
    {t : C} (ht : IsTerminal t) :
    ιSnocTerminal M σ ht ≫ (categoryChainComplex M).d (m + 2) (m + 1) =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
          ιSnocTerminal M ((nerve C).δ 0 σ) ht +
        (∑ j : Fin (m + 1), (-1 : ℤ) ^ (j.val + 1) •
          ιSnocTerminal M ((nerve C).δ j.succ σ) ht) +
        (-1 : ℤ) ^ (m + 2) • ιCategoryChainComplex M σ := by
  have heq0 : (nerve C).δ 0 (σ.snocTerminal ht) = ((nerve C).δ 0 σ).snocTerminal ht := by
    rw [← Fin.castSucc_zero (n := m + 2), nerve.δ_castSucc_snocTerminal]
  have h0 : eqToHom (congrArg M.obj (σ.snocTerminal_obj_zero ht).symm) ≫
      M.map ((σ.snocTerminal ht).map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
        ιCategoryChainComplex M ((nerve C).δ 0 (σ.snocTerminal ht)) =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
        ιSnocTerminal M ((nerve C).δ 0 σ) ht :=
    (assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (eqToHom_snocTerminal_map_zero_one M σ ht)).trans <|
        (assoc _ _ _).trans <| congrArg (_ ≫ ·)
          (eqToHom_ιCategoryChainComplex_snocTerminal M heq0 (snocTerminal_obj_succ_zero σ ht))
  rw [ιSnocTerminal, assoc, ιCategoryChainComplex_d, Preadditive.comp_add, h0]
  refine (congrArg (_ + ·) ((Preadditive.comp_sum _ _ _).trans <|
    (Fin.sum_univ_castSucc _).trans <| congrArg₂ (· + ·)
      (Finset.sum_congr rfl fun j _ ↦ ?_) ?_)).trans (add_assoc _ _ _).symm
  · exact (Preadditive.comp_zsmul _ _ _).trans <| congrArg (_ • ·) <|
      eqToHom_ιCategoryChainComplex_snocTerminal M
        ((congrArg (fun k ↦ (nerve C).δ k (σ.snocTerminal ht)) (Fin.succ_castSucc j)).trans
          (nerve.δ_castSucc_snocTerminal j.succ σ ht))
        (σ.snocTerminal_obj_zero ht)
  · exact (Preadditive.comp_zsmul _ _ _).trans <| congrArg (_ • ·) <|
      eqToHom_ιCategoryChainComplex_eq M
        ((congrArg (fun k ↦ (nerve C).δ k (σ.snocTerminal ht)) (Fin.succ_last (m + 1))).trans
          (nerve.δ_last_snocTerminal σ ht))
        (σ.snocTerminal_obj_zero ht)

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
      -ιCategoryChainComplex₁ M (ht.from X) :=
  (ι_contractingHomotopyStep M ht (.mk₀ X)).trans <|
    (neg_one_zsmul _).trans (congrArg Neg.neg (ιSnocTerminal_mk₀ M X ht))

private lemma ιCategoryChainComplex_d_contractingHomotopyStep (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) {m : ℕ} (σ : ComposableArrows C (m + 1)) :
    ιCategoryChainComplex M σ ≫
        (categoryChainComplex M).d (m + 1) m ≫ contractingHomotopyStep M ht m =
      (-1 : ℤ) ^ (m + 1) • ((M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
        ιSnocTerminal M ((nerve C).δ 0 σ) ht) + ∑ j : Fin (m + 1),
          (-1 : ℤ) ^ (j.val + 1) • ιSnocTerminal M ((nerve C).δ j.succ σ) ht) := by
  have hcomm (j : Fin (m + 1)) (x : M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X (m + 1)) :
      (-1 : ℤ) ^ (j.val + 1) • ((-1 : ℤ) ^ (m + 1) • x) =
        (-1 : ℤ) ^ (m + 1) • ((-1 : ℤ) ^ (j.val + 1) • x) := by
    rw [← mul_zsmul, mul_comm, mul_zsmul]
  rw [ιCategoryChainComplex_d_assoc, Preadditive.add_comp, zsmul_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact (assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (ι_contractingHomotopyStep M ht ((nerve C).δ 0 σ))).trans
        (Preadditive.comp_zsmul _ _ _)
  · refine (Preadditive.sum_comp _ _ _).trans <| Eq.trans ?_ (Finset.smul_sum).symm
    exact Finset.sum_congr rfl fun j _ ↦
      (Preadditive.zsmul_comp _ _ _).trans <|
        (congrArg (_ • ·) (ι_contractingHomotopyStep M ht ((nerve C).δ j.succ σ))).trans
          (hcomm j _)

private lemma ιCategoryChainComplex_contractingHomotopyStep_d (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) {m : ℕ} (σ : ComposableArrows C (m + 1)) :
    ιCategoryChainComplex M σ ≫
        contractingHomotopyStep M ht (m + 1) ≫ (categoryChainComplex M).d (m + 2) (m + 1) =
      (-1 : ℤ) ^ (m + 2) • (((M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
          ιSnocTerminal M ((nerve C).δ 0 σ) ht) + ∑ j : Fin (m + 1),
            (-1 : ℤ) ^ (j.val + 1) • ιSnocTerminal M ((nerve C).δ j.succ σ) ht) +
          (-1 : ℤ) ^ (m + 2) • ιCategoryChainComplex M σ) := by
  rw [← assoc, ι_contractingHomotopyStep, Preadditive.zsmul_comp, ιSnocTerminal_d_succ]

/- In positive degrees `m + 1`, the signed extra degeneracy `s = contractingHomotopyStep M ht`
satisfies `d ≫ s + s ≫ d = 𝟙`: the faces `0, …, m + 1` of `s(σ) = (-1)^(m + 2) • σ.snocTerminal ht`
appear in `s ≫ d` with sign `(-1)^(m + 2)`, cancelling `d ≫ s` (which carries sign `(-1)^(m + 1)`),
while the final `(m + 2)`-nd face carries sign `(-1)^(m + 2) * (-1)^(m + 2) = 1` and recovers `σ`.
-/
private lemma contractingHomotopyStep_comm_succ (M : C ⥤ A) {t : C} (ht : IsTerminal t) (m : ℕ) :
    (categoryChainComplex M).d (m + 1) m ≫ contractingHomotopyStep M ht m +
        contractingHomotopyStep M ht (m + 1) ≫ (categoryChainComplex M).d (m + 2) (m + 1) =
      𝟙 ((categoryChainComplex M).X (m + 1)) := by
  ext σ
  have hcancel (a w : M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X (m + 1)) :
      (-1 : ℤ) ^ (m + 1) • a + (-1 : ℤ) ^ (m + 2) • (a + (-1 : ℤ) ^ (m + 2) • w) = w := by
    rw [zsmul_add, ← mul_zsmul, ← mul_pow, show (-1 : ℤ) * (-1 : ℤ) = 1 from rfl, one_pow,
      one_zsmul, pow_succ (-1 : ℤ) (m + 1), mul_neg_one, neg_zsmul]; abel
  rw [Preadditive.comp_add, comp_id, ιCategoryChainComplex_d_contractingHomotopyStep,
    ιCategoryChainComplex_contractingHomotopyStep_d]
  exact hcancel _ _

section WithZeroObject

variable [HasZeroObject A]

/-- Augmentation chain map `categoryChainComplex M ⟶ (ChainComplex.single₀ A).obj (M.obj t)`
evaluated at a terminal object `t` of `C`. -/
def categoryChainComplexToSingle₀OfIsTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
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
lemma categoryChainComplexToSingle₀OfIsTerminal_f_zero (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    (categoryChainComplexToSingle₀OfIsTerminal M ht).f 0 =
      descCategoryChainComplex₀ M (fun X ↦ M.map (ht.from X)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (M.obj t)).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- Inclusion chain map `(ChainComplex.single₀ A).obj (M.obj X) ⟶ categoryChainComplex M` at an
object `X` of `C`. -/
def categoryChainComplexFromSingle₀ (M : C ⥤ A) (X : C) :
    (ChainComplex.single₀ A).obj (M.obj X) ⟶ categoryChainComplex M :=
  HomologicalComplex.mkHomFromSingle (ιCategoryChainComplex₀ M X) (fun _ hk ↦ by simp at hk)

@[simp]
lemma categoryChainComplexFromSingle₀_f_zero (M : C ⥤ A) (X : C) :
    (categoryChainComplexFromSingle₀ M X).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (M.obj X)).hom ≫
        ιCategoryChainComplex₀ M X :=
  HomologicalComplex.mkHomFromSingle_f _ _

@[reassoc (attr := simp)]
lemma categoryChainComplexFromSingle₀_comp_categoryChainComplexToSingle₀OfIsTerminal (M : C ⥤ A)
    {t : C} (ht : IsTerminal t) :
    categoryChainComplexFromSingle₀ M t ≫ categoryChainComplexToSingle₀OfIsTerminal M ht = 𝟙 _ := by
  ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    categoryChainComplexFromSingle₀_f_zero, categoryChainComplexToSingle₀OfIsTerminal_f_zero, assoc,
    ιCategoryChainComplex₀_desc₀_assoc, ht.hom_ext (ht.from t) (𝟙 t), M.map_id, id_comp,
    Iso.hom_inv_id]

private lemma contractingHomotopyStep_comm_zero (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    contractingHomotopyStep M ht 0 ≫ (categoryChainComplex M).d 1 0 +
        (categoryChainComplexToSingle₀OfIsTerminal M ht ≫
          categoryChainComplexFromSingle₀ M t).f 0 =
      𝟙 ((categoryChainComplex M).X 0) := by
  rw [HomologicalComplex.comp_f, categoryChainComplexToSingle₀OfIsTerminal_f_zero,
    categoryChainComplexFromSingle₀_f_zero, assoc, Iso.inv_hom_id_assoc]
  refine categoryChainComplex₀_hom_ext fun X ↦ ?_
  rw [Preadditive.comp_add, comp_id, ιCategoryChainComplex₀_desc₀_assoc,
    ← assoc, ι₀_contractingHomotopyStep, Preadditive.neg_comp, ιCategoryChainComplex₁_d]
  abel

/-- Contracting homotopy from `𝟙 (categoryChainComplex M)` to the projection through `M.obj t` in
degree `0` when `t` is terminal in `C`. -/
def categoryChainComplexContractingHomotopy (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    Homotopy (𝟙 (categoryChainComplex M))
      (categoryChainComplexToSingle₀OfIsTerminal M ht ≫ categoryChainComplexFromSingle₀ M t) where
  hom i j := if h : j = i + 1 then
      contractingHomotopyStep M ht i ≫ eqToHom (congrArg (categoryChainComplex M).X h.symm) else 0
  zero i j hij := dite_eq_right (by intro h; exact hij h.symm)
  comm := fun
    | 0 => by
      rw [dNext_eq_zero _ 0 (by simp), prevD_eq _ (j' := 1) rfl, dite_eq_left rfl, eqToHom_refl,
        comp_id, zero_add, HomologicalComplex.id_f, contractingHomotopyStep_comm_zero]
    | m + 1 => by
      rw [dNext_eq _ (rfl : (ComplexShape.down ℕ).Rel (m + 1) m),
        prevD_eq _ (rfl : (ComplexShape.down ℕ).Rel (m + 2) (m + 1)), dite_eq_left rfl,
        dite_eq_left rfl, eqToHom_refl, eqToHom_refl, comp_id, comp_id, HomologicalComplex.comp_f,
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 (M.obj t) (m + 1)
          (Nat.succ_ne_zero m)).eq_of_src ((categoryChainComplexFromSingle₀ M t).f (m + 1)) 0,
        comp_zero, add_zero, HomologicalComplex.id_f]
      exact (contractingHomotopyStep_comm_succ M ht m).symm

/-- On the summand of an `n`-simplex `σ`, `categoryChainComplexContractingHomotopy M ht` sends `σ`
to `(-1)^(n + 1)` times `σ.snocTerminal ht`. -/
@[reassoc (attr := simp)]
lemma ιCategoryChainComplex_contractingHomotopy_hom (M : C ⥤ A) {t : C} (ht : IsTerminal t)
    (n : ℕ) (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplexContractingHomotopy M ht).hom n (n + 1) =
      (-1 : ℤ) ^ (n + 1) • (eqToHom (congrArg M.obj (σ.snocTerminal_obj_zero ht).symm) ≫
        ιCategoryChainComplex M (σ.snocTerminal ht)) := by
  dsimp only [categoryChainComplexContractingHomotopy]
  rw [dite_eq_left rfl, eqToHom_refl, comp_id, ι_contractingHomotopyStep, ιSnocTerminal]

/-- When `t` is terminal in `C`, `categoryChainComplex M` is chain homotopy equivalent to the
complex `(ChainComplex.single₀ A).obj (M.obj t)` concentrated in degree `0`. -/
def categoryChainComplexHomotopyEquivSingle₀OfIsTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    HomotopyEquiv (categoryChainComplex M) ((ChainComplex.single₀ A).obj (M.obj t)) where
  hom := categoryChainComplexToSingle₀OfIsTerminal M ht
  inv := categoryChainComplexFromSingle₀ M t
  homotopyHomInvId := (categoryChainComplexContractingHomotopy M ht).symm
  homotopyInvHomId := Homotopy.ofEq
    (categoryChainComplexFromSingle₀_comp_categoryChainComplexToSingle₀OfIsTerminal M ht)

@[simp]
lemma categoryChainComplexHomotopyEquivSingle₀OfIsTerminal_hom (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) : (categoryChainComplexHomotopyEquivSingle₀OfIsTerminal M ht).hom =
      categoryChainComplexToSingle₀OfIsTerminal M ht := (rfl)

@[simp]
lemma categoryChainComplexHomotopyEquivSingle₀OfIsTerminal_inv (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) : (categoryChainComplexHomotopyEquivSingle₀OfIsTerminal M ht).inv =
      categoryChainComplexFromSingle₀ M t := (rfl)

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
