/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Limits.Connected
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.Basic

import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology
import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic

/-!
# Degree-zero homology of a category and contractibility for categories with a terminal object

For `C` and `M : C ⥤ A`, `TauCeti.ιCategoryHomology₀ M` forms a colimit cocone
`TauCeti.categoryHomology₀Cocone M` presenting `categoryHomology C M 0` as `colimit M`
(`TauCeti.categoryHomologyZeroIso`, `TauCeti.categoryHomologyFunctorZeroIso`). In particular,
`H₀(C, const X) ≅ X` when `[IsConnected C]` (`TauCeti.categoryHomologyZeroConstIsoOfIsConnected`).

When `C` has a terminal object `t`, appending the unique morphism to `t` yields a contracting
chain homotopy equivalence `TauCeti.categoryChainComplexTerminalHomotopyEquiv` between
`categoryChainComplex C M` and `(ChainComplex.single₀ A).obj (M.obj t)`, giving `H₀(C, M) ≅ M(t)`
and `Hₙ₊₁(C, M) = 0` (`TauCeti.isZero_categoryHomology_succ_of_isTerminal`).

## References

* [Daniel Quillen, *Higher algebraic K-theory: I*][quillen1973]
-/

public noncomputable section

universe v v' u u'

open CategoryTheory Limits Opposite HomologicalComplex
open scoped Simplicial

namespace TauCeti

section DegreeZero

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasCoproducts.{max u v} A]

/-- Canonical morphism `(categoryChainComplex C M).X 0 ⟶ s.pt` induced by a cocone `s` on `M`. -/
def fromCategoryChainComplexXZero (M : C ⥤ A) (s : Cocone M) :
    (categoryChainComplex C M).X 0 ⟶ s.pt :=
  Cofan.IsColimit.desc (isColimitCategoryChainComplexXCofan M 0) fun σ ↦ s.ι.app (σ.obj 0)

@[reassoc (attr := simp)] lemma ιCategoryChainComplex_fromCategoryChainComplexXZero (M : C ⥤ A)
    (s : Cocone M) (σ : ComposableArrows C 0) :
    ιCategoryChainComplex M σ ≫ fromCategoryChainComplexXZero M s = s.ι.app (σ.obj 0) :=
  Cofan.IsColimit.fac (isColimitCategoryChainComplexXCofan M 0) _ σ

@[reassoc (attr := simp)] lemma ιCategoryChainComplex₀_fromCategoryChainComplexXZero (M : C ⥤ A)
    (s : Cocone M) (c : C) :
    ιCategoryChainComplex₀ M c ≫ fromCategoryChainComplexXZero M s = s.ι.app c :=
  (congrArg (· ≫ fromCategoryChainComplexXZero M s) (ιCategoryChainComplex_mk₀ M c).symm).trans
    (ιCategoryChainComplex_fromCategoryChainComplexXZero M s (ComposableArrows.mk₀ c))

@[reassoc (attr := simp)] lemma d_fromCategoryChainComplexXZero (M : C ⥤ A) (s : Cocone M)
    (n : ℕ) : (categoryChainComplex C M).d n 0 ≫ fromCategoryChainComplexXZero M s = 0 := by
  by_cases hn : n = 1
  · subst hn; ext σ
    have hσ : ComposableArrows.mk₁ (σ.map' 0 1) = σ := ComposableArrows.ext₁ rfl rfl (by simp)
    rw [← hσ, ιCategoryChainComplex_mk₁, ιCategoryChainComplex₁_d_one_zero_assoc,
      Preadditive.sub_comp, Category.assoc, ιCategoryChainComplex₀_fromCategoryChainComplexXZero,
      ιCategoryChainComplex₀_fromCategoryChainComplexXZero, s.w (σ.map' 0 1), sub_self, comp_zero]
  · rw [HomologicalComplex.shape _ _ _ (by simp; omega), zero_comp]

section WithHomology

variable [CategoryWithHomology A]

/-- Canonical cocone leg `M.obj c ⟶ categoryHomology C M 0` at `c : C`. -/
def ιCategoryHomology₀ (M : C ⥤ A) (c : C) : M.obj c ⟶ categoryHomology C M 0 :=
  ιCategoryChainComplex₀ M c ≫ (categoryChainComplex C M).pOpcycles 0 ≫
    (ChainComplex.isoHomologyι₀ (categoryChainComplex C M)).inv

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_naturality (M : C ⥤ A) {c₀ c₁ : C}
    (f : c₀ ⟶ c₁) : M.map f ≫ ιCategoryHomology₀ M c₁ = ιCategoryHomology₀ M c₀ := by
  dsimp only [ιCategoryHomology₀]
  rw [← sub_eq_zero, ← Category.assoc (M.map f), ← Preadditive.sub_comp,
    ← ιCategoryChainComplex₁_d_one_zero, Category.assoc,
    ← Category.assoc ((categoryChainComplex C M).d 1 0), HomologicalComplex.d_pOpcycles,
    zero_comp, comp_zero]

/-- Cocone on `M : C ⥤ A` with vertex `categoryHomology C M 0` and legs `ιCategoryHomology₀ M`. -/
abbrev categoryHomology₀Cocone (M : C ⥤ A) : Cocone M :=
  ⟨categoryHomology C M 0, { app := ιCategoryHomology₀ M, naturality := fun _ _ _ ↦ by simp }⟩

@[ext] lemma categoryHomology₀_hom_ext {M : C ⥤ A} {T : A} {f g : categoryHomology C M 0 ⟶ T}
    (h : ∀ c : C, ιCategoryHomology₀ M c ≫ f = ιCategoryHomology₀ M c ≫ g) : f = g := by
  rw [← cancel_epi (ChainComplex.isoHomologyι₀ (categoryChainComplex C M)).inv,
    ← cancel_epi ((categoryChainComplex C M).pOpcycles 0)]
  exact categoryChainComplex_hom_ext₀ fun c ↦ by
    simpa only [ιCategoryHomology₀, Category.assoc] using h c

/-- `categoryHomology₀Cocone M` presents `categoryHomology C M 0` as a colimit of `M`. -/
def isColimitCategoryHomology₀Cocone (M : C ⥤ A) : IsColimit (categoryHomology₀Cocone M) := by
  let d (s : Cocone M) : categoryHomology C M 0 ⟶ s.pt :=
    (ChainComplex.isoHomologyι₀ (categoryChainComplex C M)).hom ≫
      (categoryChainComplex C M).descOpcycles (fromCategoryChainComplexXZero M s) 1
        (ChainComplex.prev ℕ 0) (d_fromCategoryChainComplexXZero M s 1)
  have hfac (s : Cocone M) (c : C) : ιCategoryHomology₀ M c ≫ d s = s.ι.app c := by
    dsimp only [ιCategoryHomology₀, d]
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
      HomologicalComplex.p_descOpcycles, ιCategoryChainComplex₀_fromCategoryChainComplexXZero]
  exact { desc := d, fac := hfac,
          uniq s m hm := categoryHomology₀_hom_ext fun c ↦ (hm c).trans (hfac s c).symm }

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_categoryHomologyCoeffMap {M N : C ⥤ A}
    (α : M ⟶ N) (c : C) :
    ιCategoryHomology₀ M c ≫ categoryHomologyCoeffMap α 0 = α.app c ≫ ιCategoryHomology₀ N c := by
  dsimp only [ιCategoryHomology₀, categoryHomologyCoeffMap, HomologicalComplex.homologyFunctor_map]
  rw [Category.assoc, Category.assoc, ChainComplex.isoHomologyι₀_inv_naturality,
    HomologicalComplex.p_opcyclesMap_assoc,
    ιCategoryChainComplex₀_categoryChainComplexCoeffMap_f_assoc]

/-- Canonical isomorphism `categoryHomology C M 0 ≅ s.pt` for any colimit cocone `s` on `M`. -/
def categoryHomologyZeroIsoOfIsColimit (M : C ⥤ A) (s : Cocone M) (hs : IsColimit s) :
    categoryHomology C M 0 ≅ s.pt :=
  (isColimitCategoryHomology₀Cocone M).coconePointUniqueUpToIso hs

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_categoryHomologyZeroIsoOfIsColimit_hom
    (M : C ⥤ A) (s : Cocone M) (hs : IsColimit s) (c : C) :
    ιCategoryHomology₀ M c ≫ (categoryHomologyZeroIsoOfIsColimit M s hs).hom = s.ι.app c :=
  (isColimitCategoryHomology₀Cocone M).comp_coconePointUniqueUpToIso_hom hs c

@[reassoc (attr := simp)] lemma ι_categoryHomologyZeroIsoOfIsColimit_inv (M : C ⥤ A)
    (s : Cocone M) (hs : IsColimit s) (c : C) :
    s.ι.app c ≫ (categoryHomologyZeroIsoOfIsColimit M s hs).inv = ιCategoryHomology₀ M c :=
  (isColimitCategoryHomology₀Cocone M).comp_coconePointUniqueUpToIso_inv hs c

/-- Canonical isomorphism `categoryHomology C M 0 ≅ colimit M` when `M` has a colimit. -/
def categoryHomologyZeroIso (M : C ⥤ A) [HasColimit M] : categoryHomology C M 0 ≅ colimit M :=
  categoryHomologyZeroIsoOfIsColimit M _ (colimit.isColimit M)

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_categoryHomologyZeroIso_hom (M : C ⥤ A)
    [HasColimit M] (c : C) :
    ιCategoryHomology₀ M c ≫ (categoryHomologyZeroIso M).hom = colimit.ι M c :=
  ιCategoryHomology₀_categoryHomologyZeroIsoOfIsColimit_hom M _ (colimit.isColimit M) c

@[reassoc (attr := simp)] lemma ι_categoryHomologyZeroIso_inv (M : C ⥤ A) [HasColimit M] (c : C) :
    colimit.ι M c ≫ (categoryHomologyZeroIso M).inv = ιCategoryHomology₀ M c :=
  ι_categoryHomologyZeroIsoOfIsColimit_inv M _ (colimit.isColimit M) c

variable (C A) [HasColimitsOfShape C A] in
/-- Natural isomorphism `categoryHomologyFunctor C A 0 ≅ colim`. -/
def categoryHomologyFunctorZeroIso : categoryHomologyFunctor C A 0 ≅ colim :=
  NatIso.ofComponents (fun M ↦ categoryHomologyZeroIso M) fun α ↦
    categoryHomology₀_hom_ext fun c ↦ by
      dsimp only [categoryHomologyFunctor, categoryChainComplexFunctor,
        categorySimplicialObjectFunctor, Functor.comp_map,
        HomologicalComplex.homologyFunctor, colim_map]
      rw [ιCategoryHomology₀_categoryHomologyCoeffMap_assoc,
        ιCategoryHomology₀_categoryHomologyZeroIso_hom,
        ιCategoryHomology₀_categoryHomologyZeroIso_hom_assoc, ι_colimMap]

/-- For connected `C`, `categoryHomology C ((Functor.const C).obj X) 0 ≅ X`. -/
def categoryHomologyZeroConstIsoOfIsConnected (C : Type u) [Category.{v} C] [IsConnected C]
    (X : A) : categoryHomology C ((Functor.const C).obj X) 0 ≅ X :=
  categoryHomologyZeroIsoOfIsColimit _ (constCocone C X) (isColimitConstCocone C X)

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_categoryHomologyZeroConstIsoOfIsConnected_hom
    [IsConnected C] (X : A) (c : C) : ιCategoryHomology₀ ((Functor.const C).obj X) c ≫
      (categoryHomologyZeroConstIsoOfIsConnected C X).hom = 𝟙 X :=
  ιCategoryHomology₀_categoryHomologyZeroIsoOfIsColimit_hom _ _ _ c

end WithHomology

end DegreeZero

section Terminal

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [Preadditive A] [HasCoproducts.{max u v} A]

private def nerveFace {n : ℕ} (i : Fin (n + 2)) (σ : ComposableArrows C (n + 1)) :
    ComposableArrows C n := (nerve C).δ i σ

private lemma nerveFace_zero_obj_zero {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    (nerveFace 0 σ).obj 0 = σ.obj 1 := rfl

private lemma nerveFace_succ_obj_zero {n : ℕ} (j : Fin (n + 1)) (σ : ComposableArrows C (n + 1)) :
    (nerveFace j.succ σ).obj 0 = σ.obj 0 := rfl

private lemma eqToHom_ι_of_eq (M : C ⥤ A) {m : ℕ} {τ σ : ComposableArrows C m}
    (h : τ = σ) (h₀ : M.obj (σ.obj 0) = M.obj (τ.obj 0)) :
    eqToHom h₀ ≫ ιCategoryChainComplex M τ = ιCategoryChainComplex M σ := by subst h; simp

private lemma ιCategoryChainComplex_d_nerveFace (M : C ⥤ A) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplex C M).d (n + 1) n =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
          eqToHom (congrArg M.obj (nerveFace_zero_obj_zero σ).symm) ≫
            ιCategoryChainComplex M (nerveFace 0 σ) +
        ∑ j : Fin (n + 1), (-1) ^ (j.val + 1) •
          (eqToHom (congrArg M.obj (nerveFace_succ_obj_zero j σ).symm) ≫
            ιCategoryChainComplex M (nerveFace j.succ σ)) :=
  (ιCategoryChainComplex_d M σ).trans (congrArg₂ (· + ·)
    (congrArg (_ ≫ ·) (eqToHom_ι_of_eq M rfl _).symm)
    (Finset.sum_congr rfl fun _ _ ↦ congrArg _ (eqToHom_ι_of_eq M rfl _).symm))

private def ιPostcomp (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) {Y : C} (g : σ.right ⟶ Y) :
    M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X (n + 1) :=
  eqToHom (congrArg M.obj (σ.postcomp_obj_zero g).symm) ≫ ιCategoryChainComplex M (σ.postcomp g)

private lemma eqToHom_ι_eq_ιPostcomp (M : C ⥤ A) {m : ℕ} {ρ : ComposableArrows C (m + 1)}
    {ν : ComposableArrows C m} {Y : C} {q : ν.right ⟶ Y}
    (h : ρ = ν.postcomp q) (h₀ : M.obj (ν.obj 0) = M.obj (ρ.obj 0)) :
    eqToHom h₀ ≫ ιCategoryChainComplex M ρ = ιPostcomp M ν q := by subst h; simp [ιPostcomp]

private def terminalHomotopyStep (M : C ⥤ A) {t : C} (ht : IsTerminal t) (n : ℕ) :
    (categoryChainComplex C M).X n ⟶ (categoryChainComplex C M).X (n + 1) :=
  (-1 : ℤ) ^ (n + 1) • Cofan.IsColimit.desc (isColimitCategoryChainComplexXCofan M n)
    fun σ ↦ ιPostcomp M σ (ht.from σ.right)

private lemma ι_terminalHomotopyStep (M : C ⥤ A) {t : C} (ht : IsTerminal t) {n : ℕ}
    (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ ≫ terminalHomotopyStep M ht n =
      (-1 : ℤ) ^ (n + 1) • ιPostcomp M σ (ht.from σ.right) :=
  (Preadditive.comp_zsmul _ _ _).trans (congrArg ((-1 : ℤ) ^ (n + 1) • ·)
    (Cofan.IsColimit.fac (isColimitCategoryChainComplexXCofan M n) _ σ))

private lemma ιPostcomp_d_one_zero (M : C ⥤ A) {t : C} (ht : IsTerminal t)
    (σ : ComposableArrows C 0) :
    ιPostcomp M σ (ht.from σ.right) ≫ (categoryChainComplex C M).d 1 0 =
      M.map (ht.from (σ.obj 0)) ≫ ιCategoryChainComplex₀ M t - ιCategoryChainComplex M σ := by
  let g := ht.from σ.right; let τ := σ.postcomp g
  dsimp only [ιPostcomp]
  rw [Category.assoc, ιCategoryChainComplex_d_nerveFace, Fin.sum_univ_one]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Preadditive.comp_add,
    Preadditive.comp_neg]
  have hδ₀ : nerveFace 0 τ = ComposableArrows.mk₀ t :=
    CategoryTheory.nerve.δ_zero_postcomp_zero σ g
  have hmk : t = (ComposableArrows.mk₀ t).obj 0 := rfl
  have hobj₀ : (nerveFace 0 τ).obj 0 = (ComposableArrows.mk₀ t).obj 0 :=
    congrArg (fun ρ : ComposableArrows C 0 ↦ ρ.obj 0) hδ₀
  have hmap : eqToHom (σ.postcomp_obj_zero g).symm ≫
      τ.map (homOfLE (Fin.zero_le (1 : Fin 2))) ≫ eqToHom (nerveFace_zero_obj_zero τ).symm =
      ht.from (σ.obj 0) ≫ eqToHom (hmk.trans hobj₀.symm) := by
    rw [← cancel_mono (eqToHom (hobj₀.trans hmk.symm))]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact ht.hom_ext _ _
  have h₁ : eqToHom (congrArg M.obj (σ.postcomp_obj_zero g).symm) ≫
      (M.map (τ.map (homOfLE (Fin.zero_le (1 : Fin 2)))) ≫
        eqToHom (congrArg M.obj (nerveFace_zero_obj_zero τ).symm) ≫
          ιCategoryChainComplex M (nerveFace 0 τ)) =
      M.map (ht.from (σ.obj 0)) ≫ ιCategoryChainComplex₀ M t := by
    rw [← Category.assoc, ← Category.assoc, ← eqToHom_map M (σ.postcomp_obj_zero g).symm,
      ← eqToHom_map M (nerveFace_zero_obj_zero τ).symm, ← M.map_comp, ← M.map_comp,
      Category.assoc, hmap, M.map_comp, eqToHom_map, Category.assoc]
    exact congrArg (M.map _ ≫ ·) ((eqToHom_ι_of_eq M hδ₀ _).trans (ιCategoryChainComplex_mk₀ M t))
  have h₂ : eqToHom (congrArg M.obj (σ.postcomp_obj_zero g).symm) ≫
      (eqToHom (congrArg M.obj (nerveFace_succ_obj_zero 0 τ).symm) ≫
        ιCategoryChainComplex M (nerveFace (Fin.succ 0) τ)) =
      ιCategoryChainComplex M σ := by
    rw [← Category.assoc, eqToHom_trans]
    exact eqToHom_ι_of_eq M (CategoryTheory.nerve.δ_last_postcomp σ g) _
  rw [h₁, h₂, ← sub_eq_add_neg]

private lemma ιPostcomp_d_succ (M : C ⥤ A) {t : C} (ht : IsTerminal t) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) :
    ιPostcomp M σ (ht.from σ.right) ≫ (categoryChainComplex C M).d (n + 2) (n + 1) =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
          eqToHom (congrArg M.obj (nerveFace_zero_obj_zero σ).symm) ≫
            ιPostcomp M (nerveFace 0 σ) (ht.from _) +
        (∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
          (eqToHom (congrArg M.obj (nerveFace_succ_obj_zero j σ).symm) ≫
            ιPostcomp M (nerveFace j.succ σ) (ht.from _))) +
        (-1 : ℤ) ^ (n + 2) • ιCategoryChainComplex M σ := by
  let g := ht.from σ.right; let τ := σ.postcomp g
  conv_lhs => dsimp only [ιPostcomp]
  rw [Category.assoc, ιCategoryChainComplex_d_nerveFace, Preadditive.comp_add,
    Preadditive.comp_sum, Fin.sum_univ_castSucc, ← add_assoc]
  congr 1
  · congr 1
    · have hta := σ.totalArrow_postcomp_castSucc_castSucc g 0 1 (Fin.zero_le _)
      rw [ComposableArrows.totalArrow_def, ComposableArrows.totalArrow_def] at hta
      obtain ⟨_, h₁, hm⟩ := Quiver.Total.mk.inj hta
      have h₁' : (nerveFace 0 σ).obj 0 = (nerveFace 0 τ).obj 0 :=
        (nerveFace_zero_obj_zero σ).trans (h₁.symm.trans (nerveFace_zero_obj_zero τ).symm)
      have hmap : eqToHom (σ.postcomp_obj_zero g).symm ≫
          τ.map (homOfLE (Fin.zero_le (1 : Fin (n + 3)))) ≫
            eqToHom (nerveFace_zero_obj_zero τ).symm =
          σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2)))) ≫
            eqToHom (nerveFace_zero_obj_zero σ).symm ≫ eqToHom h₁' := by
        rw [← cancel_mono (eqToHom h₁'.symm), ← cancel_mono (eqToHom (nerveFace_zero_obj_zero σ))]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
        exact ((conj_eqToHom_iff_heq' _ _ (σ.postcomp_obj_zero g).symm h₁).mpr hm.symm).symm
      rw [← Category.assoc, ← Category.assoc, ← eqToHom_map M (σ.postcomp_obj_zero g).symm,
        ← eqToHom_map M (nerveFace_zero_obj_zero τ).symm, ← M.map_comp, ← M.map_comp,
        Category.assoc, hmap, M.map_comp, M.map_comp, eqToHom_map, eqToHom_map, Category.assoc,
        Category.assoc]
      exact congrArg (M.map _ ≫ eqToHom _ ≫ ·)
        (eqToHom_ι_eq_ιPostcomp M (CategoryTheory.nerve.δ_castSucc_postcomp_isTerminal σ ht 0)
          (congrArg M.obj h₁'))
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Preadditive.comp_zsmul, Fin.val_castSucc]
      refine congrArg ((-1 : ℤ) ^ (j.val + 1) • ·) ?_
      have hδj : nerveFace j.castSucc.succ τ = (nerveFace j.succ σ).postcomp (ht.from _) :=
        (congrArg (fun i ↦ nerveFace i τ) (Fin.succ_castSucc j).symm).trans
          (CategoryTheory.nerve.δ_castSucc_postcomp_isTerminal σ ht j.succ)
      have hj₀ : M.obj ((nerveFace j.succ σ).obj 0) = M.obj ((nerveFace j.castSucc.succ τ).obj 0) :=
        congrArg M.obj ((nerveFace_succ_obj_zero j σ).trans
          ((σ.postcomp_obj_zero g).symm.trans (nerveFace_succ_obj_zero j.castSucc τ).symm))
      rw [← Category.assoc, eqToHom_trans, ← eqToHom_ι_eq_ιPostcomp M hδj hj₀,
        ← Category.assoc, eqToHom_trans]
  · rw [Preadditive.comp_zsmul, Fin.val_last, ← Category.assoc, eqToHom_trans]
    exact congrArg ((-1 : ℤ) ^ (n + 2) • ·) (eqToHom_ι_of_eq M
      ((congrArg (fun i ↦ nerveFace i τ) (Fin.succ_last (n + 1))).trans
        (CategoryTheory.nerve.δ_last_postcomp σ g)) _)

private lemma neg_one_pow_succ_add (m : ℕ) {G₀ : Type*} [AddCommGroup G₀] (x : G₀) :
    (-1 : ℤ) ^ (m + 1) • x + (-1 : ℤ) ^ (m + 2) • x = 0 := by
  rw [pow_succ (-1 : ℤ) (m + 1), mul_neg_one, neg_zsmul, add_neg_cancel]

private lemma ι_terminalHomotopy_succ (M : C ⥤ A) {t : C} (ht : IsTerminal t) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) :
    ιCategoryChainComplex M σ ≫
      ((categoryChainComplex C M).d (n + 1) n ≫ terminalHomotopyStep M ht n +
        terminalHomotopyStep M ht (n + 1) ≫ (categoryChainComplex C M).d (n + 2) (n + 1)) =
      ιCategoryChainComplex M σ := by
  let a₀ := M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
    eqToHom (congrArg M.obj (nerveFace_zero_obj_zero σ).symm) ≫
      ιPostcomp M (nerveFace 0 σ) (ht.from _)
  let aj (j : Fin (n + 1)) := eqToHom (congrArg M.obj (nerveFace_succ_obj_zero j σ).symm) ≫
    ιPostcomp M (nerveFace j.succ σ) (ht.from _)
  have h₁ : ιCategoryChainComplex M σ ≫ (categoryChainComplex C M).d (n + 1) n ≫
      terminalHomotopyStep M ht n = (-1 : ℤ) ^ (n + 1) • a₀ +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • ((-1 : ℤ) ^ (n + 1) • aj j) := by
    rw [← Category.assoc, ιCategoryChainComplex_d_nerveFace, Preadditive.add_comp,
      Category.assoc, Category.assoc, ι_terminalHomotopyStep, Preadditive.comp_zsmul,
      Preadditive.comp_zsmul, Preadditive.sum_comp]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [Preadditive.zsmul_comp, Category.assoc, ι_terminalHomotopyStep, Preadditive.comp_zsmul]
  have h₂ : ιCategoryChainComplex M σ ≫ terminalHomotopyStep M ht (n + 1) ≫
      (categoryChainComplex C M).d (n + 2) (n + 1) = (-1 : ℤ) ^ (n + 2) • a₀ +
        (∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • ((-1 : ℤ) ^ (n + 2) • aj j)) +
          ιCategoryChainComplex M σ := by
    rw [← Category.assoc, ι_terminalHomotopyStep, Preadditive.zsmul_comp, ιPostcomp_d_succ M ht σ,
      smul_add, smul_add, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_zsmul,
      Finset.smul_sum]
    exact congrArg₂ (· + ·) (congrArg (_ + ·) (Finset.sum_congr rfl fun j _ ↦
      smul_comm ((-1 : ℤ) ^ (n + 2)) ((-1 : ℤ) ^ (j.val + 1)) _)) rfl
  rw [Preadditive.comp_add, h₁, h₂, ← add_assoc, add_add_add_comm, neg_one_pow_succ_add, zero_add,
    ← Finset.sum_add_distrib, Finset.sum_eq_zero fun j _ ↦ by
      rw [← smul_add, neg_one_pow_succ_add, smul_zero], zero_add]

section Single₀

variable [HasZeroObject A]

/-- Chain map `categoryChainComplex C M ⟶ (ChainComplex.single₀ A).obj (M.obj t)` induced by a
terminal object `t`. -/
def categoryChainComplexToTerminalSingle₀ (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    categoryChainComplex C M ⟶ (ChainComplex.single₀ A).obj (M.obj t) :=
  HomologicalComplex.mkHomToSingle
    (fromCategoryChainComplexXZero M (coconeOfDiagramTerminal ht M))
    fun i _ ↦ d_fromCategoryChainComplexXZero M _ i

/-- Chain map `(ChainComplex.single₀ A).obj (M.obj t) ⟶ categoryChainComplex C M` at `t`. -/
def categoryChainComplexFromTerminalSingle₀ (M : C ⥤ A) (t : C) :
    (ChainComplex.single₀ A).obj (M.obj t) ⟶ categoryChainComplex C M :=
  HomologicalComplex.mkHomFromSingle (ιCategoryChainComplex₀ M t)
    fun _ hk ↦ absurd hk (Nat.succ_ne_zero _)

@[simp] lemma categoryChainComplexFromTerminalSingle₀_comp_toTerminalSingle₀ (M : C ⥤ A) {t : C}
    (ht : IsTerminal t) :
    categoryChainComplexFromTerminalSingle₀ M t ≫
      categoryChainComplexToTerminalSingle₀ M ht = 𝟙 _ := by
  refine HomologicalComplex.from_single_hom_ext ?_
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    categoryChainComplexFromTerminalSingle₀, categoryChainComplexToTerminalSingle₀,
    HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.mkHomToSingle_f, Category.assoc,
    ιCategoryChainComplex₀_fromCategoryChainComplexXZero_assoc, coconeOfDiagramTerminal_ι_app]
  rw [ht.hom_ext (ht.from t) (𝟙 t), M.map_id, Category.id_comp, Iso.hom_inv_id]

/-- Contracting chain homotopy on `categoryChainComplex C M` when `t` is terminal. -/
def categoryChainComplexTerminalHomotopy (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    Homotopy (𝟙 (categoryChainComplex C M))
      (categoryChainComplexToTerminalSingle₀ M ht ≫
        categoryChainComplexFromTerminalSingle₀ M t) where
  hom i j := if h : i + 1 = j then terminalHomotopyStep M ht i ≫ eqToHom (by rw [h]) else 0
  zero _ _ hij := dite_eq_right hij
  comm := fun
    | 0 => by
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add]
      dsimp only [HomologicalComplex.id_f, HomologicalComplex.comp_f]
      rw [dite_eq_left rfl, eqToHom_refl, Category.comp_id, categoryChainComplexToTerminalSingle₀,
        categoryChainComplexFromTerminalSingle₀, HomologicalComplex.mkHomToSingle_f,
        HomologicalComplex.mkHomFromSingle_f, Category.assoc, Iso.inv_hom_id_assoc]
      ext σ
      rw [Category.comp_id, Preadditive.comp_add, ← Category.assoc, ι_terminalHomotopyStep,
        Preadditive.zsmul_comp, ιPostcomp_d_one_zero M ht σ,
        ιCategoryChainComplex_fromCategoryChainComplexXZero_assoc]
      simp
    | n + 1 => by
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      dsimp only [HomologicalComplex.id_f, HomologicalComplex.comp_f]
      rw [dite_eq_left rfl, dite_eq_left rfl, eqToHom_refl, eqToHom_refl,
        Category.comp_id, Category.comp_id]
      have hzf : (categoryChainComplexFromTerminalSingle₀ M t).f (n + 1) = 0 :=
        (HomologicalComplex.isZero_single_obj_X _ 0 (M.obj t) (n + 1)
          (Nat.succ_ne_zero n)).eq_of_src _ _
      rw [hzf, comp_zero, add_zero]; ext σ
      exact (Category.comp_id _).trans (ι_terminalHomotopy_succ M ht σ).symm

/-- When `t` is terminal in `C`, `categoryChainComplex C M` is chain homotopy equivalent to
`M.obj t` concentrated in degree `0`. -/
def categoryChainComplexTerminalHomotopyEquiv (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    HomotopyEquiv (categoryChainComplex C M) ((ChainComplex.single₀ A).obj (M.obj t)) where
  hom := categoryChainComplexToTerminalSingle₀ M ht
  inv := categoryChainComplexFromTerminalSingle₀ M t
  homotopyHomInvId := (categoryChainComplexTerminalHomotopy M ht).symm
  homotopyInvHomId := Homotopy.ofEq (by simp)

end Single₀

section TerminalHomology

variable [CategoryWithHomology A]

/-- When `t` is terminal in `C`, `categoryHomology C M 0 ≅ M.obj t`. -/
def categoryHomologyZeroTerminalIso (M : C ⥤ A) {t : C} (ht : IsTerminal t) :
    categoryHomology C M 0 ≅ M.obj t :=
  categoryHomologyZeroIsoOfIsColimit M (coconeOfDiagramTerminal ht M)
    (colimitOfDiagramTerminal ht M)

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_categoryHomologyZeroTerminalIso_hom
    (M : C ⥤ A) {t : C} (ht : IsTerminal t) (c : C) :
    ιCategoryHomology₀ M c ≫ (categoryHomologyZeroTerminalIso M ht).hom = M.map (ht.from c) :=
  ιCategoryHomology₀_categoryHomologyZeroIsoOfIsColimit_hom M _ _ c

/-- When `C` has a terminal object `t`, `categoryHomology C M (n + 1)` vanishes. -/
lemma isZero_categoryHomology_succ_of_isTerminal (M : C ⥤ A) {t : C} (ht : IsTerminal t)
    (n : ℕ) : IsZero (categoryHomology C M (n + 1)) := by
  have := Preadditive.hasZeroObject_of_hasCoproduct.{max u v} A
  have : QuasiIso (categoryChainComplexToTerminalSingle₀ M ht) :=
    (categoryChainComplexTerminalHomotopyEquiv M ht).quasiIso_hom
  exact (HomologicalComplex.isZero_single_obj_homology
    (c := ComplexShape.down ℕ) (j := 0) (M.obj t) (n + 1) (Nat.succ_ne_zero n)).of_iso
    (asIso (HomologicalComplex.homologyMap (categoryChainComplexToTerminalSingle₀ M ht) (n + 1)))

end TerminalHomology

end Terminal

end TauCeti
