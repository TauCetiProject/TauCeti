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

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 91.
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
  · rw [HomologicalComplex.shape _ _ _ (by simp only [ComplexShape.down_Rel]; omega), zero_comp]

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
      rw [← categoryChainComplexCoeffMap_def, ιCategoryHomology₀_categoryHomologyCoeffMap_assoc,
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
  have hpost : σ.postcomp (ht.from σ.right) = ComposableArrows.mk₁ (ht.from (σ.obj 0)) :=
    ComposableArrows.ext₁ (σ.postcomp_obj_zero _) (σ.postcomp_obj_last _) <| by
      rw [← cancel_mono (eqToHom (σ.postcomp_obj_last _))]
      exact ht.hom_ext _ _
  have hι : ιPostcomp M σ (ht.from σ.right) = ιCategoryChainComplex₁ M (ht.from (σ.obj 0)) :=
    (eqToHom_ιCategoryChainComplex M hpost.symm _).trans (ιCategoryChainComplex_mk₁ M _)
  have hσ : ιCategoryChainComplex₀ M (σ.obj 0) = ιCategoryChainComplex M σ :=
    (ιCategoryChainComplex_mk₀ M (σ.obj 0)).symm.trans
      ((Category.id_comp _).symm.trans (eqToHom_ιCategoryChainComplex M
        (ComposableArrows.ext₀ rfl : σ = ComposableArrows.mk₀ (σ.obj 0)) rfl))
  rw [hι, ιCategoryChainComplex₁_d_one_zero, hσ]

private lemma ιPostcomp_d_succ (M : C ⥤ A) {t : C} (ht : IsTerminal t) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) :
    ιPostcomp M σ (ht.from σ.right) ≫ (categoryChainComplex C M).d (n + 2) (n + 1) =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
          ιPostcomp M ((nerve C).δ 0 σ) (ht.from _) +
        (∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
          ιPostcomp M ((nerve C).δ j.succ σ) (ht.from _)) +
        (-1 : ℤ) ^ (n + 2) • ιCategoryChainComplex M σ := by
  let g := ht.from σ.right; let τ := σ.postcomp g
  let h₀ : M.obj (σ.obj 0) = M.obj (τ.obj 0) := congrArg M.obj (σ.postcomp_obj_zero g).symm
  let δ₀σ : ComposableArrows C n := (nerve C).δ 0 σ
  let δ₀τ : ComposableArrows C (n + 1) := (nerve C).δ 0 τ
  have hexp : ιPostcomp M σ g ≫ (categoryChainComplex C M).d (n + 2) (n + 1) =
      (eqToHom h₀ ≫ (M.map (τ.map (homOfLE (Fin.zero_le (1 : Fin (n + 3))))) ≫
          ιCategoryChainComplex M δ₀τ) +
        ∑ j : Fin (n + 1), eqToHom h₀ ≫
          ((-1 : ℤ) ^ (j.castSucc.val + 1) •
            ιCategoryChainComplex M ((nerve C).δ j.castSucc.succ τ))) +
      eqToHom h₀ ≫ ((-1 : ℤ) ^ ((Fin.last (n + 1)).val + 1) •
        ιCategoryChainComplex M ((nerve C).δ (Fin.last (n + 1)).succ τ)) :=
    (Category.assoc _ _ _).trans (((congrArg (eqToHom h₀ ≫ ·) (ιCategoryChainComplex_d M τ)).trans
      ((Preadditive.comp_add _ _ _ _ _ _).trans (congrArg (_ + ·)
        ((Preadditive.comp_sum _ _ _).trans (Fin.sum_univ_castSucc _))))).trans
      (add_assoc _ _ _).symm)
  have hterm₀ : eqToHom h₀ ≫ (M.map (τ.map (homOfLE (Fin.zero_le (1 : Fin (n + 3))))) ≫
      ιCategoryChainComplex M δ₀τ) =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫ ιPostcomp M δ₀σ (ht.from _) := by
    have hta : τ.totalArrow 0 1 (Fin.zero_le _) = σ.totalArrow 0 1 (Fin.zero_le _) :=
      (τ.totalArrow_congr Fin.castSucc_zero.symm Fin.castSucc_one.symm (Fin.zero_le _)).trans
        (σ.totalArrow_postcomp_castSucc_castSucc g 0 1 (Fin.zero_le _))
    rw [ComposableArrows.totalArrow_def, ComposableArrows.totalArrow_def] at hta
    obtain ⟨_, h₁, hm⟩ := Quiver.Total.mk.inj hta
    have hmap : eqToHom (σ.postcomp_obj_zero g).symm ≫
        τ.map (homOfLE (Fin.zero_le (1 : Fin (n + 3)))) =
        σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2)))) ≫ eqToHom h₁.symm := by
      rw [← cancel_mono (eqToHom h₁), Category.assoc, Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.comp_id]
      exact ((conj_eqToHom_iff_heq' _ _ (σ.postcomp_obj_zero g).symm h₁).mpr hm.symm).symm
    have hδ₀ : δ₀τ = δ₀σ.postcomp (ht.from _) :=
      CategoryTheory.nerve.δ_castSucc_postcomp_isTerminal σ ht 0
    have hMmap : eqToHom h₀ ≫ M.map (τ.map (homOfLE (Fin.zero_le (1 : Fin (n + 3))))) =
        M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
          eqToHom (congrArg M.obj h₁.symm) := by
      rw [← eqToHom_map M (σ.postcomp_obj_zero g).symm, ← M.map_comp, hmap, M.map_comp, eqToHom_map]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hMmap).trans
      ((Category.assoc _ _ _).trans (congrArg (M.map _ ≫ ·)
        (eqToHom_ι_eq_ιPostcomp M hδ₀ (congrArg M.obj h₁.symm)))))
  have hsum : (∑ j : Fin (n + 1), eqToHom h₀ ≫ ((-1 : ℤ) ^ (j.castSucc.val + 1) •
      ιCategoryChainComplex M ((nerve C).δ j.castSucc.succ τ))) =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
        ιPostcomp M ((nerve C).δ j.succ σ) (ht.from _) :=
    Finset.sum_congr rfl fun j _ ↦ by
      have hδj : ((nerve C).δ j.castSucc.succ τ : ComposableArrows C (n + 1)) =
          ComposableArrows.postcomp ((nerve C).δ j.succ σ) (ht.from _) :=
        (congrArg (fun i ↦ ((nerve C).δ i τ : ComposableArrows C (n + 1)))
          (Fin.succ_castSucc j).symm).trans
          (CategoryTheory.nerve.δ_castSucc_postcomp_isTerminal σ ht j.succ)
      exact (Preadditive.comp_zsmul _ _ _).trans (Fin.val_castSucc j ▸
        congrArg ((-1 : ℤ) ^ (j.val + 1) • ·) (eqToHom_ι_eq_ιPostcomp M hδj h₀))
  have hlast : eqToHom h₀ ≫ ((-1 : ℤ) ^ ((Fin.last (n + 1)).val + 1) •
      ιCategoryChainComplex M ((nerve C).δ (Fin.last (n + 1)).succ τ)) =
      (-1 : ℤ) ^ (n + 2) • ιCategoryChainComplex M σ := by
    have hδl : ((nerve C).δ (Fin.last (n + 1)).succ τ : ComposableArrows C (n + 1)) = σ :=
      (congrArg (fun i ↦ ((nerve C).δ i τ : ComposableArrows C (n + 1)))
        (Fin.succ_last (n + 1))).trans (CategoryTheory.nerve.δ_last_postcomp σ g)
    have hval : (Fin.last (n + 1)).val + 1 = n + 2 := congrArg (· + 1) (Fin.val_last (n + 1))
    exact (Preadditive.comp_zsmul _ _ _).trans ((congrArg (fun k ↦ (-1 : ℤ) ^ k • _) hval).trans
      (congrArg ((-1 : ℤ) ^ (n + 2) • ·) (eqToHom_ιCategoryChainComplex M hδl.symm h₀)))
  exact hexp.trans (congrArg₂ (· + ·) (congrArg₂ (· + ·) hterm₀ hsum) hlast)

private lemma ι_terminalHomotopy_succ (M : C ⥤ A) {t : C} (ht : IsTerminal t) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) :
    ιCategoryChainComplex M σ ≫
      ((categoryChainComplex C M).d (n + 1) n ≫ terminalHomotopyStep M ht n +
        terminalHomotopyStep M ht (n + 1) ≫ (categoryChainComplex C M).d (n + 2) (n + 1)) =
      ιCategoryChainComplex M σ := by
  let T := M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X (n + 1)
  let a₀ : T := M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
    ιPostcomp M ((nerve C).δ 0 σ) (ht.from _)
  let aj (j : Fin (n + 1)) : T := ιPostcomp M ((nerve C).δ j.succ σ) (ht.from _)
  have h₁ : ιCategoryChainComplex M σ ≫ ((categoryChainComplex C M).d (n + 1) n ≫
      terminalHomotopyStep M ht n) = (-1 : ℤ) ^ (n + 1) • a₀ +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • ((-1 : ℤ) ^ (n + 1) • aj j) :=
    (Category.assoc _ _ _).symm.trans (((congrArg (· ≫ _) (ιCategoryChainComplex_d M σ)).trans
      (Preadditive.add_comp _ _ _ _ _ _)).trans (congrArg₂ (· + ·)
        ((Category.assoc _ _ _).trans ((congrArg (M.map _ ≫ ·)
          (ι_terminalHomotopyStep M ht ((nerve C).δ 0 σ))).trans (Preadditive.comp_zsmul _ _ _)))
        ((Preadditive.sum_comp _ _ _).trans (Finset.sum_congr rfl fun j _ ↦
          (Preadditive.zsmul_comp _ _ _).trans (congrArg ((-1 : ℤ) ^ (j.val + 1) • ·)
            (ι_terminalHomotopyStep M ht ((nerve C).δ j.succ σ)))))))
  have hsmul (x₀ : T) (xj : Fin (n + 1) → T) :
      (-1 : ℤ) ^ (n + 2) • (x₀ + (∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • xj j) +
          (-1 : ℤ) ^ (n + 2) • ιCategoryChainComplex M σ) =
        (-1 : ℤ) ^ (n + 2) • x₀ +
          (∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • ((-1 : ℤ) ^ (n + 2) • xj j)) +
          ιCategoryChainComplex M σ := by
    rw [smul_add, smul_add, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_zsmul,
      Finset.smul_sum]
    exact congrArg₂ (· + ·) (congrArg (_ + ·) (Finset.sum_congr rfl fun j _ ↦
      smul_comm ((-1 : ℤ) ^ (n + 2)) ((-1 : ℤ) ^ (j.val + 1)) _)) rfl
  have h₂ : ιCategoryChainComplex M σ ≫ (terminalHomotopyStep M ht (n + 1) ≫
      (categoryChainComplex C M).d (n + 2) (n + 1)) = (-1 : ℤ) ^ (n + 2) • a₀ +
        (∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • ((-1 : ℤ) ^ (n + 2) • aj j)) +
          ιCategoryChainComplex M σ :=
    (Category.assoc _ _ _).symm.trans (((congrArg (· ≫ _) (ι_terminalHomotopyStep M ht σ)).trans
      ((Preadditive.zsmul_comp _ _ _).trans
        (congrArg ((-1 : ℤ) ^ (n + 2) • ·) (ιPostcomp_d_succ M ht σ)))).trans (hsmul a₀ aj))
  have halg (x₀ : T) (xj : Fin (n + 1) → T) :
      ((-1 : ℤ) ^ (n + 1) • x₀ +
          ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • ((-1 : ℤ) ^ (n + 1) • xj j)) +
        ((-1 : ℤ) ^ (n + 2) • x₀ +
          (∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • ((-1 : ℤ) ^ (n + 2) • xj j)) +
          ιCategoryChainComplex M σ) = ιCategoryChainComplex M σ := by
    have hc (x : T) : (-1 : ℤ) ^ (n + 1) • x + (-1 : ℤ) ^ (n + 2) • x = 0 := by
      rw [pow_succ (-1 : ℤ) (n + 1), mul_neg_one, neg_zsmul, add_neg_cancel]
    rw [← add_assoc, add_add_add_comm, hc, zero_add, ← Finset.sum_add_distrib,
      Finset.sum_eq_zero fun j _ ↦ by rw [← smul_add, hc, smul_zero], zero_add]
  exact (Preadditive.comp_add _ _ _ _ _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans (halg a₀ aj))

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
