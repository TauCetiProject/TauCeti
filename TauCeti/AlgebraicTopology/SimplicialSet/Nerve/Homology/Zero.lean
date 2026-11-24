/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Connected
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Homology.Basic

/-!
# Zeroth homology of a category and colimits

For `M : C ⥤ A` in preadditive `A` with homology and coproducts of size `max u v`,
`(categoryChainComplex M).d 1 0` sends `(f : X ⟶ Y, m)` to `M(f)(m) - m`, presenting
`categoryHomology M 0` as a colimit of `M` (`TauCeti.ιCategoryHomology₀`,
`TauCeti.isColimitCategoryHomology₀Cocone`, `TauCeti.categoryHomology₀IsoOfIsColimit`,
`TauCeti.categoryHomology₀IsoColimit`, `TauCeti.categoryHomology₀NatIsoColim`, and
`TauCeti.categoryHomology₀ConstIsoOfIsConnected`).

## References

* P. Gabriel and M. Zisman, *Calculus of Fractions and Homotopy Theory* (1967), Appendix II, §3.
* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 91.
* C. A. Weibel, *The K-book*, Grad. Stud. Math. 145 (2013), Chapter IV, §3.5.
-/

public section

noncomputable section

open CategoryTheory Category Limits

universe u v u₂ v₂ u' v'

namespace TauCeti

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D] {A : Type u'}
  [Category.{v'} A] [HasCoproducts.{max u v} A] [Preadditive A] [CategoryWithHomology A]

/-- Quotient projection `(categoryChainComplex M).X 0 ⟶ categoryHomology M 0` from `0`-chains. -/
def πCategoryHomology₀ (M : C ⥤ A) : (categoryChainComplex M).X 0 ⟶ categoryHomology M 0 :=
  (categoryChainComplex M).pOpcycles 0 ≫ (categoryChainComplex M).isoHomologyι₀.inv

lemma πCategoryHomology₀_def (M : C ⥤ A) : πCategoryHomology₀ M =
    (categoryChainComplex M).pOpcycles 0 ≫ (categoryChainComplex M).isoHomologyι₀.inv := (rfl)

instance (M : C ⥤ A) : Epi (πCategoryHomology₀ M) := epi_comp _ _

@[reassoc (attr := simp)] lemma d_πCategoryHomology₀ (M : C ⥤ A) (n : ℕ) :
    (categoryChainComplex M).d n 0 ≫ πCategoryHomology₀ M = 0 := by dsimp [πCategoryHomology₀]; simp

@[reassoc (attr := simp)] lemma πCategoryHomology₀_map {M N : C ⥤ A} (α : M ⟶ N) :
    πCategoryHomology₀ M ≫ categoryHomologyMap α 0 =
      (categoryChainComplexMap α).f 0 ≫ πCategoryHomology₀ N := by
  dsimp [πCategoryHomology₀]
  rw [assoc, ChainComplex.isoHomologyι₀_inv_naturality, HomologicalComplex.p_opcyclesMap_assoc]

@[reassoc (attr := simp)] lemma πCategoryHomology₀_pushforward [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) : πCategoryHomology₀ (F ⋙ M) ≫ categoryHomologyPushforward F M 0 =
      (categoryChainComplexPushforward F M).f 0 ≫ πCategoryHomology₀ M := by
  dsimp [πCategoryHomology₀]
  rw [assoc, ChainComplex.isoHomologyι₀_inv_naturality, HomologicalComplex.p_opcyclesMap_assoc]

/-- Canonical map `M.obj X ⟶ categoryHomology M 0` sending `M(X)` to its class in `H₀(C, M)`. -/
def ιCategoryHomology₀ (M : C ⥤ A) (X : C) : M.obj X ⟶ categoryHomology M 0 :=
  ιCategoryChainComplex₀ M X ≫ πCategoryHomology₀ M

@[reassoc (attr := simp)] lemma ιCategoryChainComplex₀_πCategoryHomology₀ (M : C ⥤ A) (X : C) :
    ιCategoryChainComplex₀ M X ≫ πCategoryHomology₀ M = ιCategoryHomology₀ M X := (rfl)

/-- Every `f : X ⟶ Y` identifies `M.map f ≫ ιCategoryHomology₀ M Y = ιCategoryHomology₀ M X`. -/
@[reassoc (attr := simp)] lemma map_ιCategoryHomology₀ (M : C ⥤ A) {X Y : C} (f : X ⟶ Y) :
    M.map f ≫ ιCategoryHomology₀ M Y = ιCategoryHomology₀ M X := by
  have h := congrArg (ιCategoryChainComplex₁ M f ≫ ·) (d_πCategoryHomology₀ M 1)
  rw [ιCategoryChainComplex₁_d_assoc, Preadditive.sub_comp, assoc, comp_zero,
    ιCategoryChainComplex₀_πCategoryHomology₀, ιCategoryChainComplex₀_πCategoryHomology₀] at h
  exact sub_eq_zero.mp h

@[ext] lemma categoryHomology₀_hom_ext {M : C ⥤ A} {T : A} {f g : categoryHomology M 0 ⟶ T}
    (h : ∀ X : C, ιCategoryHomology₀ M X ≫ f = ιCategoryHomology₀ M X ≫ g) : f = g :=
  (cancel_epi (πCategoryHomology₀ M)).1 <| categoryChainComplex₀_hom_ext fun X ↦ by
    simpa only [assoc, ιCategoryChainComplex₀_πCategoryHomology₀_assoc] using h X

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_map {M N : C ⥤ A} (α : M ⟶ N) (X : C) :
    ιCategoryHomology₀ M X ≫ categoryHomologyMap α 0 = α.app X ≫ ιCategoryHomology₀ N X := by
  rw [← ιCategoryChainComplex₀_πCategoryHomology₀, assoc, πCategoryHomology₀_map,
    ιCategoryChainComplex₀_map_f_assoc, ιCategoryChainComplex₀_πCategoryHomology₀]

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_pushforward [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) (X : C) : ιCategoryHomology₀ (F ⋙ M) X ≫
      categoryHomologyPushforward F M 0 = ιCategoryHomology₀ M (F.obj X) := by
  rw [← ιCategoryChainComplex₀_πCategoryHomology₀, assoc, πCategoryHomology₀_pushforward,
    ιCategoryChainComplex₀_pushforward_f_assoc, ιCategoryChainComplex₀_πCategoryHomology₀]

/-- The cocone on `M : C ⥤ A` with point `categoryHomology M 0` and legs `ιCategoryHomology₀ M`. -/
abbrev categoryHomology₀Cocone (M : C ⥤ A) : Cocone M :=
  Cocone.mk (categoryHomology M 0) { app := ιCategoryHomology₀ M, naturality _ _ _ := by simp }

omit [CategoryWithHomology A] in
@[reassoc (attr := simp)] lemma d_descCategoryChainComplex₀_cocone (M : C ⥤ A) (s : Cocone M) :
    (categoryChainComplex M).d 1 0 ≫ descCategoryChainComplex₀ M s.ι.app = 0 := by
  ext σ; obtain ⟨X, Y, f, rfl⟩ := ComposableArrows.mk₁_surjective σ
  rw [ιCategoryChainComplex₁_d_assoc, Preadditive.sub_comp, assoc,
    ιCategoryChainComplex₀_desc₀, ιCategoryChainComplex₀_desc₀, s.w, sub_self, comp_zero]

/-- Zeroth category homology `categoryHomology M 0` is a colimit of `M : C ⥤ A`. -/
def isColimitCategoryHomology₀Cocone (M : C ⥤ A) : IsColimit (categoryHomology₀Cocone M) where
  desc s := (categoryChainComplex M).isoHomologyι₀.hom ≫
    (categoryChainComplex M).descOpcycles' (descCategoryChainComplex₀ M s.ι.app) 1 (by simp)
      (d_descCategoryChainComplex₀_cocone M s)
  fac _ _ := by
    dsimp [ιCategoryHomology₀, πCategoryHomology₀, HomologicalComplex.descOpcycles']; simp
  uniq _ _ hm := categoryHomology₀_hom_ext fun X ↦ (hm X).trans <| by
    dsimp [ιCategoryHomology₀, πCategoryHomology₀, HomologicalComplex.descOpcycles']; simp

/-- Canonical isomorphism `categoryHomology M 0 ≅ s.pt` for any colimit cocone `s` on `M`. -/
def categoryHomology₀IsoOfIsColimit (M : C ⥤ A) {s : Cocone M} (hs : IsColimit s) :
    categoryHomology M 0 ≅ s.pt :=
  (isColimitCategoryHomology₀Cocone M).coconePointUniqueUpToIso hs

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_isoOfIsColimit_hom (M : C ⥤ A) {s : Cocone M}
    (hs : IsColimit s) (X : C) :
    ιCategoryHomology₀ M X ≫ (categoryHomology₀IsoOfIsColimit M hs).hom = s.ι.app X :=
  (isColimitCategoryHomology₀Cocone M).comp_coconePointUniqueUpToIso_hom hs X

@[reassoc (attr := simp)] lemma ι_categoryHomology₀IsoOfIsColimit_inv (M : C ⥤ A) {s : Cocone M}
    (hs : IsColimit s) (X : C) :
    s.ι.app X ≫ (categoryHomology₀IsoOfIsColimit M hs).inv = ιCategoryHomology₀ M X :=
  (isColimitCategoryHomology₀Cocone M).comp_coconePointUniqueUpToIso_inv hs X

/-- Canonical isomorphism `categoryHomology M 0 ≅ colimit M` when `M` has a chosen colimit. -/
def categoryHomology₀IsoColimit (M : C ⥤ A) [HasColimit M] : categoryHomology M 0 ≅ colimit M :=
  (isColimitCategoryHomology₀Cocone M).coconePointUniqueUpToIso (colimit.isColimit M)

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_isoColimit_hom (M : C ⥤ A) [HasColimit M]
    (X : C) : ιCategoryHomology₀ M X ≫ (categoryHomology₀IsoColimit M).hom = colimit.ι M X :=
  (isColimitCategoryHomology₀Cocone M).comp_coconePointUniqueUpToIso_hom (colimit.isColimit M) X

@[reassoc (attr := simp)] lemma ι_categoryHomology₀IsoColimit_inv (M : C ⥤ A) [HasColimit M]
    (X : C) : colimit.ι M X ≫ (categoryHomology₀IsoColimit M).inv = ιCategoryHomology₀ M X :=
  colimit.comp_coconePointUniqueUpToIso_inv (isColimitCategoryHomology₀Cocone M) X

variable (C A) in
/-- Natural isomorphism `categoryHomologyFunctor C A 0 ≅ colim` on `(C ⥤ A) ⥤ A`. -/
def categoryHomology₀NatIsoColim [HasColimitsOfShape C A] : categoryHomologyFunctor C A 0 ≅ colim :=
  NatIso.ofComponents (fun M ↦ categoryHomology₀IsoColimit M) fun {M N} α ↦
    categoryHomology₀_hom_ext (f := categoryHomologyMap α 0 ≫ (categoryHomology₀IsoColimit N).hom)
      (g := (categoryHomology₀IsoColimit M).hom ≫ colimMap α) fun _ ↦ by simp

@[simp] lemma categoryHomology₀NatIsoColim_hom_app [HasColimitsOfShape C A] (M : C ⥤ A) :
    (categoryHomology₀NatIsoColim C A).hom.app M = (categoryHomology₀IsoColimit M).hom := (rfl)

@[simp] lemma categoryHomology₀NatIsoColim_inv_app [HasColimitsOfShape C A] (M : C ⥤ A) :
    (categoryHomology₀NatIsoColim C A).inv.app M = (categoryHomology₀IsoColimit M).inv := (rfl)

variable (C) in
/-- For connected `C`, `categoryHomology ((Functor.const C).obj X) 0` is isomorphic to `X`. -/
def categoryHomology₀ConstIsoOfIsConnected [IsConnected C] (X : A) :
    categoryHomology ((Functor.const C).obj X) 0 ≅ X :=
  (isColimitCategoryHomology₀Cocone ((Functor.const C).obj X)).coconePointUniqueUpToIso
    (isColimitConstCocone C X)

@[reassoc (attr := simp)] lemma ιCategoryHomology₀_constIsoOfIsConnected_hom [IsConnected C]
    (X : A) (c : C) : ιCategoryHomology₀ ((Functor.const C).obj X) c ≫
      (categoryHomology₀ConstIsoOfIsConnected C X).hom = 𝟙 X :=
  (isColimitCategoryHomology₀Cocone _).comp_coconePointUniqueUpToIso_hom _ c

lemma categoryHomology₀ConstIsoOfIsConnected_inv [IsConnected C] (X : A) (c : C) :
    (categoryHomology₀ConstIsoOfIsConnected C X).inv =
      ιCategoryHomology₀ ((Functor.const C).obj X) c := by
  rw [← cancel_mono (categoryHomology₀ConstIsoOfIsConnected C X).hom, Iso.inv_hom_id,
    ιCategoryHomology₀_constIsoOfIsConnected_hom]

end TauCeti
