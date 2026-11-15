/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

import TauCeti.CategoryTheory.ComposableArrows.Basic

/-!
# Homology of a category with coefficients in a functor

Given a category `C` and a functor `M : C ⥤ A` into a category `A` with coproducts indexed by
`ComposableArrows C n`, this file constructs:
* `TauCeti.categorySimplicialObjectFunctor` / `TauCeti.categorySimplicialObject`: the simplicial
  object `⦋n⦌ ↦ ∐ (σ : ComposableArrows C n), M.obj (σ.obj 0)`, where `δ 0` applies `M.map` to the
  first arrow `σ.obj 0 ⟶ σ.obj 1` and higher faces and degeneracies act as the identity on
  `M.obj (σ.obj 0)`.
* `TauCeti.categoryChainComplexFunctor` / `TauCeti.categoryChainComplex` and
  `TauCeti.categoryHomologyFunctor` / `TauCeti.categoryHomology`: the alternating-face chain complex
  `C_*(C, M)` and degree-`n` homology `Hₙ(C, M)`, functorial in `M` and along functors `F : C ⥤ D`
  (`TauCeti.categoryChainComplexPrecomp`, `TauCeti.categoryHomologyPrecomp`).
* `TauCeti.categoryChainComplexXLinearEquivDirectSum`: direct-sum presentation for `ModuleCat R`.
* `TauCeti.categoryChainComplexConstIso`, `TauCeti.categoryHomologyConstIso`: comparison with
  `(nerve C).chainComplex X` and `(nerve C).homology X n` for constant coefficients.

## References

* [Daniel Quillen, *Higher algebraic K-theory: I*][quillen1973], §1.
* [Charles A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*][weibel2013], Ch. IV §3.5.
-/

public noncomputable section

open CategoryTheory Limits Opposite

open scoped Simplicial DirectSum

universe v₁ u₁ v₂ u₂ v₃ u₃ v u w

/-- Deleting the final vertex of a simplex of `nerve C` via `δ (Fin.last (n + 1))` agrees with
`ComposableArrows.δlast` (dual to `CategoryTheory.nerve.δ₀_eq`). -/
@[simp]
theorem CategoryTheory.nerve.δ_last_eq {C : Type u₁} [Category.{v₁} C] {n : ℕ}
    (σ : ComposableArrows C (n + 1)) :
    (nerve C).δ (Fin.last (n + 1)) σ = σ.δlast :=
  ComposableArrows.ext_of_totalArrow fun i j hij ↦
    (σ.totalArrow_whiskerLeft _ i j hij).trans <| by
      change σ.totalArrow ((Fin.last (n + 1)).succAbove i) ((Fin.last (n + 1)).succAbove j) _ = _
      simp only [Fin.succAbove_last]
      exact (σ.totalArrow_whiskerLeft (Fin.castSuccFunctor (n + 1)) i j hij).symm

namespace TauCeti

section SimplicialObject

variable (C : Type u₁) [Category.{v₁} C] (A : Type u) [Category.{v} A]
  [HasCoproducts.{max u₁ v₁} A]

/-- Functorial assignment `M ↦ categorySimplicialObject C M` from `C ⥤ A` to `SimplicialObject A`,
with degree `n` given by `∐ (σ : ComposableArrows C n), M.obj (σ.obj 0)`. -/
@[implicit_reducible]
def categorySimplicialObjectFunctor : (C ⥤ A) ⥤ SimplicialObject A where
  obj M :=
    { obj Δ := ∐ fun (σ : ComposableArrows C Δ.unop.len) ↦ M.obj (σ.obj 0)
      map {Δ Δ'} f := Sigma.desc fun (σ : ComposableArrows C Δ.unop.len) ↦
        M.map (σ.map (homOfLE (Fin.zero_le (f.unop.toOrderHom 0)))) ≫
          Sigma.ι (fun (τ : ComposableArrows C Δ'.unop.len) ↦ M.obj (τ.obj 0))
            (σ.whiskerLeft f.unop.toOrderHom.monotone.functor)
      map_id Δ := Sigma.hom_ext _ _ fun σ ↦
        (colimit.ι_desc _ (Discrete.mk σ)).trans <| by
          dsimp only [Cofan.mk_pt, Cofan.mk_ι_app]
          refine (congrArg (fun g : σ.obj 0 ⟶ σ.obj 0 ↦ M.map g ≫
              Sigma.ι (fun (τ : ComposableArrows C Δ.unop.len) ↦ M.obj (τ.obj 0)) σ)
            ((congrArg σ.map (Subsingleton.elim _ (𝟙 _))).trans (σ.map_id 0))).trans (by simp)
      map_comp {Δ Δ' Δ''} f g := Sigma.hom_ext _ _ fun σ ↦ by
        let v₁ : (0 : Fin (Δ.unop.len + 1)) ⟶ f.unop.toOrderHom 0 := homOfLE (Fin.zero_le _)
        let v₂ : f.unop.toOrderHom 0 ⟶ (f ≫ g).unop.toOrderHom 0 :=
          homOfLE (f.unop.toOrderHom.monotone (Fin.zero_le _))
        let v₃ : (0 : Fin (Δ.unop.len + 1)) ⟶ (f ≫ g).unop.toOrderHom 0 := homOfLE (Fin.zero_le _)
        have hcomp : σ.map v₁ ≫ σ.map v₂ = σ.map v₃ :=
          (σ.map_comp v₁ v₂).symm.trans (congrArg σ.map (Subsingleton.elim _ _))
        refine (colimit.ι_desc _ (Discrete.mk σ)).trans <| Eq.symm <|
          (colimit.ι_desc_assoc _ (Discrete.mk σ) _).trans ?_
        dsimp only [Cofan.mk_pt, Cofan.mk_ι_app]
        refine (Category.assoc _ _ _).trans <|
          (congrArg (M.map (σ.map v₁) ≫ ·) (colimit.ι_desc _ (Discrete.mk _))).trans <|
            (Category.assoc _ _ _).symm.trans ?_
        exact congrArg (fun k : M.obj (σ.obj 0) ⟶ M.obj (σ.obj ((f ≫ g).unop.toOrderHom 0)) ↦
            k ≫ Sigma.ι (fun (τ : ComposableArrows C Δ''.unop.len) ↦ M.obj (τ.obj 0))
              (σ.whiskerLeft (f ≫ g).unop.toOrderHom.monotone.functor))
          ((M.map_comp _ _).symm.trans (congrArg M.map hcomp)) }
  map {M N} α :=
    { app Δ := Sigma.desc fun (σ : ComposableArrows C Δ.unop.len) ↦
        α.app (σ.obj 0) ≫ Sigma.ι (fun (τ : ComposableArrows C Δ.unop.len) ↦ N.obj (τ.obj 0)) σ
      naturality {Δ Δ'} f := Sigma.hom_ext _ _ fun σ ↦ by
        let u₁ := σ.map (homOfLE (Fin.zero_le (f.unop.toOrderHom 0)))
        refine (colimit.ι_desc_assoc _ (Discrete.mk σ) _).trans <|
          (Category.assoc _ _ _).trans <|
          (congrArg (M.map u₁ ≫ ·) (colimit.ι_desc _ (Discrete.mk _))).trans <| Eq.symm <|
          (colimit.ι_desc_assoc _ (Discrete.mk σ) _).trans <| (Category.assoc _ _ _).trans <|
          (congrArg (α.app (σ.obj 0) ≫ ·) (colimit.ι_desc _ (Discrete.mk _))).trans ?_
        dsimp only [Cofan.mk_pt, Cofan.mk_ι_app]
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ Sigma.ι (fun (τ : ComposableArrows C Δ'.unop.len) ↦ N.obj (τ.obj 0))
              (σ.whiskerLeft f.unop.toOrderHom.monotone.functor))
            (α.naturality u₁).symm).trans (Category.assoc _ _ _)) }
  map_id M := by ext Δ σ; simp
  map_comp α β := by ext Δ σ; simp

instance categorySimplicialObjectFunctor_additive [Preadditive A] :
    (categorySimplicialObjectFunctor C A).Additive where
  map_add {_ _} _ _ := by
    ext Δ; dsimp [categorySimplicialObjectFunctor]; exact Sigma.hom_ext _ _ fun _ ↦ by simp

variable {A}

/-- The simplicial object in `A` associated to `C` and `M : C ⥤ A`. -/
abbrev categorySimplicialObject (M : C ⥤ A) : SimplicialObject A :=
  (categorySimplicialObjectFunctor C A).obj M

namespace categorySimplicialObject

variable {C}

/-- The coproduct inclusion `M.obj (σ.obj 0) ⟶ (categorySimplicialObject C M) _⦋n⦌`. -/
def ι (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categorySimplicialObject C M) _⦋n⦌ :=
  Sigma.ι (fun (τ : ComposableArrows C n) ↦ M.obj (τ.obj 0)) σ

lemma ι_congr (M : C ⥤ A) {n : ℕ} {σ τ : ComposableArrows C n} (h : σ = τ)
    (h₀ : σ.obj 0 = τ.obj 0 := by rw [h]) :
    ι M σ = eqToHom (congrArg M.obj h₀) ≫ ι M τ := by
  subst h; exact (Category.id_comp _).symm

@[ext]
lemma hom_ext {M : C ⥤ A} {n : ℕ} {T : A} {f g : (categorySimplicialObject C M) _⦋n⦌ ⟶ T}
    (h : ∀ σ : ComposableArrows C n, ι M σ ≫ f = ι M σ ≫ g) : f = g :=
  Sigma.hom_ext _ _ h

@[reassoc (attr := simp)]
lemma ι_map (M : C ⥤ A) {m n : ℕ} (σ : ComposableArrows C n) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    ι M σ ≫ (categorySimplicialObject C M).map φ.op =
      M.map (σ.map (homOfLE (Fin.zero_le (φ.toOrderHom 0)))) ≫
        ι M (n := m) ((nerve C).map φ.op σ) := by
  dsimp [ι, categorySimplicialObject, categorySimplicialObjectFunctor]
  exact colimit.ι_desc _ (Discrete.mk σ)

/-- The `0`-th face `δ 0` applies `M.map` to `σ.obj 0 ⟶ σ.obj 1`. -/
@[reassoc (attr := simp)]
lemma ι_δ_zero (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ι M σ ≫ (categorySimplicialObject C M).δ 0 =
      M.map (σ.map (homOfLE (Fin.zero_le 1))) ≫ ι M (n := n) ((nerve C).δ 0 σ) := by
  rw [SimplicialObject.δ, ι_map]
  exact congrArg (fun g : σ.obj 0 ⟶ σ.obj 1 ↦ M.map g ≫ ι M (n := n) ((nerve C).δ 0 σ))
    (congrArg σ.map (Subsingleton.elim _ _))

/-- Higher faces `δ j.succ` fix vertex `0` and act as the identity on `M.obj (σ.obj 0)`. -/
@[reassoc (attr := simp)]
lemma ι_δ_succ (M : C ⥤ A) {n : ℕ} (j : Fin (n + 1)) (σ : ComposableArrows C (n + 1)) :
    ι M σ ≫ (categorySimplicialObject C M).δ j.succ = ι M (n := n) ((nerve C).δ j.succ σ) := by
  rw [SimplicialObject.δ, ι_map]
  refine (congrArg (fun g : σ.obj 0 ⟶ σ.obj 0 ↦ M.map g ≫ ι M (n := n) ((nerve C).δ j.succ σ))
    ((congrArg σ.map (Subsingleton.elim _ (𝟙 (0 : Fin (n + 2))))).trans (σ.map_id 0))).trans ?_
  exact (congrArg (· ≫ _) (M.map_id (σ.obj 0))).trans (Category.id_comp _)

@[reassoc]
lemma ι_δ_last (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ι M σ ≫ (categorySimplicialObject C M).δ (Fin.last (n + 1)) = ι M σ.δlast := by
  rw [← Fin.succ_last n, ι_δ_succ]
  have h : (nerve C).δ (Fin.last n).succ σ = σ.δlast := by rw [Fin.succ_last, nerve.δ_last_eq]
  exact (ι_congr M h rfl).trans ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))

/-- Degeneracies `σ i` fix vertex `0` and act as the identity on `M.obj (τ.obj 0)`. -/
@[reassoc (attr := simp)]
lemma ι_σ (M : C ⥤ A) {n : ℕ} (i : Fin (n + 1)) (τ : ComposableArrows C n) :
    ι M τ ≫ (categorySimplicialObject C M).σ i = ι M (n := n + 1) ((nerve C).σ i τ) := by
  rw [SimplicialObject.σ, ι_map]
  refine (congrArg (fun g : τ.obj 0 ⟶ τ.obj 0 ↦ M.map g ≫ ι M (n := n + 1) ((nerve C).σ i τ))
    ((congrArg τ.map (Subsingleton.elim _ (𝟙 (0 : Fin (n + 1))))).trans (τ.map_id 0))).trans ?_
  exact (congrArg (· ≫ _) (M.map_id (τ.obj 0))).trans (Category.id_comp _)

@[reassoc (attr := simp)]
lemma ι_map_app {M N : C ⥤ A} (α : M ⟶ N) {n : ℕ} (σ : ComposableArrows C n) :
    ι M σ ≫ ((categorySimplicialObjectFunctor C A).map α).app (op ⦋n⦌) =
      α.app (σ.obj 0) ≫ ι N σ := by
  dsimp [ι, categorySimplicialObjectFunctor]; exact colimit.ι_desc _ (Discrete.mk σ)

end categorySimplicialObject

end SimplicialObject

section SimplicialPrecomp

variable {C : Type u₁} [Category.{v₁} C] {A : Type u} [Category.{v} A]
  [HasCoproducts.{max u₁ v₁} A]

/-- Pushforward of `categorySimplicialObject` along a functor `F : C ⥤ D`. -/
def categorySimplicialObjectPrecomp {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) :
    categorySimplicialObject C (F ⋙ M) ⟶ categorySimplicialObject D M where
  app Δ := Sigma.desc fun (σ : ComposableArrows C Δ.unop.len) ↦
    Sigma.ι (fun (τ : ComposableArrows D Δ.unop.len) ↦ M.obj (τ.obj 0))
      ((F.mapComposableArrows Δ.unop.len).obj σ)
  naturality {Δ Δ'} f := by
    dsimp only [categorySimplicialObject, categorySimplicialObjectFunctor]
    refine Sigma.hom_ext _ _ fun σ ↦ (colimit.ι_desc_assoc _ (Discrete.mk σ) _).trans ?_
    dsimp only [Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app, Functor.comp_obj,
      Functor.comp_map]
    exact (Category.assoc _ _ _).trans <|
      (congrArg (M.map _ ≫ ·) (colimit.ι_desc _ (Discrete.mk _))).trans <| Eq.symm <|
      (colimit.ι_desc_assoc _ (Discrete.mk σ) _).trans (colimit.ι_desc _ (Discrete.mk _))

@[reassoc (attr := simp)]
lemma categorySimplicialObject.ι_precomp_app {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    categorySimplicialObject.ι (F ⋙ M) σ ≫ (categorySimplicialObjectPrecomp F M).app (op ⦋n⦌) =
      categorySimplicialObject.ι M ((F.mapComposableArrows n).obj σ) := by
  dsimp [categorySimplicialObject.ι, categorySimplicialObjectPrecomp]
  exact colimit.ι_desc _ (Discrete.mk σ)

@[simp]
lemma categorySimplicialObjectPrecomp_id (M : C ⥤ A) :
    categorySimplicialObjectPrecomp (𝟭 C) M =
      (categorySimplicialObjectFunctor C A).map (Functor.leftUnitor M).hom := by
  ext Δ; dsimp only [categorySimplicialObjectPrecomp, categorySimplicialObjectFunctor]
  refine Sigma.hom_ext _ _ fun σ ↦ ?_
  simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Functor.leftUnitor_hom_app]
  exact (Category.id_comp _).symm

@[reassoc]
lemma categorySimplicialObjectPrecomp_comp {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₂ v₂} A]
    [HasCoproducts.{max u₃ v₃} A] (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    (categorySimplicialObjectFunctor C A).map (Functor.associator F G M).hom ≫
        categorySimplicialObjectPrecomp F (G ⋙ M) ≫ categorySimplicialObjectPrecomp G M =
      categorySimplicialObjectPrecomp (F ⋙ G) M := by
  ext Δ
  dsimp only [NatTrans.comp_app, categorySimplicialObjectFunctor, categorySimplicialObjectPrecomp]
  refine Sigma.hom_ext _ _ fun σ ↦ ?_
  simp only [Functor.associator_hom_app, Category.id_comp, colimit.ι_desc_assoc,
    Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app, colimit.ι_desc]
  rfl

@[reassoc]
lemma categorySimplicialObjectPrecomp_naturality {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) :
    (categorySimplicialObjectFunctor C A).map (Functor.whiskerLeft F α) ≫
        categorySimplicialObjectPrecomp F N =
      categorySimplicialObjectPrecomp F M ≫ (categorySimplicialObjectFunctor D A).map α := by
  ext Δ
  dsimp only [NatTrans.comp_app, categorySimplicialObjectFunctor, categorySimplicialObjectPrecomp]
  exact Sigma.hom_ext _ _ fun σ ↦ by simp

end SimplicialPrecomp

/-! ### The category chain complex -/

section ChainComplex

variable (C : Type u₁) [Category.{v₁} C] (A : Type u) [Category.{v} A]
  [HasCoproducts.{max u₁ v₁} A] [Preadditive A]

/-- The additive functor `(C ⥤ A) ⥤ ChainComplex A ℕ` sending `M` to the alternating face map
complex of `categorySimplicialObject C M`. -/
@[expose, implicit_reducible]
def categoryChainComplexFunctor : (C ⥤ A) ⥤ ChainComplex A ℕ :=
  categorySimplicialObjectFunctor C A ⋙ AlgebraicTopology.alternatingFaceMapComplex A

instance : (categoryChainComplexFunctor C A).Additive := by
  dsimp [categoryChainComplexFunctor]; infer_instance

variable {A}

/-- The chain complex of `C` with coefficients in `M : C ⥤ A`. -/
abbrev categoryChainComplex (M : C ⥤ A) : ChainComplex A ℕ :=
  (categoryChainComplexFunctor C A).obj M

variable {C} in
/-- The chain map induced by `α : M ⟶ N`. -/
abbrev categoryChainComplexMap {M N : C ⥤ A} (α : M ⟶ N) :
    categoryChainComplex C M ⟶ categoryChainComplex C N :=
  (categoryChainComplexFunctor C A).map α

variable {C}

lemma categoryChainComplexMap_id (M : C ⥤ A) :
    categoryChainComplexMap (𝟙 M) = 𝟙 (categoryChainComplex C M) :=
  (categoryChainComplexFunctor C A).map_id M

@[reassoc]
lemma categoryChainComplexMap_comp {L M N : C ⥤ A} (α : L ⟶ M) (β : M ⟶ N) :
    categoryChainComplexMap (α ≫ β) = categoryChainComplexMap α ≫ categoryChainComplexMap β :=
  (categoryChainComplexFunctor C A).map_comp α β

namespace categoryChainComplex

/-- The inclusion `M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X n` of the summand of `σ`. -/
@[expose]
def ι (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X n :=
  categorySimplicialObject.ι M σ

lemma ι_congr (M : C ⥤ A) {n : ℕ} {σ τ : ComposableArrows C n} (h : σ = τ)
    (h₀ : σ.obj 0 = τ.obj 0 := by rw [h]) :
    ι M σ = eqToHom (congrArg M.obj h₀) ≫ ι M τ :=
  categorySimplicialObject.ι_congr M h h₀

/-- The colimit cofan presenting `(categoryChainComplex C M).X n` as a coproduct. -/
@[expose]
def xCofan (M : C ⥤ A) (n : ℕ) : Cofan fun (σ : ComposableArrows C n) ↦ M.obj (σ.obj 0) :=
  Cofan.mk ((categoryChainComplex C M).X n) (ι M)

/-- `(categoryChainComplex C M).X n` is the coproduct `∐_{σ ∈ Nₙ C} M(σ₀)`. -/
def isColimitXCofan (M : C ⥤ A) (n : ℕ) : IsColimit (xCofan M n) :=
  coproductIsCoproduct _

@[ext]
lemma hom_ext {M : C ⥤ A} {n : ℕ} {T : A} {f g : (categoryChainComplex C M).X n ⟶ T}
    (h : ∀ σ : ComposableArrows C n, ι M σ ≫ f = ι M σ ≫ g) : f = g :=
  categorySimplicialObject.hom_ext h

@[reassoc (attr := simp)]
lemma ι_map_f {M N : C ⥤ A} (α : M ⟶ N) {n : ℕ} (σ : ComposableArrows C n) :
    ι M σ ≫ (categoryChainComplexMap α).f n = α.app (σ.obj 0) ≫ ι N σ :=
  categorySimplicialObject.ι_map_app α σ

/-- Alternating-face differential on the summand of `σ : ComposableArrows C (n + 1)`. -/
@[reassoc]
lemma ι_d (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ι M σ ≫ (categoryChainComplex C M).d (n + 1) n =
      M.map (σ.map (homOfLE (Fin.zero_le 1))) ≫ ι M (n := n) ((nerve C).δ 0 σ) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) • ι M (n := n) ((nerve C).δ j.succ σ) := by
  change categorySimplicialObject.ι M σ ≫
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (categorySimplicialObject C M)).d (n + 1) n = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Preadditive.comp_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, Preadditive.comp_zsmul]
  rw [categorySimplicialObject.ι_δ_zero,
    Finset.sum_congr rfl fun j _ ↦ by rw [categorySimplicialObject.ι_δ_succ]]
  rfl

/-- Degree-`0` summand inclusion `M.obj x ⟶ (categoryChainComplex C M).X 0`. -/
@[expose]
def ι₀ (M : C ⥤ A) (x : C) : M.obj x ⟶ (categoryChainComplex C M).X 0 :=
  ι M (ComposableArrows.mk₀ x)

@[simp] lemma ι_mk₀ (M : C ⥤ A) (x : C) : ι M (ComposableArrows.mk₀ x) = ι₀ M x := by rfl

/-- Degree-`1` summand inclusion `M.obj x ⟶ (categoryChainComplex C M).X 1` for `f : x ⟶ y`. -/
@[expose]
def ι₁ (M : C ⥤ A) {x y : C} (f : x ⟶ y) : M.obj x ⟶ (categoryChainComplex C M).X 1 :=
  ι M (ComposableArrows.mk₁ f)

@[simp] lemma ι_mk₁ (M : C ⥤ A) {x y : C} (f : x ⟶ y) :
    ι M (ComposableArrows.mk₁ f) = ι₁ M f := by rfl

/-- Degree-`2` summand inclusion `M.obj x ⟶ (categoryChainComplex C M).X 2` for `f`, `g`. -/
@[expose]
def ι₂ (M : C ⥤ A) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    M.obj x ⟶ (categoryChainComplex C M).X 2 :=
  ι M (ComposableArrows.mk₂ f g)

@[simp] lemma ι_mk₂ (M : C ⥤ A) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    ι M (ComposableArrows.mk₂ f g) = ι₂ M f g := by rfl

/-- Explicit formula for `d 1 0` on `mk₁ f` associated to `f : x ⟶ y`. -/
@[reassoc]
lemma ι₁_d_one_zero (M : C ⥤ A) {x y : C} (f : x ⟶ y) :
    ι₁ M f ≫ (categoryChainComplex C M).d 1 0 = M.map f ≫ ι₀ M y - ι₀ M x := by
  have e₀ : (nerve C).δ (0 : Fin 2) (ComposableArrows.mk₁ f) = ComposableArrows.mk₀ y :=
    ComposableArrows.ext₀ rfl
  have e₁ : (nerve C).δ (0 : Fin 1).succ (ComposableArrows.mk₁ f) = ComposableArrows.mk₀ x :=
    ComposableArrows.ext₀ rfl
  have h₀ : ι M (n := 0) ((nerve C).δ (0 : Fin 2) (ComposableArrows.mk₁ f)) = ι₀ M y :=
    (ι_congr M e₀ rfl).trans ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))
  have h₁ : ι M (n := 0) ((nerve C).δ (0 : Fin 1).succ (ComposableArrows.mk₁ f)) = ι₀ M x :=
    (ι_congr M e₁ rfl).trans ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))
  let s₁ (j : Fin 1) : M.obj x ⟶ (categoryChainComplex C M).X 0 :=
    (-1 : ℤ) ^ (j.val + 1) • ι M (n := 0) ((nerve C).δ j.succ (ComposableArrows.mk₁ f))
  refine (ι_d M (ComposableArrows.mk₁ f)).trans ((congrArg₂ (· + ·) (congrArg (M.map f ≫ ·) h₀)
    ((Fin.sum_univ_one s₁).trans
      (congrArg (fun v ↦ (-1 : ℤ) ^ ((0 : Fin 1).val + 1) • v) h₁))).trans ?_)
  exact (congrArg (M.map f ≫ ι₀ M y + ·) (neg_one_zsmul (ι₀ M x))).trans (sub_eq_add_neg _ _).symm

/-- Explicit formula for `d 2 1` on `mk₂ f g` associated to `f : x ⟶ y` and `g : y ⟶ z`. -/
@[reassoc]
lemma ι₂_d_two_one (M : C ⥤ A) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    ι₂ M f g ≫ (categoryChainComplex C M).d 2 1 =
      M.map f ≫ ι₁ M g - ι₁ M (f ≫ g) + ι₁ M f := by
  have h₀ : ι M (n := 1) ((nerve C).δ (0 : Fin 3) (ComposableArrows.mk₂ f g)) = ι₁ M g :=
    (ι_congr M (nerve.δ₀_mk₂_eq f g) rfl).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))
  have h₁ : ι M (n := 1) ((nerve C).δ (0 : Fin 2).succ (ComposableArrows.mk₂ f g)) =
      ι₁ M (f ≫ g) := (ι_congr M (nerve.δ₁_mk₂_eq f g) rfl).trans
    ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))
  have h₂ : ι M (n := 1) ((nerve C).δ (1 : Fin 2).succ (ComposableArrows.mk₂ f g)) = ι₁ M f :=
    (ι_congr M (nerve.δ₂_mk₂_eq f g) rfl).trans
      ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))
  let s₂ (j : Fin 2) : M.obj x ⟶ (categoryChainComplex C M).X 1 :=
    (-1 : ℤ) ^ (j.val + 1) • ι M (n := 1) ((nerve C).δ j.succ (ComposableArrows.mk₂ f g))
  refine (ι_d M (ComposableArrows.mk₂ f g)).trans ((congrArg₂ (· + ·) (congrArg (M.map f ≫ ·) h₀)
    ((Fin.sum_univ_two s₂).trans (congrArg₂ (· + ·)
      (congrArg (fun v ↦ (-1 : ℤ) ^ ((0 : Fin 2).val + 1) • v) h₁)
      (congrArg (fun v ↦ (-1 : ℤ) ^ ((1 : Fin 2).val + 1) • v) h₂)))).trans ?_)
  exact (congrArg (M.map f ≫ ι₁ M g + ·) (congrArg₂ (· + ·) (neg_one_zsmul _) (one_zsmul _))).trans
    ((add_assoc _ _ _).symm.trans (congrArg (· + ι₁ M f) (sub_eq_add_neg _ _).symm))

end categoryChainComplex

end ChainComplex

section ChainPrecomp

variable {C : Type u₁} [Category.{v₁} C] {A : Type u} [Category.{v} A]
  [HasCoproducts.{max u₁ v₁} A] [Preadditive A]

/-- The chain map `categoryChainComplex C (F ⋙ M) ⟶ categoryChainComplex D M` for `F : C ⥤ D`. -/
@[expose]
def categoryChainComplexPrecomp {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) :
    categoryChainComplex C (F ⋙ M) ⟶ categoryChainComplex D M :=
  (AlgebraicTopology.alternatingFaceMapComplex A).map (categorySimplicialObjectPrecomp F M)

@[reassoc (attr := simp)]
lemma categoryChainComplex.ι_precomp_f {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    categoryChainComplex.ι (F ⋙ M) σ ≫ (categoryChainComplexPrecomp F M).f n =
      categoryChainComplex.ι M ((F.mapComposableArrows n).obj σ) :=
  categorySimplicialObject.ι_precomp_app F M σ

@[simp]
lemma categoryChainComplexPrecomp_id (M : C ⥤ A) :
    categoryChainComplexPrecomp (𝟭 C) M = categoryChainComplexMap (Functor.leftUnitor M).hom := by
  dsimp [categoryChainComplexPrecomp, categoryChainComplexMap, categoryChainComplexFunctor]
  rw [categorySimplicialObjectPrecomp_id]

@[reassoc]
lemma categoryChainComplexPrecomp_comp {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₂ v₂} A]
    [HasCoproducts.{max u₃ v₃} A] (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    categoryChainComplexMap (Functor.associator F G M).hom ≫
        categoryChainComplexPrecomp F (G ⋙ M) ≫ categoryChainComplexPrecomp G M =
      categoryChainComplexPrecomp (F ⋙ G) M := by
  dsimp [categoryChainComplexPrecomp, categoryChainComplexMap, categoryChainComplexFunctor]
  rw [← Functor.map_comp, ← Functor.map_comp, categorySimplicialObjectPrecomp_comp]

@[reassoc]
lemma categoryChainComplexPrecomp_naturality {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) :
    categoryChainComplexMap (Functor.whiskerLeft F α) ≫ categoryChainComplexPrecomp F N =
      categoryChainComplexPrecomp F M ≫ categoryChainComplexMap α := by
  dsimp [categoryChainComplexPrecomp, categoryChainComplexMap, categoryChainComplexFunctor]
  rw [← Functor.map_comp, ← Functor.map_comp, categorySimplicialObjectPrecomp_naturality]

end ChainPrecomp

/-! ### Module-valued chains as direct sums -/

section DirectSum

variable (C : Type u₁) [Category.{v₁} C] {R : Type*} [Ring R]
  (M : C ⥤ ModuleCat.{max u₁ v₁ w} R)

open scoped Classical in
/-- Degree-`n` chains of `M : C ⥤ ModuleCat R` are linearly equivalent to
`⨁ (σ : ComposableArrows C n), M.obj (σ.obj 0)`. -/
def categoryChainComplexXLinearEquivDirectSum (n : ℕ) :
    ((categoryChainComplex C M).X n) ≃ₗ[R] ⨁ (σ : ComposableArrows C n), M.obj (σ.obj 0) :=
  (ModuleCat.coprodIsoDirectSum fun (σ : ComposableArrows C n) ↦ M.obj (σ.obj 0)).toLinearEquiv

variable {C M} in
open scoped Classical in
@[simp]
lemma categoryChainComplexXLinearEquivDirectSum_ι {n : ℕ} (σ : ComposableArrows C n)
    (m : M.obj (σ.obj 0)) :
    categoryChainComplexXLinearEquivDirectSum C M n (categoryChainComplex.ι M σ m) =
      DirectSum.lof R (ComposableArrows C n) (fun τ ↦ M.obj (τ.obj 0)) σ m := by
  rw [categoryChainComplexXLinearEquivDirectSum, Iso.toLinearEquiv_apply,
    categoryChainComplex.ι, categorySimplicialObject.ι, ModuleCat.ι_coprodIsoDirectSum_hom_apply]

variable {C M} in
open scoped Classical in
@[simp]
lemma categoryChainComplexXLinearEquivDirectSum_symm_lof {n : ℕ} (σ : ComposableArrows C n)
    (m : M.obj (σ.obj 0)) :
    (categoryChainComplexXLinearEquivDirectSum C M n).symm
        (DirectSum.lof R (ComposableArrows C n) (fun τ ↦ M.obj (τ.obj 0)) σ m) =
      categoryChainComplex.ι M σ m := by
  rw [LinearEquiv.symm_apply_eq, categoryChainComplexXLinearEquivDirectSum_ι]

end DirectSum

/-! ### Category homology -/

section Homology

variable (C : Type u₁) [Category.{v₁} C] {A : Type u} [Category.{v} A]
  [HasCoproducts.{max u₁ v₁} A] [Preadditive A] [CategoryWithHomology A]

/-- The degree-`n` homology `Hₙ(C, M)` of `C` with coefficients in `M : C ⥤ A`. -/
abbrev categoryHomology (M : C ⥤ A) (n : ℕ) : A :=
  (categoryChainComplex C M).homology n

variable {C} in
/-- The morphism `Hₙ(C, M) ⟶ Hₙ(C, N)` induced by `α : M ⟶ N`. -/
abbrev categoryHomologyMap {M N : C ⥤ A} (α : M ⟶ N) (n : ℕ) :
    categoryHomology C M n ⟶ categoryHomology C N n :=
  HomologicalComplex.homologyMap (categoryChainComplexMap α) n

variable {C} in
@[simp]
lemma categoryHomologyMap_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyMap (𝟙 M) n = 𝟙 (categoryHomology C M n) := by simp [categoryHomologyMap]

variable {C} in
@[reassoc]
lemma categoryHomologyMap_comp {L M N : C ⥤ A} (α : L ⟶ M) (β : M ⟶ N) (n : ℕ) :
    categoryHomologyMap (α ≫ β) n = categoryHomologyMap α n ≫ categoryHomologyMap β n := by
  rw [categoryHomologyMap, categoryChainComplexMap_comp, HomologicalComplex.homologyMap_comp]

variable {C} in
@[simp]
lemma categoryHomologyMap_zero (M N : C ⥤ A) (n : ℕ) :
    categoryHomologyMap (0 : M ⟶ N) n = 0 := by
  simp [categoryHomologyMap, Functor.map_zero, HomologicalComplex.homologyMap_zero]

variable (A) in
/-- The degree-`n` category homology functor `(C ⥤ A) ⥤ A`. -/
@[expose, implicit_reducible, simps]
def categoryHomologyFunctor (n : ℕ) : (C ⥤ A) ⥤ A where
  obj M := categoryHomology C M n
  map α := categoryHomologyMap α n
  map_id M := categoryHomologyMap_id M n
  map_comp α β := categoryHomologyMap_comp α β n

instance (n : ℕ) : (categoryHomologyFunctor C A n).Additive where
  map_add := by simp [categoryHomologyMap, Functor.map_add, HomologicalComplex.homologyMap_add]

section Precomp

variable {C}

/-- The morphism `Hₙ(C, F ⋙ M) ⟶ Hₙ(D, M)` induced by `F : C ⥤ D`. -/
abbrev categoryHomologyPrecomp {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) (n : ℕ) :
    categoryHomology C (F ⋙ M) n ⟶ categoryHomology D M n :=
  HomologicalComplex.homologyMap (categoryChainComplexPrecomp F M) n

@[simp]
lemma categoryHomologyPrecomp_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyPrecomp (𝟭 C) M n = categoryHomologyMap (Functor.leftUnitor M).hom n := by
  rw [categoryHomologyPrecomp, categoryChainComplexPrecomp_id]

@[reassoc]
lemma categoryHomologyPrecomp_comp {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₂ v₂} A]
    [HasCoproducts.{max u₃ v₃} A] (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) (n : ℕ) :
    categoryHomologyMap (Functor.associator F G M).hom n ≫
        categoryHomologyPrecomp F (G ⋙ M) n ≫ categoryHomologyPrecomp G M n =
      categoryHomologyPrecomp (F ⋙ G) M n := by
  dsimp only [categoryHomologyPrecomp, categoryHomologyMap]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    categoryChainComplexPrecomp_comp]

@[reassoc]
lemma categoryHomologyPrecomp_naturality {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) (n : ℕ) :
    categoryHomologyMap (Functor.whiskerLeft F α) n ≫ categoryHomologyPrecomp F N n =
      categoryHomologyPrecomp F M n ≫ categoryHomologyMap α n := by
  dsimp only [categoryHomologyPrecomp, categoryHomologyMap]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    categoryChainComplexPrecomp_naturality]

end Precomp

end Homology

/-! ### Constant coefficients and homology of the nerve -/

section ConstantCoefficients

variable (C : Type u₁) [Category.{v₁} C] {A : Type u} [Category.{v} A]
  [HasCoproducts.{max u₁ v₁} A]

/-- For constant coefficients at `X : A`, `categorySimplicialObject C` is canonically isomorphic to
`nerve C` tensored with `X` via `sigmaConst`. -/
def categorySimplicialObjectConstIso (X : A) :
    categorySimplicialObject C ((Functor.const C).obj X) ≅
      ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj X)).obj (nerve C) :=
  NatIso.ofComponents
    (fun Δ ↦
      { hom := Sigma.desc fun (σ : ComposableArrows C Δ.unop.len) ↦
          Sigma.ι (fun (_ : (nerve C).obj Δ) ↦ X) (σ : (nerve C).obj Δ)
        inv := Sigma.desc fun (σ : (nerve C).obj Δ) ↦
          Sigma.ι (fun (τ : ComposableArrows C Δ.unop.len) ↦
            ((Functor.const C).obj X).obj (τ.obj 0)) σ
        hom_inv_id := Sigma.hom_ext _ _ fun (σ : ComposableArrows C Δ.unop.len) ↦ by
          dsimp only [categorySimplicialObject, categorySimplicialObjectFunctor]
          exact (Sigma.ι_comp_desc_assoc _ σ _).trans
            ((Sigma.ι_comp_desc _ (σ : (nerve C).obj Δ)).trans (Category.comp_id _).symm)
        inv_hom_id := Sigma.hom_ext _ _ fun (σ : (nerve C).obj Δ) ↦ by
          dsimp only [SimplicialObject.whiskering, Functor.whiskeringRight_obj_obj,
            Functor.comp_obj, sigmaConst]
          exact (Sigma.ι_comp_desc_assoc _ σ _).trans ((Sigma.ι_comp_desc _
            (σ : ComposableArrows C Δ.unop.len)).trans (Category.comp_id _).symm) })
    (fun {Δ _} _ ↦ Sigma.hom_ext _ _ fun (σ : ComposableArrows C Δ.unop.len) ↦ by
      dsimp only [categorySimplicialObject, categorySimplicialObjectFunctor,
        SimplicialObject.whiskering, Functor.whiskeringRight_obj_obj, Functor.comp_obj,
        Functor.comp_map, sigmaConst]
      refine (Sigma.ι_comp_desc_assoc _ σ _).trans ?_
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
      refine (Category.assoc _ _ _).trans ((Category.id_comp _).trans
        ((Sigma.ι_comp_desc _ _).trans (Eq.symm ?_)))
      exact (Sigma.ι_comp_desc_assoc _ σ _).trans
        ((Sigma.ι_comp_map' _ _ (σ : (nerve C).obj Δ)).trans (Category.id_comp _)))

section Preadditive

variable [Preadditive A]

/-- For constant coefficients at `X : A`, `categoryChainComplex C ((Functor.const C).obj X)` is
canonically isomorphic to `(nerve C).chainComplex X`. -/
def categoryChainComplexConstIso (X : A) :
    categoryChainComplex C ((Functor.const C).obj X) ≅ (nerve C).chainComplex X :=
  (AlgebraicTopology.alternatingFaceMapComplex A).mapIso (categorySimplicialObjectConstIso C X)

variable {C} in
@[reassoc (attr := simp)]
lemma categoryChainComplex.ι_constIso_hom_f (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    categoryChainComplex.ι ((Functor.const C).obj X) σ ≫
        (categoryChainComplexConstIso C X).hom.f n =
      (nerve C).ιChainComplex (σ : (nerve C) _⦋n⦌) := by
  dsimp [categoryChainComplex.ι, categorySimplicialObject.ι, categoryChainComplexConstIso,
    categorySimplicialObjectConstIso, SSet.ιChainComplex, SSet.chainComplex,
    SSet.chainComplexFunctor, SimplicialObject.whiskering, sigmaConst]
  exact colimit.ι_desc _ (Discrete.mk σ)

variable {C} in
@[reassoc (attr := simp)]
lemma categoryChainComplex.ιChainComplex_constIso_inv_f (X : A) {n : ℕ} (σ : (nerve C) _⦋n⦌) :
    (nerve C).ιChainComplex σ ≫ (categoryChainComplexConstIso C X).inv.f n =
      categoryChainComplex.ι ((Functor.const C).obj X) σ := by
  dsimp [categoryChainComplex.ι, categorySimplicialObject.ι, categoryChainComplexConstIso,
    categorySimplicialObjectConstIso, SSet.ιChainComplex, SSet.chainComplex,
    SSet.chainComplexFunctor, SimplicialObject.whiskering, sigmaConst,
    categoryChainComplex, categoryChainComplexFunctor, categorySimplicialObjectFunctor]
  exact colimit.ι_desc _ (Discrete.mk σ)

@[reassoc]
lemma categoryChainComplexConstIso_naturality {X Y : A} (u : X ⟶ Y) :
    categoryChainComplexMap ((Functor.const C).map u) ≫ (categoryChainComplexConstIso C Y).hom =
      (categoryChainComplexConstIso C X).hom ≫
        ((SSet.chainComplexFunctor A).map u).app (nerve C) := by
  ext n σ
  simp only [HomologicalComplex.comp_f, categoryChainComplex.ι_map_f_assoc,
    Functor.const_map_app, categoryChainComplex.ι_constIso_hom_f,
    categoryChainComplex.ι_constIso_hom_f_assoc]
  let σ' : (nerve C) _⦋n⦌ := σ
  change u ≫ (nerve C).ιChainComplex σ' =
    (nerve C).ιChainComplex σ' ≫ (((SSet.chainComplexFunctor A).map u).app (nerve C)).f n
  dsimp [SSet.chainComplexFunctor, SSet.ιChainComplex, SimplicialObject.whiskering, sigmaConst]
  simp

@[reassoc]
lemma categoryChainComplexPrecomp_const {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D) (X : A) :
    categoryChainComplexMap ((Functor.constCompWhiskeringLeftIso C F).inv.app X) ≫
        categoryChainComplexPrecomp F ((Functor.const D).obj X) ≫
          (categoryChainComplexConstIso D X).hom =
      (categoryChainComplexConstIso C X).hom ≫ SSet.chainComplexMap (nerveMap F) X := by
  ext n σ
  simp only [HomologicalComplex.comp_f, categoryChainComplex.ι_map_f_assoc,
    Functor.constCompWhiskeringLeftIso_inv_app_app]
  exact (Category.id_comp _).trans
    ((categoryChainComplex.ι_precomp_f_assoc F ((Functor.const D).obj X) σ _).trans
      ((categoryChainComplex.ι_constIso_hom_f X ((F.mapComposableArrows n).obj σ)).trans
        ((categoryChainComplex.ι_constIso_hom_f_assoc X σ _).trans
          (SSet.ι_chainComplexMap_f (nerve C) (nerve D) (nerveMap F) X (σ : (nerve C) _⦋n⦌))).symm))

end Preadditive

section Homology

variable [Preadditive A] [CategoryWithHomology A]

/-- For constant coefficients at `X : A`, `Hₙ(C, X) ≅ (nerve C).homology X n`. -/
def categoryHomologyConstIso (X : A) (n : ℕ) :
    categoryHomology C ((Functor.const C).obj X) n ≅ (nerve C).homology X n :=
  HomologicalComplex.homologyMapIso (categoryChainComplexConstIso C X) n

@[simp]
lemma categoryHomologyConstIso_hom (X : A) (n : ℕ) :
    (categoryHomologyConstIso C X n).hom =
      HomologicalComplex.homologyMap (categoryChainComplexConstIso C X).hom n := by rfl

@[simp]
lemma categoryHomologyConstIso_inv (X : A) (n : ℕ) :
    (categoryHomologyConstIso C X n).inv =
      HomologicalComplex.homologyMap (categoryChainComplexConstIso C X).inv n := by rfl

@[reassoc]
lemma categoryHomologyConstIso_naturality {X Y : A} (u : X ⟶ Y) (n : ℕ) :
    categoryHomologyMap ((Functor.const C).map u) n ≫ (categoryHomologyConstIso C Y n).hom =
      (categoryHomologyConstIso C X n).hom ≫
        HomologicalComplex.homologyMap (((SSet.chainComplexFunctor A).map u).app (nerve C)) n := by
  simp only [categoryHomologyConstIso_hom, categoryHomologyMap,
    ← HomologicalComplex.homologyMap_comp, categoryChainComplexConstIso_naturality]

@[reassoc]
lemma categoryHomologyPrecomp_const {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D) (X : A) (n : ℕ) :
    categoryHomologyMap ((Functor.constCompWhiskeringLeftIso C F).inv.app X) n ≫
        categoryHomologyPrecomp F ((Functor.const D).obj X) n ≫
          (categoryHomologyConstIso D X n).hom =
      (categoryHomologyConstIso C X n).hom ≫ SSet.homologyMap (nerveMap F) X n := by
  simp only [categoryHomologyConstIso_hom, categoryHomologyPrecomp, categoryHomologyMap,
    SSet.homologyMap, ← HomologicalComplex.homologyMap_comp, categoryChainComplexPrecomp_const]

end Homology

end ConstantCoefficients

end TauCeti
