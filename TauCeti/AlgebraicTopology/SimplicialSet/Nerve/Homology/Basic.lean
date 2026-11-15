/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Homology of a category with coefficients in a functor

For a category `C` and `M : C ⥤ A`, `TauCeti.categorySimplicialObject C M` has degree-`n` object
`∐_{σ ∈ ComposableArrows C n} M(σ₀)`, and its alternating complex `TauCeti.categoryChainComplex`
and homology `TauCeti.categoryHomology` are functorial in `M` and `F : C ⥤ D`, recover
`(nerve C).homology X n` for constant coefficients, and send short exact coefficient sequences in
`AB4` abelian categories to long exact homology sequences (`TauCeti.categoryHomologyδ`).

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, p. 91.
* C. A. Weibel, *The K-book*, Graduate Studies in Math. 145 (2013), IV.3.5.
-/

public noncomputable section

open CategoryTheory Limits Opposite Simplicial

universe u v u₂ v₂ u₃ v₃ u' v'

namespace TauCeti

section SimplicialObject

variable {A : Type u'} [Category.{v'} A]

private lemma map_zero_le_heq_id {C : Type u} [Category.{v} C] (M : C ⥤ A) {m : ℕ}
    (σ : ComposableArrows C m) {z : Fin (m + 1)} (hz : z = 0) :
    M.map (σ.map (homOfLE (Fin.zero_le z))) ≍ 𝟙 (M.obj (σ.obj 0)) := by
  subst hz
  rw [Subsingleton.elim (homOfLE (Fin.zero_le (0 : Fin (m + 1)))) (𝟙 0), σ.map_id, M.map_id]

private lemma ι_comp_desc_desc {I J : Type*} {P : I → A} {Q : J → A}
    [HasCoproduct P] [HasCoproduct Q] {T : A} (i : I) (j : I → J)
    (u : ∀ a, P a ⟶ Q (j a)) (k : ∀ b, Q b ⟶ T) :
    Sigma.ι P i ≫ (Sigma.desc (fun a ↦ u a ≫ Sigma.ι Q (j a)) ≫ Sigma.desc k) = u i ≫ k (j i) := by
  rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc, Sigma.ι_comp_desc]

private lemma ι_comp_desc_id_desc {I J : Type*} {Q : J → A} (j : I → J)
    [HasCoproduct (fun a : I ↦ Q (j a))] [HasCoproduct Q] {T : A} (i : I) (k : ∀ b, Q b ⟶ T) :
    Sigma.ι (fun a : I ↦ Q (j a)) i ≫ (Sigma.desc (fun a : I ↦ Sigma.ι Q (j a)) ≫ Sigma.desc k) =
      k (j i) := by
  rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]

/-- The simplicial object associated to `C` and `M : C ⥤ A`, with degree-`n` object
`∐_{σ : ComposableArrows C n} M.obj (σ.obj 0)`. -/
def categorySimplicialObject (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (M : C ⥤ A) : SimplicialObject A where
  obj Δ := ∐ fun σ : ComposableArrows C Δ.unop.len ↦ M.obj (σ.obj 0)
  map {Δ₁ Δ₂} f := Sigma.desc fun σ ↦
    M.map (σ.map (homOfLE (Fin.zero_le (f.unop.toOrderHom (0 : Fin (Δ₂.unop.len + 1)))))) ≫
      Sigma.ι (fun τ : ComposableArrows C Δ₂.unop.len ↦ M.obj (τ.obj 0))
        (σ.whiskerLeft f.unop.toOrderHom.monotone.functor)
  map_id Δ := by
    ext σ; refine (Sigma.ι_comp_desc _ σ).trans ((congrArg (· ≫ _)
      (eq_of_heq (map_zero_le_heq_id M σ rfl))).trans
        ((Category.id_comp _).trans (Category.comp_id _).symm))
  map_comp {Δ₁ Δ₂ Δ₃} f g := by
    ext σ; refine (Sigma.ι_comp_desc _ σ).trans (Eq.symm ((ι_comp_desc_desc σ
      (fun τ : ComposableArrows C Δ₁.unop.len ↦ τ.whiskerLeft f.unop.toOrderHom.monotone.functor)
      (fun τ ↦ M.map (τ.map (homOfLE (Fin.zero_le (f.unop.toOrderHom 0)))))
      (fun ρ ↦ M.map (ρ.map (homOfLE (Fin.zero_le (g.unop.toOrderHom 0)))) ≫
        Sigma.ι (fun υ : ComposableArrows C Δ₃.unop.len ↦ M.obj (υ.obj 0))
          (ρ.whiskerLeft g.unop.toOrderHom.monotone.functor))).trans ?_))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ((M.map_comp _ _).symm.trans
      (congrArg M.map ((σ.map_comp _ _).symm.trans (congrArg σ.map (Subsingleton.elim _ _))))))

section SimplicialLemmas

variable {C : Type u} [Category.{v} C] [HasCoproducts.{max u v} A]

/-- Inclusion `M.obj (σ.obj 0) ⟶ (categorySimplicialObject C M) _⦋n⦌` of the `σ`-summand. -/
def ιCategorySimplicialObject (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categorySimplicialObject C M) _⦋n⦌ :=
  Sigma.ι (fun τ : ComposableArrows C n ↦ M.obj (τ.obj 0)) σ

/-- Colimit cofan presenting `(categorySimplicialObject C M) _⦋n⦌` as `∐_{σ ∈ NₙC} M(σ₀)`. -/
abbrev categorySimplicialObjectXCofan (M : C ⥤ A) (n : ℕ) :
    Cofan (fun σ : ComposableArrows C n ↦ M.obj (σ.obj 0)) :=
  Cofan.mk _ (ιCategorySimplicialObject M)

/-- `categorySimplicialObjectXCofan M n` is a coproduct colimit. -/
def isColimitCategorySimplicialObjectXCofan (M : C ⥤ A) (n : ℕ) :
    IsColimit (categorySimplicialObjectXCofan M n) :=
  coproductIsCoproduct _

@[ext]
lemma categorySimplicialObject_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (categorySimplicialObject C M) _⦋n⦌ ⟶ T}
    (h : ∀ σ : ComposableArrows C n,
      ιCategorySimplicialObject M σ ≫ f = ιCategorySimplicialObject M σ ≫ g) : f = g :=
  (isColimitCategorySimplicialObjectXCofan M n).hom_ext fun ⟨σ⟩ ↦ h σ

/-- Action of `φ : ⦋m⦌ ⟶ ⦋n⦌` on the `σ`-summand of `categorySimplicialObject C M`. -/
@[reassoc]
lemma ιCategorySimplicialObject_map (M : C ⥤ A) {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows C n) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObject C M).map φ.op =
      M.map (σ.map (homOfLE (Fin.zero_le (φ.toOrderHom 0)))) ≫
        ιCategorySimplicialObject M ((nerve C).map φ.op σ) :=
  Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_δ_zero (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObject C M).δ 0 =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
        ιCategorySimplicialObject M ((nerve C).δ 0 σ) := by
  rw [SimplicialObject.δ, ιCategorySimplicialObject_map]; rfl

@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_δ_succ (M : C ⥤ A) {n : ℕ} (j : Fin (n + 1))
    (σ : ComposableArrows C (n + 1)) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObject C M).δ j.succ =
      ιCategorySimplicialObject M ((nerve C).δ j.succ σ) :=
  (ιCategorySimplicialObject_map M (SimplexCategory.δ j.succ) σ).trans
    ((congrArg (· ≫ _) (eq_of_heq (map_zero_le_heq_id M σ rfl))).trans (Category.id_comp _))

@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_σ (M : C ⥤ A) {n : ℕ} (i : Fin (n + 1))
    (τ : ComposableArrows C n) :
    ιCategorySimplicialObject M τ ≫ (categorySimplicialObject C M).σ i =
      ιCategorySimplicialObject M ((nerve C).σ i τ) :=
  (ιCategorySimplicialObject_map M (SimplexCategory.σ i) τ).trans
    ((congrArg (· ≫ _) (eq_of_heq (map_zero_le_heq_id M τ rfl))).trans (Category.id_comp _))

/-- Morphism of simplicial objects induced by `α : M ⟶ N`. -/
def categorySimplicialObjectCoeffMap {M N : C ⥤ A} (α : M ⟶ N) :
    categorySimplicialObject C M ⟶ categorySimplicialObject C N where
  app Δ := Sigma.desc fun σ ↦
    α.app (σ.obj 0) ≫ Sigma.ι (fun τ : ComposableArrows C Δ.unop.len ↦ N.obj (τ.obj 0)) σ
  naturality {Δ₁ Δ₂} f := by
    dsimp only [categorySimplicialObject]
    ext σ
    refine (ι_comp_desc_desc σ
      (fun τ : ComposableArrows C Δ₁.unop.len ↦ τ.whiskerLeft f.unop.toOrderHom.monotone.functor)
      (fun τ ↦ M.map (τ.map (homOfLE (Fin.zero_le (f.unop.toOrderHom 0)))))
      (fun ρ ↦ α.app (ρ.obj 0) ≫
        Sigma.ι (fun υ : ComposableArrows C Δ₂.unop.len ↦ N.obj (υ.obj 0)) ρ)).trans
      (Eq.symm ((ι_comp_desc_desc σ id (fun τ ↦ α.app (τ.obj 0))
        (fun τ ↦ N.map (τ.map (homOfLE (Fin.zero_le (f.unop.toOrderHom 0)))) ≫
          Sigma.ι (fun υ : ComposableArrows C Δ₂.unop.len ↦ N.obj (υ.obj 0))
            (τ.whiskerLeft f.unop.toOrderHom.monotone.functor))).trans ?_))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (α.naturality _).symm).trans (Category.assoc _ _ _))

@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_coeffMap_app {M N : C ⥤ A} (α : M ⟶ N) {n : ℕ}
    (σ : ComposableArrows C n) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObjectCoeffMap α).app (op ⦋n⦌) =
      α.app (σ.obj 0) ≫ ιCategorySimplicialObject N σ :=
  Sigma.ι_comp_desc _ _

@[simp]
lemma categorySimplicialObjectCoeffMap_id (M : C ⥤ A) :
    categorySimplicialObjectCoeffMap (𝟙 M) = 𝟙 (categorySimplicialObject C M) :=
  NatTrans.ext (funext fun ⟨⟨_⟩⟩ ↦ categorySimplicialObject_hom_ext fun _ ↦ by simp)

@[reassoc]
lemma categorySimplicialObjectCoeffMap_comp {L M N : C ⥤ A} (α : L ⟶ M) (β : M ⟶ N) :
    categorySimplicialObjectCoeffMap (α ≫ β) =
      categorySimplicialObjectCoeffMap α ≫ categorySimplicialObjectCoeffMap β :=
  NatTrans.ext (funext fun ⟨⟨_⟩⟩ ↦ categorySimplicialObject_hom_ext fun _ ↦ by simp)

/-- Morphism of simplicial objects induced by `F : C ⥤ D` and `M : D ⥤ A`. -/
def categorySimplicialObjectMap {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) :
    categorySimplicialObject C (F ⋙ M) ⟶ categorySimplicialObject D M where
  app Δ := Sigma.desc fun σ ↦
    Sigma.ι (fun τ : ComposableArrows D Δ.unop.len ↦ M.obj (τ.obj 0))
      ((F.mapComposableArrows Δ.unop.len).obj σ)
  naturality {Δ₁ Δ₂} f := by
    dsimp only [categorySimplicialObject]
    ext σ
    exact (ι_comp_desc_desc
      (Q := fun ρ : ComposableArrows C Δ₂.unop.len ↦ (F ⋙ M).obj (ρ.obj 0)) σ
      (fun τ : ComposableArrows C Δ₁.unop.len ↦ τ.whiskerLeft f.unop.toOrderHom.monotone.functor)
      (fun τ ↦ (F ⋙ M).map (τ.map (homOfLE (Fin.zero_le (f.unop.toOrderHom 0)))))
      (fun ρ ↦ Sigma.ι (fun υ : ComposableArrows D Δ₂.unop.len ↦ M.obj (υ.obj 0))
        ((F.mapComposableArrows Δ₂.unop.len).obj ρ))).trans
      (ι_comp_desc_id_desc
        (fun τ : ComposableArrows C Δ₁.unop.len ↦ (F.mapComposableArrows Δ₁.unop.len).obj τ) σ
        (fun ρ ↦ M.map (ρ.map (homOfLE (Fin.zero_le (f.unop.toOrderHom 0)))) ≫
          Sigma.ι (fun υ : ComposableArrows D Δ₂.unop.len ↦ M.obj (υ.obj 0))
            (ρ.whiskerLeft f.unop.toOrderHom.monotone.functor))).symm

@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_categorySimplicialObjectMap_app
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategorySimplicialObject (F ⋙ M) σ ≫ (categorySimplicialObjectMap F M).app (op ⦋n⦌) =
      ιCategorySimplicialObject M ((F.mapComposableArrows n).obj σ) :=
  Sigma.ι_comp_desc _ _

@[simp]
lemma categorySimplicialObjectMap_id (M : C ⥤ A) :
    categorySimplicialObjectMap (𝟭 C) M = 𝟙 (categorySimplicialObject C M) :=
  NatTrans.ext (funext fun ⟨⟨_⟩⟩ ↦ categorySimplicialObject_hom_ext fun σ ↦
    (ιCategorySimplicialObject_categorySimplicialObjectMap_app (𝟭 C) M σ).trans
      (Category.comp_id _).symm)

@[reassoc]
lemma categorySimplicialObjectMap_comp
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₃ v₃} A]
    (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    categorySimplicialObjectMap (F ⋙ G) M =
      categorySimplicialObjectMap F (G ⋙ M) ≫ categorySimplicialObjectMap G M := by
  refine NatTrans.ext (funext fun ⟨⟨n⟩⟩ ↦ categorySimplicialObject_hom_ext fun σ ↦ ?_)
  rw [ιCategorySimplicialObject_categorySimplicialObjectMap_app, NatTrans.comp_app]
  exact ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (categorySimplicialObjectMap G M).app (op ⦋n⦌))
      (ιCategorySimplicialObject_categorySimplicialObjectMap_app F (G ⋙ M) σ)).trans
      (ιCategorySimplicialObject_categorySimplicialObjectMap_app G M _))).symm

@[reassoc]
lemma categorySimplicialObjectMap_naturality
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) :
    categorySimplicialObjectCoeffMap (Functor.whiskerLeft F α) ≫ categorySimplicialObjectMap F N =
      categorySimplicialObjectMap F M ≫ categorySimplicialObjectCoeffMap α := by
  refine NatTrans.ext (funext fun ⟨⟨n⟩⟩ ↦ categorySimplicialObject_hom_ext fun σ ↦ ?_)
  simp only [NatTrans.comp_app, ιCategorySimplicialObject_coeffMap_app_assoc,
    ιCategorySimplicialObject_categorySimplicialObjectMap_app,
    ιCategorySimplicialObject_categorySimplicialObjectMap_app_assoc,
    ιCategorySimplicialObject_coeffMap_app]; rfl

end SimplicialLemmas

/-- Functoriality of `categorySimplicialObject` in `M : C ⥤ A`. -/
abbrev categorySimplicialObjectFunctor (C : Type u) [Category.{v} C]
    (A : Type u') [Category.{v'} A] [HasCoproducts.{max u v} A] :
    (C ⥤ A) ⥤ SimplicialObject A where
  obj M := categorySimplicialObject C M
  map α := categorySimplicialObjectCoeffMap α
  map_id := categorySimplicialObjectCoeffMap_id
  map_comp := categorySimplicialObjectCoeffMap_comp

/-- Identification of `categorySimplicialObject` for constant coefficients with
`(sigmaConst.obj X).obj (nerve C)`. -/
def categorySimplicialObjectConstIso (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (X : A) : categorySimplicialObject C ((Functor.const C).obj X) ≅
      (SimplicialObject.whiskering _ _ |>.obj (sigmaConst.obj X)).obj (nerve C) :=
  NatIso.ofComponents (fun Δ ↦
    { hom := Sigma.desc fun σ ↦ Sigma.ι (fun _ : (nerve C).obj Δ ↦ X) σ
      inv := Sigma.desc fun σ ↦ Sigma.ι (fun τ : ComposableArrows C Δ.unop.len ↦
        ((Functor.const C).obj X).obj (τ.obj 0)) σ
      hom_inv_id := by dsimp [categorySimplicialObject]; ext σ; simp
      inv_hom_id := by dsimp [categorySimplicialObject]; ext σ; simp })
    (fun _ ↦ by dsimp [categorySimplicialObject]; ext σ; simp [Sigma.map']; rfl)

@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_constIso_hom {C : Type u} [Category.{v} C]
    [HasCoproducts.{max u v} A] (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategorySimplicialObject ((Functor.const C).obj X) σ ≫
      (categorySimplicialObjectConstIso C X).hom.app (op ⦋n⦌) =
      Sigma.ι (fun _ : (nerve C) _⦋n⦌ ↦ X) σ := Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
lemma ι_categorySimplicialObjectConstIso_inv {C : Type u} [Category.{v} C]
    [HasCoproducts.{max u v} A] (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    Sigma.ι (fun _ : (nerve C) _⦋n⦌ ↦ X) σ ≫
      (categorySimplicialObjectConstIso C X).inv.app (op ⦋n⦌) =
      ιCategorySimplicialObject ((Functor.const C).obj X) σ := Sigma.ι_comp_desc _ _

end SimplicialObject

section ChainComplex

variable {A : Type u'} [Category.{v'} A] [Preadditive A]

/-- The category chain complex of `C` with coefficients in `M : C ⥤ A`. -/
abbrev categoryChainComplex (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (M : C ⥤ A) : ChainComplex A ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex A).obj (categorySimplicialObject C M)

/-- Functor sending `M : C ⥤ A` to `categoryChainComplex C M`. -/
abbrev categoryChainComplexFunctor (C : Type u) [Category.{v} C]
    (A : Type u') [Category.{v'} A] [Preadditive A] [HasCoproducts.{max u v} A] :
    (C ⥤ A) ⥤ ChainComplex A ℕ :=
  categorySimplicialObjectFunctor C A ⋙ AlgebraicTopology.alternatingFaceMapComplex A

/-- Comparison of `categoryChainComplex` for constant coefficients with `(nerve C).chainComplex`. -/
def categoryChainComplexConstIso (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (X : A) : categoryChainComplex C ((Functor.const C).obj X) ≅ (nerve C).chainComplex X :=
  (AlgebraicTopology.alternatingFaceMapComplex A).mapIso (categorySimplicialObjectConstIso C X)

section ChainComplexLemmas

variable {C : Type u} [Category.{v} C] [HasCoproducts.{max u v} A]

/-- `categorySimplicialObjectFunctor C A` is an additive functor, supplying additivity and
preservation of zero morphisms for `categoryChainComplexFunctor C A` and
`categoryHomologyFunctor C A n`. -/
instance : (categorySimplicialObjectFunctor C A).Additive where
  map_add {_ _} _ _ :=
    NatTrans.ext (funext fun ⟨⟨_⟩⟩ ↦ categorySimplicialObject_hom_ext fun _ ↦ by simp)

/-- Chain map induced by a natural transformation `α : M ⟶ N`. -/
abbrev categoryChainComplexCoeffMap {M N : C ⥤ A} (α : M ⟶ N) :
    categoryChainComplex C M ⟶ categoryChainComplex C N :=
  (AlgebraicTopology.alternatingFaceMapComplex A).map (categorySimplicialObjectCoeffMap α)

/-- Inclusion `M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X n` of the `σ`-summand. -/
abbrev ιCategoryChainComplex (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X n := ιCategorySimplicialObject M σ

/-- Degree-`0` summand inclusion at a vertex `c : C`. -/
def ιCategoryChainComplex₀ (M : C ⥤ A) (c : C) : M.obj c ⟶ (categoryChainComplex C M).X 0 :=
  ιCategoryChainComplex M (ComposableArrows.mk₀ c)

/-- Degree-`1` summand inclusion at an arrow `f : c₀ ⟶ c₁`. -/
def ιCategoryChainComplex₁ (M : C ⥤ A) {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    M.obj c₀ ⟶ (categoryChainComplex C M).X 1 := ιCategoryChainComplex M (ComposableArrows.mk₁ f)

/-- Degree-`2` summand inclusion at a composable pair `(f, g)`. -/
def ιCategoryChainComplex₂ (M : C ⥤ A) {c₀ c₁ c₂ : C} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) :
    M.obj c₀ ⟶ (categoryChainComplex C M).X 2 := ιCategoryChainComplex M (ComposableArrows.mk₂ f g)

@[simp]
lemma ιCategoryChainComplex_mk₀ (M : C ⥤ A) (c : C) :
    ιCategoryChainComplex M (ComposableArrows.mk₀ c) = ιCategoryChainComplex₀ M c := (rfl)

@[simp]
lemma ιCategoryChainComplex_mk₁ (M : C ⥤ A) {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    ιCategoryChainComplex M (ComposableArrows.mk₁ f) = ιCategoryChainComplex₁ M f := (rfl)

@[simp]
lemma ιCategoryChainComplex_mk₂ (M : C ⥤ A) {c₀ c₁ c₂ : C} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) :
    ιCategoryChainComplex M (ComposableArrows.mk₂ f g) = ιCategoryChainComplex₂ M f g := (rfl)

/-- Colimit cofan presenting `(categoryChainComplex C M).X n` as `∐_{σ ∈ NₙC} M(σ₀)`. -/
abbrev categoryChainComplexXCofan (M : C ⥤ A) (n : ℕ) :
    Cofan (fun σ : ComposableArrows C n ↦ M.obj (σ.obj 0)) := Cofan.mk _ (ιCategoryChainComplex M)

/-- `categoryChainComplexXCofan M n` is a coproduct colimit. -/
def isColimitCategoryChainComplexXCofan (M : C ⥤ A) (n : ℕ) :
    IsColimit (categoryChainComplexXCofan M n) := isColimitCategorySimplicialObjectXCofan M n

@[ext]
lemma categoryChainComplex_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (categoryChainComplex C M).X n ⟶ T}
    (h : ∀ σ : ComposableArrows C n,
      ιCategoryChainComplex M σ ≫ f = ιCategoryChainComplex M σ ≫ g) : f = g :=
  categorySimplicialObject_hom_ext h

lemma categoryChainComplex_hom_ext₀ {M : C ⥤ A} {T : A}
    {f g : (categoryChainComplex C M).X 0 ⟶ T}
    (h : ∀ c : C, ιCategoryChainComplex₀ M c ≫ f = ιCategoryChainComplex₀ M c ≫ g) : f = g :=
  categoryChainComplex_hom_ext fun σ ↦ by obtain ⟨c, rfl⟩ := nerveEquiv.symm.surjective σ; exact h c

lemma ιCategoryChainComplex_congr_heq {M : C ⥤ A} {n : ℕ} {σ τ : ComposableArrows C n}
    (h : σ = τ) : ιCategoryChainComplex M σ ≍ ιCategoryChainComplex M τ := by cases h; rfl

/-- Alternating-face boundary formula on the `σ`-summand of `categoryChainComplex C M`. -/
@[reassoc]
lemma ιCategoryChainComplex_d (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplex C M).d (n + 1) n =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
        ιCategoryChainComplex M ((nerve C).δ 0 σ) +
        ∑ j : Fin (n + 1),
          (-1) ^ (j.val + 1) • ιCategoryChainComplex M ((nerve C).δ j.succ σ) := by
  dsimp only [categoryChainComplex]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.comp_sum, Fin.sum_univ_succ]
  simp only [Preadditive.comp_zsmul, ιCategoryChainComplex, Fin.val_zero, pow_zero, one_smul,
    ιCategorySimplicialObject_δ_zero, Fin.val_succ, ιCategorySimplicialObject_δ_succ]; rfl

/-- Degree-`1` boundary on an arrow `f : c₀ ⟶ c₁`. -/
@[reassoc]
lemma ιCategoryChainComplex₁_d_one_zero (M : C ⥤ A) {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    ιCategoryChainComplex₁ M f ≫ (categoryChainComplex C M).d 1 0 =
      M.map f ≫ ιCategoryChainComplex₀ M c₁ - ιCategoryChainComplex₀ M c₀ := by
  refine (ιCategoryChainComplex_d M (ComposableArrows.mk₁ f)).trans ?_
  have t₀ : (M.map ((ComposableArrows.mk₁ f).map (homOfLE (Fin.zero_le (1 : Fin 2)))) ≫
      ιCategoryChainComplex M ((nerve C).δ 0 (ComposableArrows.mk₁ f)) :
        M.obj c₀ ⟶ (categoryChainComplex C M).X 0) = M.map f ≫ ιCategoryChainComplex₀ M c₁ :=
    congrArg (M.map f ≫ ·) (eq_of_heq (ιCategoryChainComplex_congr_heq (ComposableArrows.ext₀ rfl)))
  have t₁ : (∑ j : Fin 1, (-1 : ℤ) ^ (j.val + 1) •
      ιCategoryChainComplex M ((nerve C).δ j.succ (ComposableArrows.mk₁ f)) :
        M.obj c₀ ⟶ (categoryChainComplex C M).X 0) = -ιCategoryChainComplex₀ M c₀ :=
    (Fin.sum_univ_one _).trans ((neg_one_smul _ _).trans
      (congrArg (- ·) (eq_of_heq (ιCategoryChainComplex_congr_heq (ComposableArrows.ext₀ rfl)))))
  exact (congrArg₂ (· + ·) t₀ t₁).trans (sub_eq_add_neg _ _).symm

/-- Degree-`2` boundary on a composable pair `(f, g)`. -/
@[reassoc]
lemma ιCategoryChainComplex₂_d_two_one (M : C ⥤ A) {c₀ c₁ c₂ : C} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) :
    ιCategoryChainComplex₂ M f g ≫ (categoryChainComplex C M).d 2 1 =
      M.map f ≫ ιCategoryChainComplex₁ M g - ιCategoryChainComplex₁ M (f ≫ g) +
        ιCategoryChainComplex₁ M f := by
  refine ((ιCategoryChainComplex_d M (ComposableArrows.mk₂ f g)).trans ?_).trans
    (by abel : M.map f ≫ ιCategoryChainComplex₁ M g +
      (-ιCategoryChainComplex₁ M (f ≫ g) + ιCategoryChainComplex₁ M f) = _)
  have t₀ : (M.map ((ComposableArrows.mk₂ f g).map (homOfLE (Fin.zero_le (1 : Fin 3)))) ≫
      ιCategoryChainComplex M ((nerve C).δ 0 (ComposableArrows.mk₂ f g)) :
        M.obj c₀ ⟶ (categoryChainComplex C M).X 1) = M.map f ≫ ιCategoryChainComplex₁ M g :=
    congrArg (M.map f ≫ ·)
      (eq_of_heq (ιCategoryChainComplex_congr_heq (CategoryTheory.nerve.δ₀_mk₂_eq f g)))
  have t₁ : ((-1 : ℤ) ^ ((0 : Fin 2).val + 1) •
      ιCategoryChainComplex M ((nerve C).δ (0 : Fin 2).succ (ComposableArrows.mk₂ f g)) :
        M.obj c₀ ⟶ (categoryChainComplex C M).X 1) = -ιCategoryChainComplex₁ M (f ≫ g) :=
    (neg_one_smul _ _).trans (congrArg (- ·)
      (eq_of_heq (ιCategoryChainComplex_congr_heq (CategoryTheory.nerve.δ₁_mk₂_eq f g))))
  have t₂ : ((-1 : ℤ) ^ ((1 : Fin 2).val + 1) •
      ιCategoryChainComplex M ((nerve C).δ (1 : Fin 2).succ (ComposableArrows.mk₂ f g)) :
        M.obj c₀ ⟶ (categoryChainComplex C M).X 1) = ιCategoryChainComplex₁ M f :=
    (one_smul _ _).trans
      (eq_of_heq (ιCategoryChainComplex_congr_heq (CategoryTheory.nerve.δ₂_mk₂_eq f g)))
  exact congrArg₂ (· + ·) t₀ ((Fin.sum_univ_two _).trans (congrArg₂ (· + ·) t₁ t₂))

@[reassoc]
lemma ιCategoryChainComplex_categoryChainComplexCoeffMap_f {M N : C ⥤ A} (α : M ⟶ N) {n : ℕ}
    (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplexCoeffMap α).f n =
      α.app (σ.obj 0) ≫ ιCategoryChainComplex N σ :=
  ιCategorySimplicialObject_coeffMap_app α σ

@[reassoc]
lemma ιCategoryChainComplex₀_categoryChainComplexCoeffMap_f {M N : C ⥤ A} (α : M ⟶ N) (c : C) :
    ιCategoryChainComplex₀ M c ≫ (categoryChainComplexCoeffMap α).f 0 =
      α.app c ≫ ιCategoryChainComplex₀ N c :=
  ιCategorySimplicialObject_coeffMap_app α (ComposableArrows.mk₀ c)

/-- Chain map `categoryChainComplex C (F ⋙ M) ⟶ categoryChainComplex D M` along `F : C ⥤ D`. -/
def categoryChainComplexMap {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) :
    categoryChainComplex C (F ⋙ M) ⟶ categoryChainComplex D M :=
  (AlgebraicTopology.alternatingFaceMapComplex A).map (categorySimplicialObjectMap F M)

@[reassoc (attr := simp)]
lemma ιCategoryChainComplex_categoryChainComplexMap_f
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex (F ⋙ M) σ ≫ (categoryChainComplexMap F M).f n =
      ιCategoryChainComplex M ((F.mapComposableArrows n).obj σ) :=
  ιCategorySimplicialObject_categorySimplicialObjectMap_app F M σ

@[reassoc (attr := simp)]
lemma ιCategoryChainComplex₀_categoryChainComplexMap_f
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) (c : C) :
    ιCategoryChainComplex₀ (F ⋙ M) c ≫ (categoryChainComplexMap F M).f 0 =
      ιCategoryChainComplex₀ M (F.obj c) :=
  (ιCategoryChainComplex_categoryChainComplexMap_f F M (ComposableArrows.mk₀ c)).trans
    (eq_of_heq (ιCategoryChainComplex_congr_heq (ComposableArrows.ext₀ rfl)))

@[simp]
lemma categoryChainComplexMap_id (M : C ⥤ A) :
    categoryChainComplexMap (𝟭 C) M = 𝟙 (categoryChainComplex C M) :=
  (congrArg (AlgebraicTopology.alternatingFaceMapComplex A).map
    (categorySimplicialObjectMap_id M)).trans
    ((AlgebraicTopology.alternatingFaceMapComplex A).map_id _)

@[reassoc]
lemma categoryChainComplexMap_comp
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₃ v₃} A]
    (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    categoryChainComplexMap (F ⋙ G) M =
      categoryChainComplexMap F (G ⋙ M) ≫ categoryChainComplexMap G M := by
  rw [categoryChainComplexMap, categorySimplicialObjectMap_comp, Functor.map_comp]; rfl

@[reassoc]
lemma categoryChainComplexMap_naturality
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) :
    categoryChainComplexCoeffMap (Functor.whiskerLeft F α) ≫ categoryChainComplexMap F N =
      categoryChainComplexMap F M ≫ categoryChainComplexCoeffMap α := by
  simp only [categoryChainComplexCoeffMap, categoryChainComplexMap, ← Functor.map_comp,
    categorySimplicialObjectMap_naturality]

@[reassoc (attr := simp)]
lemma ιCategoryChainComplex_constIso_hom (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex ((Functor.const C).obj X) σ ≫
      (categoryChainComplexConstIso C X).hom.f n = (nerve C).ιChainComplex σ := by
  simp [categoryChainComplexConstIso, ιCategoryChainComplex, SSet.ιChainComplex]

@[reassoc (attr := simp)]
lemma ιChainComplex_constIso_inv (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    (nerve C).ιChainComplex σ ≫ (categoryChainComplexConstIso C X).inv.f n =
      ιCategoryChainComplex ((Functor.const C).obj X) σ := by
  simp [categoryChainComplexConstIso, ιCategoryChainComplex, SSet.ιChainComplex]

@[reassoc]
lemma categoryChainComplexMap_constIso_hom {D : Type u} [Category.{v} D]
    (F : C ⥤ D) (X : A) :
    categoryChainComplexMap F ((Functor.const D).obj X) ≫
      (categoryChainComplexConstIso D X).hom =
      (categoryChainComplexConstIso C X).hom ≫ SSet.chainComplexMap (nerveMap F) X := by
  refine HomologicalComplex.Hom.ext (funext fun n ↦ categoryChainComplex_hom_ext fun σ ↦ ?_)
  simp only [HomologicalComplex.comp_f, ιCategoryChainComplex_categoryChainComplexMap_f_assoc]
  exact (ιCategoryChainComplex_constIso_hom X ((F.mapComposableArrows n).obj σ)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (SSet.chainComplexMap (nerveMap F) X).f n)
        (ιCategoryChainComplex_constIso_hom X σ)).trans
        (SSet.ι_chainComplexMap_f (nerve C) (nerve D) (nerveMap F) X σ))).symm

/-- For an empty category `C`, `categoryChainComplex C M` is a zero chain complex. -/
lemma isZero_categoryChainComplex_of_isEmpty [IsEmpty C] (M : C ⥤ A) :
    IsZero (categoryChainComplex C M) := by
  rw [IsZero.iff_id_eq_zero]
  exact HomologicalComplex.Hom.ext (funext fun _ ↦ categoryChainComplex_hom_ext fun σ ↦
    (IsEmpty.false (σ.obj 0)).elim)

end ChainComplexLemmas

end ChainComplex

section Homology

variable {A : Type u'} [Category.{v'} A] [Preadditive A] [CategoryWithHomology A]

/-- Degree-`n` category homology `Hₙ(C, M)` of `C` with coefficients in `M : C ⥤ A`. -/
abbrev categoryHomology (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (M : C ⥤ A) (n : ℕ) : A :=
  (categoryChainComplex C M).homology n

/-- Functor `(C ⥤ A) ⥤ A` sending `M` to `categoryHomology C M n`. -/
abbrev categoryHomologyFunctor (C : Type u) [Category.{v} C]
    (A : Type u') [Category.{v'} A] [Preadditive A] [HasCoproducts.{max u v} A]
    [CategoryWithHomology A] (n : ℕ) : (C ⥤ A) ⥤ A :=
  categoryChainComplexFunctor C A ⋙ HomologicalComplex.homologyFunctor A _ n

/-- Comparison of `categoryHomology` for constant coefficients with `(nerve C).homology X n`. -/
def categoryHomologyConstIso (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (X : A) (n : ℕ) : categoryHomology C ((Functor.const C).obj X) n ≅ (nerve C).homology X n :=
  (HomologicalComplex.homologyFunctor A _ n).mapIso (categoryChainComplexConstIso C X)

section HomologyLemmas

variable {C : Type u} [Category.{v} C] [HasCoproducts.{max u v} A]

/-- Homology map `Hₙ(C, M) ⟶ Hₙ(C, N)` induced by `α : M ⟶ N`. -/
abbrev categoryHomologyCoeffMap {M N : C ⥤ A} (α : M ⟶ N) (n : ℕ) :
    categoryHomology C M n ⟶ categoryHomology C N n :=
  HomologicalComplex.homologyMap (categoryChainComplexCoeffMap α) n

@[simp]
lemma categoryHomologyCoeffMap_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyCoeffMap (𝟙 M) n = 𝟙 (categoryHomology C M n) := by
  simp [categoryHomologyCoeffMap, categoryChainComplexCoeffMap]

@[reassoc]
lemma categoryHomologyCoeffMap_comp {L M N : C ⥤ A} (α : L ⟶ M) (β : M ⟶ N) (n : ℕ) :
    categoryHomologyCoeffMap (α ≫ β) n =
      categoryHomologyCoeffMap α n ≫ categoryHomologyCoeffMap β n := by
  dsimp only [categoryHomologyCoeffMap, categoryChainComplexCoeffMap]
  rw [categorySimplicialObjectCoeffMap_comp, Functor.map_comp, HomologicalComplex.homologyMap_comp]

/-- Homology map `Hₙ(C, F ⋙ M) ⟶ Hₙ(D, M)` induced by `F : C ⥤ D`. -/
def categoryHomologyMap {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) (n : ℕ) :
    categoryHomology C (F ⋙ M) n ⟶ categoryHomology D M n :=
  HomologicalComplex.homologyMap (categoryChainComplexMap F M) n

@[simp]
lemma categoryHomologyMap_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyMap (𝟭 C) M n = 𝟙 (categoryHomology C M n) :=
  (congrArg (HomologicalComplex.homologyMap · n) (categoryChainComplexMap_id M)).trans
    (HomologicalComplex.homologyMap_id _ n)

@[reassoc]
lemma categoryHomologyMap_comp
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₃ v₃} A]
    (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) (n : ℕ) :
    categoryHomologyMap (F ⋙ G) M n =
      categoryHomologyMap F (G ⋙ M) n ≫ categoryHomologyMap G M n := by
  rw [categoryHomologyMap, categoryChainComplexMap_comp, HomologicalComplex.homologyMap_comp]; rfl

@[reassoc]
lemma categoryHomologyMap_naturality
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) (n : ℕ) :
    categoryHomologyCoeffMap (Functor.whiskerLeft F α) n ≫ categoryHomologyMap F N n =
      categoryHomologyMap F M n ≫ categoryHomologyCoeffMap α n := by
  simp only [categoryHomologyCoeffMap, categoryHomologyMap, ← HomologicalComplex.homologyMap_comp,
    categoryChainComplexMap_naturality]

@[reassoc]
lemma categoryHomologyMap_constIso_hom {D : Type u} [Category.{v} D]
    (F : C ⥤ D) (X : A) (n : ℕ) :
    categoryHomologyMap F ((Functor.const D).obj X) n ≫
      (categoryHomologyConstIso D X n).hom =
      (categoryHomologyConstIso C X n).hom ≫ SSet.homologyMap (nerveMap F) X n := by
  dsimp only [categoryHomologyMap, categoryHomologyConstIso, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor, SSet.homologyMap]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    categoryChainComplexMap_constIso_hom]

/-- For an empty category `C`, `categoryHomology C M n` is zero in every degree `n`. -/
lemma isZero_categoryHomology_of_isEmpty [IsEmpty C] (M : C ⥤ A) (n : ℕ) :
    IsZero (categoryHomology C M n) := by
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.homologyMap_id,
    (isZero_categoryChainComplex_of_isEmpty M).eq_of_src (𝟙 _) 0,
    HomologicalComplex.homologyMap_zero]

end HomologyLemmas

end Homology

section LongExactSequence

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [Abelian A] [HasCoproducts.{max u v} A] [AB4OfSize.{max u v} A]

/-- A short exact sequence of coefficient functors `C ⥤ A` induces a short exact sequence of
category chain complexes when `AB4OfSize.{max u v} A` holds. -/
lemma shortExact_map_categoryChainComplexFunctor {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) :
    (S.map (categoryChainComplexFunctor C A)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  let J := Discrete (ComposableArrows C n)
  let W : (C ⥤ A) ⥤ (J ⥤ A) :=
    (Functor.whiskeringLeft J C A).obj (Discrete.functor fun σ ↦ σ.obj 0)
  let S₀ : ShortComplex (J ⥤ A) := S.map W
  have hS₀ : S₀.ShortExact := hS.map_of_exact W
  let cocone (M : C ⥤ A) : Cocone (W.obj M) :=
    ⟨(categoryChainComplex C M).X n, Discrete.natTrans fun j ↦ ιCategoryChainComplex M j.as⟩
  let isColim (M : C ⥤ A) : IsColimit (cocone M) :=
    { desc s := (isColimitCategoryChainComplexXCofan M n).desc (Cofan.mk s.pt fun σ ↦ s.ι.app ⟨σ⟩)
      fac s j := (isColimitCategoryChainComplexXCofan M n).fac
        (Cofan.mk s.pt fun σ ↦ s.ι.app ⟨σ⟩) ⟨j.as⟩
      uniq s m hm := (isColimitCategoryChainComplexXCofan M n).uniq
        (Cofan.mk s.pt fun σ ↦ s.ι.app ⟨σ⟩) m fun ⟨σ⟩ ↦ hm ⟨σ⟩ }
  have hf (j : J) : (cocone S.X₁).ι.app j ≫ (categoryChainComplexCoeffMap S.f).f n =
      S₀.f.app j ≫ (cocone S.X₂).ι.app j :=
    ιCategoryChainComplex_categoryChainComplexCoeffMap_f S.f j.as
  have hg (j : J) : (cocone S.X₂).ι.app j ≫ (categoryChainComplexCoeffMap S.g).f n =
      S₀.g.app j ≫ (cocone S.X₃).ι.app j :=
    ιCategoryChainComplex_categoryChainComplexCoeffMap_f S.g j.as
  have : Mono S₀.f := hS₀.mono_f
  have : Epi S₀.g := hS₀.epi_g
  have (j : J) : Epi (S₀.g.app j) := inferInstance
  exact { exact := colim.exact_mapShortComplex hS₀.exact
            (isColim S.X₁) (isColim S.X₂) (isColim S.X₃) _ _ hf hg
          mono_f := colim.map_mono' S₀.f (isColim S.X₁) (isColim S.X₂) _ hf
          epi_g := colim.map_epi' S₀.g (cocone S.X₂) (isColim S.X₃) _ hg }

/-- Connecting homomorphism `Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁)` (for `m + 1 = n`) of a short exact
sequence `S` of coefficient functors. -/
def categoryHomologyδ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) : categoryHomology C S.X₃ n ⟶ categoryHomology C S.X₁ m :=
  (shortExact_map_categoryChainComplexFunctor hS).δ n m (by simpa)

@[reassoc (attr := simp)]
lemma comp_categoryHomologyδ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    categoryHomologyCoeffMap S.g n ≫ categoryHomologyδ hS n m h = 0 :=
  (shortExact_map_categoryChainComplexFunctor hS).comp_δ n m (by simpa)

@[reassoc (attr := simp)]
lemma categoryHomologyδ_comp {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    categoryHomologyδ hS n m h ≫ categoryHomologyCoeffMap S.f m = 0 :=
  (shortExact_map_categoryChainComplexFunctor hS).δ_comp n m (by simpa)

/-- Exactness of `Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁) ⟶ Hₘ(C, S.X₂)` for `m + 1 = n`. -/
lemma categoryHomology_exact₁ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (categoryHomologyδ_comp hS n m h)).Exact :=
  (shortExact_map_categoryChainComplexFunctor hS).homology_exact₁ n m (by simpa)

/-- Exactness of `Hₙ(C, S.X₁) ⟶ Hₙ(C, S.X₂) ⟶ Hₙ(C, S.X₃)`. -/
lemma categoryHomology_exact₂ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    (S.map (categoryHomologyFunctor C A n)).Exact :=
  (shortExact_map_categoryChainComplexFunctor hS).homology_exact₂ n

/-- Exactness of `Hₙ(C, S.X₂) ⟶ Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁)` for `m + 1 = n`. -/
lemma categoryHomology_exact₃ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (comp_categoryHomologyδ hS n m h)).Exact :=
  (shortExact_map_categoryChainComplexFunctor hS).homology_exact₃ n m (by simpa)

@[reassoc]
lemma categoryHomologyδ_naturality_coeff {S₁ S₂ : ShortComplex (C ⥤ A)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (n m : ℕ) (h : m + 1 = n := by lia) :
    categoryHomologyδ hS₁ n m h ≫ categoryHomologyCoeffMap φ.τ₁ m =
      categoryHomologyCoeffMap φ.τ₃ n ≫ categoryHomologyδ hS₂ n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((categoryChainComplexFunctor C A).mapShortComplex.map φ)
    (shortExact_map_categoryChainComplexFunctor hS₁)
    (shortExact_map_categoryChainComplexFunctor hS₂) n m (by simpa)

@[reassoc]
lemma categoryHomologyδ_naturality_functor
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A] [AB4OfSize.{max u₂ v₂} A]
    (F : C ⥤ D) {S : ShortComplex (D ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    categoryHomologyδ (hS.map_of_exact ((Functor.whiskeringLeft C D A).obj F)) n m h ≫
      categoryHomologyMap F S.X₁ m =
      categoryHomologyMap F S.X₃ n ≫ categoryHomologyδ hS n m h := by
  let Φ : (S.map ((Functor.whiskeringLeft C D A).obj F)).map (categoryChainComplexFunctor C A) ⟶
      S.map (categoryChainComplexFunctor D A) :=
    { τ₁ := categoryChainComplexMap F S.X₁, τ₂ := categoryChainComplexMap F S.X₂
      τ₃ := categoryChainComplexMap F S.X₃
      comm₁₂ := (categoryChainComplexMap_naturality F S.f).symm
      comm₂₃ := (categoryChainComplexMap_naturality F S.g).symm }
  exact HomologicalComplex.HomologySequence.δ_naturality Φ
    (shortExact_map_categoryChainComplexFunctor
      (hS.map_of_exact ((Functor.whiskeringLeft C D A).obj F)))
    (shortExact_map_categoryChainComplexFunctor hS) n m (by simpa)

end LongExactSequence

end TauCeti
