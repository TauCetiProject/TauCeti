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

Let `C` be a category and `M : C ⥤ A` a functor into a category `A` with coproducts indexed by
`Type (max u v)`. The nerve-coefficient simplicial object `TauCeti.categorySimplicialObject C M`
has degree-`n` object

`∐_{σ = (c₀ ⟶ ⋯ ⟶ cₙ) ∈ ComposableArrows C n} M(c₀)`.

For any morphism `φ : ⦋m⦌ ⟶ ⦋n⦌` in `SimplexCategory`, the induced simplicial operator sends the
`σ`-summand `M(c₀)` to the `((nerve C).map φ.op σ)`-summand via `M` applied to the arrow of `σ`
from `0` to `φ(0)`. Specialised to the elementary operators:
* the zeroth face `δ 0` applies `M(f₁) : M(c₀) ⟶ M(c₁)` and drops `c₀`;
* the interior faces `δ (j + 1)` (`0 ≤ j < n`) compose consecutive arrows without changing `M(c₀)`;
* the last face deletes the final vertex without changing `M(c₀)`;
* the degeneracies insert identity arrows without changing `M(c₀)`.

When `A` is preadditive, `TauCeti.categoryChainComplex C M` is the alternating face map complex of
`categorySimplicialObject C M`, and when `A` has homology, `TauCeti.categoryHomology C M n` is its
`n`-th homology object. The construction is functorial both in natural transformations `M ⟶ N` and
in functors `F : C ⥤ D` (giving `Hₙ(C, F ⋙ M) ⟶ Hₙ(D, M)`), recovers the ordinary simplicial chain
complex `(nerve C).chainComplex X` for constant coefficients, and sends short exact sequences of
coefficient functors into an `AB4` abelian category (such as `ModuleCat R`) to long exact sequences
in homology.

## Main definitions

* `TauCeti.categorySimplicialObject`: the simplicial object `n ↦ ∐_{σ ∈ NₙC} M(σ₀)`.
* `TauCeti.categoryChainComplex`: the alternating face map chain complex of `(C, M)`.
* `TauCeti.categoryHomology`: degree-`n` homology `Hₙ(C, M)` of `C` with coefficients in `M`.
* `TauCeti.categoryChainComplexMap`, `TauCeti.categoryHomologyMap`: functorial maps along
  `F : C ⥤ D`.
* `TauCeti.categoryChainComplexConstIso`, `TauCeti.categoryHomologyConstIso`: comparison with
  `(nerve C).chainComplex X` and `(nerve C).homology X n` for constant coefficients `X`.
* `TauCeti.categoryHomologyδ`: connecting morphism of a short exact sequence of coefficient
  diagrams.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Mathematics 341 (1973), §1, p. 91.
* C. A. Weibel, *The K-book: An introduction to algebraic K-theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter IV, §3.5, p. IV.28.
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
  have hid : homOfLE (Fin.zero_le (0 : Fin (m + 1))) = 𝟙 0 := Subsingleton.elim _ _
  rw [hid, σ.map_id, M.map_id]

private lemma ι_comp_desc_desc {I : Type*} {J : Type*} {P : I → A} {Q : J → A}
    [HasCoproduct P] [HasCoproduct Q] {T : A} (i : I) (j : I → J)
    (u : ∀ a, P a ⟶ Q (j a)) (k : ∀ b, Q b ⟶ T) :
    Sigma.ι P i ≫
      (Sigma.desc (fun a ↦ u a ≫ Sigma.ι Q (j a)) ≫ Sigma.desc k) =
      u i ≫ k (j i) := by
  rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc, Sigma.ι_comp_desc]

private lemma ι_comp_desc_id_desc {I : Type*} {J : Type*} {Q : J → A} (j : I → J)
    [HasCoproduct (fun a : I ↦ Q (j a))] [HasCoproduct Q] {T : A}
    (i : I) (k : ∀ b, Q b ⟶ T) :
    Sigma.ι (fun a : I ↦ Q (j a)) i ≫
      (Sigma.desc (fun a : I ↦ Sigma.ι Q (j a)) ≫ Sigma.desc k) =
      k (j i) := by
  rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]

/-- The simplicial object associated to a category `C` and a coefficient functor `M : C ⥤ A`, with
degree-`n` object `∐_{σ : ComposableArrows C n} M.obj (σ.obj 0)`. -/
def categorySimplicialObject (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (M : C ⥤ A) : SimplicialObject A where
  obj Δ := ∐ fun σ : ComposableArrows C Δ.unop.len ↦ M.obj (σ.obj 0)
  map {Δ₁ Δ₂} f := Sigma.desc fun σ ↦
    M.map (σ.map (homOfLE (Fin.zero_le (f.unop.toOrderHom (0 : Fin (Δ₂.unop.len + 1)))))) ≫
      Sigma.ι (fun τ : ComposableArrows C Δ₂.unop.len ↦ M.obj (τ.obj 0))
        (σ.whiskerLeft f.unop.toOrderHom.monotone.functor)
  map_id Δ := by
    ext σ
    refine (Sigma.ι_comp_desc _ σ).trans ?_
    refine ((congrArg (· ≫ _) (eq_of_heq (map_zero_le_heq_id M σ rfl))).trans ?_)
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  map_comp {Δ₁ Δ₂ Δ₃} f g := by
    ext σ
    have hL := Sigma.ι_comp_desc
      (fun σ : ComposableArrows C Δ₁.unop.len ↦
        M.map (σ.map (homOfLE (Fin.zero_le
          ((f ≫ g).unop.toOrderHom (0 : Fin (Δ₃.unop.len + 1)))))) ≫
          Sigma.ι (fun τ : ComposableArrows C Δ₃.unop.len ↦ M.obj (τ.obj 0))
            (σ.whiskerLeft (f ≫ g).unop.toOrderHom.monotone.functor)) σ
    have hR := ι_comp_desc_desc σ
      (fun τ : ComposableArrows C Δ₁.unop.len ↦ τ.whiskerLeft f.unop.toOrderHom.monotone.functor)
      (fun τ ↦ M.map (τ.map (homOfLE (Fin.zero_le
        (f.unop.toOrderHom (0 : Fin (Δ₂.unop.len + 1)))))))
      (fun ρ ↦ M.map (ρ.map (homOfLE (Fin.zero_le
        (g.unop.toOrderHom (0 : Fin (Δ₃.unop.len + 1)))))) ≫
        Sigma.ι (fun υ : ComposableArrows C Δ₃.unop.len ↦ M.obj (υ.obj 0))
          (ρ.whiskerLeft g.unop.toOrderHom.monotone.functor))
    have hcomp :
        σ.map (homOfLE (Fin.zero_le (f.unop.toOrderHom (0 : Fin (Δ₂.unop.len + 1))))) ≫
          (σ.whiskerLeft f.unop.toOrderHom.monotone.functor).map
            (homOfLE (Fin.zero_le (g.unop.toOrderHom (0 : Fin (Δ₃.unop.len + 1))))) =
          σ.map (homOfLE (Fin.zero_le
            ((f ≫ g).unop.toOrderHom (0 : Fin (Δ₃.unop.len + 1))))) :=
      (σ.map_comp _ _).symm.trans (congrArg σ.map (Subsingleton.elim _ _))
    refine hL.trans (Eq.symm (hR.trans ?_))
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) ((M.map_comp _ _).symm.trans (congrArg M.map hcomp)))

section SimplicialLemmas

variable {C : Type u} [Category.{v} C] [HasCoproducts.{max u v} A]

/-- Inclusion `M.obj (σ.obj 0) ⟶ (categorySimplicialObject C M) _⦋n⦌` of the summand indexed by an
`n`-simplex `σ` of `nerve C`. -/
def ιCategorySimplicialObject (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categorySimplicialObject C M) _⦋n⦌ :=
  Sigma.ι (fun τ : ComposableArrows C n ↦ M.obj (τ.obj 0)) σ

/-- Colimit cofan presenting `(categorySimplicialObject C M) _⦋n⦌` as `∐_{σ ∈ NₙC} M(σ₀)`. -/
abbrev categorySimplicialObjectXCofan (M : C ⥤ A) (n : ℕ) :
    Cofan (fun σ : ComposableArrows C n ↦ M.obj (σ.obj 0)) :=
  Cofan.mk _ (ιCategorySimplicialObject M)

/-- The cofan `categorySimplicialObjectXCofan M n` is a coproduct colimit. -/
def isColimitCategorySimplicialObjectXCofan (M : C ⥤ A) (n : ℕ) :
    IsColimit (categorySimplicialObjectXCofan M n) :=
  coproductIsCoproduct _

/-- Morphisms out of `(categorySimplicialObject C M) _⦋n⦌` are determined on each nerve simplex. -/
@[ext]
lemma categorySimplicialObject_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (categorySimplicialObject C M) _⦋n⦌ ⟶ T}
    (h : ∀ σ : ComposableArrows C n,
      ιCategorySimplicialObject M σ ≫ f = ιCategorySimplicialObject M σ ≫ g) :
    f = g :=
  (isColimitCategorySimplicialObjectXCofan M n).hom_ext fun ⟨σ⟩ ↦ h σ

/-- Action of a simplicial operator `φ : ⦋m⦌ ⟶ ⦋n⦌` on the `σ`-summand of
`categorySimplicialObject C M`. -/
@[reassoc]
lemma ιCategorySimplicialObject_map (M : C ⥤ A) {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows C n) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObject C M).map φ.op =
      M.map (σ.map (homOfLE (Fin.zero_le (φ.toOrderHom 0)))) ≫
        ιCategorySimplicialObject M ((nerve C).map φ.op σ) := by
  dsimp only [categorySimplicialObject, ιCategorySimplicialObject]
  exact Sigma.ι_comp_desc _ _

/-- The zeroth face `δ 0` applies `M` to the first arrow `c₀ ⟶ c₁` of `σ` and lands in the
`((nerve C).δ 0 σ)`-summand. -/
@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_δ_zero (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObject C M).δ 0 =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
        ιCategorySimplicialObject M ((nerve C).δ 0 σ) := by
  rw [SimplicialObject.δ, ιCategorySimplicialObject_map]
  rfl

/-- Positive faces `δ j.succ` leave the initial vertex `c₀` fixed and act as the identity on
`M(c₀)` into the `((nerve C).δ j.succ σ)`-summand. -/
@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_δ_succ (M : C ⥤ A) {n : ℕ} (j : Fin (n + 1))
    (σ : ComposableArrows C (n + 1)) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObject C M).δ j.succ =
      ιCategorySimplicialObject M ((nerve C).δ j.succ σ) := by
  refine (ιCategorySimplicialObject_map M (SimplexCategory.δ j.succ) σ).trans ?_
  exact (congrArg (· ≫ _) (eq_of_heq (map_zero_le_heq_id M σ rfl))).trans (Category.id_comp _)

/-- Degeneracy maps `σ i` fix the initial vertex `c₀` and send the `τ`-summand directly to the
`((nerve C).σ i τ)`-summand. -/
@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_σ (M : C ⥤ A) {n : ℕ} (i : Fin (n + 1))
    (τ : ComposableArrows C n) :
    ιCategorySimplicialObject M τ ≫ (categorySimplicialObject C M).σ i =
      ιCategorySimplicialObject M ((nerve C).σ i τ) := by
  refine (ιCategorySimplicialObject_map M (SimplexCategory.σ i) τ).trans ?_
  exact (congrArg (· ≫ _) (eq_of_heq (map_zero_le_heq_id M τ rfl))).trans (Category.id_comp _)

/-- Morphism of simplicial objects induced by a natural transformation `α : M ⟶ N` of coefficient
functors. -/
def categorySimplicialObjectCoeffMap {M N : C ⥤ A} (α : M ⟶ N) :
    categorySimplicialObject C M ⟶ categorySimplicialObject C N where
  app Δ := Sigma.desc fun σ ↦
    α.app (σ.obj 0) ≫ Sigma.ι (fun τ : ComposableArrows C Δ.unop.len ↦ N.obj (τ.obj 0)) σ
  naturality {Δ₁ Δ₂} f := by
    dsimp only [categorySimplicialObject]
    ext σ
    have hL := ι_comp_desc_desc σ
      (fun τ : ComposableArrows C Δ₁.unop.len ↦ τ.whiskerLeft f.unop.toOrderHom.monotone.functor)
      (fun τ ↦ M.map (τ.map (homOfLE (Fin.zero_le
        (f.unop.toOrderHom (0 : Fin (Δ₂.unop.len + 1)))))))
      (fun ρ ↦ α.app (ρ.obj 0) ≫
        Sigma.ι (fun υ : ComposableArrows C Δ₂.unop.len ↦ N.obj (υ.obj 0)) ρ)
    have hR := ι_comp_desc_desc σ id (fun τ ↦ α.app (τ.obj 0))
      (fun τ ↦ N.map (τ.map (homOfLE (Fin.zero_le
        (f.unop.toOrderHom (0 : Fin (Δ₂.unop.len + 1)))))) ≫
        Sigma.ι (fun υ : ComposableArrows C Δ₂.unop.len ↦ N.obj (υ.obj 0))
          (τ.whiskerLeft f.unop.toOrderHom.monotone.functor))
    refine hL.trans (Eq.symm (hR.trans ?_))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (α.naturality _).symm).trans (Category.assoc _ _ _))

/-- A natural transformation `α : M ⟶ N` acts on the `σ`-summand by `α.app (σ.obj 0)`. -/
@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_coeffMap_app {M N : C ⥤ A} (α : M ⟶ N) {n : ℕ}
    (σ : ComposableArrows C n) :
    ιCategorySimplicialObject M σ ≫ (categorySimplicialObjectCoeffMap α).app (op ⦋n⦌) =
      α.app (σ.obj 0) ≫ ιCategorySimplicialObject N σ := by
  dsimp only [categorySimplicialObject, categorySimplicialObjectCoeffMap,
    ιCategorySimplicialObject]
  exact Sigma.ι_comp_desc _ _

@[simp]
lemma categorySimplicialObjectCoeffMap_id (M : C ⥤ A) :
    categorySimplicialObjectCoeffMap (𝟙 M) = 𝟙 (categorySimplicialObject C M) := by
  refine NatTrans.ext (funext fun ⟨⟨n⟩⟩ ↦ categorySimplicialObject_hom_ext fun σ ↦ ?_)
  simp

@[reassoc]
lemma categorySimplicialObjectCoeffMap_comp {L M N : C ⥤ A} (α : L ⟶ M) (β : M ⟶ N) :
    categorySimplicialObjectCoeffMap (α ≫ β) =
      categorySimplicialObjectCoeffMap α ≫ categorySimplicialObjectCoeffMap β := by
  refine NatTrans.ext (funext fun ⟨⟨n⟩⟩ ↦ categorySimplicialObject_hom_ext fun σ ↦ ?_)
  simp

/-- Morphism of simplicial objects induced by a functor `F : C ⥤ D` and coefficients `M : D ⥤ A`.
-/
def categorySimplicialObjectMap {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) :
    categorySimplicialObject C (F ⋙ M) ⟶ categorySimplicialObject D M where
  app Δ := Sigma.desc fun σ ↦
    Sigma.ι (fun τ : ComposableArrows D Δ.unop.len ↦ M.obj (τ.obj 0))
      ((F.mapComposableArrows Δ.unop.len).obj σ)
  naturality {Δ₁ Δ₂} f := by
    dsimp only [categorySimplicialObject]
    ext σ
    have hL := ι_comp_desc_desc
      (Q := fun ρ : ComposableArrows C Δ₂.unop.len ↦ (F ⋙ M).obj (ρ.obj 0)) σ
      (fun τ : ComposableArrows C Δ₁.unop.len ↦ τ.whiskerLeft f.unop.toOrderHom.monotone.functor)
      (fun τ ↦ (F ⋙ M).map (τ.map (homOfLE (Fin.zero_le
        (f.unop.toOrderHom (0 : Fin (Δ₂.unop.len + 1)))))))
      (fun ρ ↦ Sigma.ι (fun υ : ComposableArrows D Δ₂.unop.len ↦ M.obj (υ.obj 0))
        ((F.mapComposableArrows Δ₂.unop.len).obj ρ))
    have hR := ι_comp_desc_id_desc
      (fun τ : ComposableArrows C Δ₁.unop.len ↦ (F.mapComposableArrows Δ₁.unop.len).obj τ) σ
      (fun ρ ↦ M.map (ρ.map (homOfLE (Fin.zero_le
        (f.unop.toOrderHom (0 : Fin (Δ₂.unop.len + 1)))))) ≫
        Sigma.ι (fun υ : ComposableArrows D Δ₂.unop.len ↦ M.obj (υ.obj 0))
          (ρ.whiskerLeft f.unop.toOrderHom.monotone.functor))
    exact hL.trans hR.symm

/-- On each `n`-simplex `σ`, `categorySimplicialObjectMap F M` sends the `σ`-summand to the
`((F.mapComposableArrows n).obj σ)`-summand. -/
@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_categorySimplicialObjectMap_app
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategorySimplicialObject (F ⋙ M) σ ≫ (categorySimplicialObjectMap F M).app (op ⦋n⦌) =
      ιCategorySimplicialObject M ((F.mapComposableArrows n).obj σ) := by
  dsimp only [categorySimplicialObject, categorySimplicialObjectMap, ιCategorySimplicialObject]
  exact Sigma.ι_comp_desc _ _

/-- `categorySimplicialObjectMap` sends the identity functor `𝟭 C` to the identity morphism. -/
@[simp]
lemma categorySimplicialObjectMap_id (M : C ⥤ A) :
    categorySimplicialObjectMap (𝟭 C) M = 𝟙 (categorySimplicialObject C M) := by
  refine NatTrans.ext (funext fun ⟨⟨n⟩⟩ ↦ categorySimplicialObject_hom_ext fun σ ↦ ?_)
  exact (ιCategorySimplicialObject_categorySimplicialObjectMap_app (𝟭 C) M σ).trans
    (Category.comp_id _).symm

/-- `categorySimplicialObjectMap` respects composition of functors `F : C ⥤ D` and `G : D ⥤ E`. -/
@[reassoc]
lemma categorySimplicialObjectMap_comp
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₃ v₃} A]
    (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    categorySimplicialObjectMap (F ⋙ G) M =
      categorySimplicialObjectMap F (G ⋙ M) ≫ categorySimplicialObjectMap G M := by
  refine NatTrans.ext (funext fun ⟨⟨n⟩⟩ ↦ categorySimplicialObject_hom_ext fun σ ↦ ?_)
  rw [ιCategorySimplicialObject_categorySimplicialObjectMap_app, NatTrans.comp_app]
  symm
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (· ≫ (categorySimplicialObjectMap G M).app (op ⦋n⦌))
    (ιCategorySimplicialObject_categorySimplicialObjectMap_app F (G ⋙ M) σ)).trans
    (ιCategorySimplicialObject_categorySimplicialObjectMap_app G M _)

/-- `categorySimplicialObjectMap` is natural in coefficient transformations `α : M ⟶ N`. -/
@[reassoc]
lemma categorySimplicialObjectMap_naturality
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) :
    categorySimplicialObjectCoeffMap (Functor.whiskerLeft F α) ≫ categorySimplicialObjectMap F N =
      categorySimplicialObjectMap F M ≫ categorySimplicialObjectCoeffMap α := by
  refine NatTrans.ext (funext fun ⟨⟨n⟩⟩ ↦ categorySimplicialObject_hom_ext fun σ ↦ ?_)
  rw [NatTrans.comp_app, NatTrans.comp_app, ιCategorySimplicialObject_coeffMap_app_assoc,
    ιCategorySimplicialObject_categorySimplicialObjectMap_app,
    ιCategorySimplicialObject_categorySimplicialObjectMap_app_assoc,
    ιCategorySimplicialObject_coeffMap_app]
  rfl

end SimplicialLemmas

/-- Functoriality of `categorySimplicialObject` in the coefficient diagram `M : C ⥤ A`. -/
abbrev categorySimplicialObjectFunctor (C : Type u) [Category.{v} C]
    (A : Type u') [Category.{v'} A] [HasCoproducts.{max u v} A] :
    (C ⥤ A) ⥤ SimplicialObject A where
  obj M := categorySimplicialObject C M
  map α := categorySimplicialObjectCoeffMap α
  map_id := categorySimplicialObjectCoeffMap_id
  map_comp := categorySimplicialObjectCoeffMap_comp

/-- For a constant coefficient functor `(Functor.const C).obj X`, `categorySimplicialObject`
identifies with `(sigmaConst.obj X).obj (nerve C)`. -/
def categorySimplicialObjectConstIso (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (X : A) :
    categorySimplicialObject C ((Functor.const C).obj X) ≅
      (SimplicialObject.whiskering _ _ |>.obj (sigmaConst.obj X)).obj (nerve C) :=
  NatIso.ofComponents
    (fun Δ ↦
      { hom := Sigma.desc fun σ ↦ Sigma.ι (fun _ : (nerve C).obj Δ ↦ X) σ
        inv := Sigma.desc fun σ ↦
          Sigma.ι (fun τ : ComposableArrows C Δ.unop.len ↦
            ((Functor.const C).obj X).obj (τ.obj 0)) σ
        hom_inv_id := by
          dsimp [categorySimplicialObject]
          ext σ
          simp
        inv_hom_id := by
          dsimp [categorySimplicialObject]
          ext σ
          simp })
    (fun f ↦ by
      dsimp [categorySimplicialObject]
      ext σ
      simp [Sigma.map']
      rfl)

/-- `categorySimplicialObjectConstIso.hom` identifies summand inclusions. -/
@[reassoc (attr := simp)]
lemma ιCategorySimplicialObject_constIso_hom {C : Type u} [Category.{v} C]
    [HasCoproducts.{max u v} A] (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategorySimplicialObject ((Functor.const C).obj X) σ ≫
      (categorySimplicialObjectConstIso C X).hom.app (op ⦋n⦌) =
      Sigma.ι (fun _ : (nerve C) _⦋n⦌ ↦ X) σ := by
  dsimp [categorySimplicialObject, categorySimplicialObjectConstIso, ιCategorySimplicialObject]
  exact Sigma.ι_comp_desc _ _

/-- `categorySimplicialObjectConstIso.inv` identifies summand inclusions. -/
@[reassoc (attr := simp)]
lemma ι_categorySimplicialObjectConstIso_inv {C : Type u} [Category.{v} C]
    [HasCoproducts.{max u v} A] (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    Sigma.ι (fun _ : (nerve C) _⦋n⦌ ↦ X) σ ≫
      (categorySimplicialObjectConstIso C X).inv.app (op ⦋n⦌) =
      ιCategorySimplicialObject ((Functor.const C).obj X) σ := by
  dsimp [categorySimplicialObject, categorySimplicialObjectConstIso, ιCategorySimplicialObject]
  exact Sigma.ι_comp_desc _ _

end SimplicialObject

section ChainComplex

variable {A : Type u'} [Category.{v'} A] [Preadditive A]

/-- The category chain complex of `C` with coefficients in `M : C ⥤ A`, whose degree-`n` object is
`∐_{σ ∈ NₙC} M(σ₀)` with alternating face differential. -/
abbrev categoryChainComplex (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (M : C ⥤ A) : ChainComplex A ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex A).obj (categorySimplicialObject C M)

/-- Functor sending a coefficient diagram `M : C ⥤ A` to the alternating face map chain complex of
`categorySimplicialObject C M`. -/
abbrev categoryChainComplexFunctor (C : Type u) [Category.{v} C]
    (A : Type u') [Category.{v'} A] [Preadditive A] [HasCoproducts.{max u v} A] :
    (C ⥤ A) ⥤ ChainComplex A ℕ :=
  categorySimplicialObjectFunctor C A ⋙ AlgebraicTopology.alternatingFaceMapComplex A

/-- For a constant coefficient object `X : A`, `categoryChainComplex C ((Functor.const C).obj X)`
identifies with the simplicial chain complex `(nerve C).chainComplex X`. -/
def categoryChainComplexConstIso (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (X : A) :
    categoryChainComplex C ((Functor.const C).obj X) ≅ (nerve C).chainComplex X :=
  (AlgebraicTopology.alternatingFaceMapComplex A).mapIso (categorySimplicialObjectConstIso C X)

section ChainComplexLemmas

variable {C : Type u} [Category.{v} C] [HasCoproducts.{max u v} A]

instance : (categorySimplicialObjectFunctor C A).Additive where
  map_add {M N} α β := by
    refine NatTrans.ext (funext fun ⟨⟨n⟩⟩ ↦ categorySimplicialObject_hom_ext fun σ ↦ ?_)
    simp

/-- Chain map induced by a natural transformation `α : M ⟶ N` of coefficient functors. -/
abbrev categoryChainComplexCoeffMap {M N : C ⥤ A} (α : M ⟶ N) :
    categoryChainComplex C M ⟶ categoryChainComplex C N :=
  (AlgebraicTopology.alternatingFaceMapComplex A).map (categorySimplicialObjectCoeffMap α)

/-- Inclusion `M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X n` of the summand indexed by `σ`. -/
abbrev ιCategoryChainComplex (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categoryChainComplex C M).X n :=
  ιCategorySimplicialObject M σ

/-- Degree-`0` summand inclusion `M.obj c ⟶ (categoryChainComplex C M).X 0` at a vertex `c : C`. -/
def ιCategoryChainComplex₀ (M : C ⥤ A) (c : C) :
    M.obj c ⟶ (categoryChainComplex C M).X 0 :=
  ιCategoryChainComplex M (ComposableArrows.mk₀ c)

/-- Degree-`1` summand inclusion `M.obj c₀ ⟶ (categoryChainComplex C M).X 1` at an arrow
`f : c₀ ⟶ c₁`. -/
def ιCategoryChainComplex₁ (M : C ⥤ A) {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    M.obj c₀ ⟶ (categoryChainComplex C M).X 1 :=
  ιCategoryChainComplex M (ComposableArrows.mk₁ f)

/-- Degree-`2` summand inclusion `M.obj c₀ ⟶ (categoryChainComplex C M).X 2` at a composable pair
`(f, g)`. -/
def ιCategoryChainComplex₂ (M : C ⥤ A) {c₀ c₁ c₂ : C} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) :
    M.obj c₀ ⟶ (categoryChainComplex C M).X 2 :=
  ιCategoryChainComplex M (ComposableArrows.mk₂ f g)

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
    Cofan (fun σ : ComposableArrows C n ↦ M.obj (σ.obj 0)) :=
  Cofan.mk _ (ιCategoryChainComplex M)

/-- The cofan `categoryChainComplexXCofan M n` is a coproduct colimit. -/
def isColimitCategoryChainComplexXCofan (M : C ⥤ A) (n : ℕ) :
    IsColimit (categoryChainComplexXCofan M n) :=
  isColimitCategorySimplicialObjectXCofan M n

/-- Morphisms out of `(categoryChainComplex C M).X n` are determined on each nerve `n`-simplex. -/
@[ext]
lemma categoryChainComplex_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (categoryChainComplex C M).X n ⟶ T}
    (h : ∀ σ : ComposableArrows C n,
      ιCategoryChainComplex M σ ≫ f = ιCategoryChainComplex M σ ≫ g) :
    f = g :=
  categorySimplicialObject_hom_ext h

/-- Morphisms out of `(categoryChainComplex C M).X 0` are determined on each object `c : C`. -/
lemma categoryChainComplex_hom_ext₀ {M : C ⥤ A} {T : A}
    {f g : (categoryChainComplex C M).X 0 ⟶ T}
    (h : ∀ c : C, ιCategoryChainComplex₀ M c ≫ f = ιCategoryChainComplex₀ M c ≫ g) :
    f = g := by
  refine categoryChainComplex_hom_ext fun σ ↦ ?_
  obtain ⟨c, rfl⟩ := nerveEquiv.symm.surjective σ
  exact h c

lemma ιCategoryChainComplex_congr_heq {M : C ⥤ A} {n : ℕ} {σ τ : ComposableArrows C n}
    (h : σ = τ) :
    ιCategoryChainComplex M σ ≍ ιCategoryChainComplex M τ := by
  cases h
  rfl

/-- Alternating-face boundary formula on the `σ`-summand of `categoryChainComplex C M`: `d₀`
applies `M(f₁)` on the initial arrow `c₀ ⟶ c₁`, while the remaining faces
`(-1)^(j + 1) • d_{j + 1}` keep `M(c₀)` unchanged. -/
@[reassoc]
lemma ιCategoryChainComplex_d (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplex C M).d (n + 1) n =
      M.map (σ.map (homOfLE (Fin.zero_le (1 : Fin (n + 2))))) ≫
        ιCategoryChainComplex M ((nerve C).δ 0 σ) +
        ∑ j : Fin (n + 1),
          (-1) ^ (j.val + 1) • ιCategoryChainComplex M ((nerve C).δ j.succ σ) := by
  dsimp only [categoryChainComplex]
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.comp_sum,
    Fin.sum_univ_succ]
  simp only [Preadditive.comp_zsmul, ιCategoryChainComplex, Fin.val_zero, pow_zero, one_smul,
    ιCategorySimplicialObject_δ_zero, Fin.val_succ, ιCategorySimplicialObject_δ_succ]
  rfl

/-- In degree `1`, the boundary of an arrow `f : c₀ ⟶ c₁` sends `m ∈ M(c₀)` to
`M(f)(m) ∈ M(c₁)` minus `m ∈ M(c₀)`. -/
@[reassoc]
lemma ιCategoryChainComplex₁_d_one_zero (M : C ⥤ A) {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    ιCategoryChainComplex₁ M f ≫ (categoryChainComplex C M).d 1 0 =
      M.map f ≫ ιCategoryChainComplex₀ M c₁ - ιCategoryChainComplex₀ M c₀ := by
  refine (ιCategoryChainComplex_d M (ComposableArrows.mk₁ f)).trans ?_
  have hd0 : (nerve C).δ 0 (ComposableArrows.mk₁ f) = ComposableArrows.mk₀ c₁ :=
    ComposableArrows.ext₀ rfl
  have hd1 : (nerve C).δ 1 (ComposableArrows.mk₁ f) = ComposableArrows.mk₀ c₀ :=
    ComposableArrows.ext₀ rfl
  have t0 : (M.map ((ComposableArrows.mk₁ f).map (homOfLE (Fin.zero_le (1 : Fin 2)))) ≫
      ιCategoryChainComplex M ((nerve C).δ 0 (ComposableArrows.mk₁ f)) :
        M.obj c₀ ⟶ (categoryChainComplex C M).X 0) =
      M.map f ≫ ιCategoryChainComplex₀ M c₁ :=
    congrArg (M.map f ≫ ·) (eq_of_heq (ιCategoryChainComplex_congr_heq hd0))
  have t1 : (∑ j : Fin 1, (-1 : ℤ) ^ (j.val + 1) •
      ιCategoryChainComplex M ((nerve C).δ j.succ (ComposableArrows.mk₁ f)) :
        M.obj c₀ ⟶ (categoryChainComplex C M).X 0) =
      -ιCategoryChainComplex₀ M c₀ := by
    refine (Fin.sum_univ_one _).trans ?_
    have hp : (-1 : ℤ) ^ ((0 : Fin 1).val + 1) = -1 := rfl
    rw [hp, neg_one_smul]
    exact congrArg (- ·) (eq_of_heq (ιCategoryChainComplex_congr_heq hd1))
  exact (congrArg₂ (· + ·) t0 t1).trans (sub_eq_add_neg _ _).symm

/-- In degree `2`, the boundary of a composable pair `(f, g)` (`c₀ ⟶ c₁ ⟶ c₂`) sends `M(c₀)` to
`M(f)` in the `g`-summand minus the `(f ≫ g)`-summand plus the `f`-summand. -/
@[reassoc]
lemma ιCategoryChainComplex₂_d_two_one (M : C ⥤ A) {c₀ c₁ c₂ : C} (f : c₀ ⟶ c₁) (g : c₁ ⟶ c₂) :
    ιCategoryChainComplex₂ M f g ≫ (categoryChainComplex C M).d 2 1 =
      M.map f ≫ ιCategoryChainComplex₁ M g - ιCategoryChainComplex₁ M (f ≫ g) +
        ιCategoryChainComplex₁ M f := by
  refine (ιCategoryChainComplex_d M (ComposableArrows.mk₂ f g)).trans ?_
  have hd0 : (nerve C).δ 0 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ g :=
    CategoryTheory.nerve.δ₀_mk₂_eq f g
  have hd1 : (nerve C).δ 1 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ (f ≫ g) :=
    CategoryTheory.nerve.δ₁_mk₂_eq f g
  have hd2 : (nerve C).δ 2 (ComposableArrows.mk₂ f g) = ComposableArrows.mk₁ f :=
    CategoryTheory.nerve.δ₂_mk₂_eq f g
  have t0 : (M.map ((ComposableArrows.mk₂ f g).map (homOfLE (Fin.zero_le (1 : Fin 3)))) ≫
      ιCategoryChainComplex M ((nerve C).δ 0 (ComposableArrows.mk₂ f g)) :
        M.obj c₀ ⟶ (categoryChainComplex C M).X 1) =
      M.map f ≫ ιCategoryChainComplex₁ M g :=
    congrArg (M.map f ≫ ·) (eq_of_heq (ιCategoryChainComplex_congr_heq hd0))
  have tsum : (∑ j : Fin 2, (-1 : ℤ) ^ (j.val + 1) •
      ιCategoryChainComplex M ((nerve C).δ j.succ (ComposableArrows.mk₂ f g)) :
        M.obj c₀ ⟶ (categoryChainComplex C M).X 1) =
      -ιCategoryChainComplex₁ M (f ≫ g) + ιCategoryChainComplex₁ M f := by
    refine (Fin.sum_univ_two _).trans ?_
    have t1 : ((-1 : ℤ) ^ ((0 : Fin 2).val + 1) •
        ιCategoryChainComplex M ((nerve C).δ (0 : Fin 2).succ (ComposableArrows.mk₂ f g)) :
          M.obj c₀ ⟶ (categoryChainComplex C M).X 1) =
        -ιCategoryChainComplex₁ M (f ≫ g) := by
      have hp : (-1 : ℤ) ^ ((0 : Fin 2).val + 1) = -1 := rfl
      rw [hp, neg_one_smul]
      exact congrArg (- ·) (eq_of_heq (ιCategoryChainComplex_congr_heq hd1))
    have t2 : ((-1 : ℤ) ^ ((1 : Fin 2).val + 1) •
        ιCategoryChainComplex M ((nerve C).δ (1 : Fin 2).succ (ComposableArrows.mk₂ f g)) :
          M.obj c₀ ⟶ (categoryChainComplex C M).X 1) =
        ιCategoryChainComplex₁ M f := by
      have hp : (-1 : ℤ) ^ ((1 : Fin 2).val + 1) = 1 := rfl
      rw [hp, one_smul]
      exact eq_of_heq (ιCategoryChainComplex_congr_heq hd2)
    exact congrArg₂ (· + ·) t1 t2
  exact (congrArg₂ (· + ·) t0 tsum).trans (by abel)

/-- Action of `categoryChainComplexCoeffMap α` on the `σ`-summand in degree `n`. -/
@[reassoc]
lemma ιCategoryChainComplex_categoryChainComplexCoeffMap_f {M N : C ⥤ A} (α : M ⟶ N) {n : ℕ}
    (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplexCoeffMap α).f n =
      α.app (σ.obj 0) ≫ ιCategoryChainComplex N σ :=
  ιCategorySimplicialObject_coeffMap_app α σ

/-- Action of `categoryChainComplexCoeffMap α` on the degree-`0` summand at `c : C`. -/
@[reassoc]
lemma ιCategoryChainComplex₀_categoryChainComplexCoeffMap_f {M N : C ⥤ A} (α : M ⟶ N) (c : C) :
    ιCategoryChainComplex₀ M c ≫ (categoryChainComplexCoeffMap α).f 0 =
      α.app c ≫ ιCategoryChainComplex₀ N c :=
  ιCategorySimplicialObject_coeffMap_app α (ComposableArrows.mk₀ c)

/-- Chain map `categoryChainComplex C (F ⋙ M) ⟶ categoryChainComplex D M` induced by a functor
`F : C ⥤ D`. -/
def categoryChainComplexMap {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) :
    categoryChainComplex C (F ⋙ M) ⟶ categoryChainComplex D M :=
  (AlgebraicTopology.alternatingFaceMapComplex A).map (categorySimplicialObjectMap F M)

/-- Action of `categoryChainComplexMap F M` on the `σ`-summand in degree `n`. -/
@[reassoc (attr := simp)]
lemma ιCategoryChainComplex_categoryChainComplexMap_f
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex (F ⋙ M) σ ≫ (categoryChainComplexMap F M).f n =
      ιCategoryChainComplex M ((F.mapComposableArrows n).obj σ) :=
  ιCategorySimplicialObject_categorySimplicialObjectMap_app F M σ

/-- Action of `categoryChainComplexMap F M` on the degree-`0` summand at `c : C`. -/
@[reassoc (attr := simp)]
lemma ιCategoryChainComplex₀_categoryChainComplexMap_f
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) (c : C) :
    ιCategoryChainComplex₀ (F ⋙ M) c ≫ (categoryChainComplexMap F M).f 0 =
      ιCategoryChainComplex₀ M (F.obj c) := by
  refine (ιCategoryChainComplex_categoryChainComplexMap_f F M (ComposableArrows.mk₀ c)).trans ?_
  exact eq_of_heq (ιCategoryChainComplex_congr_heq (ComposableArrows.ext₀ rfl))

/-- `categoryChainComplexMap` sends the identity functor `𝟭 C` to the identity chain map. -/
@[simp]
lemma categoryChainComplexMap_id (M : C ⥤ A) :
    categoryChainComplexMap (𝟭 C) M = 𝟙 (categoryChainComplex C M) :=
  (congrArg (AlgebraicTopology.alternatingFaceMapComplex A).map
    (categorySimplicialObjectMap_id M)).trans
    ((AlgebraicTopology.alternatingFaceMapComplex A).map_id (categorySimplicialObject C M))

/-- `categoryChainComplexMap` respects composition of functors `F : C ⥤ D` and `G : D ⥤ E`. -/
@[reassoc]
lemma categoryChainComplexMap_comp
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₃ v₃} A]
    (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    categoryChainComplexMap (F ⋙ G) M =
      categoryChainComplexMap F (G ⋙ M) ≫ categoryChainComplexMap G M := by
  rw [categoryChainComplexMap, categorySimplicialObjectMap_comp,
    CategoryTheory.Functor.map_comp]
  rfl

/-- `categoryChainComplexMap` commutes with coefficient transformations `α : M ⟶ N`. -/
@[reassoc]
lemma categoryChainComplexMap_naturality
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) :
    categoryChainComplexCoeffMap (Functor.whiskerLeft F α) ≫ categoryChainComplexMap F N =
      categoryChainComplexMap F M ≫ categoryChainComplexCoeffMap α := by
  dsimp [categoryChainComplexCoeffMap, categoryChainComplexMap]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    categorySimplicialObjectMap_naturality]

/-- `categoryChainComplexConstIso.hom` identifies `ιCategoryChainComplex` with
`SSet.ιChainComplex`. -/
@[reassoc (attr := simp)]
lemma ιCategoryChainComplex_constIso_hom (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex ((Functor.const C).obj X) σ ≫
      (categoryChainComplexConstIso C X).hom.f n =
      (nerve C).ιChainComplex σ := by
  simp [categoryChainComplexConstIso, ιCategoryChainComplex, SSet.ιChainComplex]

/-- `categoryChainComplexConstIso.inv` identifies `SSet.ιChainComplex` with
`ιCategoryChainComplex`. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_constIso_inv (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    (nerve C).ιChainComplex σ ≫ (categoryChainComplexConstIso C X).inv.f n =
      ιCategoryChainComplex ((Functor.const C).obj X) σ := by
  simp [categoryChainComplexConstIso, ιCategoryChainComplex, SSet.ιChainComplex]

/-- `categoryChainComplexConstIso` commutes with `categoryChainComplexMap` and
`SSet.chainComplexMap`. -/
@[reassoc]
lemma categoryChainComplexMap_constIso_hom {D : Type u} [Category.{v} D]
    (F : C ⥤ D) (X : A) :
    categoryChainComplexMap F ((Functor.const D).obj X) ≫
      (categoryChainComplexConstIso D X).hom =
      (categoryChainComplexConstIso C X).hom ≫ SSet.chainComplexMap (nerveMap F) X := by
  refine HomologicalComplex.Hom.ext (funext fun n ↦ categoryChainComplex_hom_ext fun σ ↦ ?_)
  simp only [HomologicalComplex.comp_f, ιCategoryChainComplex_categoryChainComplexMap_f_assoc]
  have hL : ιCategoryChainComplex ((Functor.const D).obj X) ((F.mapComposableArrows n).obj σ) ≫
      (categoryChainComplexConstIso D X).hom.f n =
      (nerve D).ιChainComplex ((nerveMap F).app (op ⦋n⦌) σ) :=
    ιCategoryChainComplex_constIso_hom X ((F.mapComposableArrows n).obj σ)
  have hR : (ιCategoryChainComplex (F ⋙ (Functor.const D).obj X) σ ≫
      (categoryChainComplexConstIso C X).hom.f n ≫
      (SSet.chainComplexMap (nerveMap F) X).f n : X ⟶ _) =
      (nerve D).ιChainComplex ((nerveMap F).app (op ⦋n⦌) σ) := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (SSet.chainComplexMap (nerveMap F) X).f n)
      (ιCategoryChainComplex_constIso_hom X σ)).trans ?_
    exact SSet.ι_chainComplexMap_f (nerve C) (nerve D) (nerveMap F) X σ
  exact hL.trans hR.symm

/-- For an empty category `C`, `categoryChainComplex C M` is a zero chain complex. -/
lemma isZero_categoryChainComplex_of_isEmpty [IsEmpty C] (M : C ⥤ A) :
    IsZero (categoryChainComplex C M) := by
  rw [IsZero.iff_id_eq_zero]
  refine HomologicalComplex.Hom.ext (funext fun n ↦ categoryChainComplex_hom_ext fun σ ↦ ?_)
  exact (IsEmpty.false (σ.obj 0)).elim

end ChainComplexLemmas

end ChainComplex

section Homology

variable {A : Type u'} [Category.{v'} A] [Preadditive A] [CategoryWithHomology A]

/-- Degree-`n` category homology `Hₙ(C, M)` of `C` with coefficients in `M : C ⥤ A`. -/
abbrev categoryHomology (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (M : C ⥤ A) (n : ℕ) : A :=
  (categoryChainComplex C M).homology n

/-- Functor `(C ⥤ A) ⥤ A` sending `M` to the `n`-th homology `Hₙ(C, M)`. -/
abbrev categoryHomologyFunctor (C : Type u) [Category.{v} C]
    (A : Type u') [Category.{v'} A] [Preadditive A] [HasCoproducts.{max u v} A]
    [CategoryWithHomology A] (n : ℕ) :
    (C ⥤ A) ⥤ A :=
  categoryChainComplexFunctor C A ⋙ HomologicalComplex.homologyFunctor A _ n

/-- For a constant coefficient object `X : A`, `categoryHomology C ((Functor.const C).obj X) n`
identifies with the simplicial homology `(nerve C).homology X n`. -/
def categoryHomologyConstIso (C : Type u) [Category.{v} C] [HasCoproducts.{max u v} A]
    (X : A) (n : ℕ) :
    categoryHomology C ((Functor.const C).obj X) n ≅ (nerve C).homology X n :=
  (HomologicalComplex.homologyFunctor A _ n).mapIso (categoryChainComplexConstIso C X)

section HomologyLemmas

variable {C : Type u} [Category.{v} C] [HasCoproducts.{max u v} A]

/-- Homology map `Hₙ(C, M) ⟶ Hₙ(C, N)` induced by a coefficient transformation `α : M ⟶ N`. -/
abbrev categoryHomologyCoeffMap {M N : C ⥤ A} (α : M ⟶ N) (n : ℕ) :
    categoryHomology C M n ⟶ categoryHomology C N n :=
  HomologicalComplex.homologyMap (categoryChainComplexCoeffMap α) n

/-- `categoryHomologyCoeffMap` preserves identities. -/
@[simp]
lemma categoryHomologyCoeffMap_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyCoeffMap (𝟙 M) n = 𝟙 (categoryHomology C M n) := by
  dsimp only [categoryHomologyCoeffMap, categoryChainComplexCoeffMap]
  rw [categorySimplicialObjectCoeffMap_id, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id]

/-- `categoryHomologyCoeffMap` preserves composition. -/
@[reassoc]
lemma categoryHomologyCoeffMap_comp {L M N : C ⥤ A} (α : L ⟶ M) (β : M ⟶ N) (n : ℕ) :
    categoryHomologyCoeffMap (α ≫ β) n =
      categoryHomologyCoeffMap α n ≫ categoryHomologyCoeffMap β n := by
  dsimp only [categoryHomologyCoeffMap, categoryChainComplexCoeffMap]
  rw [categorySimplicialObjectCoeffMap_comp, CategoryTheory.Functor.map_comp,
    HomologicalComplex.homologyMap_comp]

/-- Homology map `Hₙ(C, F ⋙ M) ⟶ Hₙ(D, M)` induced by a functor `F : C ⥤ D`. -/
def categoryHomologyMap {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) (n : ℕ) :
    categoryHomology C (F ⋙ M) n ⟶ categoryHomology D M n :=
  HomologicalComplex.homologyMap (categoryChainComplexMap F M) n

/-- `categoryHomologyMap` sends `𝟭 C` to the identity map. -/
@[simp]
lemma categoryHomologyMap_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyMap (𝟭 C) M n = 𝟙 (categoryHomology C M n) :=
  (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n) (categoryChainComplexMap_id M)).trans
    (HomologicalComplex.homologyMap_id (categoryChainComplex C M) n)

/-- `categoryHomologyMap` respects composition of functors `F : C ⥤ D` and `G : D ⥤ E`. -/
@[reassoc]
lemma categoryHomologyMap_comp
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₃ v₃} A]
    (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) (n : ℕ) :
    categoryHomologyMap (F ⋙ G) M n =
      categoryHomologyMap F (G ⋙ M) n ≫ categoryHomologyMap G M n := by
  rw [categoryHomologyMap, categoryChainComplexMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

/-- `categoryHomologyMap` commutes naturally with coefficient transformations `α : M ⟶ N`. -/
@[reassoc]
lemma categoryHomologyMap_naturality
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) (n : ℕ) :
    categoryHomologyCoeffMap (Functor.whiskerLeft F α) n ≫ categoryHomologyMap F N n =
      categoryHomologyMap F M n ≫ categoryHomologyCoeffMap α n := by
  dsimp [categoryHomologyCoeffMap, categoryHomologyMap]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    categoryChainComplexMap_naturality]

/-- `categoryHomologyConstIso` commutes with `categoryHomologyMap` and `SSet.homologyMap`. -/
@[reassoc]
lemma categoryHomologyMap_constIso_hom {D : Type u} [Category.{v} D]
    (F : C ⥤ D) (X : A) (n : ℕ) :
    categoryHomologyMap F ((Functor.const D).obj X) n ≫
      (categoryHomologyConstIso D X n).hom =
      (categoryHomologyConstIso C X n).hom ≫ SSet.homologyMap (nerveMap F) X n := by
  have h1 : (categoryHomologyConstIso D X n).hom =
      HomologicalComplex.homologyMap (categoryChainComplexConstIso D X).hom n := rfl
  have h2 : (categoryHomologyConstIso C X n).hom =
      HomologicalComplex.homologyMap (categoryChainComplexConstIso C X).hom n := rfl
  rw [h1, h2]
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  rw [categoryChainComplexMap_constIso_hom]
  exact HomologicalComplex.homologyMap_comp _ _ n

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

/-- A short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of coefficient functors `C ⥤ A` induces a short
exact sequence of category chain complexes whenever coproducts of size `max u v` in `A` are exact
(`AB4OfSize.{max u v} A`, for instance `ModuleCat R`). -/
lemma shortExact_map_categoryChainComplexFunctor {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) :
    (S.map (categoryChainComplexFunctor C A)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let J := Discrete (ComposableArrows C n)
  let W : (C ⥤ A) ⥤ (J ⥤ A) :=
    (Functor.whiskeringLeft J C A).obj (Discrete.functor fun σ ↦ σ.obj 0)
  let S₀ : ShortComplex (J ⥤ A) := S.map W
  have hS₀ : S₀.ShortExact := hS.map_of_exact W
  let cocone (M : C ⥤ A) : Cocone (W.obj M) :=
    { pt := (categoryChainComplex C M).X n
      ι := Discrete.natTrans fun j ↦ ιCategoryChainComplex M j.as }
  let isColim (M : C ⥤ A) : IsColimit (cocone M) :=
    { desc s := (isColimitCategoryChainComplexXCofan M n).desc
        (Cofan.mk s.pt fun σ ↦ s.ι.app ⟨σ⟩)
      fac s j := (isColimitCategoryChainComplexXCofan M n).fac
        (Cofan.mk s.pt fun σ ↦ s.ι.app ⟨σ⟩) ⟨j.as⟩
      uniq s m hm := (isColimitCategoryChainComplexXCofan M n).uniq
        (Cofan.mk s.pt fun σ ↦ s.ι.app ⟨σ⟩) m fun ⟨σ⟩ ↦ hm ⟨σ⟩ }
  have hf (j : J) :
      (cocone S.X₁).ι.app j ≫ (categoryChainComplexCoeffMap S.f).f n =
        S₀.f.app j ≫ (cocone S.X₂).ι.app j :=
    ιCategoryChainComplex_categoryChainComplexCoeffMap_f S.f j.as
  have hg (j : J) :
      (cocone S.X₂).ι.app j ≫ (categoryChainComplexCoeffMap S.g).f n =
        S₀.g.app j ≫ (cocone S.X₃).ι.app j :=
    ιCategoryChainComplex_categoryChainComplexCoeffMap_f S.g j.as
  have hex : ((S.map (categoryChainComplexFunctor C A)).map
      (HomologicalComplex.eval A _ n)).Exact :=
    colim.exact_mapShortComplex hS₀.exact
      (isColim S.X₁) (isColim S.X₂) (isColim S.X₃) _ _ hf hg
  have : Mono S₀.f := hS₀.mono_f
  have hmono : Mono ((S.map (categoryChainComplexFunctor C A)).map
      (HomologicalComplex.eval A _ n)).f :=
    colim.map_mono' S₀.f (isColim S.X₁) (isColim S.X₂) _ hf
  have : Epi S₀.g := hS₀.epi_g
  have (j : J) : Epi (S₀.g.app j) := inferInstance
  have hepi : Epi ((S.map (categoryChainComplexFunctor C A)).map
      (HomologicalComplex.eval A _ n)).g :=
    colim.map_epi' S₀.g _ (isColim S.X₃) _ hg
  exact { exact := hex, mono_f := hmono, epi_g := hepi }

/-- Connecting homomorphism `Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁)` (for `m + 1 = n`) associated to a short
exact sequence `S` of coefficient functors `C ⥤ A`. -/
def categoryHomologyδ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    categoryHomology C S.X₃ n ⟶ categoryHomology C S.X₁ m :=
  (shortExact_map_categoryChainComplexFunctor hS).δ n m (by simpa)

/-- The composite `Hₙ(C, S.X₂) ⟶ Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁)` vanishes. -/
@[reassoc (attr := simp)]
lemma comp_categoryHomologyδ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    categoryHomologyCoeffMap S.g n ≫ categoryHomologyδ hS n m h = 0 :=
  (shortExact_map_categoryChainComplexFunctor hS).comp_δ n m (by simpa)

/-- The composite `Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁) ⟶ Hₘ(C, S.X₂)` vanishes. -/
@[reassoc (attr := simp)]
lemma categoryHomologyδ_comp {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    categoryHomologyδ hS n m h ≫ categoryHomologyCoeffMap S.f m = 0 :=
  (shortExact_map_categoryChainComplexFunctor hS).δ_comp n m (by simpa)

/-- Exactness of the long exact coefficient sequence at `Hₘ(C, S.X₁)`:
`Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁) ⟶ Hₘ(C, S.X₂)` is exact for `m + 1 = n`. -/
lemma categoryHomology_exact₁ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (categoryHomologyδ_comp hS n m h)).Exact :=
  (shortExact_map_categoryChainComplexFunctor hS).homology_exact₁ n m (by simpa)

/-- Exactness of the long exact coefficient sequence at `Hₙ(C, S.X₂)`:
`Hₙ(C, S.X₁) ⟶ Hₙ(C, S.X₂) ⟶ Hₙ(C, S.X₃)` is exact. -/
lemma categoryHomology_exact₂ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    (S.map (categoryHomologyFunctor C A n)).Exact :=
  (shortExact_map_categoryChainComplexFunctor hS).homology_exact₂ n

/-- Exactness of the long exact coefficient sequence at `Hₙ(C, S.X₃)`:
`Hₙ(C, S.X₂) ⟶ Hₙ(C, S.X₃) ⟶ Hₘ(C, S.X₁)` is exact for `m + 1 = n`. -/
lemma categoryHomology_exact₃ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (comp_categoryHomologyδ hS n m h)).Exact :=
  (shortExact_map_categoryChainComplexFunctor hS).homology_exact₃ n m (by simpa)

/-- Naturality of `categoryHomologyδ` under morphisms of short exact sequences of coefficient
functors. -/
@[reassoc]
lemma categoryHomologyδ_naturality_coeff {S₁ S₂ : ShortComplex (C ⥤ A)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    categoryHomologyδ hS₁ n m h ≫ categoryHomologyCoeffMap φ.τ₁ m =
      categoryHomologyCoeffMap φ.τ₃ n ≫ categoryHomologyδ hS₂ n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((categoryChainComplexFunctor C A).mapShortComplex.map φ)
    (shortExact_map_categoryChainComplexFunctor hS₁)
    (shortExact_map_categoryChainComplexFunctor hS₂) n m (by simpa)

/-- Naturality of `categoryHomologyδ` under functors `F : C ⥤ D`. -/
@[reassoc]
lemma categoryHomologyδ_naturality_functor
    {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A] [AB4OfSize.{max u₂ v₂} A]
    (F : C ⥤ D) {S : ShortComplex (D ⥤ A)} (hS : S.ShortExact) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    categoryHomologyδ
        (hS.map_of_exact ((Functor.whiskeringLeft C D A).obj F)) n m h ≫
      categoryHomologyMap F S.X₁ m =
      categoryHomologyMap F S.X₃ n ≫ categoryHomologyδ hS n m h := by
  let Φ : (S.map ((Functor.whiskeringLeft C D A).obj F)).map (categoryChainComplexFunctor C A) ⟶
      S.map (categoryChainComplexFunctor D A) :=
    { τ₁ := categoryChainComplexMap F S.X₁
      τ₂ := categoryChainComplexMap F S.X₂
      τ₃ := categoryChainComplexMap F S.X₃
      comm₁₂ := (categoryChainComplexMap_naturality F S.f).symm
      comm₂₃ := (categoryChainComplexMap_naturality F S.g).symm }
  exact HomologicalComplex.HomologySequence.δ_naturality Φ
    (shortExact_map_categoryChainComplexFunctor
      (hS.map_of_exact ((Functor.whiskeringLeft C D A).obj F)))
    (shortExact_map_categoryChainComplexFunctor hS) n m (by simpa)

end LongExactSequence

end TauCeti
