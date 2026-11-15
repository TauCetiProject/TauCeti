/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory
import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic

/-!
# Homology of a category with coefficients in a functor

For `M : C ⥤ A` in `A` with coproducts of size `max u v`, `TauCeti.categorySimplicialObject M` has
`n`-simplices `∐ (σ : ComposableArrows C n), M.obj (σ.obj 0)` over `CategoryTheory.nerve C`;
`θ : ⦋m⦌ ⟶ ⦋n⦌` sends the `σ`-summand by `M(c₀ ⟶ c_{θ(0)})` to `(nerve C).map θ.op σ`. For
preadditive `A`, `TauCeti.categoryChainComplex M` has homology `TauCeti.categoryHomology M n`,
functorial in `M` and along `F : C ⥤ D`. For abelian `A`, `TauCeti.normalizedCategoryChainComplex M`
gives `TauCeti.normalizedCategoryHomologyIso`; under `AB4OfSize.{max u v} A`,
`TauCeti.categoryChainComplexFunctor` is exact
(`CategoryTheory.ShortComplex.ShortExact.categoryHomologyδ`); constant coefficients recover
`(nerve C).chainComplex X` and `(nerve C).homology X n` via `TauCeti.categoryChainComplexConstIso`
and `TauCeti.categoryHomologyConstIso`.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, pp. 89–91.
* C. A. Weibel, *The K-book*, Grad. Stud. Math. 145 (2013), Chapter IV, §3.5.
* P. Gabriel and M. Zisman, *Calculus of Fractions and Homotopy Theory* (1967), Appendix II, §3.
-/

public section

noncomputable section

open CategoryTheory Category Limits Opposite AlgebraicTopology Simplicial

universe u v u₂ v₂ u₃ v₃ u' v'

namespace TauCeti

section SimplicialObject

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]

@[reducible] private def nerveMapFn {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂)
    (σ : ComposableArrows C Δ₁.unop.len) : ComposableArrows C Δ₂.unop.len :=
  σ.whiskerLeft (SimplexCategory.toCat.map θ.unop).toFunctor

variable [HasCoproducts.{max u v} A]

variable (C A) in
/-- Functor `(C ⥤ A) ⥤ SimplicialObject A` sending `M` to `n ↦ ∐_σ M.obj (σ.obj 0)`. -/
def categorySimplicialObjectFunctor : (C ⥤ A) ⥤ SimplicialObject A where
  obj M := {
    obj Δ := ∐ fun (σ : ComposableArrows C Δ.unop.len) ↦ M.obj (σ.obj 0)
    map {Δ₁ Δ₂} θ := Limits.Sigma.map' (nerveMapFn θ) fun σ ↦
      M.map (σ.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0))))
    map_id Δ := Limits.Sigma.hom_ext _ _ fun σ ↦ (Limits.Sigma.ι_comp_map' _ _ σ).trans <| by
      change M.map (σ.map (homOfLE (Fin.zero_le 0))) ≫
        Limits.Sigma.ι (fun τ : ComposableArrows C Δ.unop.len ↦ M.obj (τ.obj 0)) σ = _; simp
    map_comp {Δ₁ Δ₂ Δ₃} θ₁ θ₂ := Limits.Sigma.hom_ext _ _ fun σ ↦ by
      have hmap : M.map (σ.map (homOfLE (Fin.zero_le ((θ₁ ≫ θ₂).unop.toOrderHom 0)))) =
          M.map (σ.map (homOfLE (Fin.zero_le (θ₁.unop.toOrderHom 0)))) ≫
            M.map ((nerveMapFn θ₁ σ).map (homOfLE (Fin.zero_le (θ₂.unop.toOrderHom 0)))) :=
        (congrArg M.map ((congrArg σ.map (Subsingleton.elim _ _)).trans
          (σ.map_comp _ _))).trans (M.map_comp _ _)
      simp only [Limits.Sigma.ι_comp_map', Limits.Sigma.ι_comp_map'_assoc]
      exact (congrArg (· ≫ _) hmap).trans (assoc _ _ _) }
  map α := {
    app Δ := Limits.Sigma.map fun (σ : ComposableArrows C Δ.unop.len) ↦ α.app (σ.obj 0)
    naturality {_ _} θ := (Limits.Sigma.map'_comp_map _ _ _).trans <|
      (congrArg (Limits.Sigma.map' (nerveMapFn θ))
        (funext fun σ ↦ α.naturality (σ.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))))).trans
        (Limits.Sigma.map_comp_map' _ _ _).symm }
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- Simplicial object of `(C, M)` with `n`-simplices `∐_{σ : ComposableArrows C n} M.obj (σ.obj 0)`;
`θ : ⦋m⦌ ⟶ ⦋n⦌` maps the `σ`-summand by `M(σ(0 ≤ θ(0)))` into `(nerve C).map θ.op σ`. -/
abbrev categorySimplicialObject (M : C ⥤ A) : SimplicialObject A :=
  (categorySimplicialObjectFunctor C A).obj M

/-- Simplicial morphism induced by a natural transformation `α : M ⟶ N` of coefficient diagrams. -/
abbrev categorySimplicialObjectMap {M N : C ⥤ A} (α : M ⟶ N) :
    categorySimplicialObject M ⟶ categorySimplicialObject N :=
  (categorySimplicialObjectFunctor C A).map α

/-- Summand inclusion `M.obj (σ.obj 0) ⟶ (categorySimplicialObject M) _⦋n⦌` at `σ`. -/
def ιCategorySimplicial (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categorySimplicialObject M) _⦋n⦌ :=
  Limits.Sigma.ι (fun (τ : ComposableArrows C n) ↦ M.obj (τ.obj 0)) σ

lemma ιCategorySimplicial_congr (M : C ⥤ A) {n : ℕ} {σ₁ σ₂ : ComposableArrows C n} (h : σ₁ = σ₂)
    (h0 : σ₁.obj 0 = σ₂.obj 0 := by exact congrArg (fun τ ↦ τ.obj 0) h) :
    ιCategorySimplicial M σ₁ = eqToHom (congrArg M.obj h0) ≫ ιCategorySimplicial M σ₂ := by
  subst h; simp

/-- The cofan presenting `(categorySimplicialObject M) _⦋n⦌` as a coproduct over `n`-simplices. -/
def categorySimplicialObjectXCofan (M : C ⥤ A) (n : ℕ) :
    Cofan (fun (σ : ComposableArrows C n) ↦ M.obj (σ.obj 0)) :=
  Cofan.mk ((categorySimplicialObject M) _⦋n⦌) (ιCategorySimplicial M)

/-- `(categorySimplicialObject M) _⦋n⦌` is the coproduct of `M.obj (σ.obj 0)` over `n`-simplices. -/
def isColimitCategorySimplicialObjectXCofan (M : C ⥤ A) (n : ℕ) :
    IsColimit (categorySimplicialObjectXCofan M n) := coproductIsCoproduct _

/-- Universal morphism out of `(categorySimplicialObject M) _⦋n⦌` specified on each summand. -/
def descCategorySimplicial (M : C ⥤ A) {n : ℕ} {T : A}
    (f : ∀ σ : ComposableArrows C n, M.obj (σ.obj 0) ⟶ T) : (categorySimplicialObject M) _⦋n⦌ ⟶ T :=
  Cofan.IsColimit.desc (isColimitCategorySimplicialObjectXCofan M n) f

@[reassoc (attr := simp)] lemma ιCategorySimplicial_desc (M : C ⥤ A) {n : ℕ} {T : A}
    (f : ∀ σ : ComposableArrows C n, M.obj (σ.obj 0) ⟶ T) (σ : ComposableArrows C n) :
    ιCategorySimplicial M σ ≫ descCategorySimplicial M f = f σ :=
  Cofan.IsColimit.fac (isColimitCategorySimplicialObjectXCofan M n) f σ

@[ext] lemma categorySimplicialObject_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (categorySimplicialObject M) _⦋n⦌ ⟶ T}
    (h : ∀ σ : ComposableArrows C n, ιCategorySimplicial M σ ≫ f = ιCategorySimplicial M σ ≫ g) :
    f = g := Cofan.IsColimit.hom_ext (isColimitCategorySimplicialObjectXCofan M n) _ _ h

@[reassoc] lemma ιCategorySimplicial_map (M : C ⥤ A) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows C n) : ιCategorySimplicial M σ ≫ (categorySimplicialObject M).map θ.op =
      M.map (σ.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))) ≫
        ιCategorySimplicial M ((nerve C).map θ.op σ) := Limits.Sigma.ι_comp_map' _ _ σ

/-- Face `δ 0` transports along `σ.obj 0 ⟶ σ.obj (Fin.succ 0)` and drops vertex `0`. -/
@[reassoc (attr := simp)] lemma ιCategorySimplicial_δ_zero (M : C ⥤ A) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) : ιCategorySimplicial M σ ≫ (categorySimplicialObject M).δ 0 =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
        ιCategorySimplicial M ((nerve C).δ 0 σ) :=
  ιCategorySimplicial_map M (SimplexCategory.δ (0 : Fin (n + 2))) σ

/-- Positive faces `δ (j.succ)` fix vertex `0` and act as the identity on `M.obj (σ.obj 0)`. -/
@[reassoc (attr := simp)] lemma ιCategorySimplicial_δ_succ (M : C ⥤ A) {n : ℕ} (j : Fin (n + 1))
    (σ : ComposableArrows C (n + 1)) :
    ιCategorySimplicial M σ ≫ (categorySimplicialObject M).δ j.succ =
      ιCategorySimplicial M ((nerve C).δ j.succ σ) :=
  (ιCategorySimplicial_map M (SimplexCategory.δ j.succ) σ).trans <| by
    change M.map (σ.map (homOfLE (Fin.zero_le 0))) ≫ _ = _
    simp only [homOfLE_refl, CategoryTheory.Functor.map_id]; exact id_comp _

@[reassoc] lemma ιCategorySimplicial_δ_last (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ιCategorySimplicial M σ ≫ (categorySimplicialObject M).δ (Fin.last (n + 1)) =
      ιCategorySimplicial M ((nerve C).δ (Fin.last (n + 1)) σ) :=
  ιCategorySimplicial_δ_succ M (Fin.last n) σ

/-- Degeneracies `σ i` fix vertex `0` and act as the identity on `M.obj (σ.obj 0)`. -/
@[reassoc (attr := simp)] lemma ιCategorySimplicial_σ (M : C ⥤ A) {n : ℕ} (i : Fin (n + 1))
    (σ : ComposableArrows C n) : ιCategorySimplicial M σ ≫ (categorySimplicialObject M).σ i =
      ιCategorySimplicial M ((nerve C).σ i σ) :=
  (ιCategorySimplicial_map M (SimplexCategory.σ i) σ).trans <| by
    change M.map (σ.map (homOfLE (Fin.zero_le 0))) ≫ _ = _
    simp only [homOfLE_refl, CategoryTheory.Functor.map_id]; exact id_comp _

@[reassoc (attr := simp)] lemma ιCategorySimplicial_map_app {M N : C ⥤ A} (α : M ⟶ N) {n : ℕ}
    (σ : ComposableArrows C n) :
    ιCategorySimplicial M σ ≫ (categorySimplicialObjectMap α).app (op ⦋n⦌) =
      α.app (σ.obj 0) ≫ ιCategorySimplicial N σ :=
  Limits.Sigma.ι_map (fun τ : ComposableArrows C n ↦ α.app (τ.obj 0)) σ

section Pushforward

variable {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]

/-- Covariant pushforward of category simplicial objects along a functor `F : C ⥤ D`. -/
def categorySimplicialObjectPushforward (F : C ⥤ D) (M : D ⥤ A) :
    categorySimplicialObject (F ⋙ M) ⟶ categorySimplicialObject M where
  app Δ := Limits.Sigma.map' (F.mapComposableArrows Δ.unop.len).obj fun _ ↦ 𝟙 _
  naturality {_ _} _ := by
    dsimp [categorySimplicialObjectFunctor]
    refine (Limits.Sigma.map'_comp_map' _ _ _ _).trans
      (Eq.trans ?_ (Limits.Sigma.map'_comp_map' _ _ _ _).symm)
    exact congrArg (Limits.Sigma.map' _) (funext fun _ ↦ (comp_id _).trans (id_comp _).symm)

@[reassoc (attr := simp)] lemma ιCategorySimplicial_pushforward_app (F : C ⥤ D) (M : D ⥤ A) {n : ℕ}
    (σ : ComposableArrows C n) :
    ιCategorySimplicial (F ⋙ M) σ ≫ (categorySimplicialObjectPushforward F M).app (op ⦋n⦌) =
      ιCategorySimplicial M ((F.mapComposableArrows n).obj σ) :=
  (Limits.Sigma.ι_comp_map' (g := fun τ : ComposableArrows C n ↦ M.obj (F.obj (τ.obj 0)))
    (f := fun τ : ComposableArrows D n ↦ M.obj (τ.obj 0))
    (F.mapComposableArrows n).obj (fun _ ↦ 𝟙 _) σ).trans (id_comp _)

@[simp, reassoc] lemma categorySimplicialObjectPushforward_comp {E : Type u₃} [Category.{v₃} E]
    [HasCoproducts.{max u₃ v₃} A] (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    categorySimplicialObjectPushforward (F ⋙ G) M =
      categorySimplicialObjectPushforward F (G ⋙ M) ≫ categorySimplicialObjectPushforward G M := by
  ext Δ; dsimp [categorySimplicialObjectFunctor, categorySimplicialObjectPushforward]
  refine Eq.trans ?_ (Limits.Sigma.map'_comp_map' _ _ _ _).symm
  exact congrArg (Limits.Sigma.map' _) (funext fun _ ↦ (id_comp _).symm)

@[reassoc] lemma categorySimplicialObjectMap_whiskerLeft_pushforward (F : C ⥤ D) {M N : D ⥤ A}
    (α : M ⟶ N) : categorySimplicialObjectMap (Functor.whiskerLeft F α) ≫
      categorySimplicialObjectPushforward F N =
        categorySimplicialObjectPushforward F M ≫ categorySimplicialObjectMap α := by
  ext ⟨⟨n⟩⟩ σ; simp

end Pushforward

@[simp] lemma categorySimplicialObjectPushforward_id (M : C ⥤ A) :
    categorySimplicialObjectPushforward (𝟭 C) M = 𝟙 (categorySimplicialObject M) := by
  ext Δ
  exact Limits.Sigma.map'_id_id (f := fun σ : ComposableArrows C Δ.unop.len ↦ M.obj (σ.obj 0))

end SimplicialObject

section ChainComplex

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Preadditive A]

variable (C A) in
instance : (categorySimplicialObjectFunctor C A).Additive where
  map_add {_ _} _ _ := by ext ⟨⟨n⟩⟩ σ; simp [NatTrans.app_add]

variable (C A) in
/-- The functor `(C ⥤ A) ⥤ ChainComplex A ℕ` sending `M` to its category chain complex. -/
@[expose] def categoryChainComplexFunctor : (C ⥤ A) ⥤ ChainComplex A ℕ :=
  categorySimplicialObjectFunctor C A ⋙ alternatingFaceMapComplex A

instance : (categoryChainComplexFunctor C A).Additive := by
  unfold categoryChainComplexFunctor; infer_instance

/-- Alternating-face chain complex of `(C, M)` with degree `n` equal to
`∐_{σ : ComposableArrows C n} M.obj (σ.obj 0)`. -/
abbrev categoryChainComplex (M : C ⥤ A) : ChainComplex A ℕ :=
  (categoryChainComplexFunctor C A).obj M

/-- The chain map `categoryChainComplex M ⟶ categoryChainComplex N` induced by `α : M ⟶ N`. -/
abbrev categoryChainComplexMap {M N : C ⥤ A} (α : M ⟶ N) :
    categoryChainComplex M ⟶ categoryChainComplex N := (categoryChainComplexFunctor C A).map α

/-- The summand inclusion `M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X n` at `σ`. -/
def ιCategoryChainComplex (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X n := ιCategorySimplicial M σ

lemma ιCategoryChainComplex_eq (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ = ιCategorySimplicial M σ := (rfl)

lemma ιCategoryChainComplex_congr (M : C ⥤ A) {n : ℕ} {σ₁ σ₂ : ComposableArrows C n}
    (h : σ₁ = σ₂) (h0 : σ₁.obj 0 = σ₂.obj 0 := by exact congrArg (fun τ ↦ τ.obj 0) h) :
    ιCategoryChainComplex M σ₁ = eqToHom (congrArg M.obj h0) ≫ ιCategoryChainComplex M σ₂ :=
  ιCategorySimplicial_congr M h h0

/-- The cofan presenting `(categoryChainComplex M).X n` as a coproduct over `n`-simplices. -/
def categoryChainComplexXCofan (M : C ⥤ A) (n : ℕ) :
    Cofan (fun (σ : ComposableArrows C n) ↦ M.obj (σ.obj 0)) := categorySimplicialObjectXCofan M n

/-- `(categoryChainComplex M).X n` is the coproduct of `M.obj (σ.obj 0)` over `n`-simplices `σ`. -/
def isColimitCategoryChainComplexXCofan (M : C ⥤ A) (n : ℕ) :
    IsColimit (categoryChainComplexXCofan M n) := isColimitCategorySimplicialObjectXCofan M n

/-- Universal morphism out of `(categoryChainComplex M).X n` specified on each simplex summand. -/
def descCategoryChainComplex (M : C ⥤ A) {n : ℕ} {T : A}
    (f : ∀ σ : ComposableArrows C n, M.obj (σ.obj 0) ⟶ T) : (categoryChainComplex M).X n ⟶ T :=
  descCategorySimplicial M f

@[reassoc (attr := simp)] lemma ιCategoryChainComplex_desc (M : C ⥤ A) {n : ℕ} {T : A}
    (f : ∀ σ : ComposableArrows C n, M.obj (σ.obj 0) ⟶ T) (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ ≫ descCategoryChainComplex M f = f σ :=
  ιCategorySimplicial_desc M f σ

@[ext] lemma categoryChainComplex_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (categoryChainComplex M).X n ⟶ T} (h : ∀ σ : ComposableArrows C n,
      ιCategoryChainComplex M σ ≫ f = ιCategoryChainComplex M σ ≫ g) : f = g :=
  categorySimplicialObject_hom_ext h

/-- Alternating-face differential on `σ : ComposableArrows C (n + 1)`: `δ 0` acts via
`M(σ(0 ≤ 1))` and `δ (j.succ)` acts with sign `(-1) ^ (j + 1)`. -/
@[reassoc] lemma ιCategoryChainComplex_d (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplex M).d (n + 1) n =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
          ιCategoryChainComplex M ((nerve C).δ 0 σ) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
          (ιCategoryChainComplex M ((nerve C).δ j.succ σ) :
            M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X n) :=
  (congrArg (ιCategorySimplicial M σ ≫ ·)
    (alternatingFaceMapComplex_obj_d (categorySimplicialObject M) n)).trans <|
    (Preadditive.comp_sum _ _ _).trans <| (Fin.sum_univ_succ _).trans (by simp; rfl)

/-- Degree-`0` chain summand inclusion `M.obj X ⟶ (categoryChainComplex M).X 0` at `X : C`. -/
abbrev ιCategoryChainComplex₀ (M : C ⥤ A) (X : C) : M.obj X ⟶ (categoryChainComplex M).X 0 :=
  ιCategoryChainComplex M (ComposableArrows.mk₀ X)

/-- Degree-`1` chain summand inclusion `M.obj X ⟶ (categoryChainComplex M).X 1` at `f : X ⟶ Y`. -/
abbrev ιCategoryChainComplex₁ (M : C ⥤ A) {X Y : C} (f : X ⟶ Y) :
    M.obj X ⟶ (categoryChainComplex M).X 1 := ιCategoryChainComplex M (ComposableArrows.mk₁ f)

/-- Degree-`2` chain summand inclusion at a composable pair `f : X ⟶ Y`, `g : Y ⟶ Z`. -/
abbrev ιCategoryChainComplex₂ (M : C ⥤ A) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    M.obj X ⟶ (categoryChainComplex M).X 2 := ιCategoryChainComplex M (ComposableArrows.mk₂ f g)

/-- Degree-`3` chain summand inclusion at composable arrows `f`, `g`, `h`. -/
abbrev ιCategoryChainComplex₃ (M : C ⥤ A) {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    M.obj W ⟶ (categoryChainComplex M).X 3 := ιCategoryChainComplex M (ComposableArrows.mk₃ f g h)

/-- Universal morphism out of `(categoryChainComplex M).X 0` from components `M.obj X ⟶ T`. -/
def descCategoryChainComplex₀ (M : C ⥤ A) {T : A} (f : ∀ X : C, M.obj X ⟶ T) :
    (categoryChainComplex M).X 0 ⟶ T := descCategoryChainComplex M fun σ ↦ f (σ.obj 0)

@[reassoc (attr := simp)] lemma ιCategoryChainComplex₀_desc₀ (M : C ⥤ A) {T : A}
    (f : ∀ X : C, M.obj X ⟶ T) (X : C) :
    ιCategoryChainComplex₀ M X ≫ descCategoryChainComplex₀ M f = f X :=
  ιCategoryChainComplex_desc M (fun σ ↦ f (σ.obj 0)) (ComposableArrows.mk₀ X)

lemma categoryChainComplex₀_hom_ext {M : C ⥤ A} {T : A} {f g : (categoryChainComplex M).X 0 ⟶ T}
    (h : ∀ X : C, ιCategoryChainComplex₀ M X ≫ f = ιCategoryChainComplex₀ M X ≫ g) : f = g := by
  ext σ; obtain ⟨X, rfl⟩ := ComposableArrows.mk₀_surjective σ; exact h X

/-- On `ComposableArrows.mk₁ f` (`f : X ⟶ Y`), `d 1 0` sends `m ∈ M(X)` to `M(f)(m) - m`. -/
@[reassoc (attr := simp)] lemma ιCategoryChainComplex₁_d (M : C ⥤ A) {X Y : C} (f : X ⟶ Y) :
    ιCategoryChainComplex₁ M f ≫ (categoryChainComplex M).d 1 0 =
      M.map f ≫ ιCategoryChainComplex₀ M Y - ιCategoryChainComplex₀ M X := by
  have h0 := (ιCategoryChainComplex_congr M
    (ComposableArrows.ext₀ rfl : (nerve C).δ 0 (.mk₁ f) = .mk₀ Y) rfl).trans (id_comp _)
  have h1 := (ιCategoryChainComplex_congr M
    (ComposableArrows.ext₀ rfl : (nerve C).δ 1 (.mk₁ f) = .mk₀ X) rfl).trans (id_comp _)
  refine (ιCategoryChainComplex_d M (.mk₁ f)).trans ?_
  exact (congrArg₂ (· + · : (M.obj X ⟶ (categoryChainComplex M).X 0) → _ → _)
    (by simp [h0] : _ = M.map f ≫ ιCategoryChainComplex₀ M Y)
    ((Fin.sum_univ_one _).trans ((neg_one_zsmul _).trans (congrArg (- ·) h1)))).trans
      (sub_eq_add_neg _ _).symm

/-- On `ComposableArrows.mk₂ f g`, `d 2 1` is `M(f)` on `g`, minus `f ≫ g`, plus `f`. -/
@[reassoc (attr := simp)] lemma ιCategoryChainComplex₂_d (M : C ⥤ A) {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) : ιCategoryChainComplex₂ M f g ≫ (categoryChainComplex M).d 2 1 =
      M.map f ≫ ιCategoryChainComplex₁ M g -
        ιCategoryChainComplex₁ M (f ≫ g) + ιCategoryChainComplex₁ M f := by
  have h0 := (ιCategoryChainComplex_congr M (nerve.δ₀_mk₂_eq f g) rfl).trans (id_comp _)
  have h1 := (ιCategoryChainComplex_congr M (nerve.δ₁_mk₂_eq f g) rfl).trans (id_comp _)
  have h2 := (ιCategoryChainComplex_congr M (nerve.δ₂_mk₂_eq f g) rfl).trans (id_comp _)
  refine (ιCategoryChainComplex_d M (.mk₂ f g)).trans ?_
  exact (congrArg₂ (· + · : (M.obj X ⟶ (categoryChainComplex M).X 1) → _ → _)
    (by simp [h0] : _ = M.map f ≫ ιCategoryChainComplex₁ M g) ((Fin.sum_univ_two _).trans <|
      congrArg₂ (· + ·) ((neg_one_zsmul _).trans (congrArg (- ·) h1))
        ((one_zsmul _).trans h2))).trans (by abel)

/-- On `ComposableArrows.mk₃ f g h`, `d 3 2` is `M(f)` on `(g, h)`, minus `(f ≫ g, h)`, plus
`(f, g ≫ h)`, minus `(f, g)`. -/
@[reassoc (attr := simp)] lemma ιCategoryChainComplex₃_d (M : C ⥤ A) {W X Y Z : C} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) : ιCategoryChainComplex₃ M f g h ≫ (categoryChainComplex M).d 3 2 =
      M.map f ≫ ιCategoryChainComplex₂ M g h - ιCategoryChainComplex₂ M (f ≫ g) h +
        ιCategoryChainComplex₂ M f (g ≫ h) - ιCategoryChainComplex₂ M f g := by
  have h0 := (ιCategoryChainComplex_congr M (nerve.δ₀_mk₃_eq f g h) rfl).trans (id_comp _)
  have h1 := (ιCategoryChainComplex_congr M (nerve.δ₁_mk₃_eq f g h) rfl).trans (id_comp _)
  have h2 := (ιCategoryChainComplex_congr M (nerve.δ₂_mk₃_eq f g h) rfl).trans (id_comp _)
  have h3 := (ιCategoryChainComplex_congr M (nerve.δ₃_mk₃_eq f g h) rfl).trans (id_comp _)
  refine (ιCategoryChainComplex_d M (.mk₃ f g h)).trans ?_
  exact (congrArg₂ (· + · : (M.obj W ⟶ (categoryChainComplex M).X 2) → _ → _)
    (by simp [h0] : _ = M.map f ≫ ιCategoryChainComplex₂ M g h) ((Fin.sum_univ_three _).trans <|
      congrArg₂ (· + ·)
        (congrArg₂ (· + ·) ((neg_one_zsmul _).trans (congrArg (- ·) h1)) ((one_zsmul _).trans h2))
        ((neg_one_zsmul _).trans (congrArg (- ·) h3)))).trans (by abel)

@[reassoc (attr := simp)] lemma ιCategoryChainComplex_map_f {M N : C ⥤ A} (α : M ⟶ N) {n : ℕ}
    (σ : ComposableArrows C n) : ιCategoryChainComplex M σ ≫ (categoryChainComplexMap α).f n =
      α.app (σ.obj 0) ≫ ιCategoryChainComplex N σ := ιCategorySimplicial_map_app α σ

@[reassoc (attr := simp)] lemma ιCategoryChainComplex₀_map_f {M N : C ⥤ A} (α : M ⟶ N) (X : C) :
    ιCategoryChainComplex₀ M X ≫ (categoryChainComplexMap α).f 0 =
      α.app X ≫ ιCategoryChainComplex₀ N X := ιCategoryChainComplex_map_f α (.mk₀ X)

instance {M N : C ⥤ A} (α : M ⟶ N) [∀ X, Epi (α.app X)] (n : ℕ) :
    Epi ((categoryChainComplexMap α).f n) := ⟨fun _ _ h ↦ categoryChainComplex_hom_ext fun σ ↦
  (cancel_epi (α.app (σ.obj 0))).1 (by simpa using ιCategoryChainComplex M σ ≫= h)⟩

instance {M N : C ⥤ A} (α : M ⟶ N) [∀ X, Epi (α.app X)] : Epi (categoryChainComplexMap α) :=
  HomologicalComplex.epi_of_epi_f _ fun _ ↦ inferInstance

private def isColimitCategoryChainComplexCocone (M : C ⥤ A) (n : ℕ) :
    IsColimit (Cocone.mk ((categoryChainComplex M).X n)
      { app := fun ⟨σ⟩ ↦ ιCategoryChainComplex M σ
        naturality := fun ⟨_⟩ ⟨_⟩ f ↦ by cases Discrete.eq_of_hom f; dsimp; simp } :
      Cocone (Discrete.functor (fun (σ : ComposableArrows C n) ↦ σ.obj 0) ⋙ M)) where
  desc s := descCategoryChainComplex M fun σ ↦ s.ι.app ⟨σ⟩
  fac _ _ := ιCategoryChainComplex_desc M _ _
  uniq _ _ hm := categoryChainComplex_hom_ext fun σ ↦ by simpa using hm ⟨σ⟩

private def categoryChainComplexEvalIso (n : ℕ) :
    categoryChainComplexFunctor C A ⋙ HomologicalComplex.eval A _ n ≅
      (Functor.whiskeringLeft (Discrete (ComposableArrows C n)) C A).obj
        (Discrete.functor fun σ ↦ σ.obj 0) ⋙ colim :=
  NatIso.ofComponents (fun M ↦ (isColimitCategoryChainComplexCocone M n).coconePointUniqueUpToIso
    (colimit.isColimit _)) fun {M N} α ↦ categoryChainComplex_hom_ext fun σ ↦ by
      have h (P : C ⥤ A) :=
        (isColimitCategoryChainComplexCocone P n).comp_coconePointUniqueUpToIso_hom
          (colimit.isColimit _) ⟨σ⟩
      dsimp at h ⊢; rw [ιCategoryChainComplex_map_f_assoc, h N, ← assoc, h M, ι_colimMap]; rfl

instance {J : Type*} [Category* J] [HasColimitsOfShape J A] :
    PreservesColimitsOfShape J (categoryChainComplexFunctor C A) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n ↦
    preservesColimitsOfShape_of_natIso (categoryChainComplexEvalIso (C := C) (A := A) n).symm

instance [HasFiniteColimits A] : PreservesFiniteColimits (categoryChainComplexFunctor C A) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

section Pushforward

variable {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]

/-- Covariant chain map `categoryChainComplex (F ⋙ M) ⟶ categoryChainComplex M` along `F`. -/
def categoryChainComplexPushforward (F : C ⥤ D) (M : D ⥤ A) :
    categoryChainComplex (F ⋙ M) ⟶ categoryChainComplex M :=
  (alternatingFaceMapComplex A).map (categorySimplicialObjectPushforward F M)

@[reassoc (attr := simp)] lemma ιCategoryChainComplex_pushforward_f (F : C ⥤ D) (M : D ⥤ A) {n : ℕ}
    (σ : ComposableArrows C n) :
    ιCategoryChainComplex (F ⋙ M) σ ≫ (categoryChainComplexPushforward F M).f n =
      ιCategoryChainComplex M ((F.mapComposableArrows n).obj σ) :=
  ιCategorySimplicial_pushforward_app F M σ

@[reassoc (attr := simp)] lemma ιCategoryChainComplex₀_pushforward_f (F : C ⥤ D) (M : D ⥤ A)
    (X : C) : ιCategoryChainComplex₀ (F ⋙ M) X ≫ (categoryChainComplexPushforward F M).f 0 =
      ιCategoryChainComplex₀ M (F.obj X) :=
  (ιCategoryChainComplex_pushforward_f F M (.mk₀ X)).trans <| (ιCategoryChainComplex_congr M
    (ComposableArrows.ext₀ rfl : (F.mapComposableArrows 0).obj (.mk₀ X) = .mk₀ (F.obj X))
    rfl).trans (id_comp _)

@[simp, reassoc] lemma categoryChainComplexPushforward_comp {E : Type u₃} [Category.{v₃} E]
    [HasCoproducts.{max u₃ v₃} A] (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    categoryChainComplexPushforward (F ⋙ G) M =
      categoryChainComplexPushforward F (G ⋙ M) ≫ categoryChainComplexPushforward G M :=
  (congrArg (alternatingFaceMapComplex A).map
    (categorySimplicialObjectPushforward_comp F G M)).trans
    ((alternatingFaceMapComplex A).map_comp _ _)

@[reassoc] lemma categoryChainComplexMap_whiskerLeft_pushforward (F : C ⥤ D) {M N : D ⥤ A}
    (α : M ⟶ N) :
    categoryChainComplexMap (Functor.whiskerLeft F α) ≫ categoryChainComplexPushforward F N =
      categoryChainComplexPushforward F M ≫ categoryChainComplexMap α :=
  ((alternatingFaceMapComplex A).map_comp _ _).symm.trans <|
    (congrArg (alternatingFaceMapComplex A).map
      (categorySimplicialObjectMap_whiskerLeft_pushforward F α)).trans
      ((alternatingFaceMapComplex A).map_comp _ _)

end Pushforward

@[simp] lemma categoryChainComplexPushforward_id (M : C ⥤ A) :
    categoryChainComplexPushforward (𝟭 C) M = 𝟙 (categoryChainComplex M) :=
  (congrArg (alternatingFaceMapComplex A).map (categorySimplicialObjectPushforward_id M)).trans
    ((alternatingFaceMapComplex A).map_id _)

end ChainComplex

section Homology

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Preadditive A] [CategoryWithHomology A]

variable (C A) in
/-- The degree-`n` category homology functor `(C ⥤ A) ⥤ A`. -/
abbrev categoryHomologyFunctor (n : ℕ) : (C ⥤ A) ⥤ A :=
  categoryChainComplexFunctor C A ⋙ HomologicalComplex.homologyFunctor A _ n

/-- The degree-`n` homology of `C` with coefficients in `M : C ⥤ A`. -/
abbrev categoryHomology (M : C ⥤ A) (n : ℕ) : A := (categoryChainComplex M).homology n

/-- The morphism on degree-`n` category homology induced by `α : M ⟶ N`. -/
abbrev categoryHomologyMap {M N : C ⥤ A} (α : M ⟶ N) (n : ℕ) :
    categoryHomology M n ⟶ categoryHomology N n :=
  HomologicalComplex.homologyMap (categoryChainComplexMap α) n

@[simp] lemma categoryHomologyMap_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyMap (𝟙 M) n = 𝟙 (categoryHomology M n) := by simp [categoryHomologyMap]

@[reassoc] lemma categoryHomologyMap_comp {M N P : C ⥤ A} (α : M ⟶ N) (β : N ⟶ P) (n : ℕ) :
    categoryHomologyMap (α ≫ β) n = categoryHomologyMap α n ≫ categoryHomologyMap β n := by
  simp [categoryHomologyMap, ← HomologicalComplex.homologyMap_comp]

section Pushforward

variable {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]

/-- Covariant map `categoryHomology (F ⋙ M) n ⟶ categoryHomology M n` induced by `F : C ⥤ D`. -/
abbrev categoryHomologyPushforward (F : C ⥤ D) (M : D ⥤ A) (n : ℕ) :
    categoryHomology (F ⋙ M) n ⟶ categoryHomology M n :=
  HomologicalComplex.homologyMap (categoryChainComplexPushforward F M) n

@[reassoc] lemma categoryHomologyPushforward_comp {E : Type u₃} [Category.{v₃} E]
    [HasCoproducts.{max u₃ v₃} A] (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) (n : ℕ) :
    categoryHomologyPushforward (F ⋙ G) M n =
      categoryHomologyPushforward F (G ⋙ M) n ≫ categoryHomologyPushforward G M n := by
  simp [categoryHomologyPushforward, ← HomologicalComplex.homologyMap_comp]

@[reassoc] lemma categoryHomologyMap_whiskerLeft_pushforward (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N)
    (n : ℕ) :
    categoryHomologyMap (Functor.whiskerLeft F α) n ≫ categoryHomologyPushforward F N n =
      categoryHomologyPushforward F M n ≫ categoryHomologyMap α n := by
  simp only [categoryHomologyMap, categoryHomologyPushforward,
    ← HomologicalComplex.homologyMap_comp, categoryChainComplexMap_whiskerLeft_pushforward]

end Pushforward

@[simp] lemma categoryHomologyPushforward_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyPushforward (𝟭 C) M n = 𝟙 (categoryHomology M n) :=
  (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
    (categoryChainComplexPushforward_id M)).trans (HomologicalComplex.homologyMap_id _ n)

instance {M N : C ⥤ A} (α : M ⟶ N) [∀ X, Epi (α.app X)] : Epi (categoryHomologyMap α 0) :=
  HomologicalComplex.epi_homologyMap_of_epi_of_not_rel (categoryChainComplexMap α) 0 (by simp)

instance [HasPushouts A] : (categoryHomologyFunctor C A 0).PreservesEpimorphisms where
  preserves α _ := by
    have (X : C) : Epi (α.app X) := ((evaluation C A).obj X).map_epi α
    exact inferInstanceAs (Epi (categoryHomologyMap α 0))

end Homology

section Normalization

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Abelian A]

variable (C A) in
/-- Normalized Moore complex functor `(C ⥤ A) ⥤ ChainComplex A ℕ` on `categorySimplicialObject`. -/
@[expose] def normalizedCategoryChainComplexFunctor : (C ⥤ A) ⥤ ChainComplex A ℕ :=
  categorySimplicialObjectFunctor C A ⋙ normalizedMooreComplex A

/-- The normalized category chain complex of `(C, M)`. -/
abbrev normalizedCategoryChainComplex (M : C ⥤ A) : ChainComplex A ℕ :=
  (normalizedCategoryChainComplexFunctor C A).obj M

/-- Chain map on normalized category chain complexes induced by `α : M ⟶ N`. -/
abbrev normalizedCategoryChainComplexMap {M N : C ⥤ A} (α : M ⟶ N) :
    normalizedCategoryChainComplex M ⟶ normalizedCategoryChainComplex N :=
  (normalizedCategoryChainComplexFunctor C A).map α

variable (C A) in
/-- Natural inclusion of normalized category chains into `categoryChainComplexFunctor`. -/
def normalizedCategoryChainComplexInclusion :
    normalizedCategoryChainComplexFunctor C A ⟶ categoryChainComplexFunctor C A :=
  Functor.whiskerLeft (categorySimplicialObjectFunctor C A) (inclusionOfMooreComplex A)

@[simp] lemma normalizedCategoryChainComplexInclusion_app (M : C ⥤ A) :
    (normalizedCategoryChainComplexInclusion C A).app M =
      (inclusionOfMooreComplex A).app (categorySimplicialObject M) := (rfl)

/-- Dold–Kan homotopy equivalence `normalizedCategoryChainComplex M ≃ categoryChainComplex M`. -/
def normalizedCategoryChainComplexHomotopyEquiv (M : C ⥤ A) :
    HomotopyEquiv (normalizedCategoryChainComplex M) (categoryChainComplex M) :=
  DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

@[simp] lemma normalizedCategoryChainComplexHomotopyEquiv_hom (M : C ⥤ A) :
    (normalizedCategoryChainComplexHomotopyEquiv M).hom =
      (inclusionOfMooreComplex A).app (categorySimplicialObject M) := (rfl)

@[simp] lemma normalizedCategoryChainComplexHomotopyEquiv_inv (M : C ⥤ A) :
    (normalizedCategoryChainComplexHomotopyEquiv M).inv =
      DoldKan.PInftyToNormalizedMooreComplex (categorySimplicialObject M) := (rfl)

instance quasiIso_normalizedCategoryChainComplexInclusion (M : C ⥤ A) :
    QuasiIso ((normalizedCategoryChainComplexInclusion C A).app M) :=
  HomotopyEquiv.quasiIso_hom (normalizedCategoryChainComplexHomotopyEquiv M)

/-- Normalization isomorphism `(normalizedCategoryChainComplex M).homology n ≅ H_n(C, M)`. -/
def normalizedCategoryHomologyIso (M : C ⥤ A) (n : ℕ) :
    (normalizedCategoryChainComplex M).homology n ≅ categoryHomology M n :=
  (normalizedCategoryChainComplexHomotopyEquiv M).toHomologyIso n

@[simp] lemma normalizedCategoryHomologyIso_hom (M : C ⥤ A) (n : ℕ) :
    (normalizedCategoryHomologyIso M n).hom = HomologicalComplex.homologyMap
      ((inclusionOfMooreComplex A).app (categorySimplicialObject M)) n := (rfl)

@[simp] lemma normalizedCategoryHomologyIso_inv (M : C ⥤ A) (n : ℕ) :
    (normalizedCategoryHomologyIso M n).inv = HomologicalComplex.homologyMap
      (DoldKan.PInftyToNormalizedMooreComplex (categorySimplicialObject M)) n := (rfl)

@[reassoc] lemma normalizedCategoryHomologyIso_hom_naturality {M N : C ⥤ A} (α : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap (normalizedCategoryChainComplexMap α) n ≫
        (normalizedCategoryHomologyIso N n).hom =
      (normalizedCategoryHomologyIso M n).hom ≫ categoryHomologyMap α n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
      ((normalizedCategoryChainComplexInclusion C A).naturality α)).trans
      (HomologicalComplex.homologyMap_comp _ _ n))

variable (C A) in
/-- Natural isomorphism between normalized homology and `categoryHomologyFunctor C A n`. -/
def normalizedCategoryHomologyNatIso (n : ℕ) :
    normalizedCategoryChainComplexFunctor C A ⋙ HomologicalComplex.homologyFunctor A _ n ≅
      categoryHomologyFunctor C A n :=
  NatIso.ofComponents (fun M ↦ normalizedCategoryHomologyIso M n)
    (fun α ↦ normalizedCategoryHomologyIso_hom_naturality α n)

@[simp] lemma normalizedCategoryHomologyNatIso_hom_app (M : C ⥤ A) (n : ℕ) :
    (normalizedCategoryHomologyNatIso C A n).hom.app M =
      (normalizedCategoryHomologyIso M n).hom := (rfl)

@[simp] lemma normalizedCategoryHomologyNatIso_inv_app (M : C ⥤ A) (n : ℕ) :
    (normalizedCategoryHomologyNatIso C A n).inv.app M =
      (normalizedCategoryHomologyIso M n).inv := (rfl)

section Pushforward

variable {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]

/-- Covariant chain map on normalized category chain complexes along `F : C ⥤ D`. -/
def normalizedCategoryChainComplexPushforward (F : C ⥤ D) (M : D ⥤ A) :
    normalizedCategoryChainComplex (F ⋙ M) ⟶ normalizedCategoryChainComplex M :=
  (normalizedMooreComplex A).map (categorySimplicialObjectPushforward F M)

@[simp, reassoc] lemma normalizedCategoryChainComplexPushforward_comp {E : Type u₃}
    [Category.{v₃} E] [HasCoproducts.{max u₃ v₃} A] (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    normalizedCategoryChainComplexPushforward (F ⋙ G) M =
      normalizedCategoryChainComplexPushforward F (G ⋙ M) ≫
        normalizedCategoryChainComplexPushforward G M :=
  (congrArg (normalizedMooreComplex A).map (categorySimplicialObjectPushforward_comp F G M)).trans
    ((normalizedMooreComplex A).map_comp _ _)

@[reassoc] lemma normalizedCategoryChainComplexMap_whiskerLeft_pushforward (F : C ⥤ D)
    {M N : D ⥤ A} (α : M ⟶ N) :
    normalizedCategoryChainComplexMap (Functor.whiskerLeft F α) ≫
        normalizedCategoryChainComplexPushforward F N =
      normalizedCategoryChainComplexPushforward F M ≫ normalizedCategoryChainComplexMap α :=
  ((normalizedMooreComplex A).map_comp _ _).symm.trans
    ((congrArg (normalizedMooreComplex A).map
      (categorySimplicialObjectMap_whiskerLeft_pushforward F α)).trans
      ((normalizedMooreComplex A).map_comp _ _))

@[reassoc] lemma normalizedCategoryChainComplexPushforward_inclusion (F : C ⥤ D) (M : D ⥤ A) :
    normalizedCategoryChainComplexPushforward F M ≫
        (normalizedCategoryChainComplexInclusion D A).app M =
      (normalizedCategoryChainComplexInclusion C A).app (F ⋙ M) ≫
        categoryChainComplexPushforward F M :=
  (inclusionOfMooreComplex A).naturality (categorySimplicialObjectPushforward F M)

@[reassoc] lemma normalizedCategoryHomologyIso_hom_pushforward (F : C ⥤ D) (M : D ⥤ A) (n : ℕ) :
    HomologicalComplex.homologyMap (normalizedCategoryChainComplexPushforward F M) n ≫
        (normalizedCategoryHomologyIso M n).hom =
      (normalizedCategoryHomologyIso (F ⋙ M) n).hom ≫ categoryHomologyPushforward F M n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
      (normalizedCategoryChainComplexPushforward_inclusion F M)).trans
      (HomologicalComplex.homologyMap_comp _ _ n))

end Pushforward

@[simp] lemma normalizedCategoryChainComplexPushforward_id (M : C ⥤ A) :
    normalizedCategoryChainComplexPushforward (𝟭 C) M = 𝟙 (normalizedCategoryChainComplex M) :=
  (congrArg (normalizedMooreComplex A).map (categorySimplicialObjectPushforward_id M)).trans
    ((normalizedMooreComplex A).map_id _)

end Normalization

end TauCeti

namespace CategoryTheory.ShortComplex.ShortExact

open TauCeti

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Abelian A]

/-- In degree `0`, `categoryHomologyMap S.g 0 : H_0(C, M₂) ⟶ H_0(C, M₃)` is an epimorphism. -/
lemma epi_categoryHomologyMap_zero {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) :
    Epi (categoryHomologyMap S.g 0) := by
  have := hS.epi_g; exact (categoryHomologyFunctor C A 0).map_epi S.g

variable [AB4OfSize.{max u v} A]

/-- Under `AB4OfSize.{max u v} A`, `categoryChainComplexFunctor C A` preserves short exactness. -/
theorem map_categoryChainComplexFunctor {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) :
    (S.map (categoryChainComplexFunctor C A)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ShortComplex.shortExact_of_iso
    (S.mapNatIso (TauCeti.categoryChainComplexEvalIso (C := C) (A := A) n).symm)
    (hS.map_of_exact ((Functor.whiskeringLeft (Discrete (ComposableArrows C n)) C A).obj
      (Discrete.functor fun σ ↦ σ.obj 0) ⋙ colim))

/-- Connecting morphism `categoryHomology S.X₃ (n + 1) ⟶ categoryHomology S.X₁ n` of `S`. -/
def categoryHomologyδ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    categoryHomology S.X₃ (n + 1) ⟶ categoryHomology S.X₁ n :=
  hS.map_categoryChainComplexFunctor.δ (n + 1) n rfl

lemma categoryHomologyδ_def {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    hS.categoryHomologyδ n = hS.map_categoryChainComplexFunctor.δ (n + 1) n rfl := (rfl)

@[reassoc (attr := simp)] lemma categoryHomologyδ_comp {S : ShortComplex (C ⥤ A)}
    (hS : S.ShortExact) (n : ℕ) : hS.categoryHomologyδ n ≫ categoryHomologyMap S.f n = 0 :=
  hS.map_categoryChainComplexFunctor.δ_comp (n + 1) n rfl

@[reassoc (attr := simp)] lemma comp_categoryHomologyδ {S : ShortComplex (C ⥤ A)}
    (hS : S.ShortExact) (n : ℕ) : categoryHomologyMap S.g (n + 1) ≫ hS.categoryHomologyδ n = 0 :=
  hS.map_categoryChainComplexFunctor.comp_δ (n + 1) n rfl

/-- Exactness of `H_{n+1}(C, M₃) ⟶ H_n(C, M₁) ⟶ H_n(C, M₂)` in category homology. -/
lemma categoryHomology_exact₁ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (hS.categoryHomologyδ n) (categoryHomologyMap S.f n)
      (hS.categoryHomologyδ_comp n)).Exact :=
  hS.map_categoryChainComplexFunctor.homology_exact₁ (n + 1) n rfl

/-- Exactness of `H_n(C, M₁) ⟶ H_n(C, M₂) ⟶ H_n(C, M₃)` in category homology (for all `n ≥ 0`). -/
lemma categoryHomology_exact₂ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (categoryHomologyMap S.f n) (categoryHomologyMap S.g n)
      (by rw [← categoryHomologyMap_comp, S.zero]; simp [categoryHomologyMap])).Exact :=
  hS.map_categoryChainComplexFunctor.homology_exact₂ n

/-- Exactness of `H_{n+1}(C, M₂) ⟶ H_{n+1}(C, M₃) ⟶ H_n(C, M₁)` in category homology. -/
lemma categoryHomology_exact₃ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (categoryHomologyMap S.g (n + 1)) (hS.categoryHomologyδ n)
      (hS.comp_categoryHomologyδ n)).Exact :=
  hS.map_categoryChainComplexFunctor.homology_exact₃ (n + 1) n rfl

@[reassoc] lemma categoryHomologyδ_pushforward {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] [AB4OfSize.{max u₂ v₂} A] {S : ShortComplex (D ⥤ A)}
    (hS : S.ShortExact) (F : C ⥤ D) (n : ℕ)
    (hSF : (S.map ((Functor.whiskeringLeft C D A).obj F)).ShortExact :=
      hS.map_of_exact ((Functor.whiskeringLeft C D A).obj F)) :
    hSF.categoryHomologyδ n ≫ categoryHomologyPushforward F S.X₁ n =
      categoryHomologyPushforward F S.X₃ (n + 1) ≫ hS.categoryHomologyδ n :=
  HomologicalComplex.HomologySequence.δ_naturality
    { τ₁ := categoryChainComplexPushforward F S.X₁, τ₂ := categoryChainComplexPushforward F S.X₂
      τ₃ := categoryChainComplexPushforward F S.X₃
      comm₁₂ := (categoryChainComplexMap_whiskerLeft_pushforward F S.f).symm
      comm₂₃ := (categoryChainComplexMap_whiskerLeft_pushforward F S.g).symm }
    hSF.map_categoryChainComplexFunctor hS.map_categoryChainComplexFunctor (n + 1) n rfl

end CategoryTheory.ShortComplex.ShortExact

namespace TauCeti

section LongExactSequence

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Abelian A] [AB4OfSize.{max u v} A]

instance : PreservesFiniteLimits (categoryChainComplexFunctor C A) :=
  (((Functor.exact_tfae (categoryChainComplexFunctor C A)).out 1 4 rfl rfl).mp
    (fun _ hS ↦ hS.map_categoryChainComplexFunctor)).1

@[reassoc] lemma categoryHomologyδ_naturality {S₁ S₂ : ShortComplex (C ⥤ A)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (n : ℕ) :
    hS₁.categoryHomologyδ n ≫ categoryHomologyMap φ.τ₁ n =
      categoryHomologyMap φ.τ₃ (n + 1) ≫ hS₂.categoryHomologyδ n :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((categoryChainComplexFunctor C A).mapShortComplex.map φ)
    hS₁.map_categoryChainComplexFunctor hS₂.map_categoryChainComplexFunctor (n + 1) n rfl

end LongExactSequence

section ConstantCoefficients

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] [HasCoproducts.{max u v} A]

variable (C) in
/-- Identification of `categorySimplicialObject ((Functor.const C).obj X)` with
`((SimplicialObject.whiskering _ _).obj (sigmaConst.obj X)).obj (nerve C)`. -/
def categorySimplicialObjectConstIso (X : A) :
    categorySimplicialObject ((Functor.const C).obj X) ≅
      ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj X)).obj (nerve C) :=
  NatIso.ofComponents (fun Δ ↦
    { hom := descCategorySimplicial ((Functor.const C).obj X) fun σ ↦
        Limits.Sigma.ι (fun (_ : (nerve C).obj Δ) ↦ X) σ
      inv := Limits.Sigma.desc fun (σ : (nerve C).obj Δ) ↦
        ιCategorySimplicial ((Functor.const C).obj X) σ
      hom_inv_id := categorySimplicialObject_hom_ext fun σ ↦ (ιCategorySimplicial_desc_assoc _ _ σ
        _).trans ((Limits.Sigma.ι_comp_desc _ σ).trans (comp_id _).symm)
      inv_hom_id := Limits.Sigma.hom_ext _ _ fun σ ↦ (Limits.Sigma.ι_comp_desc_assoc _ σ _).trans
        ((ιCategorySimplicial_desc _ _ σ).trans (comp_id _).symm) })
    fun {Δ₁ Δ₂} θ ↦ categorySimplicialObject_hom_ext fun σ ↦ by
      dsimp [SimplicialObject.whiskering, sigmaConst]
      rw [← Quiver.Hom.op_unop θ, ιCategorySimplicial_map_assoc]
      simp only [Functor.const_obj_obj, SimplexCategory.mk_len, op_unop, homOfLE_leOfHom,
        Functor.const_obj_map, Quiver.Hom.op_unop, id_comp, ιCategorySimplicial_desc_assoc]
      exact (ιCategorySimplicial_desc ((Functor.const C).obj X) _ _).trans
        ((Limits.Sigma.ι_comp_map' (g := fun _ : (nerve C).obj Δ₁ ↦ X)
          (f := fun _ : (nerve C).obj Δ₂ ↦ X) ((nerve C).map θ) (fun _ ↦ 𝟙 X) σ).trans
          (id_comp _)).symm

@[reassoc (attr := simp)] lemma ιCategorySimplicial_categorySimplicialObjectConstIso_hom_app
    (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategorySimplicial ((Functor.const C).obj X) σ ≫
        (categorySimplicialObjectConstIso C X).hom.app (op ⦋n⦌) =
      Limits.Sigma.ι (fun (_ : (nerve C) _⦋n⦌) ↦ X) σ := by
  dsimp [categorySimplicialObjectConstIso]; exact ιCategorySimplicial_desc _ _ σ

@[reassoc (attr := simp)] lemma ι_categorySimplicialObjectConstIso_inv_app (X : A) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) : Limits.Sigma.ι (fun (_ : (nerve C) _⦋n⦌) ↦ X) σ ≫
      (categorySimplicialObjectConstIso C X).inv.app (op ⦋n⦌) =
        ιCategorySimplicial ((Functor.const C).obj X) σ := by
  dsimp [categorySimplicialObjectConstIso]; exact Limits.Sigma.ι_comp_desc _ σ

section Preadditive

variable [Preadditive A]

variable (C) in
/-- Isomorphism `categoryChainComplex ((Functor.const C).obj X) ≅ (nerve C).chainComplex X`. -/
def categoryChainComplexConstIso (X : A) :
    categoryChainComplex ((Functor.const C).obj X) ≅ (nerve C).chainComplex X :=
  (alternatingFaceMapComplex A).mapIso (categorySimplicialObjectConstIso C X)

@[reassoc (attr := simp)] lemma ιCategoryChainComplex_constIso_hom_f (X : A) {n : ℕ}
    (σ : ComposableArrows C n) :
    ιCategoryChainComplex ((Functor.const C).obj X) σ ≫
        (categoryChainComplexConstIso C X).hom.f n = (nerve C).ιChainComplex σ := by
  dsimp [categoryChainComplexConstIso, ιCategoryChainComplex, SSet.ιChainComplex]
  exact ιCategorySimplicial_categorySimplicialObjectConstIso_hom_app X σ

@[reassoc (attr := simp)] lemma ιChainComplex_categoryChainComplexConstIso_inv_f (X : A) {n : ℕ}
    (σ : ComposableArrows C n) :
    (nerve C).ιChainComplex σ ≫ (categoryChainComplexConstIso C X).inv.f n =
      ιCategoryChainComplex ((Functor.const C).obj X) σ := by
  dsimp [categoryChainComplexConstIso, ιCategoryChainComplex, SSet.ιChainComplex]
  exact ι_categorySimplicialObjectConstIso_inv_app X σ

private lemma ιChainComplex_chainComplexFunctor_map_app_nerve_f {X Y : A} (f : X ⟶ Y)
    {n : ℕ} (σ : ComposableArrows C n) :
    (nerve C).ιChainComplex σ ≫ (((SSet.chainComplexFunctor A).map f).app (nerve C)).f n =
      f ≫ (nerve C).ιChainComplex σ := by
  dsimp [SSet.chainComplexFunctor, SSet.ιChainComplex, SimplicialObject.whiskering, sigmaConst]
  exact Limits.Sigma.ι_map (fun _ : (nerve C) _⦋n⦌ ↦ f) σ

@[reassoc] lemma categoryChainComplexConstIso_hom_naturality {X Y : A} (f : X ⟶ Y) :
    categoryChainComplexMap ((Functor.const C).map f) ≫ (categoryChainComplexConstIso C Y).hom =
      (categoryChainComplexConstIso C X).hom ≫
        ((SSet.chainComplexFunctor A).map f).app (nerve C) := by
  ext n σ; simp [ιChainComplex_chainComplexFunctor_map_app_nerve_f]

@[reassoc] lemma categoryChainComplexPushforward_constIso_hom {D : Type u} [Category.{v} D]
    (F : C ⥤ D) (X : A) :
    categoryChainComplexPushforward F ((Functor.const D).obj X) ≫
        (categoryChainComplexConstIso D X).hom =
      (categoryChainComplexConstIso C X).hom ≫ SSet.chainComplexMap (nerveMap F) X := by
  ext n σ
  have happ : (nerveMap F).app (op ⦋n⦌) σ = (F.mapComposableArrows n).obj σ := by
    rw [nerveMap_app]; rfl
  simp only [HomologicalComplex.comp_f, ιCategoryChainComplex_pushforward_f_assoc,
    ιCategoryChainComplex_constIso_hom_f]
  change (nerve D).ιChainComplex ((F.mapComposableArrows n).obj σ) =
    ιCategoryChainComplex ((Functor.const C).obj X) σ ≫ _
  rw [ιCategoryChainComplex_constIso_hom_f_assoc]
  exact (congrArg (nerve D).ιChainComplex happ.symm).trans
    (SSet.ι_chainComplexMap_f (nerve C) (nerve D) (nerveMap F) X σ).symm

section CategoryWithHomology

variable [CategoryWithHomology A]

variable (C) in
/-- Isomorphism `categoryHomology ((Functor.const C).obj X) n ≅ (nerve C).homology X n`. -/
def categoryHomologyConstIso (X : A) (n : ℕ) :
    categoryHomology ((Functor.const C).obj X) n ≅ (nerve C).homology X n :=
  (HomologicalComplex.homologyFunctor A _ n).mapIso (categoryChainComplexConstIso C X)

@[simp] lemma categoryHomologyConstIso_hom (X : A) (n : ℕ) :
    (categoryHomologyConstIso C X n).hom =
      HomologicalComplex.homologyMap (categoryChainComplexConstIso C X).hom n := (rfl)

@[simp] lemma categoryHomologyConstIso_inv (X : A) (n : ℕ) :
    (categoryHomologyConstIso C X n).inv =
      HomologicalComplex.homologyMap (categoryChainComplexConstIso C X).inv n := (rfl)

@[reassoc] lemma categoryHomologyConstIso_hom_naturality {X Y : A} (f : X ⟶ Y) (n : ℕ) :
    categoryHomologyMap ((Functor.const C).map f) n ≫ (categoryHomologyConstIso C Y n).hom =
      (categoryHomologyConstIso C X n).hom ≫
        HomologicalComplex.homologyMap (((SSet.chainComplexFunctor A).map f).app (nerve C)) n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
      (categoryChainComplexConstIso_hom_naturality f)).trans
      (HomologicalComplex.homologyMap_comp _ _ n))

@[reassoc] lemma categoryHomologyPushforward_constIso_hom {D : Type u} [Category.{v} D]
    (F : C ⥤ D) (X : A) (n : ℕ) :
    categoryHomologyPushforward F ((Functor.const D).obj X) n ≫
        (categoryHomologyConstIso D X n).hom =
      (categoryHomologyConstIso C X n).hom ≫ SSet.homologyMap (nerveMap F) X n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
      (categoryChainComplexPushforward_constIso_hom F X)).trans
      (HomologicalComplex.homologyMap_comp _ _ n))

end CategoryWithHomology

end Preadditive

end ConstantCoefficients

end TauCeti
