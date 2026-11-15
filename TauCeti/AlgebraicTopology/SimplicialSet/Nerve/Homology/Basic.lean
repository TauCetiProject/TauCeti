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
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory

/-!
# Homology of a category with coefficients in a functor

For a category `C` and `M : C ⥤ A` in `A` with coproducts of size `max u v`, the simplicial object
`TauCeti.categorySimplicialObject M` has `n`-simplices
`∐ (σ : ComposableArrows C n), M.obj (σ.obj 0)` over strings `c₀ ⟶ ⋯ ⟶ cₙ` of
`CategoryTheory.nerve C`; `θ : ⦋m⦌ ⟶ ⦋n⦌` maps the `σ`-summand by `M(c₀ ⟶ c_{θ(0)})` to
`(nerve C).map θ.op σ` (`δ 0` applies `M(f₁)`, while `δ (j.succ)` and `σ i` fix `c₀`).

For preadditive `A`, the alternating-face complex `TauCeti.categoryChainComplex M` has homology
`TauCeti.categoryHomology M n` when `A` has homology, functorial in `M` and along `F : C ⥤ D` via
pushforward. For abelian `A`, Dold–Kan normalization (`TauCeti.normalizedCategoryChainComplex M`)
gives `TauCeti.normalizedCategoryHomologyIso`; under `AB4OfSize.{max u v} A`,
`TauCeti.categoryChainComplexFunctor` is exact (`TauCeti.categoryHomologyδ`); constant coefficients
recover `(nerve C).chainComplex X` and `(nerve C).homology X n` via
`TauCeti.categoryChainComplexConstIso` and `TauCeti.categoryHomologyConstIso`.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1, pp. 89–91.
* C. A. Weibel, *The K-book*, Grad. Stud. Math. 145 (2013), Chapter IV, §3.5, p. IV.28.
* P. Gabriel and M. Zisman, *Calculus of Fractions and Homotopy Theory* (1967), Appendix II, §3.
-/

public section

noncomputable section

open CategoryTheory Category Limits Opposite AlgebraicTopology

open scoped Simplicial

universe u v u₂ v₂ u₃ v₃ u' v'

namespace TauCeti

section SimplicialObject

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]

@[reducible]
private def nerveMapFn {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂)
    (σ : ComposableArrows C Δ₁.unop.len) : ComposableArrows C Δ₂.unop.len :=
  σ.whiskerLeft (SimplexCategory.toCat.map θ.unop).toFunctor

private lemma map_zero_le_zero (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.map (σ.map (homOfLE (Fin.zero_le (0 : Fin (n + 1))))) = 𝟙 (M.obj (σ.obj 0)) := by simp

variable [HasCoproducts.{max u v} A]

private def categorySimplicialObjectImpl (M : C ⥤ A) : SimplicialObject A where
  obj Δ := ∐ fun (σ : ComposableArrows C Δ.unop.len) ↦ M.obj (σ.obj 0)
  map {Δ₁ Δ₂} θ := Limits.Sigma.map' (nerveMapFn θ) fun σ ↦
    M.map (σ.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0))))
  map_id Δ := Limits.Sigma.hom_ext _ _ fun σ ↦
    (Limits.Sigma.ι_comp_map' _ _ σ).trans
      ((congrArg (· ≫ _) (map_zero_le_zero M σ)).trans ((id_comp _).trans (comp_id _).symm))
  map_comp {Δ₁ Δ₂ Δ₃} θ₁ θ₂ := Limits.Sigma.hom_ext _ _ fun σ ↦ by
    have hmap : M.map (σ.map (homOfLE (Fin.zero_le ((θ₁ ≫ θ₂).unop.toOrderHom 0)))) =
        M.map (σ.map (homOfLE (Fin.zero_le (θ₁.unop.toOrderHom 0)))) ≫
          M.map ((nerveMapFn θ₁ σ).map (homOfLE (Fin.zero_le (θ₂.unop.toOrderHom 0)))) :=
      (congrArg M.map ((congrArg σ.map (Subsingleton.elim _ _)).trans
        (σ.map_comp _ _))).trans (M.map_comp _ _)
    simp only [Limits.Sigma.ι_comp_map', Limits.Sigma.ι_comp_map'_assoc]
    exact (congrArg (· ≫ _) hmap).trans (assoc _ _ _)

private def categorySimplicialObjectMapImpl {M N : C ⥤ A} (α : M ⟶ N) :
    categorySimplicialObjectImpl M ⟶ categorySimplicialObjectImpl N where
  app Δ := Limits.Sigma.map fun (σ : ComposableArrows C Δ.unop.len) ↦ α.app (σ.obj 0)
  naturality {_ _} θ :=
    (Limits.Sigma.map'_comp_map _ _ _).trans <|
      (congrArg (Limits.Sigma.map' (nerveMapFn θ))
        (funext fun σ ↦ α.naturality (σ.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))))).trans
        (Limits.Sigma.map_comp_map' _ _ _).symm

variable (C A) in
/-- The functor `(C ⥤ A) ⥤ SimplicialObject A` sending `M` to its category simplicial object
`n ↦ ∐_{σ : ComposableArrows C n} M.obj (σ.obj 0)`. -/
def categorySimplicialObjectFunctor : (C ⥤ A) ⥤ SimplicialObject A where
  obj := categorySimplicialObjectImpl
  map := categorySimplicialObjectMapImpl
  map_id M := by
    ext Δ; exact Limits.Sigma.map_id (f := fun σ : ComposableArrows C Δ.unop.len ↦ M.obj (σ.obj 0))
  map_comp _ _ := by
    ext Δ; dsimp [categorySimplicialObjectImpl, categorySimplicialObjectMapImpl]
    exact (Limits.Sigma.map_comp_map _ _).symm

/-- The simplicial object in `A` associated to a category `C` and a functor `M : C ⥤ A`, with
`n`-simplices `∐_{σ : ComposableArrows C n} M.obj (σ.obj 0)`. Along `θ : ⦋m⦌ ⟶ ⦋n⦌`, the summand of
`σ` is transported by `M(σ(0 ≤ θ(0)))` into the summand of `(nerve C).map θ.op σ`. -/
abbrev categorySimplicialObject (M : C ⥤ A) : SimplicialObject A :=
  (categorySimplicialObjectFunctor C A).obj M

/-- The morphism of simplicial objects induced by a natural transformation `α : M ⟶ N` of
coefficient diagrams. -/
abbrev categorySimplicialObjectMap {M N : C ⥤ A} (α : M ⟶ N) :
    categorySimplicialObject M ⟶ categorySimplicialObject N :=
  (categorySimplicialObjectFunctor C A).map α

/-- The summand inclusion `M.obj (σ.obj 0) ⟶ (categorySimplicialObject M) _⦋n⦌` attached to an
`n`-simplex `σ : ComposableArrows C n` of `nerve C`. -/
def ιCategorySimplicial (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categorySimplicialObject M) _⦋n⦌ :=
  Limits.Sigma.ι (fun (τ : ComposableArrows C n) ↦ M.obj (τ.obj 0)) σ

/-- Two morphisms out of `(categorySimplicialObject M) _⦋n⦌` agree when they agree on every
simplex summand. -/
@[ext]
lemma categorySimplicialObject_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (categorySimplicialObject M) _⦋n⦌ ⟶ T}
    (h : ∀ σ : ComposableArrows C n,
      ιCategorySimplicial M σ ≫ f = ιCategorySimplicial M σ ≫ g) : f = g :=
  Limits.Sigma.hom_ext _ _ h

/-- Action of a simplicial operator `θ : ⦋m⦌ ⟶ ⦋n⦌` on the summand of `σ` in
`categorySimplicialObject M`. -/
@[reassoc]
lemma ιCategorySimplicial_map (M : C ⥤ A) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (σ : ComposableArrows C n) :
    ιCategorySimplicial M σ ≫ (categorySimplicialObject M).map θ.op =
      M.map (σ.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))) ≫
        ιCategorySimplicial M ((nerve C).map θ.op σ) :=
  Limits.Sigma.ι_comp_map' _ _ σ

/-- The zeroth face `δ 0` on `categorySimplicialObject M` transports the coefficient along the
first arrow `σ.obj 0 ⟶ σ.obj (Fin.succ 0)` and drops the initial vertex of `σ`. -/
@[reassoc (attr := simp)]
lemma ιCategorySimplicial_δ_zero (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ιCategorySimplicial M σ ≫ (categorySimplicialObject M).δ 0 =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
        ιCategorySimplicial M ((nerve C).δ 0 σ) :=
  ιCategorySimplicial_map M (SimplexCategory.δ (0 : Fin (n + 2))) σ

/-- Every positive face `δ (j.succ)` on `categorySimplicialObject M` fixes the initial vertex `0`,
hence acts as the identity on `M.obj (σ.obj 0)` while applying `(nerve C).δ j.succ` to `σ`. -/
@[reassoc (attr := simp)]
lemma ιCategorySimplicial_δ_succ (M : C ⥤ A) {n : ℕ} (j : Fin (n + 1))
    (σ : ComposableArrows C (n + 1)) :
    ιCategorySimplicial M σ ≫ (categorySimplicialObject M).δ j.succ =
      ιCategorySimplicial M ((nerve C).δ j.succ σ) :=
  (ιCategorySimplicial_map M (SimplexCategory.δ j.succ) σ).trans
    ((congrArg (· ≫ _) (map_zero_le_zero M σ)).trans (id_comp _))

/-- The final face `δ (Fin.last (n + 1))` deletes the last vertex of `σ` without changing the
coefficient in `M.obj (σ.obj 0)`. -/
@[reassoc]
lemma ιCategorySimplicial_δ_last (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ιCategorySimplicial M σ ≫ (categorySimplicialObject M).δ (Fin.last (n + 1)) =
      ιCategorySimplicial M ((nerve C).δ (Fin.last (n + 1)) σ) :=
  ιCategorySimplicial_δ_succ M (Fin.last n) σ

/-- Every degeneracy `σ i` on `categorySimplicialObject M` fixes the initial vertex `0`, hence acts
as the identity on `M.obj (σ.obj 0)` and inserts an identity arrow in `σ`. -/
@[reassoc (attr := simp)]
lemma ιCategorySimplicial_σ (M : C ⥤ A) {n : ℕ} (i : Fin (n + 1)) (σ : ComposableArrows C n) :
    ιCategorySimplicial M σ ≫ (categorySimplicialObject M).σ i =
      ιCategorySimplicial M ((nerve C).σ i σ) :=
  (ιCategorySimplicial_map M (SimplexCategory.σ i) σ).trans
    ((congrArg (· ≫ _) (map_zero_le_zero M σ)).trans (id_comp _))

/-- Component of `categorySimplicialObjectMap α` on the summand of an `n`-simplex `σ`. -/
@[reassoc (attr := simp)]
lemma ιCategorySimplicial_map_app {M N : C ⥤ A} (α : M ⟶ N) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategorySimplicial M σ ≫ (categorySimplicialObjectMap α).app (op ⦋n⦌) =
      α.app (σ.obj 0) ≫ ιCategorySimplicial N σ :=
  Limits.Sigma.ι_map (fun τ : ComposableArrows C n ↦ α.app (τ.obj 0)) σ

/-- Covariant pushforward of simplicial objects along a functor `F : C ⥤ D`: on degree `n`, it maps
the summand of `σ : ComposableArrows C n` identically on `M.obj (F.obj (σ.obj 0))` into the summand
of `(F.mapComposableArrows n).obj σ`. -/
def categorySimplicialObjectPushforward {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) :
    categorySimplicialObject (F ⋙ M) ⟶ categorySimplicialObject M where
  app Δ := Limits.Sigma.map' (F.mapComposableArrows Δ.unop.len).obj fun _ ↦ 𝟙 _
  naturality {_ _} _ := by
    dsimp [categorySimplicialObjectFunctor, categorySimplicialObjectImpl]
    refine (Limits.Sigma.map'_comp_map' _ _ _ _).trans
      (Eq.trans ?_ (Limits.Sigma.map'_comp_map' _ _ _ _).symm)
    exact congrArg (Limits.Sigma.map' _) (funext fun _ ↦ (comp_id _).trans (id_comp _).symm)

/-- Action of `categorySimplicialObjectPushforward F M` on the summand of `σ`. -/
@[reassoc (attr := simp)]
lemma ιCategorySimplicial_pushforward_app {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategorySimplicial (F ⋙ M) σ ≫
        (categorySimplicialObjectPushforward F M).app (op ⦋n⦌) =
      ιCategorySimplicial M ((F.mapComposableArrows n).obj σ) :=
  (Limits.Sigma.ι_comp_map' (g := fun τ : ComposableArrows C n ↦ M.obj (F.obj (τ.obj 0)))
    (f := fun τ : ComposableArrows D n ↦ M.obj (τ.obj 0))
    (F.mapComposableArrows n).obj (fun _ ↦ 𝟙 _) σ).trans (id_comp _)

/-- Pushing forward along `𝟭 C` is the identity on `categorySimplicialObject M`. -/
@[simp]
lemma categorySimplicialObjectPushforward_id (M : C ⥤ A) :
    categorySimplicialObjectPushforward (𝟭 C) M = 𝟙 (categorySimplicialObject M) := by
  ext Δ
  exact Limits.Sigma.map'_id_id (f := fun σ : ComposableArrows C Δ.unop.len ↦ M.obj (σ.obj 0))

/-- Pushing forward along a composite functor `F ⋙ G` factors as the composite of pushforwards. -/
@[simp, reassoc]
lemma categorySimplicialObjectPushforward_comp {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] {E : Type u₃} [Category.{v₃} E]
    [HasCoproducts.{max u₃ v₃} A] (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    categorySimplicialObjectPushforward (F ⋙ G) M =
      categorySimplicialObjectPushforward F (G ⋙ M) ≫
        categorySimplicialObjectPushforward G M := by
  ext Δ
  dsimp [categorySimplicialObjectFunctor, categorySimplicialObjectImpl,
    categorySimplicialObjectPushforward]
  refine Eq.trans ?_ (Limits.Sigma.map'_comp_map' _ _ _ _).symm
  exact congrArg (Limits.Sigma.map' _) (funext fun _ ↦ (id_comp _).symm)

/-- Pushforward along `F : C ⥤ D` commutes with coefficient transformations `α : M ⟶ N`. -/
@[reassoc]
lemma categorySimplicialObjectMap_whiskerLeft_pushforward {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) :
    categorySimplicialObjectMap (Functor.whiskerLeft F α) ≫
        categorySimplicialObjectPushforward F N =
      categorySimplicialObjectPushforward F M ≫ categorySimplicialObjectMap α := by
  ext ⟨⟨n⟩⟩ σ; simp

end SimplicialObject

/-! ### Alternating-face category chain complex -/

section ChainComplex

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Preadditive A]

instance (C : Type u) [Category.{v} C] (A : Type u') [Category.{v'} A]
    [HasCoproducts.{max u v} A] [Preadditive A] :
    (categorySimplicialObjectFunctor C A).Additive where
  map_add {_ _} _ _ := by ext ⟨⟨n⟩⟩ σ; simp [NatTrans.app_add]

variable (C A) in
/-- The functor `(C ⥤ A) ⥤ ChainComplex A ℕ` sending `M` to its category chain complex. -/
@[expose]
def categoryChainComplexFunctor : (C ⥤ A) ⥤ ChainComplex A ℕ :=
  categorySimplicialObjectFunctor C A ⋙ alternatingFaceMapComplex A

instance : (categoryChainComplexFunctor C A).Additive := by
  unfold categoryChainComplexFunctor; infer_instance

/-- The alternating-face chain complex of a category `C` with coefficients in `M : C ⥤ A`. In
degree `n`, `(categoryChainComplex M).X n` is `∐_{σ : ComposableArrows C n} M.obj (σ.obj 0)`. -/
abbrev categoryChainComplex (M : C ⥤ A) : ChainComplex A ℕ :=
  (categoryChainComplexFunctor C A).obj M

/-- The chain map `categoryChainComplex M ⟶ categoryChainComplex N` induced by `α : M ⟶ N`. -/
abbrev categoryChainComplexMap {M N : C ⥤ A} (α : M ⟶ N) :
    categoryChainComplex M ⟶ categoryChainComplex N :=
  (categoryChainComplexFunctor C A).map α

/-- The summand inclusion `M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X n` at `σ`. -/
def ιCategoryChainComplex (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X n :=
  ιCategorySimplicial M σ

/-- `ιCategoryChainComplex` agrees with the simplicial summand inclusion `ιCategorySimplicial`. -/
lemma ιCategoryChainComplex_eq (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ = ιCategorySimplicial M σ := (rfl)

/-- Transporting the simplex index along an equality `σ₁ = σ₂` in `ιCategoryChainComplex M`. -/
lemma ιCategoryChainComplex_congr (M : C ⥤ A) {n : ℕ} {σ₁ σ₂ : ComposableArrows C n}
    (h : σ₁ = σ₂) (h0 : σ₁.obj 0 = σ₂.obj 0 := by exact congrArg (fun τ ↦ τ.obj 0) h) :
    ιCategoryChainComplex M σ₁ = eqToHom (congrArg M.obj h0) ≫ ιCategoryChainComplex M σ₂ := by
  subst h; simp

/-- Rewrite `eqToHom _ ≫ ιCategoryChainComplex M σ₁` along `h : σ₁ = σ₂`. -/
lemma eqToHom_ιCategoryChainComplex_eq (M : C ⥤ A) {n : ℕ}
    {σ₁ σ₂ : ComposableArrows C n} (h : σ₁ = σ₂) (h0 : σ₁.obj 0 = σ₂.obj 0 := by rfl) :
    eqToHom (congrArg M.obj h0.symm) ≫ ιCategoryChainComplex M σ₁ =
      ιCategoryChainComplex M σ₂ := by
  subst h; simp

/-- The cofan presenting `(categoryChainComplex M).X n` as a coproduct over `n`-simplices. -/
def categoryChainComplexXCofan (M : C ⥤ A) (n : ℕ) :
    Cofan (fun (σ : ComposableArrows C n) ↦ M.obj (σ.obj 0)) :=
  Cofan.mk ((categoryChainComplex M).X n) (ιCategoryChainComplex M)

/-- `(categoryChainComplex M).X n` is the coproduct of `M.obj (σ.obj 0)` over `n`-simplices `σ`. -/
def isColimitCategoryChainComplexXCofan (M : C ⥤ A) (n : ℕ) :
    IsColimit (categoryChainComplexXCofan M n) := coproductIsCoproduct _

/-- Universal morphism out of `(categoryChainComplex M).X n` specified on each simplex summand. -/
def descCategoryChainComplex (M : C ⥤ A) {n : ℕ} {T : A}
    (f : ∀ σ : ComposableArrows C n, M.obj (σ.obj 0) ⟶ T) : (categoryChainComplex M).X n ⟶ T :=
  Cofan.IsColimit.desc (isColimitCategoryChainComplexXCofan M n) f

@[reassoc (attr := simp)]
lemma ιCategoryChainComplex_desc (M : C ⥤ A) {n : ℕ} {T : A}
    (f : ∀ σ : ComposableArrows C n, M.obj (σ.obj 0) ⟶ T) (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ ≫ descCategoryChainComplex M f = f σ :=
  Cofan.IsColimit.fac (isColimitCategoryChainComplexXCofan M n) f σ

/-- Morphisms out of `(categoryChainComplex M).X n` are determined on every simplex summand. -/
@[ext]
lemma categoryChainComplex_hom_ext {M : C ⥤ A} {n : ℕ} {T : A}
    {f g : (categoryChainComplex M).X n ⟶ T}
    (h : ∀ σ : ComposableArrows C n,
      ιCategoryChainComplex M σ ≫ f = ιCategoryChainComplex M σ ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (isColimitCategoryChainComplexXCofan M n) _ _ h

/-- Alternating-face differential of `categoryChainComplex M` on an `(n + 1)`-simplex `σ`: `δ 0`
transports along `σ.obj 0 ⟶ σ.obj (Fin.succ 0)` and `δ (j.succ)` acts with sign `(-1) ^ (j + 1)`. -/
@[reassoc]
lemma ιCategoryChainComplex_d (M : C ⥤ A) {n : ℕ} (σ : ComposableArrows C (n + 1)) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplex M).d (n + 1) n =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
          ιCategoryChainComplex M ((nerve C).δ 0 σ) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
          (ιCategoryChainComplex M ((nerve C).δ j.succ σ) :
            M.obj (σ.obj 0) ⟶ (categoryChainComplex M).X n) :=
  (congrArg (ιCategorySimplicial M σ ≫ ·) (alternatingFaceMapComplex_obj_d _ n)).trans <|
    (Preadditive.comp_sum _ _ _).trans <| (Fin.sum_univ_succ _).trans <|
      congrArg₂ (· + ·)
        ((Preadditive.comp_zsmul _ _ _).trans
          ((one_zsmul _).trans (ιCategorySimplicial_δ_zero M σ)))
        (Finset.sum_congr rfl fun j _ ↦
          (Preadditive.comp_zsmul _ _ _).trans
            (congrArg ((-1 : ℤ) ^ (j.val + 1) • ·) (ιCategorySimplicial_δ_succ M j σ)))

/-- Degree-`0` chain summand inclusion `M.obj X ⟶ (categoryChainComplex M).X 0` at `X : C`. -/
abbrev ιCategoryChainComplex₀ (M : C ⥤ A) (X : C) : M.obj X ⟶ (categoryChainComplex M).X 0 :=
  ιCategoryChainComplex M (ComposableArrows.mk₀ X)

/-- Degree-`1` chain summand inclusion `M.obj X ⟶ (categoryChainComplex M).X 1` at `f : X ⟶ Y`. -/
abbrev ιCategoryChainComplex₁ (M : C ⥤ A) {X Y : C} (f : X ⟶ Y) :
    M.obj X ⟶ (categoryChainComplex M).X 1 := ιCategoryChainComplex M (ComposableArrows.mk₁ f)

/-- Degree-`2` chain summand inclusion at a composable pair `f : X ⟶ Y`, `g : Y ⟶ Z`. -/
abbrev ιCategoryChainComplex₂ (M : C ⥤ A) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    M.obj X ⟶ (categoryChainComplex M).X 2 := ιCategoryChainComplex M (ComposableArrows.mk₂ f g)

/-- Universal morphism out of `(categoryChainComplex M).X 0` from components `M.obj X ⟶ T`. -/
def descCategoryChainComplex₀ (M : C ⥤ A) {T : A} (f : ∀ X : C, M.obj X ⟶ T) :
    (categoryChainComplex M).X 0 ⟶ T := descCategoryChainComplex M fun σ ↦ f (σ.obj 0)

@[reassoc (attr := simp)]
lemma ιCategoryChainComplex₀_desc₀ (M : C ⥤ A) {T : A} (f : ∀ X : C, M.obj X ⟶ T) (X : C) :
    ιCategoryChainComplex₀ M X ≫ descCategoryChainComplex₀ M f = f X :=
  ιCategoryChainComplex_desc M (fun σ ↦ f (σ.obj 0)) (ComposableArrows.mk₀ X)

/-- Morphisms out of `(categoryChainComplex M).X 0` are determined on `ιCategoryChainComplex₀`. -/
lemma categoryChainComplex₀_hom_ext {M : C ⥤ A} {T : A} {f g : (categoryChainComplex M).X 0 ⟶ T}
    (h : ∀ X : C, ιCategoryChainComplex₀ M X ≫ f = ιCategoryChainComplex₀ M X ≫ g) : f = g := by
  ext σ; obtain ⟨X, rfl⟩ := ComposableArrows.mk₀_surjective σ; exact h X

/-- On `ComposableArrows.mk₁ f` (`f : X ⟶ Y`), `d 1 0` sends `m ∈ M(X)` to `M(f)(m) - m`. -/
@[reassoc (attr := simp)]
lemma ιCategoryChainComplex₁_d (M : C ⥤ A) {X Y : C} (f : X ⟶ Y) :
    ιCategoryChainComplex₁ M f ≫ (categoryChainComplex M).d 1 0 =
      M.map f ≫ ιCategoryChainComplex₀ M Y - ιCategoryChainComplex₀ M X := by
  have h0 : ιCategoryChainComplex M ((nerve C).δ 0 (.mk₁ f)) = ιCategoryChainComplex₀ M Y :=
    (ιCategoryChainComplex_congr M
      (ComposableArrows.ext₀ rfl : (nerve C).δ 0 (.mk₁ f) = .mk₀ Y) rfl).trans (id_comp _)
  have h1 : (ιCategoryChainComplex M ((nerve C).δ 1 (.mk₁ f)) :
      M.obj X ⟶ (categoryChainComplex M).X 0) = ιCategoryChainComplex₀ M X :=
    (ιCategoryChainComplex_congr M
      (ComposableArrows.ext₀ rfl : (nerve C).δ 1 (.mk₁ f) = .mk₀ X) rfl).trans (id_comp _)
  calc ιCategoryChainComplex₁ M f ≫ (categoryChainComplex M).d 1 0
    _ = _ := ιCategoryChainComplex_d M (.mk₁ f)
    _ = M.map f ≫ ιCategoryChainComplex₀ M Y + -ιCategoryChainComplex₀ M X :=
        congrArg₂ (· + ·) (by simp [h0])
          ((Fin.sum_univ_one _).trans ((neg_one_zsmul _).trans (congrArg Neg.neg h1)))
    _ = _ := by abel

/-- On `ComposableArrows.mk₂ f g`, `d 2 1` is `M(f)` on `g`, minus `f ≫ g`, plus `f`. -/
@[reassoc (attr := simp)]
lemma ιCategoryChainComplex₂_d (M : C ⥤ A) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ιCategoryChainComplex₂ M f g ≫ (categoryChainComplex M).d 2 1 =
      M.map f ≫ ιCategoryChainComplex₁ M g -
        ιCategoryChainComplex₁ M (f ≫ g) + ιCategoryChainComplex₁ M f := by
  have h0 : ιCategoryChainComplex M ((nerve C).δ 0 (.mk₂ f g)) = ιCategoryChainComplex₁ M g :=
    (ιCategoryChainComplex_congr M (nerve.δ₀_mk₂_eq f g) rfl).trans (id_comp _)
  have h1 : (ιCategoryChainComplex M ((nerve C).δ 1 (.mk₂ f g)) :
      M.obj X ⟶ (categoryChainComplex M).X 1) = ιCategoryChainComplex₁ M (f ≫ g) :=
    (ιCategoryChainComplex_congr M (nerve.δ₁_mk₂_eq f g) rfl).trans (id_comp _)
  have h2 : (ιCategoryChainComplex M ((nerve C).δ 2 (.mk₂ f g)) :
      M.obj X ⟶ (categoryChainComplex M).X 1) = ιCategoryChainComplex₁ M f :=
    (ιCategoryChainComplex_congr M (nerve.δ₂_mk₂_eq f g) rfl).trans (id_comp _)
  calc ιCategoryChainComplex₂ M f g ≫ (categoryChainComplex M).d 2 1
    _ = _ := ιCategoryChainComplex_d M (.mk₂ f g)
    _ = M.map f ≫ ιCategoryChainComplex₁ M g +
          (-ιCategoryChainComplex₁ M (f ≫ g) + ιCategoryChainComplex₁ M f) :=
        congrArg₂ (· + ·) (by simp [h0]) ((Fin.sum_univ_two _).trans
          (congrArg₂ (· + ·) ((neg_one_zsmul _).trans (congrArg Neg.neg h1))
            ((one_zsmul _).trans h2)))
    _ = _ := by abel

/-- Action of `categoryChainComplexMap α` on the summand of an `n`-simplex `σ`. -/
@[reassoc (attr := simp)]
lemma ιCategoryChainComplex_map_f {M N : C ⥤ A} (α : M ⟶ N) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex M σ ≫ (categoryChainComplexMap α).f n =
      α.app (σ.obj 0) ≫ ιCategoryChainComplex N σ :=
  ιCategorySimplicial_map_app α σ

@[reassoc (attr := simp)]
lemma ιCategoryChainComplex₀_map_f {M N : C ⥤ A} (α : M ⟶ N) (X : C) :
    ιCategoryChainComplex₀ M X ≫ (categoryChainComplexMap α).f 0 =
      α.app X ≫ ιCategoryChainComplex₀ N X :=
  ιCategoryChainComplex_map_f α (ComposableArrows.mk₀ X)

/-- Covariant chain map `categoryChainComplex (F ⋙ M) ⟶ categoryChainComplex M` along `F`. -/
def categoryChainComplexPushforward {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) :
    categoryChainComplex (F ⋙ M) ⟶ categoryChainComplex M :=
  (alternatingFaceMapComplex A).map (categorySimplicialObjectPushforward F M)

/-- Action of `categoryChainComplexPushforward F M` in degree `n` on the summand of `σ`. -/
@[reassoc (attr := simp)]
lemma ιCategoryChainComplex_pushforward_f {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex (F ⋙ M) σ ≫ (categoryChainComplexPushforward F M).f n =
      ιCategoryChainComplex M ((F.mapComposableArrows n).obj σ) :=
  ιCategorySimplicial_pushforward_app F M σ

@[reassoc (attr := simp)]
lemma ιCategoryChainComplex₀_pushforward_f {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) (M : D ⥤ A) (X : C) :
    ιCategoryChainComplex₀ (F ⋙ M) X ≫ (categoryChainComplexPushforward F M).f 0 =
      ιCategoryChainComplex₀ M (F.obj X) :=
  (ιCategoryChainComplex_pushforward_f F M (.mk₀ X)).trans <|
    (ιCategoryChainComplex_congr M
      (ComposableArrows.ext₀ rfl : (F.mapComposableArrows 0).obj (.mk₀ X) = .mk₀ (F.obj X))
      rfl).trans (id_comp _)

/-- Pushing forward chains along the identity functor `𝟭 C` is the identity chain map. -/
@[simp]
lemma categoryChainComplexPushforward_id (M : C ⥤ A) :
    categoryChainComplexPushforward (𝟭 C) M = 𝟙 (categoryChainComplex M) :=
  (congrArg (alternatingFaceMapComplex A).map (categorySimplicialObjectPushforward_id M)).trans
    ((alternatingFaceMapComplex A).map_id _)

/-- Pushing forward chains along `F ⋙ G` is the composite of the pushforward chain maps. -/
@[simp, reassoc]
lemma categoryChainComplexPushforward_comp {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] {E : Type u₃} [Category.{v₃} E]
    [HasCoproducts.{max u₃ v₃} A] (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) :
    categoryChainComplexPushforward (F ⋙ G) M =
      categoryChainComplexPushforward F (G ⋙ M) ≫ categoryChainComplexPushforward G M :=
  (congrArg (alternatingFaceMapComplex A).map
    (categorySimplicialObjectPushforward_comp F G M)).trans
    ((alternatingFaceMapComplex A).map_comp _ _)

/-- Pushforward of category chains along `F : C ⥤ D` commutes with coefficient maps `α : M ⟶ N`. -/
@[reassoc]
lemma categoryChainComplexMap_whiskerLeft_pushforward {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) :
    categoryChainComplexMap (Functor.whiskerLeft F α) ≫ categoryChainComplexPushforward F N =
      categoryChainComplexPushforward F M ≫ categoryChainComplexMap α :=
  ((alternatingFaceMapComplex A).map_comp _ _).symm.trans
    ((congrArg (alternatingFaceMapComplex A).map
      (categorySimplicialObjectMap_whiskerLeft_pushforward F α)).trans
      ((alternatingFaceMapComplex A).map_comp _ _))

end ChainComplex

/-! ### Category homology -/

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

/-- `categoryHomologyMap` preserves identity natural transformations. -/
@[simp]
lemma categoryHomologyMap_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyMap (𝟙 M) n = 𝟙 (categoryHomology M n) := by simp [categoryHomologyMap]

/-- `categoryHomologyMap` preserves composition of natural transformations. -/
@[reassoc]
lemma categoryHomologyMap_comp {M N P : C ⥤ A} (α : M ⟶ N) (β : N ⟶ P) (n : ℕ) :
    categoryHomologyMap (α ≫ β) n = categoryHomologyMap α n ≫ categoryHomologyMap β n := by
  simp [categoryHomologyMap, ← HomologicalComplex.homologyMap_comp]

/-- Covariant map `categoryHomology (F ⋙ M) n ⟶ categoryHomology M n` induced by `F : C ⥤ D`. -/
abbrev categoryHomologyPushforward {D : Type u₂} [Category.{v₂} D] [HasCoproducts.{max u₂ v₂} A]
    (F : C ⥤ D) (M : D ⥤ A) (n : ℕ) : categoryHomology (F ⋙ M) n ⟶ categoryHomology M n :=
  HomologicalComplex.homologyMap (categoryChainComplexPushforward F M) n

/-- Pushing forward category homology along `𝟭 C` is the identity morphism. -/
@[simp]
lemma categoryHomologyPushforward_id (M : C ⥤ A) (n : ℕ) :
    categoryHomologyPushforward (𝟭 C) M n = 𝟙 (categoryHomology M n) :=
  (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
    (categoryChainComplexPushforward_id M)).trans (HomologicalComplex.homologyMap_id _ n)

/-- Pushing forward category homology along `F ⋙ G` factors as the composite of pushforwards. -/
@[reassoc]
lemma categoryHomologyPushforward_comp {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] {E : Type u₃} [Category.{v₃} E] [HasCoproducts.{max u₃ v₃} A]
    (F : C ⥤ D) (G : D ⥤ E) (M : E ⥤ A) (n : ℕ) :
    categoryHomologyPushforward (F ⋙ G) M n =
      categoryHomologyPushforward F (G ⋙ M) n ≫ categoryHomologyPushforward G M n := by
  simp [categoryHomologyPushforward, ← HomologicalComplex.homologyMap_comp]

/-- Pushforward in category homology along `F : C ⥤ D` is natural in `M : D ⥤ A`. -/
@[reassoc]
lemma categoryHomologyMap_whiskerLeft_pushforward {D : Type u₂} [Category.{v₂} D]
    [HasCoproducts.{max u₂ v₂} A] (F : C ⥤ D) {M N : D ⥤ A} (α : M ⟶ N) (n : ℕ) :
    categoryHomologyMap (Functor.whiskerLeft F α) n ≫ categoryHomologyPushforward F N n =
      categoryHomologyPushforward F M n ≫ categoryHomologyMap α n := by
  simp only [categoryHomologyMap, categoryHomologyPushforward,
    ← HomologicalComplex.homologyMap_comp, categoryChainComplexMap_whiskerLeft_pushforward]

end Homology

/-! ### Normalization via Dold–Kan -/

section Normalization

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Abelian A]

variable (C A) in
/-- Normalized Moore complex functor `(C ⥤ A) ⥤ ChainComplex A ℕ` on `categorySimplicialObject`. -/
def normalizedCategoryChainComplexFunctor : (C ⥤ A) ⥤ ChainComplex A ℕ :=
  categorySimplicialObjectFunctor C A ⋙ normalizedMooreComplex A

/-- The normalized category chain complex of `(C, M)`. -/
abbrev normalizedCategoryChainComplex (M : C ⥤ A) : ChainComplex A ℕ :=
  (normalizedCategoryChainComplexFunctor C A).obj M

variable (C A) in
/-- Natural inclusion of normalized category chains into `categoryChainComplexFunctor`. -/
def normalizedCategoryChainComplexInclusion :
    normalizedCategoryChainComplexFunctor C A ⟶ categoryChainComplexFunctor C A :=
  Functor.whiskerLeft (categorySimplicialObjectFunctor C A) (inclusionOfMooreComplex A)

/-- Dold–Kan homotopy equivalence `normalizedCategoryChainComplex M ≃ categoryChainComplex M`. -/
def normalizedCategoryChainComplexHomotopyEquiv (M : C ⥤ A) :
    HomotopyEquiv (normalizedCategoryChainComplex M) (categoryChainComplex M) :=
  DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

@[simp]
lemma normalizedCategoryChainComplexHomotopyEquiv_hom (M : C ⥤ A) :
    (normalizedCategoryChainComplexHomotopyEquiv M).hom =
      (normalizedCategoryChainComplexInclusion C A).app M := (rfl)

/-- Normalization of `categoryChainComplex M` is a quasi-isomorphism in every degree. -/
instance quasiIso_normalizedCategoryChainComplexInclusion (M : C ⥤ A) :
    QuasiIso ((normalizedCategoryChainComplexInclusion C A).app M) :=
  HomotopyEquiv.quasiIso_hom (normalizedCategoryChainComplexHomotopyEquiv M)

/-- Normalization isomorphism `(normalizedCategoryChainComplex M).homology n ≅ H_n(C, M)`. -/
def normalizedCategoryHomologyIso (M : C ⥤ A) (n : ℕ) :
    (normalizedCategoryChainComplex M).homology n ≅ categoryHomology M n :=
  (normalizedCategoryChainComplexHomotopyEquiv M).toHomologyIso n

/-- Naturality of `normalizedCategoryHomologyIso` in `α : M ⟶ N`. -/
@[reassoc]
lemma normalizedCategoryHomologyIso_hom_naturality {M N : C ⥤ A} (α : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap ((normalizedCategoryChainComplexFunctor C A).map α) n ≫
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

@[simp]
lemma normalizedCategoryHomologyNatIso_hom_app (M : C ⥤ A) (n : ℕ) :
    (normalizedCategoryHomologyNatIso C A n).hom.app M = (normalizedCategoryHomologyIso M n).hom :=
  (rfl)

@[simp]
lemma normalizedCategoryHomologyNatIso_inv_app (M : C ⥤ A) (n : ℕ) :
    (normalizedCategoryHomologyNatIso C A n).inv.app M = (normalizedCategoryHomologyIso M n).inv :=
  (rfl)

end Normalization

/-! ### Exactness and the long exact sequence in coefficients -/

section LongExactSequence

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A] [Abelian A] [AB4OfSize.{max u v} A]

/-- Under `AB4OfSize.{max u v} A`, `categoryChainComplexFunctor C A` preserves short exactness. -/
theorem categoryChainComplex_shortExact {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) :
    (S.map (categoryChainComplexFunctor C A)).ShortExact := by
  have := hS.mono_f; have := hS.epi_g
  have hmono_app (X : C) : Mono (S.f.app X) := ((evaluation C A).obj X).map_mono S.f
  have hexact_n (n : ℕ) :
      (S.map (categoryChainComplexFunctor C A ⋙ HomologicalComplex.eval A _ n)).Exact := by
    let Sₙ : ShortComplex (Discrete (ComposableArrows C n) ⥤ A) :=
      ShortComplex.mk (X₁ := Discrete.functor fun σ ↦ S.X₁.obj (σ.obj 0))
        (X₂ := Discrete.functor fun σ ↦ S.X₂.obj (σ.obj 0))
        (X₃ := Discrete.functor fun σ ↦ S.X₃.obj (σ.obj 0))
        (Discrete.natTrans fun ⟨σ⟩ ↦ S.f.app (σ.obj 0))
        (Discrete.natTrans fun ⟨σ⟩ ↦ S.g.app (σ.obj 0))
        (by ext ⟨σ⟩; exact NatTrans.congr_app S.zero (σ.obj 0))
    have hSₙ : Sₙ.Exact := (ShortComplex.exact_iff_evaluation Sₙ).2 fun ⟨σ⟩ ↦
      ShortComplex.exact_of_iso
        (ShortComplex.isoMk (.refl _) (.refl _) (.refl _) (by simp [Sₙ]) (by simp [Sₙ]))
        ((ShortComplex.exact_iff_evaluation S).1 hS.exact (σ.obj 0))
    exact ShortComplex.exact_of_iso
      (ShortComplex.isoMk (.refl _) (.refl _) (.refl _) (by simp) (by simp))
      (colim.exact_mapShortComplex hSₙ
        (isColimitCategoryChainComplexXCofan S.X₁ n) (isColimitCategoryChainComplexXCofan S.X₂ n)
        (isColimitCategoryChainComplexXCofan S.X₃ n) ((categoryChainComplexMap S.f).f n)
        ((categoryChainComplexMap S.g).f n) (fun ⟨σ⟩ ↦ ιCategoryChainComplex_map_f S.f σ)
        (fun ⟨σ⟩ ↦ ιCategoryChainComplex_map_f S.g σ))
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    { exact := hexact_n n
      mono_f := by
        have (σ : ComposableArrows C n) : Mono (S.f.app (σ.obj 0)) := hmono_app (σ.obj 0)
        exact inferInstanceAs (Mono (Limits.Sigma.map fun σ : ComposableArrows C n ↦
          S.f.app (σ.obj 0)))
      epi_g := ⟨fun _ _ h ↦ categoryChainComplex_hom_ext fun σ ↦ by
        have : Epi (S.g.app (σ.obj 0)) := ((evaluation C A).obj (σ.obj 0)).map_epi S.g
        exact (cancel_epi (S.g.app (σ.obj 0))).1 (by simpa using ιCategoryChainComplex _ σ ≫= h)⟩ }

instance : PreservesFiniteLimits (categoryChainComplexFunctor C A) :=
  (((Functor.exact_tfae (categoryChainComplexFunctor C A)).out 1 4 rfl rfl).mp
    (fun _ hS ↦ categoryChainComplex_shortExact hS)).1

instance : PreservesFiniteColimits (categoryChainComplexFunctor C A) :=
  (((Functor.exact_tfae (categoryChainComplexFunctor C A)).out 1 4 rfl rfl).mp
    (fun _ hS ↦ categoryChainComplex_shortExact hS)).2

/-- The connecting morphism `categoryHomology S.X₃ (n + 1) ⟶ categoryHomology S.X₁ n` associated to
a short exact sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of coefficient functors `C ⥤ A`. -/
def categoryHomologyδ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    categoryHomology S.X₃ (n + 1) ⟶ categoryHomology S.X₁ n :=
  (categoryChainComplex_shortExact hS).δ (n + 1) n rfl

@[reassoc (attr := simp)]
lemma categoryHomologyδ_comp {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    categoryHomologyδ hS n ≫ categoryHomologyMap S.f n = 0 :=
  (categoryChainComplex_shortExact hS).δ_comp (n + 1) n rfl

@[reassoc (attr := simp)]
lemma comp_categoryHomologyδ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    categoryHomologyMap S.g (n + 1) ≫ categoryHomologyδ hS n = 0 :=
  (categoryChainComplex_shortExact hS).comp_δ (n + 1) n rfl

/-- Exactness of `H_{n+1}(C, M₃) ⟶ H_n(C, M₁) ⟶ H_n(C, M₂)` in category homology. -/
lemma categoryHomology_exact₁ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (categoryHomologyδ hS n) (categoryHomologyMap S.f n)
      (categoryHomologyδ_comp hS n)).Exact :=
  (categoryChainComplex_shortExact hS).homology_exact₁ (n + 1) n rfl

/-- Exactness of `H_n(C, M₁) ⟶ H_n(C, M₂) ⟶ H_n(C, M₃)` in category homology (for all `n ≥ 0`). -/
lemma categoryHomology_exact₂ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (categoryHomologyMap S.f n) (categoryHomologyMap S.g n)
      (by rw [← categoryHomologyMap_comp, S.zero]; simp [categoryHomologyMap])).Exact :=
  (categoryChainComplex_shortExact hS).homology_exact₂ n

/-- Exactness of `H_{n+1}(C, M₂) ⟶ H_{n+1}(C, M₃) ⟶ H_n(C, M₁)` in category homology. -/
lemma categoryHomology_exact₃ {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (categoryHomologyMap S.g (n + 1)) (categoryHomologyδ hS n)
      (comp_categoryHomologyδ hS n)).Exact :=
  (categoryChainComplex_shortExact hS).homology_exact₃ (n + 1) n rfl

/-- In degree `0`, `categoryHomologyMap S.g 0 : H_0(C, M₂) ⟶ H_0(C, M₃)` is an epimorphism. -/
lemma epi_categoryHomologyMap_zero {S : ShortComplex (C ⥤ A)} (hS : S.ShortExact) :
    Epi (categoryHomologyMap S.g 0) := by
  let K := S.map (categoryChainComplexFunctor C A)
  have := (categoryChainComplex_shortExact hS).epi_g
  have h0 (L : ChainComplex A ℕ) : IsIso (L.homologyι 0) :=
    ShortComplex.isIso_homologyι (L.sc 0) (L.shape 0 _ (by simp))
  have := epi_of_epi_fac (HomologicalComplex.p_opcyclesMap K.g 0)
  have hnat : categoryHomologyMap S.g 0 ≫ K.X₃.homologyι 0 =
      K.X₂.homologyι 0 ≫ HomologicalComplex.opcyclesMap K.g 0 :=
    HomologicalComplex.homologyι_naturality K.g 0
  have := h0 K.X₂; have := h0 K.X₃
  exact (epi_comp_iff_of_isIso (categoryHomologyMap S.g 0) (K.X₃.homologyι 0)).1
    (by rw [hnat]; infer_instance)

/-- Naturality of `categoryHomologyδ` with respect to morphisms of short exact sequences. -/
@[reassoc]
lemma categoryHomologyδ_naturality {S₁ S₂ : ShortComplex (C ⥤ A)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (n : ℕ) :
    categoryHomologyδ hS₁ n ≫ categoryHomologyMap φ.τ₁ n =
      categoryHomologyMap φ.τ₃ (n + 1) ≫ categoryHomologyδ hS₂ n :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((categoryChainComplexFunctor C A).mapShortComplex.map φ)
    (categoryChainComplex_shortExact hS₁) (categoryChainComplex_shortExact hS₂) (n + 1) n rfl

end LongExactSequence

/-! ### Comparison with `(nerve C).chainComplex` for constant coefficients -/

section ConstantCoefficients

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{max u v} A]

variable (C) in
/-- For a constant coefficient diagram at `X : A`,
`categorySimplicialObject ((Functor.const C).obj X)` identifies with the simplicial object
`n ↦ ∐_{(nerve C) _⦋n⦌} X` underlying `(nerve C).chainComplex X`. -/
def categorySimplicialObjectConstIso (X : A) :
    categorySimplicialObject ((Functor.const C).obj X) ≅
      ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj X)).obj (nerve C) :=
  NatIso.ofComponents
    (fun Δ ↦
      { hom := Limits.Sigma.desc fun (σ : ComposableArrows C Δ.unop.len) ↦
          Limits.Sigma.ι (fun (_ : (nerve C).obj Δ) ↦ X) σ
        inv := Limits.Sigma.desc fun (σ : (nerve C).obj Δ) ↦
          Limits.Sigma.ι (fun (_ : ComposableArrows C Δ.unop.len) ↦ X) σ
        hom_inv_id := Limits.Sigma.hom_ext _ _ fun σ ↦ (Limits.Sigma.ι_comp_desc_assoc _ σ _).trans
          ((Limits.Sigma.ι_comp_desc _ σ).trans (comp_id _).symm)
        inv_hom_id := Limits.Sigma.hom_ext _ _ fun σ ↦ (Limits.Sigma.ι_comp_desc_assoc _ σ _).trans
          ((Limits.Sigma.ι_comp_desc _ σ).trans (comp_id _).symm) })
    (fun {Δ₁ Δ₂} θ ↦ by
      dsimp [categorySimplicialObjectFunctor, categorySimplicialObjectImpl]
      refine Limits.Sigma.hom_ext _ _ fun σ ↦ (Limits.Sigma.ι_comp_map'_assoc _ _ σ _).trans
        ((congrArg (· ≫ _) (Functor.const_obj_map C X _)).trans ((id_comp _).trans ?_))
      refine (Limits.Sigma.ι_comp_desc (f := fun _ : ComposableArrows C Δ₂.unop.len ↦ X) _ _).trans
        (((Limits.Sigma.ι_comp_desc_assoc (f := fun _ : ComposableArrows C Δ₁.unop.len ↦ X)
          (fun τ ↦ Limits.Sigma.ι (fun _ : (nerve C).obj Δ₁ ↦ X) τ) σ _).trans ?_).symm)
      exact (Limits.Sigma.ι_comp_map' (g := fun _ : (nerve C).obj Δ₁ ↦ X)
        (f := fun _ : (nerve C).obj Δ₂ ↦ X) (ConcreteCategory.hom ((nerve C).map θ))
        (fun _ ↦ 𝟙 X) σ).trans (id_comp _))

section Preadditive

variable [Preadditive A]

variable (C) in
/-- For a constant functor at `X : A`, `categoryChainComplex ((Functor.const C).obj X)` is
canonically isomorphic to the simplicial chain complex `(nerve C).chainComplex X`. -/
def categoryChainComplexConstIso (X : A) :
    categoryChainComplex ((Functor.const C).obj X) ≅ (nerve C).chainComplex X :=
  (alternatingFaceMapComplex A).mapIso (categorySimplicialObjectConstIso C X)

/-- `categoryChainComplexConstIso` identifies the simplex summand inclusion of
`categoryChainComplex` with `SSet.ιChainComplex` on `nerve C`. -/
@[reassoc (attr := simp)]
lemma ιCategoryChainComplex_constIso_hom_f (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    ιCategoryChainComplex ((Functor.const C).obj X) σ ≫
        (categoryChainComplexConstIso C X).hom.f n = (nerve C).ιChainComplex σ :=
  Limits.Sigma.ι_comp_desc (f := fun _ : ComposableArrows C n ↦ X)
    (fun τ : ComposableArrows C n ↦ Limits.Sigma.ι (fun _ : (nerve C) _⦋n⦌ ↦ X) τ) σ

@[reassoc (attr := simp)]
lemma ιChainComplex_constIso_inv_f (X : A) {n : ℕ} (σ : ComposableArrows C n) :
    (nerve C).ιChainComplex σ ≫ (categoryChainComplexConstIso C X).inv.f n =
      ιCategoryChainComplex ((Functor.const C).obj X) σ :=
  Limits.Sigma.ι_comp_desc (f := fun _ : (nerve C) _⦋n⦌ ↦ X)
    (fun τ : (nerve C) _⦋n⦌ ↦ Limits.Sigma.ι (fun _ : ComposableArrows C n ↦ X) τ) σ

/-- Naturality of `categoryChainComplexConstIso` with respect to morphisms `f : X ⟶ Y` in `A`. -/
@[reassoc]
lemma categoryChainComplexConstIso_hom_naturality {X Y : A} (f : X ⟶ Y) :
    categoryChainComplexMap ((Functor.const C).map f) ≫ (categoryChainComplexConstIso C Y).hom =
      (categoryChainComplexConstIso C X).hom ≫
        ((SSet.chainComplexFunctor A).map f).app (nerve C) := by
  ext n σ
  exact (ιCategoryChainComplex_map_f_assoc ((Functor.const C).map f) σ _).trans
    ((congrArg (f ≫ ·) (ιCategoryChainComplex_constIso_hom_f Y σ)).trans
      ((Limits.Sigma.ι_map (fun _ : (nerve C) _⦋n⦌ ↦ f) σ).symm.trans
        (ιCategoryChainComplex_constIso_hom_f_assoc X σ _).symm))

/-- Compatibility of `categoryChainComplexConstIso` with a functor `F : C ⥤ D` and `nerveMap F`. -/
@[reassoc]
lemma categoryChainComplexPushforward_constIso_hom {D : Type u} [Category.{v} D]
    (F : C ⥤ D) (X : A) :
    categoryChainComplexPushforward F ((Functor.const D).obj X) ≫
        (categoryChainComplexConstIso D X).hom =
      (categoryChainComplexConstIso C X).hom ≫ SSet.chainComplexMap (nerveMap F) X := by
  ext n σ
  exact (ιCategoryChainComplex_pushforward_f_assoc F ((Functor.const D).obj X) σ _).trans
    ((ιCategoryChainComplex_constIso_hom_f X ((F.mapComposableArrows n).obj σ)).trans
      ((SSet.ι_chainComplexMap_f (nerve C) (nerve D) (nerveMap F) X σ).symm.trans
        (ιCategoryChainComplex_constIso_hom_f_assoc X σ _).symm))

section CategoryWithHomology

variable [CategoryWithHomology A]

variable (C) in
/-- For a constant functor at `X : A`, `categoryHomology ((Functor.const C).obj X) n` is
canonically isomorphic to `(nerve C).homology X n`. -/
def categoryHomologyConstIso (X : A) (n : ℕ) :
    categoryHomology ((Functor.const C).obj X) n ≅ (nerve C).homology X n :=
  (HomologicalComplex.homologyFunctor A _ n).mapIso (categoryChainComplexConstIso C X)

@[simp]
lemma categoryHomologyConstIso_hom (X : A) (n : ℕ) :
    (categoryHomologyConstIso C X n).hom =
      HomologicalComplex.homologyMap (categoryChainComplexConstIso C X).hom n := (rfl)

@[simp]
lemma categoryHomologyConstIso_inv (X : A) (n : ℕ) :
    (categoryHomologyConstIso C X n).inv =
      HomologicalComplex.homologyMap (categoryChainComplexConstIso C X).inv n := (rfl)

/-- Naturality of `categoryHomologyConstIso` in the constant coefficient `X : A`. -/
@[reassoc]
lemma categoryHomologyConstIso_hom_naturality {X Y : A} (f : X ⟶ Y) (n : ℕ) :
    categoryHomologyMap ((Functor.const C).map f) n ≫ (categoryHomologyConstIso C Y n).hom =
      (categoryHomologyConstIso C X n).hom ≫
        HomologicalComplex.homologyMap (((SSet.chainComplexFunctor A).map f).app (nerve C)) n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n)
      (categoryChainComplexConstIso_hom_naturality f)).trans
      (HomologicalComplex.homologyMap_comp _ _ n))

/-- Compatibility of `categoryHomologyConstIso` with `F : C ⥤ D` and `nerveMap F`. -/
@[reassoc]
lemma categoryHomologyPushforward_constIso_hom {D : Type u} [Category.{v} D]
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
