/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# The preadditive Yoneda and coYoneda functors

For a preadditive category `C`, the preadditive Yoneda embedding sends `Y : C` to the functor
`(-, Y) : Cᵒᵖ ⥤ AddCommGrpCat`. This file records how it acts on morphisms, and four facts
about it.

* The embedding is itself additive: `preadditiveYoneda.map (f + g)` is the sum of the images.
* A natural transformation out of `(-, Y)` is determined by its value on `𝟙 Y`, by the Yoneda
  lemma. No additivity of the target functor is needed.
* A morphism `(-, Y) ⟶ F` lifts along every epimorphism `(-, Y') ⟶ F` to the image of a morphism
  `Y ⟶ Y'`. This is the form in which representable functors are projective that is used to
  build presentations of finitely presented functors.
* A sequence `(-, W) ⟶ (-, Z) ⟶ F` whose first map is `(-, w)` is exact exactly when every
  morphism `z : V ⟶ Z` killed by the second map factors through `w`. So exactness at a
  representable functor is a factorization property in `C`.

Dually, for an object `M` with `Γ = End M`, the functor `Hom(M, -)` (Mathlib's
`CategoryTheory.preadditiveCoyonedaObj M`) takes values in `Γᵐᵒᵖ`-modules. By the Yoneda
argument, it is bijective on the morphisms `M ⟶ Y`: a `Γᵐᵒᵖ`-linear map
`φ : Hom(M, M) → Hom(M, Y)` is composition with `φ (𝟙 M)`, since
`φ f = φ (f • 𝟙 M) = f ≫ φ (𝟙 M)`.

For an additive functor `G : C ⥤ D`, Mathlib's natural transformation
`CategoryTheory.preadditiveYonedaMap G X : (-, X) ⟶ (G -, G X)` is an epimorphism when `G` is
full, and the morphisms `f` with `(-, f)` killed by it are those killed by `G`. For the quotient
functor by an ideal `I` of `C`, its target is the quotient `(-, X) / I(-, X)`.

Dually, for an additive functor `G : C ⥤ Ab` corepresented by an object `P`, the bijection
`(P ⟶ X) ≃ G(X)` of the corepresentation is additive: it preserves zero, and so does its inverse,
which is moreover additive.

## Main declarations

* `CategoryTheory.preadditiveYoneda_map_app_apply`: the natural transformation `(-, f)` acts by
  postcomposition with `f`, and `CategoryTheory.preadditiveYoneda_obj_map_apply` the functor
  `(-, X)` by precomposition.
* `CategoryTheory.preadditiveYoneda_additive`: the preadditive Yoneda embedding is additive.
* `CategoryTheory.preadditiveYoneda_obj_hom_ext`: morphisms out of `(-, Y)` agreeing on `𝟙 Y`
  are equal.
* `CategoryTheory.exists_preadditiveYoneda_map_comp_eq`: lifting along an epimorphism out of a
  representable functor.
* `CategoryTheory.preadditiveCoyonedaObj_map_bijective_self`: `Hom(M, -)` is bijective on the
  morphisms out of `M`.
* `CategoryTheory.preadditiveYonedaMap_app_apply`: the natural transformation
  `(-, X) ⟶ (G -, G X)` acts by applying `G`.
* `CategoryTheory.preadditiveYoneda_map_comp_preadditiveYonedaMap_eq_zero_iff`: the natural
  transformation `(-, X) ⟶ (G -, G X)` kills `(-, f)` exactly when `G` kills `f`.
* `CategoryTheory.exact_preadditiveYoneda_map_iff`: exactness at a representable functor.
* `CategoryTheory.Functor.CorepresentableBy.homEquiv_zero` and
  `CategoryTheory.Functor.CorepresentableBy.homEquiv_symm_zero`: the corepresentation and its
  inverse preserve zero.
* `CategoryTheory.Functor.CorepresentableBy.homEquiv_symm_add`: the inverse of the
  corepresentation is additive.
-/

public section

universe t v u u'

open Opposite CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The natural transformation `(-, f) : (-, X) ⟶ (-, Y)` is postcomposition with `f`. -/
@[simp]
theorem preadditiveYoneda_map_app_apply {X Y : C} (f : X ⟶ Y) (Z : Cᵒᵖ) (g : Z.unop ⟶ X) :
    (preadditiveYoneda.map f).app Z g = g ≫ f :=
  rfl

/-- The functor `(-, X)` acts on morphisms by precomposition. -/
@[simp]
theorem preadditiveYoneda_obj_map_apply {X : C} {Z W : Cᵒᵖ} (f : Z ⟶ W) (g : Z.unop ⟶ X) :
    (preadditiveYoneda.obj X).map f g = f.unop ≫ g :=
  rfl

/-- Two morphisms out of the representable functor `(-, Y)` agree as soon as they agree on the
identity of `Y`. -/
theorem preadditiveYoneda_obj_hom_ext {Y : C} {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    {α β : preadditiveYoneda.obj Y ⟶ F} (h : α.app (op Y) (𝟙 Y) = β.app (op Y) (𝟙 Y)) :
    α = β :=
  ((Functor.whiskeringRight Cᵒᵖ _ _).obj (forget AddCommGrpCat)).map_injective
    (yonedaEquiv.injective h)

/-- The preadditive Yoneda embedding `Y ↦ (-, Y)` is an additive functor. -/
instance preadditiveYoneda_additive :
    (preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{v}).Additive where
  map_add {_ _ f g} := by
    -- An element of `(preadditiveYoneda.obj X).obj Z` is a morphism `h : Z.unop ⟶ X` and
    -- `(-, f)` sends it to `h ≫ f` (`preadditiveYoneda_map_app_apply`), so additivity is
    -- distributivity of composition.
    ext Z (h : Z.unop ⟶ _)
    exact Preadditive.comp_add _ _ _ h f g

/-- A morphism from a representable functor `(-, Y)` to `F` lifts along any epimorphism
`(-, Y') ⟶ F`, and the lift is the image of a morphism `Y ⟶ Y'`. -/
theorem exists_preadditiveYoneda_map_comp_eq {Y Y' : C} {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (p : preadditiveYoneda.obj Y' ⟶ F) [Epi p] (α : preadditiveYoneda.obj Y ⟶ F) :
    ∃ u : Y ⟶ Y', preadditiveYoneda.map u ≫ p = α := by
  obtain ⟨u, hu⟩ :=
    (AddCommGrpCat.epi_iff_surjective (p.app (op Y))).1 inferInstance (α.app (op Y) (𝟙 Y))
  refine ⟨u, preadditiveYoneda_obj_hom_ext ?_⟩
  exact (congrArg (p.app (op Y))
    ((preadditiveYoneda_map_app_apply u (op Y) (𝟙 Y)).trans (Category.id_comp u))).trans hu

/-- **Yoneda for `Hom(M, -)` as a `Γᵐᵒᵖ`-module, `Γ = End M`.** Composition identifies the
morphisms `M ⟶ Y` with the `Γᵐᵒᵖ`-linear maps `Hom(M, M) → Hom(M, Y)`: a linear map `φ` is
composition with `φ (𝟙 M)`. -/
theorem preadditiveCoyonedaObj_map_bijective_self (M Y : C) :
    Function.Bijective ((preadditiveCoyonedaObj M).map : (M ⟶ Y) → _) := by
  -- The elements of `(preadditiveCoyonedaObj M).obj X` are the morphisms `M ⟶ X`, and
  -- `(preadditiveCoyonedaObj M).map g` acts on them by composition with `g`; both facts hold by
  -- definition, so the steps below are stated as equalities of morphisms of `C`.
  refine ⟨fun g g' h ↦ ?_, fun φ ↦ ⟨φ.hom (𝟙 M), ?_⟩⟩
  · exact (Category.id_comp g).symm.trans (congr(($h).hom (𝟙 M)).trans (Category.id_comp g'))
  · let ψ : (M ⟶ M) →ₗ[(End M)ᵐᵒᵖ] (M ⟶ Y) := φ.hom
    have key (f : M ⟶ M) : f ≫ ψ (𝟙 M) = ψ f :=
      calc f ≫ ψ (𝟙 M) = MulOpposite.op (End.of f) • ψ (𝟙 M) :=
            (End.smul_left (r := .op (.of f)) (f := ψ (𝟙 M))).symm
        _ = ψ (MulOpposite.op (End.of f) • 𝟙 M) := (ψ.map_smul _ _).symm
        _ = ψ f := congrArg ψ ((End.smul_left (r := .op (.of f)) (f := 𝟙 M)).trans
            (Category.comp_id f))
    ext f
    exact key f

/-! ### The natural transformation `(-, X) ⟶ (G -, G X)` induced by an additive functor -/

section preadditiveYonedaMap

variable {D : Type u'} [Category.{v} D] [Preadditive D] (G : C ⥤ D) [G.Additive]

/-- The natural transformation `(-, X) ⟶ (G -, G X)` applies `G`. -/
theorem preadditiveYonedaMap_app_apply (X : C) (Z : Cᵒᵖ) (g : Z.unop ⟶ X) :
    (preadditiveYonedaMap G X).app Z g = G.map g :=
  rfl

/-- The natural transformation `(-, X) ⟶ (G -, G X)` is an epimorphism when `G` is full. -/
instance epi_preadditiveYonedaMap [G.Full] (X : C) : Epi (preadditiveYonedaMap G X) := by
  have (Z : Cᵒᵖ) : Epi ((preadditiveYonedaMap G X).app Z) :=
    (AddCommGrpCat.epi_iff_surjective _).2 fun g ↦ ⟨G.preimage g, G.map_preimage g⟩
  exact NatTrans.epi_of_epi_app _

/-- The natural transformation `(-, X) ⟶ (G -, G X)` kills `(-, f)` exactly when `G` kills `f`. -/
@[simp]
theorem preadditiveYoneda_map_comp_preadditiveYonedaMap_eq_zero_iff {Y X : C}
    (f : Y ⟶ X) : preadditiveYoneda.map f ≫ preadditiveYonedaMap G X = 0 ↔ G.map f = 0 := by
  -- Both sides are read off on `𝟙 Y`, where `(-, f)` followed by the transformation gives
  -- `G.map (𝟙 Y ≫ f)`.
  have key : (preadditiveYoneda.map f ≫ preadditiveYonedaMap G X).app (op Y) (𝟙 Y) = G.map f := by
    rw [NatTrans.comp_app]
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    rw [preadditiveYoneda_map_app_apply, preadditiveYonedaMap_app_apply, Category.id_comp]
  -- Stated for an abstract element: `simp` cannot rewrite at `𝟙 Y`, whose type `Y ⟶ Y` is only
  -- definitionally the carrier of `(-, Y)` at `op Y`.
  have hzero (x : (preadditiveYoneda.obj Y).obj (op Y)) :
      (0 : preadditiveYoneda.obj Y ⟶ G.op ⋙ preadditiveYoneda.obj (G.obj X)).app (op Y) x = 0 := by
    simp
  refine ⟨fun h ↦ ?_, fun h ↦ preadditiveYoneda_obj_hom_ext ?_⟩
  · exact key.symm.trans ((congrArg (fun α ↦ α.app (op Y) (𝟙 Y)) h).trans (hzero _))
  · exact key.trans (h.trans (hzero _).symm)

end preadditiveYonedaMap

/-- A sequence `(-, W) ⟶ (-, Z) ⟶ F` whose first map is `(-, w)` is exact exactly when every
morphism `z : V ⟶ Z` killed by `α` factors through `w`. -/
theorem exact_preadditiveYoneda_map_iff {W Z : C} (w : W ⟶ Z) {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (α : preadditiveYoneda.obj Z ⟶ F) (h : preadditiveYoneda.map w ≫ α = 0) :
    (ShortComplex.mk _ _ h).Exact ↔
      ∀ ⦃V : C⦄ (z : V ⟶ Z), α.app (op V) z = 0 → ∃ x : V ⟶ W, x ≫ w = z := by
  -- Exactness in the functor category is exactness at each object, which in `AddCommGrpCat`
  -- is the elementwise statement `ShortComplex.ab_exact_iff`; there `(-, w)` sends `x` to
  -- `x ≫ w` (`preadditiveYoneda_map_app_apply`).
  have key : ∀ V : C,
      ((ShortComplex.mk _ _ h).map ((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op V))).Exact ↔
        ∀ z : V ⟶ Z, α.app (op V) z = 0 → ∃ x : V ⟶ W, x ≫ w = z := fun V ↦
    ShortComplex.ab_exact_iff _
  refine ⟨fun hS V ↦ (key V).1 (hS.map _), fun H ↦ ?_⟩
  rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
  intro V
  refine IsZero.of_iso ?_ ((ShortComplex.mk _ _ h).mapHomologyIso
    ((evaluation Cᵒᵖ AddCommGrpCat.{v}).obj V)).symm
  rw [← ShortComplex.exact_iff_isZero_homology]
  exact (key V.unop).2 (@H V.unop)

namespace Functor.CorepresentableBy

variable {G : C ⥤ AddCommGrpCat.{t}} [G.Additive]
  {P : C} (R : (G ⋙ forget AddCommGrpCat).CorepresentableBy P)

/-- The corepresentation of an additive functor `G : C ⥤ Ab` sends the zero morphism to zero. -/
lemma homEquiv_zero {X : C} : R.homEquiv (0 : P ⟶ X) = (0 : G.obj X) := by
  rw [R.homEquiv_eq, Functor.comp_map, G.map_zero]
  rfl

/-- The inverse of the corepresentation of an additive functor `G : C ⥤ Ab` sends zero to the zero
morphism. -/
lemma homEquiv_symm_zero {X : C} : R.homEquiv.symm (0 : G.obj X) = 0 :=
  R.homEquiv.symm_apply_eq.2 R.homEquiv_zero.symm

/-- The inverse of the corepresentation `(P ⟶ X) ≃ G(X)` of an additive functor `G : C ⥤ Ab` is
additive. -/
lemma homEquiv_symm_add {X : C} (x y : G.obj X) :
    R.homEquiv.symm (x + y) = R.homEquiv.symm x + R.homEquiv.symm y := by
  have h (z : G.obj X) : G.map (R.homEquiv.symm z) (R.homEquiv (𝟙 P)) = z :=
    (R.homEquiv_eq _).symm.trans (R.homEquiv.apply_symm_apply z)
  rw [R.homEquiv.symm_apply_eq, R.homEquiv_eq, Functor.comp_map, G.map_add]
  exact (congrArg₂ (· + ·) (h x) (h y)).symm

end Functor.CorepresentableBy

end CategoryTheory
