/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import TauCeti.AlgebraicTopology.SimplicialSet.Homotopy
public import TauCeti.AlgebraicTopology.SimplicialSet.PiZero
public import TauCeti.AlgebraicTopology.SimplicialSet.WeaklyContractible

/-!
# Simplicial homotopies, products, and connected components of nerves

A natural transformation `η : F₀ ⟶ F₁` induces `η.nerveHomotopy : SSet.Homotopy (nerveMap F₀)
(nerveMap F₁)`, showing that categories with an initial or terminal object have weakly contractible
nerves. We also construct `CategoryTheory.nerve.discreteIso`, `CategoryTheory.nerve.prodIso`,
`CategoryTheory.nerve.asSmallIso`, and `CategoryTheory.nerve.π₀EquivConnectedComponents`.

## References

* D. Quillen, *Higher algebraic K-theory: I*, Lecture Notes in Math. 341 (1973), §1.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Chapter I, §1.
-/

public section

universe w v u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial

namespace SSet.IsWeaklyContractible

/-- A simplicial set with a homotopy from `𝟙 K` to `SSet.const x` is weakly contractible via
precomposition on the Kan complex `Fun(K, Z)`. -/
lemma of_homotopy_id_const {K : SSet.{u}} {x : K _⦋0⦌} (H : SSet.Homotopy (𝟙 K) (SSet.const x)) :
    SSet.IsWeaklyContractible K where
  exists_homotopyInverse Z _ := by
    let φ : (ihom K).obj Z ⊗ Δ[1] ⟶ (ihom K).obj Z :=
      MonoidalClosed.curry (lift (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ H.h)
        (snd _ _ ≫ fst _ _) ≫ (ihom.ev K).app Z)
    have hlift (i : Δ[1] _⦋0⦌) :
        lift (𝟙 _) (SSet.const i) ≫ φ =
          MonoidalClosed.curry (lift (fst _ _ ≫ lift (𝟙 K) (SSet.const i) ≫ H.h) (snd _ _) ≫
            (ihom.ev K).app Z) := by
      have hi : K ◁ lift (𝟙 ((ihom K).obj Z)) (SSet.const i) ≫
          lift (fst _ _) (snd _ _ ≫ snd _ _) = fst _ _ ≫ lift (𝟙 K) (SSet.const i) := by
        ext : 1 <;> simp
      rw [← MonoidalClosed.curry_natural_left]
      simp [comp_lift_assoc, reassoc_of% hi]
    have h₀ : ι₀ ≫ φ = 𝟙 _ := by
      rw [ι₀, hlift, ← ι₀, H.h₀]; simp [← MonoidalClosed.uncurry_id_eq_ev]
    have h₁ : ι₁ ≫ φ = evalAt x Z ≫ constMaps K Z := by
      rw [ι₁, hlift, ← ι₁, H.h₁, evalAt_constMaps, evalAt_eq, comp_lift_assoc]; simp
    exact ⟨evalAt x Z, ⟨.ofEq (congrArg _ (constMaps_evalAt K x Z))⟩,
      (Homotopy.mk' φ h₀ h₁).nonempty_symm⟩

end SSet.IsWeaklyContractible

namespace CategoryTheory

local macro "functor_ext_rfl" : term =>
  `(CategoryTheory.Functor.ext (fun _ ↦ rfl)
    fun _ _ _ ↦ ((Category.id_comp _).trans (Category.comp_id _)).symm)

section Functoriality

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]

/-- `nerveMap` sends the identity functor to the identity morphism of `nerve C`. -/
@[simp]
lemma nerveMap_id (C : Type u) [Category.{v} C] : nerveMap (𝟭 C) = 𝟙 (nerve C) := by
  ext n σ : 4; exact functor_ext_rfl

/-- `nerveMap` sends composite functors to composite morphisms of simplicial sets. -/
@[simp, reassoc]
lemma nerveMap_comp (F : C ⥤ D) (G : D ⥤ E) : nerveMap (F ⋙ G) = nerveMap F ≫ nerveMap G := by
  ext n σ : 4; exact functor_ext_rfl

/-- `nerveMap` of a constant functor at `d` is the constant simplicial map at the vertex `d`. -/
@[simp]
lemma nerveMap_const (C : Type u) [Category.{v} C] {D : Type u} [Category.{v} D] (d : D) :
    nerveMap ((Functor.const C).obj d) = SSet.const (nerveEquiv.symm d) := by
  ext ⟨n⟩ σ : 4; induction n using SimplexCategory.rec with | _ n => exact functor_ext_rfl

/-- `nerveMap F` maps the vertex `nerveEquiv.symm c` to `nerveEquiv.symm (F.obj c)`. -/
@[simp]
lemma nerveMap_app_zero_nerveEquiv_symm (F : C ⥤ D) (c : C) :
    (nerveMap F).app (op ⦋0⦌) (nerveEquiv.symm c) = nerveEquiv.symm (F.obj c) :=
  nerveMap_app_mk₀ F c

/-- `nerveMap F` maps the edge `nerve.edgeMk f` to `nerve.edgeMk (F.map f)`. -/
lemma nerveMap_app_one_edgeMk {x y : C} (F : C ⥤ D) (f : x ⟶ y) :
    (nerveMap F).app (op ⦋1⦌) (nerve.edgeMk f).edge = (nerve.edgeMk (F.map f)).edge :=
  nerveMap_app_mk₁ F f

/-- Push a simplex of `nerve C` forward along a functor `F : C ⥤ D` across arbitrary universes,
typed syntactically in `(nerve D).obj n`. -/
@[expose]
def Functor.mapNerveObj {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {n : SimplexCategoryᵒᵖ} (σ : (nerve C).obj n) : (nerve D).obj n :=
  σ ⋙ F

@[simp]
lemma Functor.id_mapNerveObj {C : Type*} [Category* C] {n : SimplexCategoryᵒᵖ}
    (σ : (nerve C).obj n) : (𝟭 C).mapNerveObj σ = σ :=
  CategoryTheory.Functor.comp_id σ

@[simp]
lemma Functor.comp_mapNerveObj {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) {n : SimplexCategoryᵒᵖ}
    (σ : (nerve C).obj n) : (F ⋙ G).mapNerveObj σ = G.mapNerveObj (F.mapNerveObj σ) :=
  (CategoryTheory.Functor.assoc σ F G).symm

/-- `Functor.mapNerveObj` carries the edge `nerve.edgeMk f` to `nerve.edgeMk (F.map f)`. -/
lemma Functor.mapNerveObj_edgeMk {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {x y : C} (f : x ⟶ y) :
    F.mapNerveObj (nerve.edgeMk f).edge = (nerve.edgeMk (F.map f)).edge :=
  ComposableArrows.ext₁ rfl rfl
    (((Category.id_comp (F.map f ≫ 𝟙 _)).trans (Category.comp_id (F.map f))).symm)

end Functoriality

namespace nerve

/-- The nerve of the discrete category `Discrete ι` is naturally isomorphic to the constant
simplicial set on `ι`. -/
def discreteIso (ι : Type u) :
    nerve (Discrete ι) ≅ (Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun σ := (σ.obj 0).as, invFun i := (Functor.const _).obj ⟨i⟩
      left_inv σ := ext_of_isThin <| funext fun k ↦
        Discrete.ext (Discrete.eq_of_hom (σ.map (homOfLE (Fin.zero_le k))))
      right_inv _ := rfl })
    fun _ ↦ by ext σ; exact (Discrete.eq_of_hom (σ.map (homOfLE (Fin.zero_le _)))).symm

@[simp]
lemma discreteIso_hom_app_apply (ι : Type u) {n : SimplexCategoryᵒᵖ}
    (σ : (nerve (Discrete ι)).obj n) :
    dsimp% (discreteIso ι).hom.app n σ = (σ.obj 0).as := (rfl)

@[simp]
lemma discreteIso_inv_app_obj (ι : Type u) {n : SimplexCategoryᵒᵖ} (i : ι)
    (k : Fin (n.unop.len + 1)) :
    dsimp% (((discreteIso ι).inv.app n i).obj k) = ⟨i⟩ := (rfl)

lemma discreteIso_hom_app_nerveEquiv_symm (ι : Type u) (i : Discrete ι) :
    (discreteIso ι).hom.app (op ⦋0⦌) (nerveEquiv.symm i) = i.as := (rfl)

@[simp]
lemma discreteIso_inv_app_zero (ι : Type u) (i : ι) :
    dsimp% (discreteIso ι).inv.app (op ⦋0⦌) i = nerveEquiv.symm ⟨i⟩ :=
  ComposableArrows.ext₀ rfl

/-- The nerve of a product category `C × D` is naturally isomorphic to the Cartesian product
`nerve C ⊗ nerve D`. -/
def prodIso (C D : Type u) [Category.{v} C] [Category.{v} D] :
    nerve (C × D) ≅ (nerve C ⊗ nerve D : SSet.{max u v}) :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun σ := (σ ⋙ CategoryTheory.Prod.fst C D, σ ⋙ CategoryTheory.Prod.snd C D)
      invFun p := p.1.prod' p.2, left_inv _ := functor_ext_rfl
      right_inv _ := Prod.ext functor_ext_rfl functor_ext_rfl }) fun _ ↦ rfl

@[simp]
lemma prodIso_hom_app_fst (C D : Type u) [Category.{v} C] [Category.{v} D]
    {n : SimplexCategoryᵒᵖ} (σ : (nerve (C × D)).obj n) :
    dsimp% ((prodIso C D).hom.app n σ).1 = σ ⋙ CategoryTheory.Prod.fst C D := (rfl)

@[simp]
lemma prodIso_hom_app_snd (C D : Type u) [Category.{v} C] [Category.{v} D]
    {n : SimplexCategoryᵒᵖ} (σ : (nerve (C × D)).obj n) :
    dsimp% ((prodIso C D).hom.app n σ).2 = σ ⋙ CategoryTheory.Prod.snd C D := (rfl)

@[simp]
lemma prodIso_inv_app_apply (C D : Type u) [Category.{v} C] [Category.{v} D]
    {n : SimplexCategoryᵒᵖ} (p : (nerve C ⊗ nerve D : SSet.{max u v}).obj n) :
    dsimp% (prodIso C D).inv.app n p = p.1.prod' p.2 := (rfl)

/-- The nerve of `AsSmall.{w} C` is naturally isomorphic to the universe lift
`SSet.uliftFunctor.obj (nerve C)`. -/
def asSmallIso (C : Type u) [Category.{v} C] :
    nerve (AsSmall.{w} C) ≅ SSet.uliftFunctor.{w, max u v}.obj (nerve C) :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun σ := ULift.up (AsSmall.down.mapNerveObj σ), invFun τ := AsSmall.up.mapNerveObj τ.down
      left_inv _ := functor_ext_rfl, right_inv _ := ULift.ext functor_ext_rfl }) fun _ ↦ rfl

@[simp]
lemma asSmallIso_hom_app_down (C : Type u) [Category.{v} C] {n : SimplexCategoryᵒᵖ}
    (σ : (nerve (AsSmall.{w} C)).obj n) :
    ((asSmallIso.{w} C).hom.app n σ).down = AsSmall.down.mapNerveObj σ := (rfl)

@[simp]
lemma asSmallIso_inv_app_apply (C : Type u) [Category.{v} C] {n : SimplexCategoryᵒᵖ}
    (τ : (SSet.uliftFunctor.{w, max u v}.obj (nerve C)).obj n) :
    (asSmallIso.{w} C).inv.app n τ = AsSmall.up.mapNerveObj τ.down := (rfl)

@[simp]
lemma asSmallIso_hom_app_nerveEquiv_symm (C : Type u) [Category.{v} C] (c : AsSmall.{w} C) :
    (asSmallIso.{w} C).hom.app (op ⦋0⦌) (nerveEquiv.symm c) =
      ULift.up (nerveEquiv.symm (AsSmall.down.obj c)) :=
  ULift.ext (ComposableArrows.ext₀ rfl)

@[simp]
lemma asSmallIso_inv_app_nerveEquiv_symm (C : Type u) [Category.{v} C] (c : C) :
    (asSmallIso.{w} C).inv.app (op ⦋0⦌) (ULift.up (nerveEquiv.symm c)) =
      nerveEquiv.symm (AsSmall.up.obj c) :=
  ComposableArrows.ext₀ rfl

end nerve

namespace NatTrans

section NerveHomotopy

variable {B C D E : Type u} [Category.{v} B] [Category.{v} C] [Category.{v} D] [Category.{v} E]

private def nerveHomotopyMap {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app _ := ↾fun p ↦
    p.1.prod' ((nerve (C ⥤ D)).map (SSet.stdSimplex.objEquiv p.2).op (ComposableArrows.mk₁ η)) ⋙
      evaluationUncurried C D
  naturality _ _ _ := rfl

/-- A natural transformation `η : F₀ ⟶ F₁` induces a simplicial homotopy from `nerveMap F₀` to
`nerveMap F₁`. -/
noncomputable def nerveHomotopy {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) :
    SSet.Homotopy (nerveMap F₀) (nerveMap F₁) :=
  SSet.Homotopy.mk' (nerveHomotopyMap η)
    (by ext ⟨m⟩ σ : 4; induction m using SimplexCategory.rec with | _ m =>
        exact CategoryTheory.Functor.ext (fun _ ↦ rfl)
          fun _ _ g ↦ (Category.id_comp (F₀.map (σ.map g) ≫ 𝟙 _)).symm)
    (by ext ⟨m⟩ σ : 4; induction m using SimplexCategory.rec with | _ m =>
        exact CategoryTheory.Functor.ext (fun _ ↦ rfl)
          fun _ _ g ↦ (Category.id_comp (F₁.map (σ.map g) ≫ 𝟙 _)).symm)

private lemma nerveHomotopy_h {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) :
    η.nerveHomotopy.h = nerveHomotopyMap η := rfl

lemma nerveHomotopy_h_app {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (n : SimplexCategoryᵒᵖ)
    (p : (nerve C ⊗ Δ[1]).obj n) :
    η.nerveHomotopy.h.app n p =
      p.1.prod' ((nerve (C ⥤ D)).map (SSet.stdSimplex.objEquiv p.2).op
        (ComposableArrows.mk₁ η)) ⋙ evaluationUncurried C D := (rfl)

/-- Along the vertical edge over a vertex `c`, `η.nerveHomotopy` traces the edge of `nerve D`
corresponding to the component `η.app c`. -/
@[simp]
lemma nerveHomotopy_h_verticalEdge {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (c : C) :
    dsimp% η.nerveHomotopy.h.app (op ⦋1⦌)
        (SSet.verticalEdge (X := nerve C) (nerveEquiv.symm c)) =
      (nerve.edgeMk (η.app c)).edge := by
  let v : (nerve C) _⦋0⦌ := nerveEquiv.symm c
  have h₁ : (SSet.verticalEdge v).1 = ComposableArrows.mk₁ (𝟙 c) :=
    (SSet.verticalEdge_fst v).trans (nerve.σ_zero_nerveEquiv_symm c)
  have h₂_eq : SSet.stdSimplex.objEquiv (SSet.verticalEdge v).2 = 𝟙 ⦋1⦌ := by
    rw [SSet.verticalEdge_snd]; ext i : 3; fin_cases i <;> rfl
  have h₂ : (nerve (C ⥤ D)).map (SSet.stdSimplex.objEquiv (SSet.verticalEdge v).2).op
      (ComposableArrows.mk₁ η) = ComposableArrows.mk₁ η :=
    congrArg (fun φ : ⦋1⦌ ⟶ ⦋1⦌ ↦ (nerve (C ⥤ D)).map φ.op (ComposableArrows.mk₁ η)) h₂_eq
  refine (nerveHomotopy_h_app η (op ⦋1⦌) (SSet.verticalEdge v)).trans
    ((congrArg (· ⋙ evaluationUncurried C D) (congrArg₂ Functor.prod' h₁ h₂)).trans
      (ComposableArrows.ext₁ rfl rfl ?_))
  dsimp [evaluationUncurried, ComposableArrows.mk₁, ComposableArrows.Mk₁.obj,
    ComposableArrows.Mk₁.map, ComposableArrows.hom]; simp

private lemma mk₁_whiskerLeft_obj (K : B ⥤ C) {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (k : Fin 2) (b : B) :
    ((ComposableArrows.mk₁ (Functor.whiskerLeft K η)).obj k).obj b =
      ((ComposableArrows.mk₁ η).obj k).obj (K.obj b) := by fin_cases k <;> rfl

private lemma mk₁_whiskerLeft_eval_map (K : B ⥤ C) {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) {k₀ k₁ : Fin 2}
    (u : k₀ ⟶ k₁) {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    ((ComposableArrows.mk₁ (Functor.whiskerLeft K η)).obj k₀).map f ≫
        ((ComposableArrows.mk₁ (Functor.whiskerLeft K η)).map u).app b₁ =
      eqToHom (mk₁_whiskerLeft_obj K η k₀ b₀) ≫
        (((ComposableArrows.mk₁ η).obj k₀).map (K.map f) ≫
          ((ComposableArrows.mk₁ η).map u).app (K.obj b₁)) ≫
        eqToHom (mk₁_whiskerLeft_obj K η k₁ b₁).symm := by
  fin_cases k₀ <;> fin_cases k₁ <;>
    first
    | exact absurd (Fin.le_iff_val_le_val.1 (leOfHom u)) (Nat.not_succ_le_zero _)
    | (simp only [eqToHom_refl, Category.id_comp, Category.comp_id]; rfl)

private lemma mk₁_whiskerRight_obj {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (G : D ⥤ E) (k : Fin 2) (c : C) :
    ((ComposableArrows.mk₁ (Functor.whiskerRight η G)).obj k).obj c =
      G.obj (((ComposableArrows.mk₁ η).obj k).obj c) := by fin_cases k <;> rfl

private lemma mk₁_whiskerRight_eval_map {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (G : D ⥤ E) {k₀ k₁ : Fin 2}
    (u : k₀ ⟶ k₁) {c₀ c₁ : C} (f : c₀ ⟶ c₁) :
    ((ComposableArrows.mk₁ (Functor.whiskerRight η G)).obj k₀).map f ≫
        ((ComposableArrows.mk₁ (Functor.whiskerRight η G)).map u).app c₁ =
      eqToHom (mk₁_whiskerRight_obj η G k₀ c₀) ≫
        G.map (((ComposableArrows.mk₁ η).obj k₀).map f ≫ ((ComposableArrows.mk₁ η).map u).app c₁) ≫
        eqToHom (mk₁_whiskerRight_obj η G k₁ c₁).symm := by
  fin_cases k₀ <;> fin_cases k₁ <;>
    first
    | exact absurd (Fin.le_iff_val_le_val.1 (leOfHom u)) (Nat.not_succ_le_zero _)
    | simp [ComposableArrows.mk₁, ComposableArrows.Mk₁.obj, ComposableArrows.Mk₁.map]

/-- Whiskering a natural transformation on the left corresponds to precomposing the cylinder map of
`nerveHomotopy` with `nerveMap K ▷ Δ[1]`. -/
lemma whiskerLeft_nerveHomotopy_h (K : B ⥤ C) {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) :
    (Functor.whiskerLeft K η).nerveHomotopy.h = nerveMap K ▷ Δ[1] ≫ η.nerveHomotopy.h := by
  rw [nerveHomotopy_h, nerveHomotopy_h]; ext ⟨m⟩ p : 4
  induction m using SimplexCategory.rec with | _ m
  let φ := (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv p.2)).toFunctor
  exact CategoryTheory.Functor.ext (fun i ↦ mk₁_whiskerLeft_obj K η (φ.obj i) (p.1.obj i))
    fun _ _ g ↦ mk₁_whiskerLeft_eval_map K η (φ.map g) (p.1.map g)

/-- Whiskering a natural transformation on the right corresponds to postcomposing the cylinder map
of `nerveHomotopy` with `nerveMap G`. -/
lemma whiskerRight_nerveHomotopy_h {F₀ F₁ : C ⥤ D} (η : F₀ ⟶ F₁) (G : D ⥤ E) :
    (Functor.whiskerRight η G).nerveHomotopy.h = η.nerveHomotopy.h ≫ nerveMap G := by
  rw [nerveHomotopy_h, nerveHomotopy_h]; ext ⟨m⟩ p : 4
  induction m using SimplexCategory.rec with | _ m
  let φ := (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv p.2)).toFunctor
  exact CategoryTheory.Functor.ext (fun i ↦ mk₁_whiskerRight_obj η G (φ.obj i) (p.1.obj i))
    fun _ _ g ↦ mk₁_whiskerRight_eval_map η G (φ.map g) (p.1.map g)

end NerveHomotopy

end NatTrans

namespace Limits

variable {C : Type u} [Category.{v} C]

/-- An initial object `x : C` induces a simplicial homotopy from the constant map at `x` to the
identity of `nerve C`. -/
noncomputable def IsInitial.nerveHomotopy {x : C} (hx : IsInitial x) :
    SSet.Homotopy (SSet.const (nerveEquiv.symm x)) (𝟙 (nerve C)) := by
  simpa only [nerveMap_const, nerveMap_id] using
    ({ app := fun c ↦ hx.to c, naturality := fun _ _ _ ↦ hx.hom_ext _ _ } :
      (Functor.const C).obj x ⟶ 𝟭 C).nerveHomotopy

/-- A terminal object `x : C` induces a simplicial homotopy from the identity of `nerve C` to the
constant map at `x`. -/
noncomputable def IsTerminal.nerveHomotopy {x : C} (hx : IsTerminal x) :
    SSet.Homotopy (𝟙 (nerve C)) (SSet.const (nerveEquiv.symm x)) := by
  simpa only [nerveMap_id, nerveMap_const] using
    ({ app := fun c ↦ hx.from c, naturality := fun _ _ _ ↦ hx.hom_ext _ _ } :
      𝟭 C ⟶ (Functor.const C).obj x).nerveHomotopy

/-- The nerve of a category with an initial object is weakly contractible. -/
instance isWeaklyContractible_nerve_of_hasInitial (C : Type u) [Category.{v} C] [HasInitial C] :
    SSet.IsWeaklyContractible (nerve C) :=
  SSet.IsWeaklyContractible.of_homotopy initialIsInitial.nerveHomotopy

/-- The nerve of a category with a terminal object is weakly contractible. -/
instance isWeaklyContractible_nerve_of_hasTerminal (C : Type u) [Category.{v} C] [HasTerminal C] :
    SSet.IsWeaklyContractible (nerve C) :=
  SSet.IsWeaklyContractible.of_homotopy_id_const terminalIsTerminal.nerveHomotopy

end Limits

/-- `ConnectedComponents J` has a single element if and only if `J` is connected. -/
lemma nonempty_unique_connectedComponents_iff (J : Type u) [Category.{v} J] :
    Nonempty (Unique (ConnectedComponents J)) ↔ CategoryTheory.IsConnected J := by
  rw [unique_iff_subsingleton_and_nonempty]
  refine ⟨fun ⟨hsub, ⟨z⟩⟩ ↦ ?_, fun _ ↦
    ⟨⟨_root_.Quotient.ind₂ fun a b ↦ _root_.Quotient.sound (isPreconnected_zigzag a b)⟩,
      ⟨ConnectedComponents.mk (Classical.arbitrary J)⟩⟩⟩
  obtain ⟨j₀, -⟩ := _root_.Quotient.exists_rep z
  have : Nonempty J := ⟨j₀⟩
  exact zigzag_isConnected fun a b ↦
    _root_.Quotient.exact (hsub.elim (ConnectedComponents.mk a) (ConnectedComponents.mk b))

namespace nerve

/-- The connected components of `nerve C` correspond naturally to `ConnectedComponents C`. -/
def π₀EquivConnectedComponents (C : Type u) [Category.{v} C] :
    SSet.π₀ (nerve C) ≃ ConnectedComponents C where
  toFun := SSet.π₀.lift (fun x ↦ ConnectedComponents.mk (nerveEquiv x))
    (fun _ _ e ↦ _root_.Quotient.sound (Zigzag.of_hom (homEquiv e)))
  invFun := _root_.Quotient.lift (fun c ↦ SSet.π₀.mk (X := nerve C) (nerveEquiv.symm c))
    fun _ _ (h : Zigzag _ _) ↦ by
      induction h with
      | refl => rfl
      | tail _ hzag ih =>
        exact hzag.rec (fun ⟨f⟩ ↦ ih.trans (SSet.π₀.sound (edgeMk f)))
          fun ⟨f⟩ ↦ ih.trans (SSet.π₀.sound (edgeMk f)).symm
  left_inv := SSet.π₀.rec fun x ↦ by
    dsimp only [SSet.π₀.lift_mk, ConnectedComponents.mk, _root_.Quotient.lift_mk]
    exact congrArg (SSet.π₀.mk (X := nerve C)) (Equiv.symm_apply_apply nerveEquiv x)
  right_inv := _root_.Quotient.ind fun c ↦ by
    dsimp only [SSet.π₀.lift_mk, ConnectedComponents.mk, _root_.Quotient.lift_mk]
    exact congrArg ConnectedComponents.mk (Equiv.apply_symm_apply nerveEquiv c)

@[simp]
lemma π₀EquivConnectedComponents_mk (C : Type u) [Category.{v} C] (x : (nerve C) _⦋0⦌) :
    π₀EquivConnectedComponents C (SSet.π₀.mk x) = ConnectedComponents.mk (nerveEquiv x) := (rfl)

@[simp]
lemma π₀EquivConnectedComponents_mk_nerveEquiv_symm (C : Type u) [Category.{v} C] (c : C) :
    π₀EquivConnectedComponents C (SSet.π₀.mk (X := nerve C) (nerveEquiv.symm c)) =
      ConnectedComponents.mk c :=
  (π₀EquivConnectedComponents_mk C (show (nerve C) _⦋0⦌ from nerveEquiv.symm c)).trans
    (congrArg ConnectedComponents.mk (Equiv.apply_symm_apply nerveEquiv c))

@[simp]
lemma π₀EquivConnectedComponents_symm_mk (C : Type u) [Category.{v} C] (c : C) :
    (π₀EquivConnectedComponents C).symm (ConnectedComponents.mk c) =
      SSet.π₀.mk (X := nerve C) (nerveEquiv.symm c) := (rfl)

/-- `π₀EquivConnectedComponents` intertwines `SSet.mapπ₀ (nerveMap F)` with
`F.mapConnectedComponents`. -/
@[simp]
lemma π₀EquivConnectedComponents_mapπ₀_nerveMap {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (z : SSet.π₀ (nerve C)) :
    π₀EquivConnectedComponents D (SSet.mapπ₀ (nerveMap F) z) =
      F.mapConnectedComponents (π₀EquivConnectedComponents C z) := by
  induction z using SSet.π₀.rec with | mk x =>
  obtain ⟨c, rfl⟩ := nerveEquiv.symm.surjective x
  have hv : SSet.mapπ₀ (nerveMap F) (SSet.π₀.mk (X := nerve C) (nerveEquiv.symm c)) =
      SSet.π₀.mk (X := nerve D) (nerveEquiv.symm (F.obj c)) :=
    (SSet.mapπ₀_mk (nerveMap F) _).trans
      (congrArg (SSet.π₀.mk (X := nerve D)) (nerveMap_app_zero_nerveEquiv_symm F c))
  rw [hv, π₀EquivConnectedComponents_mk_nerveEquiv_symm,
    π₀EquivConnectedComponents_mk_nerveEquiv_symm, Functor.mapConnectedComponents_mk]

/-- `nerve C` is connected as a simplicial set if and only if `C` is a connected category. -/
lemma isConnected_iff (C : Type u) [Category.{v} C] :
    (nerve C).IsConnected ↔ CategoryTheory.IsConnected C := by
  rw [SSet.isConnected_iff_nonempty_unique, ← nonempty_unique_connectedComponents_iff]
  exact ⟨fun ⟨h⟩ ↦ ⟨(π₀EquivConnectedComponents C).symm.unique⟩,
    fun ⟨h⟩ ↦ ⟨(π₀EquivConnectedComponents C).unique⟩⟩

end nerve

end CategoryTheory
