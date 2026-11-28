/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Representable presheaves restricted along a left adjoint

Let `L : C ⥤ D` be left adjoint to `R : D ⥤ C`. If a presheaf `F` on `D` is represented by
`Y : D`, then its restriction `L.op ⋙ F` to `C` is represented by `R.obj Y`, through the natural
bijections `(X ⟶ R.obj Y) ≃ (L.obj X ⟶ Y) ≃ F.obj (op (L.obj X))`.

For example, restricting a presheaf on schemes over `S` along `Over.map g : Over S' ⥤ Over S`
for a morphism `g : S' ⟶ S` is base change of functors of points, and its right adjoint
`Over.pullback g` sends a representing `S`-scheme to the representing `S'`-scheme. Mathlib's
`CategoryTheory.Adjunction.representableBy` is the case of `F = yoneda.obj Y`, represented by
`Y`.

As a special case, if `U₀` is a terminal object of `C` and the restriction `(Over.forget U₀).op ⋙ F`
is represented by `Over.mk (hU₀.from X)`, then `F` itself is represented by `X`
(`CategoryTheory.Functor.RepresentableBy.ofOverIsTerminal`).

## Main declarations

* `CategoryTheory.Adjunction.representableByComp`: `L.op ⋙ F` is represented by `R.obj Y`
  when `F` is represented by `Y`.
* `CategoryTheory.Adjunction.compYonedaIso_hom_app_app_apply` and
  `CategoryTheory.Adjunction.compYonedaIso_inv_app_app_apply`: evaluation formulas for
  `Adjunction.compYonedaIso`.
* `CategoryTheory.Functor.RepresentableBy.ofOverIsTerminal`: `F` is represented by `X` when its
  restriction to `Over U₀` at a terminal object `U₀` is represented by `Over.mk (hU₀.from X)`.
-/

public section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Adjunction

section RepresentableBy

variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {F : Dᵒᵖ ⥤ Type w} {Y : D}

/-- If `L ⊣ R` and the presheaf `F` on `D` is represented by `Y`, then its restriction
`L.op ⋙ F` along `L` is represented by `R.obj Y`: a morphism `X ⟶ R.obj Y` corresponds to its
adjoint `L.obj X ⟶ Y`, hence to an element of `F.obj (op (L.obj X))`. -/
def representableByComp (e : F.RepresentableBy Y) : (L.op ⋙ F).RepresentableBy (R.obj Y) where
  homEquiv := (adj.homEquiv _ _).symm.trans e.homEquiv
  homEquiv_comp f g := by simp [adj.homEquiv_naturality_left_symm, e.homEquiv_comp]

/-- The representation `representableByComp` sends `φ : X ⟶ R.obj Y` to the element of
`F.obj (op (L.obj X))` corresponding to its adjoint `L.obj X ⟶ Y`. -/
@[simp]
lemma representableByComp_homEquiv_apply (e : F.RepresentableBy Y) {X : C} (φ : X ⟶ R.obj Y) :
    (adj.representableByComp e).homEquiv φ = e.homEquiv ((adj.homEquiv _ _).symm φ) :=
  (rfl)

end RepresentableBy

/-- Evaluating the forward component of `adj.compYonedaIso` at `X` and `W` applies the inverse
adjunction equivalence `(adj.homEquiv W.unop X).symm`. -/
@[simp]
lemma compYonedaIso_hom_app_app_apply {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₁} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (X : D) (W : Cᵒᵖ)
    (s : W.unop ⟶ R.obj X) :
    dsimp% ((adj.compYonedaIso.hom.app X).app W) s = (adj.homEquiv W.unop X).symm s := by
  simp only [compYonedaIso, NatIso.ofComponents_hom_app, Iso.symm_hom, Equiv.toIso_inv_hom_apply]

/-- Evaluating the inverse component of `adj.compYonedaIso` at `X` and `W` applies the
adjunction equivalence `adj.homEquiv W.unop X`. -/
@[simp]
lemma compYonedaIso_inv_app_app_apply {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₁} D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (X : D) (W : Cᵒᵖ)
    (s : L.obj W.unop ⟶ X) :
    dsimp% ((adj.compYonedaIso.inv.app X).app W) s = adj.homEquiv W.unop X s := by
  simp only [compYonedaIso, NatIso.ofComponents_inv_app, Iso.symm_inv, Equiv.toIso_hom_hom_apply]

end Adjunction

namespace Functor.RepresentableBy

/-- If `U₀` is a terminal object of `C` and the restriction `(Over.forget U₀).op ⋙ F` of a
presheaf `F : Cᵒᵖ ⥤ Type w` to `Over U₀` is represented by `Over.mk (hU₀.from X)`, then `F`
is represented by `X`. -/
def ofOverIsTerminal {U₀ : C} (hU₀ : Limits.IsTerminal U₀) {F : Cᵒᵖ ⥤ Type w} {X : C}
    (e : ((Over.forget U₀).op ⋙ F).RepresentableBy (Over.mk (hU₀.from X))) :
    F.RepresentableBy X where
  homEquiv {Y} :=
    { toFun φ := e.homEquiv (X := Over.mk (hU₀.from Y)) (Over.homMk φ (hU₀.hom_ext _ _))
      invFun y := ((e.homEquiv (X := Over.mk (hU₀.from Y))).symm y).left
      left_inv φ := by simp
      right_inv y := by
        refine (congrArg (e.homEquiv (X := Over.mk (hU₀.from Y))) ?_).trans
          ((e.homEquiv (X := Over.mk (hU₀.from Y))).apply_symm_apply y)
        ext1
        exact Over.homMk_left _ _ }
  homEquiv_comp {Y' Y} f φ := by
    have hcomp :
        (Over.homMk (f ≫ φ) (hU₀.hom_ext _ _) : Over.mk (hU₀.from Y') ⟶ Over.mk (hU₀.from X)) =
          (Over.homMk f (hU₀.hom_ext _ _) : Over.mk (hU₀.from Y') ⟶ Over.mk (hU₀.from Y)) ≫
            (Over.homMk φ (hU₀.hom_ext _ _) : Over.mk (hU₀.from Y) ⟶ Over.mk (hU₀.from X)) := by
      ext1
      simp only [Over.comp_left, Over.homMk_left]
    exact (congrArg (e.homEquiv (X := Over.mk (hU₀.from Y'))) hcomp).trans (e.homEquiv_comp _ _)

/-- The representation `ofOverIsTerminal` sends `φ : Y ⟶ X` to the section corresponding via `e`
to the induced morphism `Over.mk (hU₀.from Y) ⟶ Over.mk (hU₀.from X)` over `U₀`. -/
@[simp]
lemma ofOverIsTerminal_homEquiv_apply {U₀ : C} (hU₀ : Limits.IsTerminal U₀)
    {F : Cᵒᵖ ⥤ Type w} {X : C}
    (e : ((Over.forget U₀).op ⋙ F).RepresentableBy (Over.mk (hU₀.from X)))
    {Y : C} (φ : Y ⟶ X) :
    (ofOverIsTerminal hU₀ e).homEquiv φ =
      e.homEquiv (X := Over.mk (hU₀.from Y)) (Over.homMk φ (hU₀.hom_ext _ _)) :=
  (rfl)

end Functor.RepresentableBy

end CategoryTheory
