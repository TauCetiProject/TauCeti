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
* `CategoryTheory.Functor.RepresentableBy.ofOverIsTerminal`: `F` is represented by `X` when its
  restriction to `Over U₀` at a terminal object `U₀` is represented by `Over.mk (hU₀.from X)`.
-/

public section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Adjunction

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

end Adjunction

namespace Functor.RepresentableBy

/-- If `U₀` is a terminal object of `C` and the restriction `(Over.forget U₀).op ⋙ F` of a
presheaf `F : Cᵒᵖ ⥤ Type w` to `Over U₀` is represented by `Over.mk (hU₀.from X)`, then `F`
is represented by `X`. -/
def ofOverIsTerminal {U₀ : C} (hU₀ : Limits.IsTerminal U₀) {F : Cᵒᵖ ⥤ Type w} {X : C}
    (e : ((Over.forget U₀).op ⋙ F).RepresentableBy (Over.mk (hU₀.from X))) :
    F.RepresentableBy X :=
  let eqU₀ := (Over.equivalenceOfIsTerminal hU₀).symm
  (eqU₀.toAdjunction.representableByComp e).ofIso
    ((Functor.associator eqU₀.functor.op (Over.forget U₀).op F).symm ≪≫
      Functor.isoWhiskerRight
        (NatIso.op (Over.equivalenceOfIsTerminal hU₀).counitIso.symm) F ≪≫
      Functor.leftUnitor F)

/-- The representation `ofOverIsTerminal` sends `φ : Y ⟶ X` to the section corresponding via `e`
to the induced morphism `Over.mk (hU₀.from Y) ⟶ Over.mk (hU₀.from X)` over `U₀`. -/
@[simp]
lemma ofOverIsTerminal_homEquiv_apply {U₀ : C} (hU₀ : Limits.IsTerminal U₀)
    {F : Cᵒᵖ ⥤ Type w} {X : C}
    (e : ((Over.forget U₀).op ⋙ F).RepresentableBy (Over.mk (hU₀.from X)))
    {Y : C} (φ : Y ⟶ X) :
    (ofOverIsTerminal hU₀ e).homEquiv φ =
      e.homEquiv (Over.homMk φ (hU₀.hom_ext _ _) :
        Over.mk (hU₀.from Y) ⟶ Over.mk (hU₀.from X)) := by
  have h1 : (ofOverIsTerminal hU₀ e).homEquiv φ =
      e.homEquiv (((Over.equivalenceOfIsTerminal hU₀).symm.toAdjunction.homEquiv _ _).symm φ) := by
    simp [ofOverIsTerminal, Functor.RepresentableBy.ofIso, Over.equivalenceOfIsTerminal]
    rfl
  let ψ : Y ⟶ (Over.equivalenceOfIsTerminal hU₀).symm.inverse.obj (Over.mk (hU₀.from X)) := φ
  have h2 :
      (((Over.equivalenceOfIsTerminal hU₀).symm.toAdjunction.homEquiv Y
          (Over.mk (hU₀.from X))).symm ψ) =
      Over.homMk φ (hU₀.hom_ext _ _) := by
    rw [Adjunction.homEquiv_counit]
    ext1
    simp [Equivalence.toAdjunction, Over.equivalenceOfIsTerminal, ψ]
    rfl
  exact h1.trans (congrArg e.homEquiv h2)

end Functor.RepresentableBy

end CategoryTheory
