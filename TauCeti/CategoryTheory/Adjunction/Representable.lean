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

private def ofOverIsTerminalIso {U₀ : C} (hU₀ : Limits.IsTerminal U₀)
    (F : Cᵒᵖ ⥤ Type w) :
    ((Over.equivalenceOfIsTerminal hU₀).symm.functor.op ⋙ (Over.forget U₀).op ⋙ F) ≅ F :=
  (Functor.associator _ (Over.forget U₀).op F).symm ≪≫
    Functor.isoWhiskerRight
      (NatIso.op (Over.equivalenceOfIsTerminal hU₀).counitIso.symm) F ≪≫
    Functor.leftUnitor F

private lemma ofOverIsTerminalIso_hom_app_apply {U₀ : C} (hU₀ : Limits.IsTerminal U₀)
    (F : Cᵒᵖ ⥤ Type w) (Y : C)
    (x : ((Over.equivalenceOfIsTerminal hU₀).symm.functor.op ⋙
      (Over.forget U₀).op ⋙ F).obj (Opposite.op Y)) :
    ((ofOverIsTerminalIso hU₀ F).hom.app (Opposite.op Y)) x = x := by
  dsimp only [ofOverIsTerminalIso, Equivalence.symm_functor, Over.equivalenceOfIsTerminal]
  rw [Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, NatIso.op_hom, NatTrans.op_app, Iso.symm_hom]
  simp only [NatIso.ofComponents_inv_app, Iso.refl_inv, Opposite.unop_op,
    Functor.comp_obj, Over.forget_obj, Over.mk_left, Functor.leftUnitor_hom_app,
    Category.id_comp]
  -- `((Over.equivalenceOfIsTerminal hU₀).inverse ⋙ Over.forget U₀).obj Y` is defeq to `Y`.
  change (ConcreteCategory.hom (F.map (𝟙 (Opposite.op Y)) ≫ 𝟙 (F.obj (Opposite.op Y)))) x = x
  rw [Functor.map_id, Category.id_comp]
  exact ConcreteCategory.id_apply _

/-- If `U₀` is a terminal object of `C` and the restriction `(Over.forget U₀).op ⋙ F` of a
presheaf `F : Cᵒᵖ ⥤ Type w` to `Over U₀` is represented by `Over.mk (hU₀.from X)`, then `F`
is represented by `X`. -/
def ofOverIsTerminal {U₀ : C} (hU₀ : Limits.IsTerminal U₀) {F : Cᵒᵖ ⥤ Type w} {X : C}
    (e : ((Over.forget U₀).op ⋙ F).RepresentableBy (Over.mk (hU₀.from X))) :
    F.RepresentableBy X :=
  (((Over.equivalenceOfIsTerminal hU₀).symm).toAdjunction.representableByComp e).ofIso
    (ofOverIsTerminalIso hU₀ F)

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
  let ψ : Y ⟶ (Over.equivalenceOfIsTerminal hU₀).symm.inverse.obj (Over.mk (hU₀.from X)) := φ
  have h1 : (ofOverIsTerminal hU₀ e).homEquiv φ =
      e.homEquiv (((Over.equivalenceOfIsTerminal hU₀).symm.toAdjunction.homEquiv _ _).symm ψ) := by
    change ((ofOverIsTerminalIso hU₀ F).app (Opposite.op Y)).hom
      ((((Over.equivalenceOfIsTerminal hU₀).symm.toAdjunction.representableByComp e).homEquiv) ψ) =
      _
    rw [Iso.app_hom, ofOverIsTerminalIso_hom_app_apply hU₀ F Y]
    exact Adjunction.representableByComp_homEquiv_apply _ e ψ
  have h2 :
      (((Over.equivalenceOfIsTerminal hU₀).symm.toAdjunction.homEquiv Y
          (Over.mk (hU₀.from X))).symm ψ) =
      Over.homMk φ (hU₀.hom_ext _ _) := by
    rw [Adjunction.homEquiv_counit]
    ext1
    dsimp only [Over.Hom.left]
    simp only [Over.equivalenceOfIsTerminal, Functor.id_obj, Functor.comp_obj, Over.forget_obj,
      Over.mk_left, Equivalence.symm_functor, Equivalence.symm_inverse, Equivalence.toAdjunction,
      Equivalence.symm_counit, Equivalence.Equivalence_mk'_unitInv, NatIso.ofComponents_inv_app,
      Over.comp_left, Over.homMk_left, Over.isoMk_inv_left, Iso.refl_inv, Category.comp_id, ψ]
    exact (Over.homMk_left (U := Over.mk (hU₀.from Y)) (V := Over.mk (hU₀.from X))
      φ (hU₀.hom_ext _ _)).symm
  exact h1.trans (congrArg e.homEquiv h2)

end Functor.RepresentableBy

end CategoryTheory
