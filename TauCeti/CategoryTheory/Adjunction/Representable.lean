/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

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

## Main declarations

* `CategoryTheory.Adjunction.representableByComp`: `L.op ⋙ F` is represented by `R.obj Y`
  when `F` is represented by `Y`.
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

end CategoryTheory
