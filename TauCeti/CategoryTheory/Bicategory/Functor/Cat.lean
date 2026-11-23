/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor

/-!
# Components of the comparison isomorphisms of `Cat`-valued pseudofunctors

For a pseudofunctor `F` into `Cat`, the flexible composition comparison `F.mapComp' f g fg h`
depends on the chosen `1`-morphism `fg` equal to `f ≫ g`. This file records, on objects, how it
changes when `fg` is replaced by an equal `1`-morphism, and the right unit law for an arbitrary
`fg` equal to `f ≫ 𝟙 _` when the source bicategory is strict. These are the forms in which the
comparisons appear when `fg` is computed rather than written as a composite, as for the
transition maps of a discrete pseudofunctor.

## Main results

* `CategoryTheory.Pseudofunctor.mapComp'_hom_toNatTrans_app_of_eq`: replacing `fg` by an equal
  `1`-morphism composes the component with an `eqToHom`.
* `CategoryTheory.Pseudofunctor.mapComp'_comp_id_hom_app_mapId_hom_app`: the right unit law at an
  arbitrary `fg` equal to `f ≫ 𝟙 _`.
-/

public section

universe w v' u' v u

namespace CategoryTheory.Pseudofunctor

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B] (F : B ⥤ᵖ Cat.{v', u'})

/-- Replacing the `1`-morphism `fg` in `F.mapComp' f g fg h` by an equal `1`-morphism `fg'`
composes the component of the comparison with an `eqToHom`. -/
lemma mapComp'_hom_toNatTrans_app_of_eq {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
    (fg fg' : b₀ ⟶ b₂) (h : f ≫ g = fg) (hfg : fg = fg') (x : F.obj b₀) :
    (F.mapComp' f g fg h).hom.toNatTrans.app x =
      eqToHom (by rw [hfg]) ≫ (F.mapComp' f g fg' (h.trans hfg)).hom.toNatTrans.app x := by
  subst hfg
  simp

/-- The right unit law of a pseudofunctor out of a strict bicategory into `Cat`, on objects, at
an arbitrary `1`-morphism `fg` equal to `f ≫ 𝟙 _`. -/
lemma mapComp'_comp_id_hom_app_mapId_hom_app [Strict B] {b₀ b₁ : B} (f fg : b₀ ⟶ b₁)
    (h : f ≫ 𝟙 b₁ = fg) (x : F.obj b₀) :
    (F.mapComp' f (𝟙 b₁) fg h).hom.toNatTrans.app x ≫
      (F.mapId b₁).hom.toNatTrans.app ((F.map f).toFunctor.obj x) =
        eqToHom (by rw [← h, Strict.comp_id]; rfl) := by
  obtain rfl : fg = f := h.symm.trans (Strict.comp_id f)
  simp [mapComp'_comp_id_hom_app]

end CategoryTheory.Pseudofunctor
