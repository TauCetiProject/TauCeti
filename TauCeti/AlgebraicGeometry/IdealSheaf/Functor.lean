/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The functor of ideal sheaves on base changes

Let `f : X ⟶ S` be a morphism of schemes. For a scheme `T` over `S`, write `X_T = T ×_S X` for
the base change of `X`. A morphism `T' ⟶ T` over `S` induces `X_{T'} ⟶ X_T`, and pulling back
ideal sheaves along it makes `T ↦ {ideal sheaves on X_T}` a functor `(Over S)ᵒᵖ ⥤ Type`.

The base change `X_T = T ×_S X` and the induced morphisms `((Over.pullback f).map φ).left` are
those used by `TauCeti.AlgebraicGeometry.rigidifiedPicardFunctor`.

## Main declarations

* `TauCeti.AlgebraicGeometry.baseChangeIdealSheafFunctor`: the functor `T ↦ IdealSheafData X_T`
  of closed subschemes of the base changes of `X`, acting by pullback of ideal sheaves.
-/

public section

open CategoryTheory Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The functor of closed subschemes of the base changes of `f : X ⟶ S`: it sends a scheme `T`
over `S` to the ideal sheaves on `X_T = T ×_S X`, and a morphism `T' ⟶ T` over `S` to pullback
of ideal sheaves along the induced morphism `X_{T'} ⟶ X_T`. -/
-- Expose the object type so that the values of the functor, and of its subfunctors, can be used
-- directly as ideal sheaves on the base change.
@[expose]
def baseChangeIdealSheafFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := (pullback T.unop.hom f).IdealSheafData
  map φ := TypeCat.ofHom fun I ↦ I.comap ((Over.pullback f).map φ.unop).left
  map_id T := by
    ext I
    simp
  map_comp φ ψ := by
    ext I
    simp

/-- The value of `baseChangeIdealSheafFunctor f` at `T` is the type of ideal sheaves on
`T ×_S X`. -/
lemma baseChangeIdealSheafFunctor_obj (T : (Over S)ᵒᵖ) :
    (baseChangeIdealSheafFunctor f).obj T = (pullback T.unop.hom f).IdealSheafData :=
  rfl

/-- `baseChangeIdealSheafFunctor f` acts by pullback of ideal sheaves along the induced morphism
of base changes. -/
@[simp]
lemma baseChangeIdealSheafFunctor_map_apply {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (I : (baseChangeIdealSheafFunctor f).obj T) :
    (baseChangeIdealSheafFunctor f).map φ I =
      Scheme.IdealSheafData.comap I ((Over.pullback f).map φ.unop).left :=
  rfl

/-- Base change preserves the unit ideal sheaf, that is, the empty closed subscheme. -/
@[simp]
lemma baseChangeIdealSheafFunctor_map_top {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (baseChangeIdealSheafFunctor f).map φ (⊤ : (pullback T.unop.hom f).IdealSheafData) =
      (⊤ : (pullback T'.unop.hom f).IdealSheafData) :=
  Scheme.IdealSheafData.comap_top _

end

end AlgebraicGeometry

end TauCeti
