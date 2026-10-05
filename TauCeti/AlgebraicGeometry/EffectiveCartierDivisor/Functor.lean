/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Relative
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# The functor of relative effective Cartier divisors

Let `f : X ⟶ S` be a morphism of schemes. For a scheme `T` over `S`, write `X_T = T ×_S X` for
the base change of `X`, viewed over `T` through the first projection. A morphism `T' ⟶ T` over
`S` induces `X_{T'} ⟶ X_T`, and pulling back ideal sheaves along it makes
`T ↦ {ideal sheaves on X_T}` a functor `(Over S)ᵒᵖ ⥤ Type`. The relative effective Cartier
divisors on `X_T` over `T` form a subfunctor: since the square formed by `X_{T'} ⟶ X_T` and the
two projections is a pullback square, pullback along `X_{T'} ⟶ X_T` preserves relative effective
Cartier divisors (`Scheme.IdealSheafData.IsRelativeEffectiveCartier.comap_of_isPullback`), with
no flatness assumption on `T' ⟶ T` or on `f`.

This is the functor `Div_{X/S}` of relative effective Cartier divisors. For a smooth proper curve
over a field, its subfunctor of divisors of degree `d` is the functor represented by the
symmetric power `Symᵈ X`, and `D ↦ 𝒪(D)` defines the Abel maps from it to the Picard functor;
neither the degree, the representability nor the Abel maps are treated here. The empty divisor
is a relative effective Cartier divisor on every base change, so the functor has a distinguished
point.

The base change `X_T = T ×_S X` and the induced morphisms `((Over.pullback f).map φ).left` are
those used by `TauCeti.AlgebraicGeometry.rigidifiedPicardFunctor`.

## Main declarations

* `TauCeti.AlgebraicGeometry.baseChangeIdealSheafFunctor`: the functor `T ↦ IdealSheafData X_T`
  of closed subschemes of the base changes of `X`, acting by pullback of ideal sheaves;
* `TauCeti.AlgebraicGeometry.relativeEffectiveCartierSubfunctor`: its subfunctor of relative
  effective Cartier divisors on `X_T` over `T`, whose `Subfunctor.toFunctor` is `Div_{X/S}`;
* `TauCeti.AlgebraicGeometry.top_mem_relativeEffectiveCartierSubfunctor_obj`: the empty divisor.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.3.
* The Stacks Project, *Divisors*, section *Relative effective Cartier divisors*, and *Picard
  Schemes of Curves*, section *Moduli of divisors on smooth curves*.
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
-- Expose the object type so that the values of the functor, and of its subfunctor of relative
-- effective Cartier divisors, can be used directly as ideal sheaves on the base change.
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

/-- **The functor of relative effective Cartier divisors** of `f : X ⟶ S`, as a subfunctor of
`baseChangeIdealSheafFunctor f`: at a scheme `T` over `S` it consists of the relative effective
Cartier divisors on `X_T = T ×_S X` over `T`. -/
def relativeEffectiveCartierSubfunctor : Subfunctor (baseChangeIdealSheafFunctor f) where
  obj T := {I | I.IsRelativeEffectiveCartier (pullback.fst T.unop.hom f)}
  map {T T'} φ I hI := by
    -- The induced morphism `X_{T'} ⟶ X_T` and the two projections form a pullback square over
    -- `T' ⟶ T`, by pasting with the pullback square defining `X_T`.
    have h : IsPullback ((Over.pullback f).map φ.unop).left (pullback.fst T'.unop.hom f)
        (pullback.fst T.unop.hom f) φ.unop.left := by
      refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback T.unop.hom f).flip
      simpa using (IsPullback.of_hasPullback T'.unop.hom f).flip
    exact hI.comap_of_isPullback h

/-- An ideal sheaf on `T ×_S X` lies in `relativeEffectiveCartierSubfunctor f` exactly when it is
a relative effective Cartier divisor over `T`. -/
@[simp]
lemma mem_relativeEffectiveCartierSubfunctor_obj_iff {T : (Over S)ᵒᵖ}
    {I : (baseChangeIdealSheafFunctor f).obj T} :
    I ∈ (relativeEffectiveCartierSubfunctor f).obj T ↔
      Scheme.IdealSheafData.IsRelativeEffectiveCartier I (pullback.fst T.unop.hom f) :=
  Iff.rfl

/-- The empty divisor is a relative effective Cartier divisor on every base change of `X`. -/
lemma top_mem_relativeEffectiveCartierSubfunctor_obj (T : (Over S)ᵒᵖ) :
    (⊤ : (pullback T.unop.hom f).IdealSheafData) ∈
      (relativeEffectiveCartierSubfunctor f).obj T :=
  Scheme.IdealSheafData.isRelativeEffectiveCartier_top _

/-- Base change preserves the empty divisor. -/
@[simp]
lemma baseChangeIdealSheafFunctor_map_top {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    (baseChangeIdealSheafFunctor f).map φ (⊤ : (pullback T.unop.hom f).IdealSheafData) =
      (⊤ : (pullback T'.unop.hom f).IdealSheafData) :=
  Scheme.IdealSheafData.comap_top _

end

end AlgebraicGeometry

end TauCeti
