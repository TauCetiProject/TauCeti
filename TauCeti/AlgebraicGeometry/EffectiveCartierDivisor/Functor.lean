/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Relative
public import TauCeti.AlgebraicGeometry.IdealSheaf.Functor
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

* `TauCeti.AlgebraicGeometry.relativeEffectiveCartierSubfunctor`: the subfunctor of relative
  effective Cartier divisors on `X_T` over `T` of the functor
  `TauCeti.AlgebraicGeometry.baseChangeIdealSheafFunctor` of ideal sheaves on base changes
  (from `TauCeti.AlgebraicGeometry.IdealSheaf.Functor`), whose `Subfunctor.toFunctor` is
  `Div_{X/S}`;
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

/-- The morphism between two base changes induced by a morphism of `S`-schemes forms a pullback
square with their first projections. -/
lemma isPullback_over_pullback_map_left {T T' : Over S} (φ : T' ⟶ T) :
    IsPullback ((Over.pullback f).map φ).left (pullback.fst T'.hom f)
      (pullback.fst T.hom f) φ.left := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback T.hom f).flip
  simpa using (IsPullback.of_hasPullback T'.hom f).flip

/-- **The functor of relative effective Cartier divisors** of `f : X ⟶ S`, as a subfunctor of
`baseChangeIdealSheafFunctor f`: at a scheme `T` over `S` it consists of the relative effective
Cartier divisors on `X_T = T ×_S X` over `T`. -/
def relativeEffectiveCartierSubfunctor : Subfunctor (baseChangeIdealSheafFunctor f) where
  obj T := {I | I.IsRelativeEffectiveCartier (pullback.fst T.unop.hom f)}
  map φ _ hI := hI.comap_of_isPullback (isPullback_over_pullback_map_left f φ.unop)

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

end

end AlgebraicGeometry

end TauCeti
