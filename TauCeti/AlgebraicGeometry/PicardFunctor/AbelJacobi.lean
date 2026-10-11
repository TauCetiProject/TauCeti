/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Graph
public import TauCeti.AlgebraicGeometry.PicardFunctor.Abel

/-!
# The Abel–Jacobi map on functors of points

Let `f : X ⟶ S` be a separated morphism of schemes which is smooth of relative dimension one,
with a section `x₀`. A `T`-point `x : T ⟶ X` of `X` over `S` has a graph `Γₓ ⊆ X_T = T ×_S X`,
a relative effective Cartier divisor on `X_T` over `T`, natural in `T`
(`TauCeti.AlgebraicGeometry.graphDivisor`). Composing with the Abel map `D ↦ 𝒪(D)` into the
relative Picard presheaf `T ↦ Pic(X_T) / Pic(T)` (`TauCeti.AlgebraicGeometry.abelMap`) gives the
degree-one Abel map `x ↦ 𝒪(Γₓ)`. Dividing by its value at the base point normalizes it to the
**Abel–Jacobi map** `abelJacobiMap`, which sends a `T`-point `x` to the class of
`𝒪(Γₓ) ⊗ 𝒪(x₀_T)⁻¹ = 𝒪(Γₓ - x₀_T)`, where `x₀_T` is the base change of `x₀`, and sends the base
point to the identity (`abelJacobiMap_app_basePoint`).

For a smooth proper geometrically connected curve `X` over a field with a rational point `x₀`, this
is the map `x ↦ 𝒪(x - x₀)` from `X` to its Jacobian, written on functors of points.
Representability of the Picard functor and of its degree-zero part is not treated here, so no
morphism of schemes is constructed.

## Main declarations

* `TauCeti.AlgebraicGeometry.abelJacobiMap`: the natural transformation from the functor of points
  `T ↦ Hom_S(T, X)` to `T ↦ Pic(X_T) / Pic(T)`, sending `x` to the class of `𝒪(Γₓ - x₀_T)`
  (`abelJacobiMap_app_apply`);
* `TauCeti.AlgebraicGeometry.abelJacobiMap_app_basePoint`: it sends `x₀` to the identity.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.3 (the Abel map).
* J. S. Milne, *Jacobian varieties*, in *Arithmetic Geometry* (G. Cornell, J. H. Silverman,
  eds.), Springer, 1986, Section 2 (the canonical map `Q ↦ 𝒪(Q - P)` from a curve to its
  Jacobian).
-/

public section

open CategoryTheory Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {x₀ : S ⟶ X} (hx₀ : x₀ ≫ f = 𝟙 S)

/-- The class of `𝒪(Γₓ - x₀_T)` in `Pic(X_T) / Pic(T)` attached to a `T`-point `x`. -/
private def abelJacobiClass {T : (Over S)ᵒᵖ} (x : T.unop ⟶ Over.mk f) :
    (relativePicardPresheaf f).obj T :=
  (abelMap f).app T (ULift.up ((graphDivisor f).app T x)) /
    (abelMap f).app T (ULift.up ((graphDivisor f).app T (basePoint hx₀ T.unop)))

/-- The class of `𝒪(Γₓ - x₀_T)` is compatible with base change. -/
private lemma relativePicardPresheaf_map_abelJacobiClass {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (x : T.unop ⟶ Over.mk f) :
    (relativePicardPresheaf f).map φ (abelJacobiClass f hx₀ x) =
      abelJacobiClass f hx₀ (φ.unop ≫ x) := by
  -- Naturality of the graph divisor and of the Abel map.
  have hD (y : T.unop ⟶ Over.mk f) :
      (relativePicardPresheaf f).map φ ((abelMap f).app T (ULift.up ((graphDivisor f).app T y))) =
        (abelMap f).app T' (ULift.up ((graphDivisor f).app T' (φ.unop ≫ y))) := by
    rw [graphDivisor_app_comp]
    exact (NatTrans.naturality_apply (abelMap f) φ
      (ULift.up ((graphDivisor f).app T y) :
        ((relativeEffectiveCartierSubfunctor f).toFunctor ⋙ uliftFunctor.{u + 1}).obj T)).symm
  rw [abelJacobiClass, abelJacobiClass, map_div, ← comp_basePoint hx₀ φ.unop]
  exact congrArg₂ (· / ·) (hD x) (hD _)

/-- The **Abel–Jacobi map** of a separated morphism `f : X ⟶ S`, smooth of relative dimension
one, with a section `x₀`: the natural transformation from the functor of points `T ↦ Hom_S(T, X)`
of `X` to the relative Picard presheaf `T ↦ Pic(X_T) / Pic(T)`, sending a `T`-point `x` to the
class of `𝒪(Γₓ - x₀_T) = 𝒪(Γₓ) ⊗ 𝒪(x₀_T)⁻¹`, where `Γₓ` is the graph of `x` and `x₀_T` the base
change of `x₀` (`abelJacobiMap_app_apply`). -/
def abelJacobiMap : yoneda.obj (Over.mk f) ⋙ uliftFunctor.{u + 1} ⟶
    relativePicardPresheaf f ⋙ forget CommGrpCat where
  app T := TypeCat.ofHom fun x ↦ abelJacobiClass f hx₀ x.down
  naturality T T' φ := by
    ext ⟨x⟩
    exact (relativePicardPresheaf_map_abelJacobiClass f hx₀ φ x).symm

-- The source and target of `(abelJacobiMap f hx₀).app T` are spelled out in their simp-normal form
-- (without `Functor.comp_obj` and `yoneda_obj_obj`), so that the left-hand sides pass the `simpNF`
-- linter.
/-- The Abel–Jacobi map sends a `T`-point `x` to the quotient of the Abel map at its graph by the
Abel map at the graph of the base point, that is, to the class of `𝒪(Γₓ - x₀_T)`. -/
lemma abelJacobiMap_app_apply {T : (Over S)ᵒᵖ} (x : T.unop ⟶ Over.mk f) :
    ConcreteCategory.hom (C := Type (u + 1)) (X := uliftFunctor.{u + 1}.obj (T.unop ⟶ Over.mk f))
      (Y := ToType ((relativePicardPresheaf f).obj T)) ((abelJacobiMap f hx₀).app T)
      (ULift.up x) =
      (abelMap f).app T (ULift.up ((graphDivisor f).app T x)) /
        (abelMap f).app T (ULift.up ((graphDivisor f).app T (basePoint hx₀ T.unop))) :=
  (rfl)

/-- **The Abel–Jacobi map sends the base point to the identity**: `𝒪(x₀_T - x₀_T) = 𝒪`. -/
@[simp]
lemma abelJacobiMap_app_basePoint (T : (Over S)ᵒᵖ) :
    ConcreteCategory.hom (C := Type (u + 1)) (X := uliftFunctor.{u + 1}.obj (T.unop ⟶ Over.mk f))
      (Y := ToType ((relativePicardPresheaf f).obj T)) ((abelJacobiMap f hx₀).app T)
      (ULift.up (basePoint hx₀ T.unop)) = 1 := by
  rw [abelJacobiMap_app_apply, div_self']

end

end AlgebraicGeometry

end TauCeti
