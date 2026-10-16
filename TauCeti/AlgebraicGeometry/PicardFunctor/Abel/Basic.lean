/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Functor
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
public import TauCeti.AlgebraicGeometry.PicardFunctor.Relative

/-!
# The Abel map from divisors to the relative Picard presheaf

Let `f : X ⟶ S` be a morphism of schemes. A relative effective Cartier divisor `D` on the base
change `X_T = T ×_S X` has an invertible ideal sheaf `𝒪(-D)`, and its dual is the line bundle
`𝒪(D)`. Sending `D` to the class of `𝒪(D)` in `Pic(X_T) / Pic(T)` is natural in the scheme `T`
over `S`: pulling back `D` along `X_{T'} ⟶ X_T` gives a relative effective Cartier divisor whose
ideal sheaf is the pullback of `𝒪(-D)`
(`Scheme.IdealSheafData.IsEffectiveCartier.pullback_mk_toInvertibleSheaf`). This gives the
**Abel map** `D ↦ 𝒪(D)` from the functor `Div_{X/S}` of relative effective Cartier divisors to the
relative Picard presheaf `T ↦ Pic(X_T) / Pic(T)`, as a natural transformation
`TauCeti.AlgebraicGeometry.abelMap`. The empty divisor goes to the identity
(`TauCeti.AlgebraicGeometry.abelMap_app_top`).

For a smooth proper curve `X` over a field, restricting to divisors of degree `d` gives the Abel
maps `Symᵈ X ⟶ Pic^d`, and in degree one the degree-one Abel map `X ⟶ Pic¹`. A base point `x₀`
then gives the Abel–Jacobi map `x ↦ 𝒪(x - x₀)` into `Pic⁰`, by translating by `𝒪(-x₀)`.
Separately, when `f` has a section, the target of the Abel map is also the rigidified Picard
functor (`TauCeti.AlgebraicGeometry.rigidifiedPicardFunctorIso`). Neither the degree nor the
representability of these functors is treated here.

The functor `Div_{X/S}` takes values in `Type u`, while line-bundle classes live in `Type (u + 1)`,
so the source of the Abel map is `Div_{X/S}` composed with `uliftFunctor`.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.3 (the Abel map `Div_{X/S} ⟶ Pic_{X/S}`).
* The Stacks Project, *Picard Schemes of Curves* (Tag 0B95).
-/

public section

open CategoryTheory Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The class of `𝒪(D)` in `Pic(X_T) / Pic(T)`, the inverse of the class of the ideal sheaf. -/
private def abelClass {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) :
    (relativePicardPresheaf f).obj T :=
  QuotientGroup.mk (LineBundleClass.mk ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp
    D.2).isEffectiveCartier.toInvertibleSheaf)⁻¹

/-- Pulling back a divisor along a morphism of base changes pulls back the class of `𝒪(D)`. -/
private lemma relativePicardPresheaf_map_abelClass {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T')
    (D : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) :
    (relativePicardPresheaf f).map φ (abelClass f D) =
      abelClass f ((relativeEffectiveCartierSubfunctor f).toFunctor.map φ D) := by
  have hD := ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp D.2).isEffectiveCartier
  have hD' := ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp
    ((relativeEffectiveCartierSubfunctor f).toFunctor.map φ D).2).isEffectiveCartier
  rw [abelClass, abelClass, relativePicardPresheaf_map_mk, ← LineBundleClass.pullbackHom_apply,
    map_inv, LineBundleClass.pullbackHom_apply,
    Scheme.IdealSheafData.IsEffectiveCartier.pullback_mk_toInvertibleSheaf hD hD']
  -- Both sides are the class of the ideal sheaf of the pulled-back divisor; they differ only in
  -- the proof that this divisor is effective Cartier.
  rfl

/-- **The Abel map** `D ↦ 𝒪(D)` of a morphism of schemes `f : X ⟶ S`: the natural transformation
from the functor of relative effective Cartier divisors on the base changes `X_T = T ×_S X` to the
relative Picard presheaf `T ↦ Pic(X_T) / Pic(T)`, sending a divisor `D` to the class of the line
bundle `𝒪(D)`, the dual of its ideal sheaf (`abelMap_app_apply`). -/
def abelMap : (relativeEffectiveCartierSubfunctor f).toFunctor ⋙ uliftFunctor.{u + 1} ⟶
    relativePicardPresheaf f ⋙ forget CommGrpCat where
  app T := TypeCat.ofHom fun D ↦ abelClass f D.down
  naturality T T' φ := by
    ext ⟨D⟩
    exact (relativePicardPresheaf_map_abelClass f φ D).symm

-- The source and target of `(abelMap f).app T` are spelled out in their simp-normal form (without
-- `Functor.comp_obj`), so that the left-hand side passes the `simpNF` linter.
/-- The Abel map sends a relative effective Cartier divisor `D` on `X_T` to the image in
`Pic(X_T) / Pic(T)` of the inverse of the class of its ideal sheaf, that is, of the class of
`𝒪(D)`. -/
@[simp]
lemma abelMap_app_apply {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) :
    ConcreteCategory.hom (C := Type (u + 1))
      (X := uliftFunctor.{u + 1}.obj ((relativeEffectiveCartierSubfunctor f).obj T))
      (Y := ToType ((relativePicardPresheaf f).obj T)) ((abelMap f).app T) (ULift.up D) =
      (QuotientGroup.mk (LineBundleClass.mk ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp
        D.2).isEffectiveCartier.toInvertibleSheaf)⁻¹ : (relativePicardPresheaf f).obj T) :=
  (rfl)

/-- The Abel map sends the empty divisor to the identity: `𝒪(∅) = 𝒪`. -/
lemma abelMap_app_top (T : (Over S)ᵒᵖ) :
    (abelMap f).app T (ULift.up ⟨(⊤ : (pullback T.unop.hom f).IdealSheafData),
      top_mem_relativeEffectiveCartierSubfunctor_obj f T⟩) =
      (1 : (relativePicardPresheaf f).obj T) := by
  rw [abelMap_app_apply, LineBundleClass.mk_eq_one_iff.mpr ?_, inv_one]
  · exact QuotientGroup.mk_one _
  · rw [Scheme.IdealSheafData.IsEffectiveCartier.toInvertibleSheaf_obj]
    exact ⟨asIso (⊤ : (pullback T.unop.hom f).IdealSheafData).sheafι⟩

end

end AlgebraicGeometry

end TauCeti
