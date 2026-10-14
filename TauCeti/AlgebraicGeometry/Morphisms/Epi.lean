/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier
import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Epimorphisms of schemes with injective stalk or section maps

A surjective morphism of schemes `f : X ⟶ Y` whose stalk maps `𝒪_{Y, f x} → 𝒪_{X, x}` are all
injective is an epimorphism in the category of schemes: two morphisms out of `Y` which agree after
composing with `f` agree on points because `f` is surjective, and on stalks because the stalk maps
of `f` are injective. This is the criterion behind Mathlib's
`AlgebraicGeometry.Flat.epi_of_flat_of_surjective`, where faithful flatness of the stalk maps
supplies their injectivity; here injectivity is assumed directly. It applies, for instance, to the
quotient of an affine scheme by a finite group, whose stalk maps are injective but need not be flat.

The same argument works with the maps on sections `Γ(Y, U) → Γ(X, f⁻¹ U)` in place of the stalk
maps. Their injectivity holds when `𝒪_Y → f_* 𝒪_X` is an isomorphism, a condition on sections
rather than on stalks, which is how contraction morphisms of curves are controlled. This version
uses nothing about schemes and is deduced from its presheafed-space form
`AlgebraicGeometry.PresheafedSpace.epi_of_base_surjective_of_c_app_mono`.

Both hypotheses survive base change along an open immersion `U ⟶ Y`: surjectivity is stable under
base change, and the stalk maps of `X ×_Y U ⟶ U` are those of `f`, up to the stalk isomorphisms of
the two open immersions `X ×_Y U ⟶ X` and `U ⟶ Y`. So such an `f` remains an epimorphism over
every open subscheme of `Y`, which is what gluing arguments over an open cover of `Y` need: a
morphism out of `X` which factors locally over an open cover of `Y` then factors through `f`.
This gluing step follows the proof of Mathlib's
`AlgebraicGeometry.isRegularEpi_of_flat_of_surjective_of_isAffine`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.epi_of_surjective_of_stalkMap_injective`: a surjective morphism
  with injective stalk maps is an epimorphism.
* `AlgebraicGeometry.Scheme.Hom.epi_of_surjective_of_app_injective`: a surjective morphism which
  is injective on sections over every open is an epimorphism.
* `AlgebraicGeometry.Scheme.Hom.epi_of_surjective_of_isIso_app`: a surjective morphism which is
  an isomorphism on sections over every open is an epimorphism.
* `AlgebraicGeometry.Scheme.Hom.stalkMap_pullback_snd_injective`: the stalk maps of a base change
  along an open immersion are injective when those of `f` are.
* `AlgebraicGeometry.Scheme.Hom.epi_pullback_snd_of_isOpenImmersion`: the base change of such an
  `f` along an open immersion is again an epimorphism.
* `AlgebraicGeometry.Scheme.Hom.exists_comp_eq_of_openCover`: if every base change of `π` along an
  open immersion is an epimorphism, local factorizations through `π` over an open cover glue.

## References

* The Stacks Project, Tag 02VW, for the flat case.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y Z : Scheme.{u}}

/-- **A surjective morphism of schemes with injective stalk maps is an epimorphism.** -/
theorem epi_of_surjective_of_stalkMap_injective (f : X ⟶ Y) [Surjective f]
    (h : ∀ x, Function.Injective (f.stalkMap x)) : Epi f := by
  apply Functor.epi_of_epi_map Scheme.forgetToLocallyRingedSpace
  apply Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  refine SheafedSpace.epi_of_base_surjective_of_stalk_mono _ ‹Surjective f›.surj fun x ↦ ?_
  exact ConcreteCategory.mono_of_injective _ (h x)

/-- **A surjective morphism of schemes injective on sections is an epimorphism.** If
`f : X ⟶ Y` is surjective and every `Γ(Y, U) ⟶ Γ(X, f⁻¹ U)` is injective, as when
`𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism, then two morphisms out of `Y` which agree after composing
with `f` agree on points because `f` is surjective, and on sections because `f` is injective on
sections. -/
theorem epi_of_surjective_of_app_injective (f : X ⟶ Y) [Surjective f]
    (h : ∀ U, Function.Injective (f.app U)) : Epi f := by
  apply Functor.epi_of_epi_map Scheme.forgetToLocallyRingedSpace
  apply Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply Functor.epi_of_epi_map SheafedSpace.forgetToPresheafedSpace
  exact PresheafedSpace.epi_of_base_surjective_of_c_app_mono _ f.surjective
    fun U ↦ ConcreteCategory.mono_of_injective _ (h U.unop)

/-- A surjective morphism of schemes which is an isomorphism on sections over every open is an
epimorphism. -/
theorem epi_of_surjective_of_isIso_app (f : X ⟶ Y) [Surjective f]
    (h : ∀ U, IsIso (f.app U)) : Epi f :=
  epi_of_surjective_of_app_injective f fun _ ↦ (ConcreteCategory.bijective_of_isIso _).1

/-- The stalk maps of the base change of `f` along an open immersion are injective when those of
`f` are. -/
theorem stalkMap_pullback_snd_injective (f : X ⟶ Y) (g : Z ⟶ Y) [IsOpenImmersion g]
    (h : ∀ x, Function.Injective (f.stalkMap x)) (z : ↥(pullback f g)) :
    Function.Injective ((pullback.snd f g).stalkMap z) := by
  -- The stalk map of `pullback.fst ≫ f` is injective, since `pullback.fst` is an open immersion.
  have hfst : Mono ((pullback.fst f g ≫ f).stalkMap z) := by
    rw [stalkMap_comp]
    exact mono_comp' (ConcreteCategory.mono_of_injective _ (h _)) inferInstance
  -- It is the stalk map of `pullback.snd ≫ g`, which first applies the bijective stalk map of `g`.
  have hsnd : Mono (g.stalkMap (pullback.snd f g z) ≫ (pullback.snd f g).stalkMap z) := by
    rw [← stalkMap_comp, stalkMap_congr_hom _ _ pullback.condition.symm]
    exact (mono_comp_iff_of_isIso (Y.presheaf.stalkCongr _).hom _).mpr hfst
  rw [mono_comp_iff_of_isIso] at hsnd
  exact ConcreteCategory.injective_of_mono_of_preservesPullback _

/-- The base change of a surjective morphism with injective stalk maps along an open immersion is
an epimorphism. -/
theorem epi_pullback_snd_of_isOpenImmersion (f : X ⟶ Y) [Surjective f] (g : Z ⟶ Y)
    [IsOpenImmersion g] (h : ∀ x, Function.Injective (f.stalkMap x)) :
    Epi (pullback.snd f g) :=
  epi_of_surjective_of_stalkMap_injective _ (stalkMap_pullback_snd_injective f g h)

/-- **Descent along a morphism which stays an epimorphism over open subschemes.** Let `π : X ⟶ Y`
be a morphism whose base change along every open immersion is an epimorphism, and let `f : X ⟶ Z`.
If over each member `U_i` of an open cover of `Y` the base change of `f` factors through
`X ×_Y U_i ⟶ U_i`, then `f` factors through `π`. The local factorizations agree on overlaps
because the base change of `π` to an overlap is an epimorphism, so they glue. -/
theorem exists_comp_eq_of_openCover (π : X ⟶ Y)
    (hπ : ∀ ⦃U : Scheme.{u}⦄ (g : U ⟶ Y), IsOpenImmersion g → Epi (pullback.snd π g))
    (𝒰 : Y.OpenCover) (f : X ⟶ Z) (u : ∀ i, 𝒰.X i ⟶ Z)
    (hu : ∀ i, pullback.fst π (𝒰.f i) ≫ f = pullback.snd π (𝒰.f i) ≫ u i) :
    ∃ h : Y ⟶ Z, π ≫ h = f := by
  refine ⟨𝒰.glueMorphisms u fun i k ↦ ?_, ?_⟩
  · -- Over the overlap `V = U_i ×_Y U_k`, both restrictions agree with `f` on `X ×_Y V`.
    have := hπ (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) inferInstance
    have key (j : 𝒰.I₀) (p : pullback (𝒰.f i) (𝒰.f k) ⟶ 𝒰.X j)
        (hp : p ≫ 𝒰.f j = pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) :
        pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) ≫ p ≫ u j =
          pullback.fst π (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) ≫ f := by
      have w : pullback.fst π (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) ≫ π =
          (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i) ≫ p) ≫ 𝒰.f j := by
        rw [Category.assoc, hp]
        exact pullback.condition
      rw [← Category.assoc, ← pullback.lift_snd _ _ w, Category.assoc, ← hu j,
        pullback.lift_fst_assoc]
    rw [← cancel_epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i)), key i _ rfl,
      key k _ pullback.condition.symm]
  · refine Cover.hom_ext (𝒰.pullback₁ π) _ _ fun (i : 𝒰.I₀) ↦ ?_
    -- The components of the pulled-back cover are `pullback.fst` by definition
    -- (`PreZeroHypercover.pullback₁_f`); that `simps` lemma does not fire through `Scheme.Cover.f`.
    calc _ = pullback.fst π (𝒰.f i) ≫ π ≫ 𝒰.glueMorphisms u _ := rfl
      _ = pullback.fst π (𝒰.f i) ≫ f := by
        rw [pullback.condition_assoc, Cover.ι_glueMorphisms, hu i]

end AlgebraicGeometry.Scheme.Hom
