/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Epimorphisms of schemes with injective stalk maps

A surjective morphism of schemes `f : X ⟶ Y` whose stalk maps `𝒪_{Y, f x} → 𝒪_{X, x}` are all
injective is an epimorphism in the category of schemes: two morphisms out of `Y` which agree after
composing with `f` agree on points because `f` is surjective, and on stalks because the stalk maps
of `f` are injective. This is the criterion behind Mathlib's
`AlgebraicGeometry.Flat.epi_of_flat_of_surjective`, where faithful flatness of the stalk maps
supplies their injectivity; here injectivity is assumed directly. It applies, for instance, to the
quotient of an affine scheme by a finite group, whose stalk maps are injective but need not be flat.

Both hypotheses survive base change along an open immersion `U ⟶ Y`: surjectivity is stable under
base change, and the stalk maps of `X ×_Y U ⟶ U` are those of `f`, up to the stalk isomorphisms of
the two open immersions `X ×_Y U ⟶ X` and `U ⟶ Y`. So such an `f` remains an epimorphism over
every open subscheme of `Y`, which is what gluing arguments over an open cover of `Y` need.

## Main results

* `AlgebraicGeometry.Scheme.Hom.epi_of_surjective_of_stalkMap_injective`: a surjective morphism
  with injective stalk maps is an epimorphism.
* `AlgebraicGeometry.Scheme.Hom.stalkMap_pullback_snd_injective`: the stalk maps of a base change
  along an open immersion are injective when those of `f` are.
* `AlgebraicGeometry.Scheme.Hom.epi_pullback_snd_of_isOpenImmersion`: the base change of such an
  `f` along an open immersion is again an epimorphism.

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

/-- The stalk maps of the base change of `f` along an open immersion are injective when those of
`f` are. -/
theorem stalkMap_pullback_snd_injective (f : X ⟶ Y) (g : Z ⟶ Y) [IsOpenImmersion g]
    (h : ∀ x, Function.Injective (f.stalkMap x)) (z : ↥(pullback f g)) :
    Function.Injective ((pullback.snd f g).stalkMap z) := by
  -- The stalk map of `pullback.fst ≫ f` is injective, since `pullback.fst` is an open immersion.
  have : Mono (f.stalkMap (pullback.fst f g z)) := ConcreteCategory.mono_of_injective _ (h _)
  have hfst : Mono ((pullback.fst f g ≫ f).stalkMap z) := by
    rw [stalkMap_comp]
    exact @mono_comp _ _ _ _ _ _ this _ inferInstance
  -- It is the stalk map of `pullback.snd ≫ g`, which first applies the bijective stalk map of `g`.
  rw [stalkMap_congr_hom _ _ pullback.condition, stalkMap_comp] at hfst
  have hg : IsIso (g.stalkMap (pullback.snd f g z)) := inferInstance
  have : Mono ((pullback.snd f g).stalkMap z) :=
    (@mono_comp_iff_of_isIso _ _ _ _ _ _ (by exact hg) _).mp
      ((mono_comp_iff_of_isIso _ _).mp hfst)
  exact ConcreteCategory.injective_of_mono_of_preservesPullback _

/-- The base change of a surjective morphism with injective stalk maps along an open immersion is
an epimorphism. -/
theorem epi_pullback_snd_of_isOpenImmersion (f : X ⟶ Y) [Surjective f] (g : Z ⟶ Y)
    [IsOpenImmersion g] (h : ∀ x, Function.Injective (f.stalkMap x)) :
    Epi (pullback.snd f g) :=
  epi_of_surjective_of_stalkMap_injective _ (stalkMap_pullback_snd_injective f g h)

end AlgebraicGeometry.Scheme.Hom
