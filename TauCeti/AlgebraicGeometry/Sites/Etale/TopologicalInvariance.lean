/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Etale.UniversalHomeomorphism

/-!
# Base change of étale schemes along a universal homeomorphism

For a morphism `f : X ⟶ Y`, base change along `f` gives a functor
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale` between the categories of étale schemes. When `f`
is a universal homeomorphism, this functor is fully faithful: base change along `f` is bijective
on morphisms into an étale `Y`-scheme
(`TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism.overPullback_map_bijective`), because
universal homeomorphisms have the unique left lifting property with respect to étale morphisms.
This is the full faithfulness half of the topological invariance of the small étale site
(Stacks, Theorem 04DZ); essential surjectivity is not proved here.

## Main results

* `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChange`: base change `Y.Etale ⥤ X.Etale` along
  `f : X ⟶ Y`, with `AlgebraicGeometry.Scheme.Hom.full_smallEtaleBaseChange` and
  `AlgebraicGeometry.Scheme.Hom.faithful_smallEtaleBaseChange` for a universal homeomorphism `f`.

## References

* The Stacks Project, [Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ), topological
  invariance of the small étale site.
-/

public section

open CategoryTheory Limits MorphismProperty

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Base change along `f : X ⟶ Y`, from schemes étale over `Y` to schemes étale over `X`: an étale
`V ⟶ Y` is sent to `V ×_Y X ⟶ X`. -/
noncomputable def smallEtaleBaseChange : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

/-- On underlying schemes over `X`, `smallEtaleBaseChange f` is base change along `f`. -/
noncomputable def smallEtaleBaseChangeCompForgetIso :
    f.smallEtaleBaseChange ⋙ Etale.forget X ≅ Etale.forget Y ⋙ Over.pullback f :=
  Iso.refl _

variable [IsUniversalHomeomorphism f]

/-- Base change along a universal homeomorphism `f : X ⟶ Y` is faithful on schemes étale over
`Y`. -/
instance faithful_smallEtaleBaseChange : f.smallEtaleBaseChange.Faithful :=
  have : (Etale.forget Y ⋙ Over.pullback f).Faithful := ⟨fun {_ B} _ _ h ↦
    have : Etale ((Etale.forget Y).obj B).hom := B.prop
    (Etale.forget Y).map_injective ((IsUniversalHomeomorphism.overPullback_map_bijective f).1 h)⟩
  .of_comp_iso f.smallEtaleBaseChangeCompForgetIso

/-- Base change along a universal homeomorphism `f : X ⟶ Y` is full on schemes étale over `Y`. -/
instance full_smallEtaleBaseChange : f.smallEtaleBaseChange.Full :=
  have : (Etale.forget Y ⋙ Over.pullback f).Full := ⟨fun {_ B} c ↦
    have : Etale ((Etale.forget Y).obj B).hom := B.prop
    have ⟨a, ha⟩ := (IsUniversalHomeomorphism.overPullback_map_bijective f).2 c
    ⟨(Etale.forget Y).preimage a, by simpa using ha⟩⟩
  .of_comp_faithful_iso f.smallEtaleBaseChangeCompForgetIso

end AlgebraicGeometry.Scheme.Hom
