/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Etale.UniversalHomeomorphism
public import TauCeti.AlgebraicGeometry.Sites.Etale.BaseChange

/-!
# Base change of étale schemes along a universal homeomorphism

For a morphism `f : X ⟶ Y`, base change along `f` gives a functor
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale` between the categories of étale schemes
(`TauCeti/AlgebraicGeometry/Sites/Etale/Over/Basic.lean`), which is faithful whenever `f` is
surjective (`AlgebraicGeometry.Scheme.Hom.faithful_smallEtaleBaseChange`, in
`TauCeti/AlgebraicGeometry/Sites/Etale/BaseChange.lean`). When `f` is a universal
homeomorphism, `f.smallEtaleBaseChange` is also full: base change along `f` is bijective on
morphisms into an étale `Y`-scheme
(`TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism.overPullback_map_bijective`), because universal
homeomorphisms have the unique left lifting property with respect to étale morphisms. Together,
these give the full faithfulness half of the topological invariance of the small étale site
(Stacks, Theorem 04DZ); essential surjectivity is not proved here.

For counterexamples showing that fullness fails when `f` is merely a homeomorphism rather than a
universal homeomorphism (such as `Spec.algebraMap K L` for a nontrivial separable field extension),
see `TauCeti/Examples/AlgebraicGeometry/Sites/Etale/TopologicalInvariance.lean`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.full_smallEtaleBaseChange`: `f.smallEtaleBaseChange` is full when
  `f` is a universal homeomorphism (and faithful by
  `AlgebraicGeometry.Scheme.Hom.faithful_smallEtaleBaseChange`).

## References

* The Stacks Project, [Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ), topological
  invariance of the small étale site.
-/

public section

open CategoryTheory MorphismProperty

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f]

/-- Base change along a universal homeomorphism `f : X ⟶ Y` is full on schemes étale over `Y`. -/
instance full_smallEtaleBaseChange : f.smallEtaleBaseChange.Full :=
  have : (Etale.forget Y ⋙ CategoryTheory.Over.pullback f).Full := ⟨fun {_ B} c ↦
    have : Etale ((Etale.forget Y).obj B).hom := B.prop
    have ⟨a, ha⟩ := (IsUniversalHomeomorphism.overPullback_map_bijective f).2 c
    ⟨(Etale.forget Y).preimage a, by simpa using ha⟩⟩
  .of_comp_faithful_iso f.smallEtaleBaseChangeCompForgetIso

end AlgebraicGeometry.Scheme.Hom
