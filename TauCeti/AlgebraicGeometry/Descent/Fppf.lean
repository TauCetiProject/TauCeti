/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import TauCeti.AlgebraicGeometry.Descent.MorphismProperty
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent

/-!
# Finite locally free morphisms satisfy fppf descent

A morphism whose base change along a surjective, flat morphism locally of finite presentation is
locally of finite presentation is itself locally of finite presentation (the instance
`descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation` in the namespace
`AlgebraicGeometry.LocallyOfFinitePresentation`).
Being locally of finite presentation is local on the target, so this is Mathlib's fpqc descent of
local finite presentation in `Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`, through
Mathlib's fpqc-to-fppf descent instance in `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`.

Together with fppf descent of finite morphisms
(`AlgebraicGeometry.IsFinite.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation`)
and of flat morphisms
(`AlgebraicGeometry.Flat.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation`), this
gives fppf descent of finite locally free morphisms, that is of morphisms which are finite, flat
and locally of finite presentation
(`AlgebraicGeometry.descendsAlong_isFinite_inf_flat_inf_locallyOfFinitePresentation`).

## References

* The Stacks Project, *Descent*, Section 35.23 (properties local in the fpqc topology).
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

namespace LocallyOfFinitePresentation

/-- **Morphisms locally of finite presentation satisfy fppf descent.** A morphism whose base change
along a surjective, flat morphism locally of finite presentation is locally of finite presentation
is itself locally of finite presentation. -/
instance descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation :
    MorphismProperty.DescendsAlong @LocallyOfFinitePresentation.{u}
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  -- Mathlib's fpqc-to-fppf instance is stated for a bundled `MorphismProperty`, which instance
  -- search does not unify with `@LocallyOfFinitePresentation`, so its inputs are supplied as
  -- local instances.
  let P : MorphismProperty Scheme.{u} := @LocallyOfFinitePresentation
  have : IsZariskiLocalAtTarget P :=
    HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFinitePresentation
  have : P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := inferInstance
  exact (inferInstance : P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation))

end LocallyOfFinitePresentation

/-- **Finite locally free morphisms satisfy fppf descent.** A morphism whose base change along a
surjective, flat morphism locally of finite presentation is finite, flat and locally of finite
presentation is itself so. -/
instance descendsAlong_isFinite_inf_flat_inf_locallyOfFinitePresentation :
    (@IsFinite ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).DescendsAlong
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have : (@IsFinite ⊓ @Flat : MorphismProperty Scheme.{u}).DescendsAlong
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    MorphismProperty.DescendsAlong.inf
  MorphismProperty.DescendsAlong.inf

end AlgebraicGeometry
