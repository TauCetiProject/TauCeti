/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# The étale topologies are subcanonical

The big étale topology on schemes is coarser than the fpqc topology, through the pro-étale
topology, so every representable presheaf is an étale sheaf. The same holds on the small étale
site `S.Etale` of a scheme `S`: its topology is induced along the fully faithful forgetful functor
to `Over S`, which is continuous for the étale topology localized at `S`.

Consequently `(Scheme.smallEtaleTopology S).yoneda` is a fully faithful functor from schemes
étale over `S` to étale sheaves of sets on `S`. This is how an étale `S`-scheme, for example a
finite étale cover, is regarded as an étale sheaf.

## Main results

* `AlgebraicGeometry.Scheme.etaleTopology.Subcanonical`: the big étale topology is subcanonical.
* `(AlgebraicGeometry.Scheme.Etale.forget S).IsContinuous`: the forgetful functor from the small
  étale site of `S` to `Over S` is continuous.
* `(AlgebraicGeometry.Scheme.smallEtaleTopology S).Subcanonical`: the small étale topology is
  subcanonical.

## References

* J. S. Milne, *Étale cohomology*, Chapter II, §1 (representable functors are sheaves for the
  fpqc and étale topologies).
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Representable presheaves on schemes are étale sheaves, because the étale topology is coarser
than the fpqc topology. -/
instance : etaleTopology.{u}.Subcanonical :=
  .of_le etaleTopology_le_proetaleTopology

/-- The forgetful functor from schemes étale over `S` to schemes over `S` is continuous for the
small étale topology and the étale topology localized at `S`. -/
instance (S : Scheme.{u}) :
    (Etale.forget S).IsContinuous (smallEtaleTopology S) (etaleTopology.over S) := by
  have : RepresentablyFlat (Etale.forget S) := flat_of_preservesFiniteLimits _
  rw [Functor.isContinuous_iff_coverPreserving]
  -- The small étale topology is the topology restricted along `Etale.forget S`. Instance search
  -- does not unify the morphism property `@Etale` with the bound variables of the generic
  -- instances, so the local cover density is passed explicitly.
  have : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact @Functor.coverPreserving_restrictedTopology _ _ _ _ (Etale.forget S) _
    (locallyCoverDense_of_le (P := @Etale) (Q := @Etale) S le_rfl) _ _

/-- Representable presheaves on the small étale site of a scheme are sheaves. -/
instance (S : Scheme.{u}) : (smallEtaleTopology S).Subcanonical :=
  GrothendieckTopology.subcanonical_of_full_of_faithful (Etale.forget S) _ (etaleTopology.over S)

end AlgebraicGeometry.Scheme
