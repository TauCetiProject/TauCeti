/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.IndEtale
public import TauCeti.RingTheory.Henselization.Algebra

/-!
# The henselization is ind-étale

The henselization of a ring `R` along an ideal `I` is, by construction, the filtered colimit of
the étale neighbourhoods of `(R, I)`, which are étale `R`-algebras. Hence it is an ind-étale
`R`-algebra, and in particular `R → algebra I` is flat (Stacks, Lemma 15.12.2 (0AGU), flatness).

## Main results

* `TauCeti.Henselization.indEtale`: the henselization of `(R, I)` is an ind-étale `R`-algebra.
  The flatness of `R → algebra I` follows by `TauCeti.Algebra.IndEtale.flat`.

## References

* [Stacks Project, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU)
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R]

/-- The henselization of `(R, I)` is an ind-étale `R`-algebra: it is the colimit of the small
filtered diagram `diagram I` of étale neighbourhoods of `(R, I)`. -/
instance indEtale (I : Ideal R) : Algebra.IndEtale R (algebra I) :=
  have : IsFiltered (SmallModel.{u} (Neighbourhood.{u, u} I)) :=
    IsFiltered.of_equivalence (equivSmallModel.{u} (Neighbourhood.{u, u} I))
  Algebra.IndEtale.of_isColimit
    (fun j => ((isNeighbourhood_iff I _).mp
      ((equivSmallModel.{u} (Neighbourhood.{u, u} I)).inverse.obj j).property).1)
    (colimit.isColimit (diagram I)) (CommAlgCat.algEquivOfIso (algebraIsoColimitDiagram I).symm)

-- The henselization is flat over the base ring.
example (I : Ideal R) : Module.Flat R (algebra I) := inferInstance

end TauCeti.Henselization
