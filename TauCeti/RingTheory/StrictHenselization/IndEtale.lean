/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.IndEtale
public import TauCeti.RingTheory.StrictHenselization.Algebra

/-!
# The strict henselization is ind-étale

The colimit `algebra R Ω` of the pointed étale neighbourhoods of `R → Ω` is, by construction, a
filtered colimit of étale `R`-algebras. Hence it is an ind-étale `R`-algebra, and in particular
`R → algebra R Ω` is flat. For a local ring `R` and a separable closure `Ω` of its residue field
this is the flatness of the strict henselization: the colimit description is Stacks, Tag 04GW,
and a filtered colimit of flat modules is flat (Stacks, Lemma 10.39.3 (05UU)).

## Main results

* `TauCeti.StrictHenselization.indEtale`: `algebra R Ω` is an ind-étale `R`-algebra. Flatness of
  `R → algebra R Ω` follows by `TauCeti.Algebra.IndEtale.flat`.

## References

* [Stacks Project, Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks Project, Tag 05UU](https://stacks.math.columbia.edu/tag/05UU)
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.StrictHenselization

variable (R Ω : Type u) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- The colimit of the pointed étale neighbourhoods of `R → Ω` is an ind-étale `R`-algebra: it is
the colimit of étale `R`-algebras indexed by their essentially small filtered category. -/
instance indEtale : Algebra.IndEtale R (algebra R Ω) :=
  -- `diagram R Ω` is indexed by a small model; reindexing along the equivalence with the small
  -- model returns to the filtered category of neighbourhoods itself.
  ⟨ObjectProperty.of_essentiallySmall_index
    (((ColimitPresentation.colimit (diagram R Ω)).ofIso (algebraIsoColimitDiagram R Ω).symm).reindex
      (equivSmallModel.{u} (Neighbourhood R Ω)).functor)
    fun _ => Neighbourhood.etale R Ω _⟩

-- The strict henselization is flat over the base ring.
example : Module.Flat R (algebra R Ω) := inferInstance

end TauCeti.StrictHenselization
