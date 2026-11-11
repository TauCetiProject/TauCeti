/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.StrictHenselization
public import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.DiscreteValuationRing.Etale

/-!
# Strict henselizations of discrete valuation rings

The strict henselization of a discrete valuation ring is again a discrete valuation ring,
and every uniformizer of the base remains a uniformizer. More generally, the results hold
for the colimit of étale neighbourhoods pointed in any field through a local map, without
assuming that the field is separably closed or algebraic over the residue field.

Regularity of the pointed étale colimit supplies the domain property. Its Noetherianity,
flatness over the base, and the equality of its maximal ideal with the extension of the
base maximal ideal then give the discrete valuation ring structure and preservation of
uniformizers. For a separable closure of the residue field, this constructs the discrete
valuation ring underlying the strictly henselian trait, with no completion involved.

## Main results

* `TauCeti.StrictHenselization.isDiscreteValuationRing_algebra`: the pointed étale colimit of
  a discrete valuation ring is a discrete valuation ring.
* `TauCeti.StrictHenselization.irreducible_algebraMap`: a uniformizer remains a uniformizer
  in this extension.

## References

* [Stacks Project, Tag 0AP3](https://stacks.math.columbia.edu/tag/0AP3), discrete valuation
  rings and their strict henselizations.
-/

public section

universe u

namespace TauCeti.StrictHenselization

variable (R Ω : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]

/-- The colimit of the étale neighbourhoods of a discrete valuation ring pointed in a field
through a local map is a discrete valuation ring. In particular, the strict henselization
of a discrete valuation ring is a discrete valuation ring. -/
@[stacks 0AP3 "strict henselization"]
instance isDiscreteValuationRing_algebra : IsDiscreteValuationRing (algebra R Ω) :=
  IsDiscreteValuationRing.of_flat_of_map_maximalIdeal_eq (maximalIdeal_eq_map R Ω).symm

/-- A uniformizer of a discrete valuation ring remains a uniformizer in its pointed étale
colimit, in particular in its strict henselization. -/
theorem irreducible_algebraMap {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R (algebra R Ω) π) :=
  IsDiscreteValuationRing.irreducible_algebraMap_of_map_maximalIdeal_eq
    (maximalIdeal_eq_map R Ω).symm hπ

end TauCeti.StrictHenselization
