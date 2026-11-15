/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Noetherian
public import TauCeti.RingTheory.RegularLocalRing.Descent
public import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# Regularity of strict henselizations

A local ring is regular if and only if its strict henselization is regular. More generally,
this holds for the colimit of its étale neighbourhoods pointed in any field through a local
map. Noetherianity is part of regularity, not an additional hypothesis.

The structure map is flat and local, and the maximal ideal of the source generates the maximal
ideal of the target. Together with Noetherianity of the pointed étale colimit, these properties
allow regularity to ascend and descend. In particular, the strict henselization of a discrete
valuation ring is a regular local ring; hence it is a domain without needing normality of strict
henselizations in general.

## Main results

* `TauCeti.StrictHenselization.isRegularLocalRing_iff`: regularity is equivalent for the base
  and its pointed étale colimit.
* `TauCeti.StrictHenselization.isRegularLocalRing`: the pointed étale colimit of a regular
  local ring is regular local.

## References

* [Stacks Project, Tag 06LN](https://stacks.math.columbia.edu/tag/06LN), regularity of
  henselizations and strict henselizations.
-/

public section

universe u

namespace TauCeti.StrictHenselization

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  [IsLocalHom (algebraMap R Ω)]

/-- A local ring is regular if and only if the colimit of its étale neighbourhoods pointed
in a field through a local map is regular. In particular this applies to the strict
henselization, pointed in a separable closure of the residue field. -/
@[stacks 06LN "strict henselization"]
theorem isRegularLocalRing_iff [IsLocalRing R] :
    IsRegularLocalRing (algebra R Ω) ↔ IsRegularLocalRing R :=
  ⟨fun _ ↦ IsRegularLocalRing.of_flat_of_isLocalHom (S := algebra R Ω),
    fun _ ↦ IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq
      (maximalIdeal_eq_map R Ω).symm⟩

/-- The pointed étale colimit of a regular local ring is regular local. In particular,
strict henselization preserves regular local rings. -/
instance isRegularLocalRing [IsRegularLocalRing R] : IsRegularLocalRing (algebra R Ω) :=
  (isRegularLocalRing_iff R Ω).mpr ‹_›

end TauCeti.StrictHenselization
