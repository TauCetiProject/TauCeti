/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Local
public import TauCeti.RingTheory.Henselization.Noetherian
public import TauCeti.RingTheory.RegularLocalRing.Descent
public import TauCeti.RingTheory.RegularLocalRing.Flat
import TauCeti.RingTheory.Henselization.IndEtale

/-!
# Regularity of henselizations

A local ring is regular if and only if its henselization is regular.

The structure map from a local ring `R` to its henselization `R^h` is flat (the henselization is
ind-étale), local, and the maximal ideal of `R` generates the maximal ideal of `R^h`; moreover
`R^h` is Noetherian exactly when `R` is. Regularity therefore ascends and descends along
`R → R^h`.

## Main results

* `TauCeti.Henselization.isRegularLocalRing_iff`: the henselization of a local ring at its maximal
  ideal is regular if and only if the ring is.

## References

* [Stacks Project, Tag 06LN](https://stacks.math.columbia.edu/tag/06LN), regularity of
  henselizations
* [Stacks Project, Tag 06LJ](https://stacks.math.columbia.edu/tag/06LJ), Noetherianity of the
  henselization
-/

public section

open IsLocalRing

universe u

namespace TauCeti

namespace Henselization

variable (R : Type u) [CommRing R]

/-- A local ring is regular if and only if its henselization at the maximal ideal is regular.
Noetherianity is not assumed: it is part of regularity on both sides. -/
@[stacks 06LN "henselization"]
theorem isRegularLocalRing_iff [IsLocalRing R] :
    IsRegularLocalRing (algebra (maximalIdeal R)) ↔ IsRegularLocalRing R :=
  ⟨fun _ ↦ IsRegularLocalRing.of_flat_of_isLocalHom (S := algebra (maximalIdeal R)),
    fun _ ↦ IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq
      (maximalIdeal_eq_extended (maximalIdeal R)).symm⟩

/-- The henselization of a regular local ring at its maximal ideal is a regular local ring. -/
instance isRegularLocalRing [IsRegularLocalRing R] :
    IsRegularLocalRing (algebra (maximalIdeal R)) :=
  (isRegularLocalRing_iff R).mpr ‹_›

end Henselization

end TauCeti
