/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.IndEtale.Normal
public import TauCeti.RingTheory.StrictHenselization.IndEtale
public import TauCeti.RingTheory.StrictHenselization.Local

/-!
# Strict henselizations of normal domains

The strict henselization of a local ring that is an integrally closed domain is again an
integrally closed domain (Stacks, Lemma 10.156.6 (06DI)). More generally this holds for the colimit
`algebra R Ω` of the étale neighbourhoods of an integrally closed domain `R` pointed in any local
ring `Ω`: that colimit is a local ring, ind-étale over `R`, and a local ring ind-étale over a normal
domain is a normal domain (`TauCeti.Algebra.IndEtale.isIntegrallyClosed_of_isLocalRing`). Neither
locality of `R` nor any Noetherian hypothesis is needed.

Normality cannot be weakened to `R` being a domain: the local ring of the node `y² = x²(1 + x)` at
the origin is a domain, but in its strict henselization `1 + x` acquires a square root `s`, and
`(y - x s)(y + x s) = 0` with neither factor zero.

## Main results

* `TauCeti.StrictHenselization.isDomain_algebra`: the strict henselization of a normal domain is
  a domain.
* `TauCeti.StrictHenselization.isIntegrallyClosed_algebra`: it is integrally closed.

## References

* [Stacks Project, Lemma 10.156.6 (06DI)](https://stacks.math.columbia.edu/tag/06DI)
-/

public section

open IsLocalRing

universe u

namespace TauCeti.StrictHenselization

variable (R Ω : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing Ω]
  [IsLocalRing Ω] [Algebra R Ω]

/-- The localization of `R` at the prime under the maximal ideal of `algebra R Ω` is integrally
closed, as a localization of the integrally closed domain `R`. -/
private theorem isIntegrallyClosed_localization_under :
    IsIntegrallyClosed (Localization.AtPrime ((maximalIdeal (algebra R Ω)).under R)) :=
  isIntegrallyClosed_of_isLocalization _ _
    ((maximalIdeal (algebra R Ω)).under R).primeCompl_le_nonZeroDivisors

/-- **The strict henselization of a normal domain is a domain.** For an integrally closed domain
`R`, the colimit of the étale neighbourhoods of `R` pointed in a local ring `Ω` is a domain; in
particular so is the strict henselization of a local ring that is an integrally closed domain. -/
@[stacks 06DI "strict henselization, domain part"]
instance isDomain_algebra : IsDomain (algebra R Ω) :=
  have := isIntegrallyClosed_localization_under R Ω
  Algebra.IndEtale.isDomain_of_isLocalRing R (algebra R Ω)

/-- **The strict henselization of a normal domain is integrally closed.** For an integrally closed
domain `R`, the colimit of the étale neighbourhoods of `R` pointed in a local ring `Ω` is an
integrally closed domain; in particular so is the strict henselization of a local ring that is an
integrally closed domain. -/
@[stacks 06DI "strict henselization"]
instance isIntegrallyClosed_algebra : IsIntegrallyClosed (algebra R Ω) :=
  have := isIntegrallyClosed_localization_under R Ω
  Algebra.IndEtale.isIntegrallyClosed_of_isLocalRing R (algebra R Ω)

-- The colimit of the étale neighbourhoods of `ℤ` pointed in any field, such as an algebraic
-- closure of `𝔽_p`, is an integrally closed domain.
example (Ω : Type) [Field Ω] : IsDomain (algebra ℤ Ω) ∧ IsIntegrallyClosed (algebra ℤ Ω) :=
  ⟨inferInstance, inferInstance⟩

end TauCeti.StrictHenselization
