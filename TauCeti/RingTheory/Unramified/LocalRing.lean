/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Unramifiedness of a local algebra at its maximal ideal

`Algebra.IsUnramifiedAt R q` is formal unramifiedness over `R` of the localization of the ambient
algebra at the prime `q`. When the ambient algebra `S` is already local and `q` is its maximal
ideal, that localization is `S` itself, because every element outside the maximal ideal is
already a unit. This file records the resulting equivalence, which is what lets a formal
unramifiedness statement about a local ring be read by Mathlib's unramified-locus API, and
conversely.

## Main results

* `TauCeti.isUnramifiedAt_maximalIdeal_iff`: a local `R`-algebra is unramified at its maximal
  ideal exactly when it is formally unramified over `R`.
-/

public section

namespace TauCeti

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]

/-- A local `R`-algebra is unramified at its maximal ideal exactly when it is formally unramified
over `R`: localizing a local ring at its maximal ideal inverts only units. -/
theorem isUnramifiedAt_maximalIdeal_iff :
    Algebra.IsUnramifiedAt R (IsLocalRing.maximalIdeal S) ↔ Algebra.FormallyUnramified R S :=
  (Algebra.FormallyUnramified.iff_of_equiv
    ((IsLocalization.atUnits S (IsLocalRing.maximalIdeal S).primeCompl
      fun x ↦ by simpa using! fun a ↦ a).restrictScalars R)).symm

end TauCeti
