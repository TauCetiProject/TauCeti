/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Flat.Tower
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Detecting flatness by completing the target

For an algebra `S` over a commutative ring `R`, with `S` Noetherian and local,
flatness over `R` is equivalent to flatness of the maximal-ideal completion of `S`
over `R`. Only the target is completed: `R` need not be local or Noetherian.

This criterion allows one to establish flatness of a local analytic algebra over
its base by identifying its completion with a flat formal algebra. The formal
presentation is a separate input; no analytic-to-formal comparison is assumed here.

Mathlib supplies flatness of Noetherian adic completion and the local homomorphism
from a local ring to its maximal-ideal completion. Together these imply faithful
flatness, to which the tower descent criterion applies.

## References

* Stacks Project, Lemma 10.39.10, Tag 039V (flatness in a faithfully flat tower).
* Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 10
  (completion of Noetherian local rings).
-/

public section

namespace AdicCompletion

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing S] [IsLocalRing S]

/-- The maximal-ideal completion of a Noetherian local ring is faithfully flat over it. -/
instance faithfullyFlat_of_isLocalRing :
    Module.FaithfullyFlat S (AdicCompletion (IsLocalRing.maximalIdeal S) S) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Completing a Noetherian local target detects flatness over any base ring.
The base is unchanged, and need not be local or Noetherian. -/
theorem flat_iff :
    Module.Flat R (AdicCompletion (IsLocalRing.maximalIdeal S) S) ↔ Module.Flat R S :=
  (Module.Flat.iff_of_faithfullyFlat R S _).symm

end AdicCompletion
