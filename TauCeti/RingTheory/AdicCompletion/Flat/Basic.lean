/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Flat.Tower
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.Flat.Jacobson

/-!
# Detecting flatness by completing the target

For an algebra `S` over a commutative ring `R`, with `S` Noetherian and local,
flatness over `R` is equivalent to flatness of the maximal-ideal completion of `S`
over `R`. Only the target is completed: `R` need not be local or Noetherian.

This criterion allows one to establish flatness of a local analytic algebra over
its base by identifying its completion with a flat formal algebra. The formal
presentation is a separate input; no analytic-to-formal comparison is assumed here.

More generally, an adic completion of a ring along an ideal in its Jacobson radical
is faithfully flat as soon as it is flat, which Mathlib supplies for Noetherian rings.
The completion has the same quotient by the ideal as the ring, so every maximal ideal
extends to a proper ideal of the completion. The flatness hypothesis is kept separate
because it can hold without Noetherianity of the ring itself: for instance, the
completion of a henselization is flat over it before the henselization is known to be
Noetherian.

## Main results

* `AdicCompletion.faithfullyFlat_of_le_jacobson`: a flat adic completion along an ideal
  in the Jacobson radical is faithfully flat.
* `AdicCompletion.faithfullyFlat_of_isLocalRing`: the maximal-ideal completion of a
  Noetherian local ring is faithfully flat.
* `AdicCompletion.flat_iff_of_isLocalRing`: completing a Noetherian local target detects
  flatness over any base.

## References

* Stacks Project, Lemma 10.39.10, Tag 039V (flatness in a faithfully flat tower).
* Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 10
  (completion of Noetherian local rings).
-/

public section

namespace AdicCompletion

/-- An adic completion along an ideal in the Jacobson radical is faithfully flat once it is
flat, for instance over a Noetherian ring. -/
theorem faithfullyFlat_of_le_jacobson {S : Type*} [CommRing S] {J : Ideal S}
    [Module.Flat S (AdicCompletion J S)] (hJ : J ≤ (⊥ : Ideal S).jacobson) :
    Module.FaithfullyFlat S (AdicCompletion J S) :=
  .of_le_jacobson_of_algHom ((Ideal.pow_le_self one_ne_zero).trans hJ) (evalₐ J 1)

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing S] [IsLocalRing S]

/-- The maximal-ideal completion of a Noetherian local ring is faithfully flat over it. -/
instance faithfullyFlat_of_isLocalRing :
    Module.FaithfullyFlat S (AdicCompletion (IsLocalRing.maximalIdeal S) S) :=
  faithfullyFlat_of_le_jacobson (IsLocalRing.maximalIdeal_le_jacobson ⊥)

/-- Completing a Noetherian local target detects flatness over any base ring.
The base is unchanged, and need not be local or Noetherian. -/
theorem flat_iff_of_isLocalRing :
    Module.Flat R (AdicCompletion (IsLocalRing.maximalIdeal S) S) ↔ Module.Flat R S :=
  (Module.Flat.iff_of_faithfullyFlat R S _).symm

end AdicCompletion
