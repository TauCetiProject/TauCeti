/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.RegularLocalRing.Flat

import TauCeti.RingTheory.AdicCompletion.Localization

/-!
# Dimension and regularity of the completion of a local ring

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and let `R̂` be its `𝔪`-adic completion.
Then `R̂` is a Noetherian local ring, flat over `R`, with maximal ideal `𝔪 R̂` and the same residue
field. This file shows that `R̂` has the same Krull dimension as `R`, and that `R̂` is regular if
and only if `R` is. Together with Mathlib's `AdicCompletion.spanFinrank_maximalIdeal_eq`, these
are among the invariants of a local ring that are unchanged by completion.

Descent of regularity from `R̂` to `R` lets regularity be tested on complete local rings, where the
Cohen structure theorem presents them as quotients of power series rings over a field or, in mixed
characteristic, over a complete discrete valuation ring.

## Main results

* `TauCeti.AdicCompletion.ringKrullDim_eq`: `R̂` and `R` have the same Krull dimension.
* `TauCeti.AdicCompletion.isRegularLocalRing_iff`: `R̂` is regular if and only if `R` is.
* `TauCeti.AdicCompletion.isRegularLocalRing_iff_of_isMaximal`: completing a Noetherian ring `R` at
  a maximal ideal `p` is regular if and only if any localization `Rₚ` of `R` at `p` is regular.

## References

* [Stacks Project, Lemma 15.44.1](https://stacks.math.columbia.edu/tag/07NV), the dimension of
  the completion.
* [Stacks Project, Lemma 15.44.4](https://stacks.math.columbia.edu/tag/07NY), regularity of the
  completion.
-/

public section

open IsLocalRing

namespace TauCeti.AdicCompletion

section

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The completion of a Noetherian local ring at its maximal ideal has the same Krull dimension as
the ring. -/
@[stacks 07NV]
theorem ringKrullDim_eq : ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R :=
  ringKrullDim_eq_of_hasGoingDown_of_map_maximalIdeal_eq AdicCompletion.maximalIdeal_eq_map.symm

/-- The completion of a Noetherian local ring at its maximal ideal is regular if and only if the
ring is. -/
@[stacks 07NY]
theorem isRegularLocalRing_iff :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) ↔ IsRegularLocalRing R :=
  isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq AdicCompletion.maximalIdeal_eq_map.symm

end

/-- The completion of a regular local ring at its maximal ideal is regular. -/
instance {R : Type*} [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
  isRegularLocalRing_iff.mpr ‹_›

/-- Completing a Noetherian ring `R` at a maximal ideal `p` yields a regular local ring if and only
if any localization `Rₚ` of `R` at `p` is a regular local ring. -/
theorem isRegularLocalRing_iff_of_isMaximal {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsMaximal] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
    IsRegularLocalRing (AdicCompletion p R) ↔ IsRegularLocalRing Rₚ := by
  have : IsNoetherianRing Rₚ := IsLocalization.isNoetherianRing p.primeCompl Rₚ ‹_›
  let e := (_root_.AdicCompletion.equivMaximalIdealOfAtPrime p Rₚ).toRingEquiv
  exact ⟨fun _ ↦ isRegularLocalRing_iff.mp (.of_ringEquiv e),
    fun _ ↦ .of_ringEquiv (R := AdicCompletion (maximalIdeal Rₚ) Rₚ) e.symm⟩

end TauCeti.AdicCompletion
