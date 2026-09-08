/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The different ideal

This file supplies general lemmas about trace-dual fractional ideals.
-/

public section

open Module

open scoped nonZeroDivisors

namespace TauCeti

universe uR uS uK uL

variable {R : Type uR} {S : Type uS} {K : Type uK} {L : Type uL}
variable [CommRing R] [CommRing S] [Field K] [Field L]
variable [Algebra R S] [Algebra R K] [Algebra K L] [Algebra R L] [Algebra S L]
variable [IsScalarTower R K L] [IsScalarTower R S L]
variable [IsDomain R]
variable [IsFractionRing R K] [IsFractionRing S L]
variable [IsIntegrallyClosed R] [IsIntegralClosure S R L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

namespace FractionalIdeal

/-- Over a domain, the fractional-ideal trace dual of one coerces to the submodule trace dual. -/
@[simp]
theorem coe_dual_one_of_isDomain [IsDomain S] :
    (↑(FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) : Submodule S L) =
      Submodule.traceDual R K (1 : Submodule S L) := by
  ext x
  change x ∈ FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L) ↔ _
  have h : (1 : FractionalIdeal S⁰ L) ≠ 0 := one_ne_zero
  simp [FractionalIdeal.dual, h]
  rfl

end FractionalIdeal

end TauCeti

end
