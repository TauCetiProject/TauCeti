/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic

import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import TauCeti.RingTheory.LocalRing.RingHom

/-!
# Lifting units between ideal quotients of a Dedekind domain

Reduction between quotients by nonzero ideals is surjective on units. This is stronger than
surjectivity on ring elements: a representative must also avoid the extra prime divisors of the
larger modulus.

Every prime over a nonzero ideal `J` of a Dedekind domain is maximal, so `R ⧸ J` is Artinian and
in particular semilocal. The statement is then the special case of
`RingHom.surjective_units_map_of_surjective`, which lifts units along any surjective map out of
a semilocal ring. This lifting statement supplies the residue-unit transition maps for ray class
groups.
-/

public section

open Ideal.Quotient

namespace TauCeti

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Reduction between ideal quotients of a Dedekind domain is surjective on units when the source
ideal is nonzero. No finiteness assumption on the residue fields is needed. -/
theorem units_map_quotient_factor_surjective {I J : Ideal R} (h : J ≤ I) (hJ : J ≠ ⊥) :
    Function.Surjective (Units.map (factor h).toMonoidHom) := by
  -- Every prime over `J` is maximal, so `R ⧸ J` is Artinian and has finitely many maximal ideals.
  have : Ring.KrullDimLE 0 (R ⧸ J) :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr fun P hP ↦
      hP.1.1.isMaximal (ne_bot_of_le_ne_bot hJ hP.1.2)
  have : IsArtinianRing (R ⧸ J) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact (factor h).surjective_units_map_of_surjective (factor_surjective h)

end TauCeti
