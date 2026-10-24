/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Content

/-!
# Polynomial content under coefficient equivalences

A coefficient ring equivalence carries polynomial content to the content of the mapped
polynomial up to associates. Equality need not hold: the normalized gcd structures on the two
rings need not choose corresponding representatives.
-/

public section

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]
  [NormalizedGCDMonoid R] [NormalizedGCDMonoid S]

/-- A coefficient equivalence preserves content up to associates, without any compatibility
assumption on the chosen normalizations. -/
theorem associated_content_map_equiv {e : R ≃+* S} {p : Polynomial R} :
    Associated (p.map e).content (e p.content) := by
  apply associated_of_dvd_dvd
  · have h : e.symm (p.map e).content ∣ p.content := by
      rw [Polynomial.dvd_content_iff_C_dvd]
      simpa only [Polynomial.map_C, Polynomial.map_map, RingEquiv.toRingHom_eq_coe,
        RingEquiv.symm_comp, Polynomial.map_id, RingEquiv.coe_toRingHom] using
          Polynomial.map_dvd e.symm.toRingHom (Polynomial.C_content_dvd (p.map e))
    simpa using map_dvd e h
  · rw [Polynomial.dvd_content_iff_C_dvd]
    simpa only [Polynomial.map_C, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
      Polynomial.map_dvd e.toRingHom (Polynomial.C_content_dvd p)

end TauCeti
