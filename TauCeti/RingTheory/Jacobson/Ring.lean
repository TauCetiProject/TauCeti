/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ring

/-!
# Jacobson rings via principal quotients

A commutative ring is a Jacobson ring as soon as its Jacobson radical vanishes and its quotient by
every nonzero principal ideal is a Jacobson ring. Indeed, every nonzero prime ideal contains a
nonzero element, and so is the preimage of a prime ideal of such a quotient.

This is the shape of the Jacobson criterion of Bosch–Güntzer–Remmert for rings with a Weierstrass
theory: Weierstrass division makes the quotient by a nonzero element finite over a smaller ring,
so that `isJacobsonRing_of_isIntegral` applies to it, while the vanishing of the Jacobson radical
is checked separately.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.2.5–5.2.6.
-/

public section

namespace TauCeti

open Ideal

/-- **Jacobson rings via principal quotients.** A commutative ring whose Jacobson radical is
zero, and whose quotient by every nonzero principal ideal is a Jacobson ring, is a Jacobson
ring. -/
theorem isJacobsonRing_of_quotient_span_singleton {R : Type*} [CommRing R]
    (hR : (⊥ : Ideal R).jacobson = ⊥)
    (h : ∀ x : R, x ≠ 0 → IsJacobsonRing (R ⧸ span {x})) : IsJacobsonRing R := by
  refine isJacobsonRing_iff_prime_eq.mpr fun P hP ↦ ?_
  rcases eq_or_ne P ⊥ with rfl | hP0
  · exact hR
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hxP' : span {x} ≤ P := (span_singleton_le_iff_mem P).mpr hxP
  -- `P` is the preimage of its image in `R ⧸ (x)`, which is prime there.
  rw [← comap_map_mk hxP', ← comap_jacobson_of_surjective Ideal.Quotient.mk_surjective,
    isJacobsonRing_iff_prime_eq.mp (h x hx0) _ (isPrime_map_quotientMk_of_isPrime hxP')]

end TauCeti
