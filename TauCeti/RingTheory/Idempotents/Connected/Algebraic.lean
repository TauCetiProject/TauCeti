/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Algebraic
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum

/-!
# Reduced connected algebraic algebras are fields

A reduced algebra over a field, all of whose elements are algebraic, is a field if its
spectrum is connected. Indeed, every nonzero element has a nonzero idempotent multiple;
connectedness forces that multiple to be one. No finite-dimensionality is needed.

This applies to the global functions of a reduced connected scheme universally closed over
a field: those functions are integral over the ground field.

## References

* The Stacks Project, Section 10.60, Dimension: reduced connected zero-dimensional rings.
-/

public section

namespace TauCeti

/-- A reduced algebraic algebra over a field with connected spectrum is a field. -/
theorem isField_of_isAlgebraic_of_isReduced_of_connectedSpace
    (k A : Type*) [Field k] [CommRing A] [Algebra k A] [Algebra.IsAlgebraic k A]
    [IsReduced A] [ConnectedSpace (PrimeSpectrum A)] : IsField A := by
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  refine ⟨exists_pair_ne A, mul_comm, fun {x} hx ↦ ?_⟩
  obtain ⟨p, he, hne⟩ := IsAlgebraic.exists_isIdempotentElem_aeval_mul_ne_zero
    (Algebra.IsAlgebraic.isAlgebraic (R := k) x) (by simpa using hx)
  have hone := he.eq_zero_or_eq_one_of_preconnectedSpace.resolve_left hne
  exact ⟨Polynomial.aeval x p, (mul_comm _ _).trans hone⟩

end TauCeti
