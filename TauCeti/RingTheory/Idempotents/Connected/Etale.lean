/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Idempotents.Etale
public import TauCeti.RingTheory.Idempotents.Connected.Component

/-!
# Étale coordinate algebras of connected components

For a ring with locally connected prime spectrum, the quotient cutting out a connected
component is étale over the original ring. Thus a component of a smooth affine scheme is
again smooth. No reducedness or Noetherian hypothesis on the ring is needed.

## References

* The Stacks Project, Section 10.143, Étale ring maps.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [LocallyConnectedSpace (PrimeSpectrum R)]

/-- The coordinate algebra of a connected component is étale over the ambient ring. -/
instance etale_quotient_connectedComponentIdeal (x : PrimeSpectrum R) :
    Algebra.Etale R (R ⧸ PrimeSpectrum.connectedComponentIdeal x) := by
  -- The ideal's definition is not exposed across the module boundary, so recover its
  -- presentation using the exported membership theorem.
  have hI : PrimeSpectrum.connectedComponentIdeal x =
      Ideal.span {1 - PrimeSpectrum.connectedComponentIdempotent x} := by
    ext r
    rw [PrimeSpectrum.mem_connectedComponentIdeal_iff, Ideal.mem_span_singleton']
  rw [hI]
  exact etale_quotient_span_of_isIdempotentElem
    (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent x).one_sub

end TauCeti
