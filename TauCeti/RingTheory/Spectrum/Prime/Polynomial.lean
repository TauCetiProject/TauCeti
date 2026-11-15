/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# The prime spectrum of a polynomial ring

The map on prime spectra induced by evaluation at zero identifies the spectrum of the
coefficient ring with the vanishing locus of the polynomial coordinate.

## Main results

* `Polynomial.range_comap_evalRingHom_zero`: the image of evaluation at zero on prime spectra
  consists of the prime ideals containing `X`.
-/

public section

namespace Polynomial

/-- Evaluation at zero induces a map on prime spectra whose image is the vanishing locus of
the polynomial coordinate. -/
theorem range_comap_evalRingHom_zero (R : Type*) [CommRing R] :
    Set.range (PrimeSpectrum.comap (evalRingHom (0 : R))) =
      {q : PrimeSpectrum R[X] | X ∈ q.asIdeal} := by
  rw [range_comap_of_surjective _ _ (eval_surjective (0 : R)), ker_evalRingHom]
  ext q
  simp [PrimeSpectrum.mem_zeroLocus]

end Polynomial
