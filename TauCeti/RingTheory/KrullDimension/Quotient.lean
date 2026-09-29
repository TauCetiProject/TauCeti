/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The dimension of a closed subset of a spectrum

For an ideal `I` of a commutative ring `R`, the quotient map `R → R ⧸ I` identifies
`Spec (R ⧸ I)` homeomorphically with the closed subset `V(I)` of `Spec R`. So the topological Krull
dimension of `V(I)` is the Krull dimension of `R ⧸ I`.

## Main results

* `Ideal.topologicalKrullDim_zeroLocus`: the closed subset `V(I)` of `Spec R` has the Krull
  dimension of `R ⧸ I`.
-/

public section

namespace Ideal

open PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- The closed subset `V(I)` of `Spec R` has the Krull dimension of `R ⧸ I`. -/
@[simp]
theorem topologicalKrullDim_zeroLocus (I : Ideal R) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set R)) = ringKrullDim (R ⧸ I) := by
  have hi := isClosedEmbedding_comap_of_surjective _ _ (Quotient.mk_surjective (I := I))
  have hrange :
      Set.range (PrimeSpectrum.comap (Quotient.mk I)) = PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [range_comap_of_surjective _ _ Quotient.mk_surjective, mk_ker]
  rw [← topologicalKrullDim_eq_ringKrullDim]
  exact ((hi.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm.isHomeomorph
    |>.topologicalKrullDim_eq

end Ideal
