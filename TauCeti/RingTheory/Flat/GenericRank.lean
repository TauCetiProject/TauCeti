/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Generic rank of a finite flat module over a domain

The rank of a finite flat module over an integral domain is the dimension of the module over
the domain, even when the module is not globally free. This identifies the common fibre rank
of a finite flat algebra with the degree computed after passing to fraction fields.

The key point is that the generic stalk is a localization at nonzero elements, which preserves
dimension over the original domain. Finite flatness then makes the stalk rank constant along
specialization from the generic point.
-/

public section

universe u v

namespace TauCeti

/-- A finite flat module over a domain has the same stalk rank at every prime, namely its
dimension over the domain. This applies to finite projective modules that need not be free. -/
theorem rankAtStalk_eq_finrank_of_isDomain {R : Type u} {M : Type v}
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] [Module.Finite R M] (p : PrimeSpectrum R) :
    Module.rankAtStalk M p = Module.finrank R M := by
  have hgeneric : Module.rankAtStalk M (⊥ : PrimeSpectrum R) = Module.finrank R M := by
    unfold Module.rankAtStalk
    exact (IsLocalization.finrank_eq (Localization.AtPrime (⊥ : Ideal R))
      (⊥ : Ideal R).primeCompl (Ideal.primeCompl_le_nonZeroDivisors ⊥)).trans
      (IsLocalizedModule.finrank_eq (⊥ : Ideal R).primeCompl
        (LocalizedModule.mkLinearMap _ M) (Ideal.primeCompl_le_nonZeroDivisors ⊥))
  exact (Module.rankAtStalk_eq_of_le_of_finite_of_flat M bot_le).symm.trans hgeneric

end TauCeti
