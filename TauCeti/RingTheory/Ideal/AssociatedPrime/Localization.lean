/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Associated primes and localization at a prime

For a module `M` over a Noetherian ring `R` and a prime `p`, this file characterises when the
maximal ideal of `R_p` is an associated prime of `M_p`.

## Main results

* `TauCeti.maximalIdeal_mem_associatedPrimes_localizedModule_iff`: the maximal ideal of `R_p` is
  associated to `M_p` exactly when `p` is an associated prime of `M`.
-/

public section

universe u v

open IsLocalRing

namespace TauCeti

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]

open Module

/-- For a module `M` over a Noetherian ring `R` and a prime `p`, the maximal ideal of `R_p` is an
associated prime of `M_p` exactly when `p` is an associated prime of `M`. This upgrades Mathlib's
`Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes` to an iff. -/
theorem maximalIdeal_mem_associatedPrimes_localizedModule_iff {p : Ideal R} [p.IsPrime] :
    maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M) ↔
      p ∈ associatedPrimes R M := by
  refine ⟨fun h ↦ ?_, associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes⟩
  simpa [← Ideal.under_def, Localization.AtPrime.under_maximalIdeal] using
    associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) _ h (IsNoetherian.noetherian _)

end TauCeti
