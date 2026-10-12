/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Minimal primes below a prime with a domain localization

Let `m` be a prime of a commutative ring `A` such that the localization `A_m` is a domain, as it
is when `A_m` is a regular local ring. Then the kernel of `A → A_m` is a prime contained in every
prime `q ≤ m`, so it is the only minimal prime of `A` contained in `m`. Consequently every prime
`q ≤ m` contains every minimal prime `P ≤ m`: the primes below `m` all lie on the single
irreducible component `V(P)` of `Spec A` through `m`. This is what makes the height of `m` a lower
bound for the dimension of that component.

## Main results

* `TauCeti.le_of_mem_minimalPrimes_of_isDomain_localization`: if `A_m` is a domain, a minimal
  prime `P ≤ m` lies below every prime `q ≤ m`.
-/

public section

namespace TauCeti

/-- If the localization of `A` at a prime `m` is a domain, then a minimal prime `P ≤ m` of `A`
lies below every prime `q ≤ m`. -/
theorem le_of_mem_minimalPrimes_of_isDomain_localization {A : Type*} [CommRing A]
    {m P q : Ideal A} [m.IsPrime] [q.IsPrime] [IsDomain (Localization.AtPrime m)]
    (hP : P ∈ minimalPrimes A) (hPm : P ≤ m) (hqm : q ≤ m) : P ≤ q := by
  -- The kernel of `A → A_m` lies below every prime contained in `m`.
  have hker {q' : Ideal A} [q'.IsPrime] (hq' : q' ≤ m) :
      RingHom.ker (algebraMap A (Localization.AtPrime m)) ≤ q' := fun a ha ↦ by
    obtain ⟨⟨s, hs⟩, hsa⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ a).mp ha
    exact (‹q'.IsPrime›.mem_or_mem (hsa ▸ q'.zero_mem)).resolve_left fun h ↦ hs (hq' h)
  have := hP.1.1
  exact (hP.2 ⟨RingHom.ker_isPrime _, bot_le⟩ (hker hPm)).trans (hker hqm)

end TauCeti
