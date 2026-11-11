/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Reduced rings embed into their minimal-prime quotients

Since the minimal primes of a reduced ring intersect in `0`, a reduced ring embeds into the
product of its quotients by its minimal primes. No finiteness of the set of minimal primes is
needed.

## Main results

* `Ideal.injective_pi_quotient_mk_minimalPrimes`: a reduced ring embeds into the product of its
  quotients by its minimal primes.
-/

public section

namespace Ideal

/-- A reduced ring embeds into the product of its quotients by its minimal primes: the
intersection of the minimal primes is the nilradical, which is `0`. -/
theorem injective_pi_quotient_mk_minimalPrimes (A : Type*) [CommRing A] [IsReduced A] :
    Function.Injective (RingHom.pi fun p : minimalPrimes A ↦ Ideal.Quotient.mk p.1) := by
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_Pi_Quotient_mk, iInf_subtype, ← sInf_eq_iInf,
    minimalPrimes, Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced]

end Ideal
