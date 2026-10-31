/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Quasi-finiteness of the local homomorphism at a pair of primes

For an `R`-algebra `S` and primes `q` of `S` and `p = q ∩ R` of `R`, the local homomorphism
`R_p → S_q` is quasi-finite iff `S_q` is quasi-finite over `R`, that is, iff `S` is quasi-finite
over `R` at `q` (`Algebra.QuasiFiniteAt R q`): `R_p` is quasi-finite over `R`, and
quasi-finiteness is transitive (Mathlib's `Algebra.QuasiFinite.trans`) and descends along the
second map of a tower (Mathlib's `Algebra.QuasiFinite.of_restrictScalars`). Stalk maps of
morphisms of affine schemes are such local homomorphisms, so this is how quasi-finiteness at a
point is read off from a stalk.

## Main results

* `Localization.quasiFinite_localRingHom_iff`: the local homomorphism `R_p → S_q` is
  quasi-finite iff `S` is quasi-finite over `R` at `q`.
-/

public section

namespace Localization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The local homomorphism `R_p → S_q` at primes `q` over `p` is quasi-finite iff `S` is
quasi-finite over `R` at `q`. -/
theorem quasiFinite_localRingHom_iff (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (h : p = q.comap (algebraMap R S)) :
    (localRingHom p q (algebraMap R S) h).QuasiFinite ↔ Algebra.QuasiFiniteAt R q := by
  have : q.LiesOver p := ⟨h⟩
  let := AtPrime.algebraOfLiesOver p q
  refine RingHom.quasiFinite_algebraMap.trans
    ⟨fun _ ↦ .trans R (Localization.AtPrime p) _, fun _ ↦ .of_restrictScalars R _ _⟩

end Localization
