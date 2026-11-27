/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.Algebra.CharP.Lemmas

/-!
# Frobenius and characteristic under localization at a prime

Let `R` be a commutative ring and `J` a prime ideal of `R`. If `R` has prime characteristic `p`,
so does its localization `R_J`, since `R_J` is a nontrivial ring receiving a ring map from `R`.
Frobenius of `R` sends the complement of `J` to itself, because `J` is its own preimage under
Frobenius (`Ideal.IsPrime.comap_frobenius`), and the induced endomorphism of `R_J` is Frobenius of
`R_J`.

## Main results

* `TauCeti.charP_localization_atPrime`: the localization of a ring of prime characteristic `p`
  at a prime ideal has characteristic `p`.
* `TauCeti.localRingHom_frobenius`: Frobenius of `R` induces Frobenius of `R_J`.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- Localizing a ring of prime characteristic `p` at a prime ideal preserves the characteristic. -/
instance charP_localization_atPrime (p : ℕ) [Fact p.Prime] [CharP R p] (J : Ideal R)
    [J.IsPrime] : CharP (Localization.AtPrime J) p :=
  charP_of_ringHom_of_prime (algebraMap R _) p

/-- Frobenius of `R` induces Frobenius of the localization `R_J` at a prime ideal `J`. -/
theorem localRingHom_frobenius (p : ℕ) [ExpChar R p] (J : Ideal R) [J.IsPrime]
    [ExpChar (Localization.AtPrime J) p] (hJ : J = J.comap (frobenius R p)) :
    Localization.localRingHom J J (frobenius R p) hJ = frobenius (Localization.AtPrime J) p :=
  IsLocalization.ringHom_ext J.primeCompl <| RingHom.ext fun a ↦ by
    simp [Localization.localRingHom_to_map, frobenius_def]

end TauCeti
