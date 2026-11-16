/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Frobenius on localizations at prime ideals

Let `R` be a commutative semiring of exponential characteristic `p` and `J` a prime ideal of `R`.
Since `a ^ p ∈ J` if and only if `a ∈ J`, the preimage of `J` under the Frobenius endomorphism of
`R` is `J` itself, and the induced local ring homomorphism `R_J →+* R_J` agrees with the Frobenius
endomorphism of the localization `R_J`.

## Main results

* `TauCeti.frobenius_localization_atPrime_eq_localRingHom`: Frobenius on `Localization.AtPrime J`
  equals `Localization.localRingHom J J (frobenius R p)`.
-/

public section

namespace TauCeti

/-- The Frobenius endomorphism of the localization `R_J` at a prime ideal `J` agrees with the local
ring homomorphism induced by the Frobenius endomorphism of `R`. -/
theorem frobenius_localization_atPrime_eq_localRingHom {R : Type*} [CommSemiring R] (p : ℕ)
    [ExpChar R p] (J : Ideal R) [hJ : J.IsPrime] [ExpChar (Localization.AtPrime J) p] :
    frobenius (Localization.AtPrime J) p =
      Localization.localRingHom J J (frobenius R p)
        (Ideal.ext fun _ ↦ (hJ.pow_mem_iff_mem p (expChar_pos R p)).symm) :=
  (Localization.localRingHom_unique J J (frobenius R p) _ fun a ↦ by
    simp [frobenius_def]).symm

end TauCeti
