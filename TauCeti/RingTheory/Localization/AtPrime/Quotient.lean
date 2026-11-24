/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Localizations at primes of quotients

Localization at a prime commutes with quotients: for an ideal `J` of a commutative ring `R`, a
prime ideal `Q` of `R ⧸ J`, and a localization `S` of `R` at the preimage of `Q` in `R`, the
quotient `S ⧸ J S` is a localization of `R ⧸ J` at `Q`, and is therefore canonically
`(R ⧸ J)`-algebra isomorphic to `(R ⧸ J)_Q`.

## Main results

* `Ideal.isLocalization_atPrime_quotient`: `S ⧸ J S` is a localization of `R ⧸ J` at `Q`.
* `Ideal.quotientLocalizationAtPrimeEquiv`: the canonical `(R ⧸ J)`-algebra equivalence
  `S ⧸ J S ≃ₐ[R ⧸ J] Localization.AtPrime Q`.
* `Ideal.quotientLocalizationAtPrimeEquiv_algebraMap`: evaluation on elements of `R`.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Localization at a prime commutes with quotients: if `Q` is a prime ideal of `R ⧸ J` and `S` is
a localization of `R` at the preimage of `Q`, then `S ⧸ J S` is a localization of `R ⧸ J` at
`Q`. -/
instance isLocalization_atPrime_quotient (J : Ideal R) (Q : Ideal (R ⧸ J)) [Q.IsPrime]
    [IsLocalization.AtPrime S (Q.comap (Ideal.Quotient.mk J))] :
    IsLocalization.AtPrime (S ⧸ J.map (algebraMap R S)) Q := by
  have h := (inferInstance : IsLocalization
    (Algebra.algebraMapSubmonoid (R ⧸ J) (Q.comap (Ideal.Quotient.mk J)).primeCompl)
    (S ⧸ J.map (algebraMap R S)))
  rwa [Algebra.algebraMapSubmonoid, Ideal.Quotient.algebraMap_eq,
    Ideal.map_primeCompl_comap_of_surjective _ Ideal.Quotient.mk_surjective Q] at h

/-- For a prime ideal `Q` of `R ⧸ J` and a localization `S` of `R` at the preimage of `Q`, the
canonical `(R ⧸ J)`-algebra isomorphism `S ⧸ J S ≃ₐ[R ⧸ J] Localization.AtPrime Q`. -/
noncomputable def quotientLocalizationAtPrimeEquiv (J : Ideal R) (Q : Ideal (R ⧸ J)) [Q.IsPrime]
    [IsLocalization.AtPrime S (Q.comap (Ideal.Quotient.mk J))] :
    (S ⧸ J.map (algebraMap R S)) ≃ₐ[R ⧸ J] Localization.AtPrime Q :=
  IsLocalization.algEquiv Q.primeCompl (S ⧸ J.map (algebraMap R S)) (Localization.AtPrime Q)

/-- On elements of `R`, `quotientLocalizationAtPrimeEquiv` sends the image of `r` in `S ⧸ J S` to
the image of `r mod J` in `(R ⧸ J)_Q`. -/
@[simp]
theorem quotientLocalizationAtPrimeEquiv_algebraMap (J : Ideal R) (Q : Ideal (R ⧸ J)) [Q.IsPrime]
    [IsLocalization.AtPrime S (Q.comap (Ideal.Quotient.mk J))] (r : R) :
    J.quotientLocalizationAtPrimeEquiv (S := S) Q
        (algebraMap R (S ⧸ J.map (algebraMap R S)) r) =
      algebraMap (R ⧸ J) (Localization.AtPrime Q) (Ideal.Quotient.mk J r) := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ J) (S ⧸ J.map (algebraMap R S)),
    Ideal.Quotient.algebraMap_eq]
  exact (J.quotientLocalizationAtPrimeEquiv (S := S) Q).commutes (Ideal.Quotient.mk J r)

end Ideal
