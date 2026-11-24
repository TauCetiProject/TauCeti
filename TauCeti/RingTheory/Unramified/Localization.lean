/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Unramifiedness at a prime after localizing the base

Let `S` be an `R`-algebra, `M` a submonoid of `R`, and `Sₘ` the localization of `S` at the image
of `M`, an algebra over the localization `Rₘ`. A prime `q` of `Sₘ` and the prime `q ∩ S` below it
have the same local ring, and inverting elements of `R` does not change formal unramifiedness. So
`Sₘ` is unramified over `Rₘ` at `q` exactly when `S` is unramified over `R` at `q ∩ S`.

This is what lets a statement about the unramified locus of `S` over `R` be checked after
localizing the base at a prime, as in inductions on the dimension of the base.

## Main results

* `Algebra.isUnramifiedAt_localization_iff`: `Sₘ` is unramified over `Rₘ` at `q` iff `S` is
  unramified over `R` at `q ∩ S`.
-/

public section

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ] [Algebra R Rₘ] [Algebra S Sₘ] [Algebra Rₘ Sₘ]
  [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]

/-- Let `Sₘ` be the localization of an `R`-algebra `S` at the image of a submonoid `M` of `R`, an
algebra over the localization `Rₘ` of `R` at `M`. Then `Sₘ` is unramified over `Rₘ` at a prime
`q` if and only if `S` is unramified over `R` at the prime `q ∩ S`. -/
theorem isUnramifiedAt_localization_iff (M : Submonoid R) [IsLocalization M Rₘ]
    [IsLocalization (algebraMapSubmonoid S M) Sₘ] (q : Ideal Sₘ) [q.IsPrime] :
    IsUnramifiedAt Rₘ q ↔ IsUnramifiedAt R (q.under S) := by
  -- The local ring of `Sₘ` at `q` is the local ring of `S` at `q ∩ S`, as an `S`-algebra.
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (algebraMapSubmonoid S M) (Localization.AtPrime q) q
  let e : Localization.AtPrime (q.under S) ≃ₐ[R] Localization.AtPrime q :=
    (IsLocalization.algEquiv (q.under S).primeCompl _ _).restrictScalars R
  have : FormallyUnramified R Rₘ := .of_isLocalization M
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have := FormallyUnramified.comp R Rₘ (Localization.AtPrime q)
    exact .of_equiv e.symm
  · have : FormallyUnramified R (Localization.AtPrime q) := .of_equiv e
    exact FormallyUnramified.of_restrictScalars R _ _

end Algebra
