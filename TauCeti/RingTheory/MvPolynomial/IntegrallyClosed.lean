/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import TauCeti.RingTheory.Localization.LocalizationLocalization

/-!
# Polynomial rings over an integrally closed domain are integrally closed

If `R` is an integrally closed domain, then so is the polynomial ring `MvPolynomial σ R` in any
set of variables (Stacks, Lemma 10.37.8 (030A), for one variable). Mathlib provides the
one-variable instance for `R[X]`; this file gives the multivariable one, by the same argument.
Over the fraction field `K` of `R`, the ring `MvPolynomial σ K` is a unique factorization domain,
hence integrally closed, and an element of `MvPolynomial σ K` integral over `MvPolynomial σ R`
has coefficients integral over `R` (Mathlib's `MvPolynomial.isIntegral_iff_isIntegral_coeff`),
hence in `R`.

The same holds for normal rings, those whose localizations at primes are integrally closed
domains (Stacks, Definition 10.37.11 (00GV)): the local ring of `MvPolynomial σ R` at a prime `Q`
over `q` is a localization of `MvPolynomial σ R_q`.

## Main results

* `TauCeti.MvPolynomial.isIntegrallyClosed`: `MvPolynomial σ R` is integrally closed when `R` is an
  integrally closed domain.
* `TauCeti.MvPolynomial.forall_isDomain_and_isIntegrallyClosed`: a polynomial ring in any set of
  variables over a normal ring is normal.

## References

* [Stacks Project, Lemma 10.37.8](https://stacks.math.columbia.edu/tag/030A) and
  [Definition 10.37.11](https://stacks.math.columbia.edu/tag/00GV)
-/

public section

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial

attribute [local instance] algebraMvPolynomial in
/-- A polynomial ring, in any set of variables, over an integrally closed domain is integrally
closed. Stacks, Lemma 10.37.8 (030A), for any number of variables. -/
@[stacks 030A "any number of variables"]
instance isIntegrallyClosed {σ R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsIntegrallyClosed (MvPolynomial σ R) := by
  let K := FractionRing R
  have : IsIntegrallyClosed (MvPolynomial σ K) := UniqueFactorizationMonoid.instIsIntegrallyClosed
  suffices IsIntegrallyClosedIn (MvPolynomial σ R) (MvPolynomial σ K) from
    .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ (MvPolynomial σ K)
  refine isIntegrallyClosedIn_iff.mpr ⟨map_injective _ (IsFractionRing.injective _ _), ?_⟩
  refine fun {f} hf ↦ (mem_range_map_iff_coeffs_subset (f := algebraMap R K)).mpr ?_
  intro c hc
  obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp hc
  exact IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_iff_isIntegral_coeff.mp hf n)

attribute [local instance] algebraMvPolynomial in
/-- **A polynomial ring over a normal ring is normal.** If every localization of `R` at a prime is
an integrally closed domain, then so is every localization at a prime of the polynomial ring
`MvPolynomial σ R`, in any set of variables. For a prime `Q` over `q`, the local ring at `Q` is a
localization at a prime of `MvPolynomial σ R_q`, an integrally closed domain. Stacks, Lemma 10.37.8
(030A), for any number of variables. -/
@[stacks 030A "normal rings, any number of variables"]
theorem forall_isDomain_and_isIntegrallyClosed {σ R : Type*} [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (Q : Ideal (MvPolynomial σ R)) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  let q := Q.under R
  obtain ⟨_, _⟩ := hR q
  let M := q.primeCompl.map (C : R →+* MvPolynomial σ R)
  -- `MvPolynomial σ R_q` is the localization of `MvPolynomial σ R` at `M`, which misses `Q`.
  have hM : Disjoint (M : Set (MvPolynomial σ R)) Q := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ haQ
    exact ha haQ
  obtain ⟨P, _, -, ⟨e⟩⟩ := IsLocalization.exists_ringEquiv_localization_atPrime M
    (MvPolynomial σ (Localization.AtPrime q)) Q hM
  have : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  have : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization _ _ P.primeCompl_le_nonZeroDivisors
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv (R := Localization.AtPrime P) e.symm⟩

end TauCeti.MvPolynomial
