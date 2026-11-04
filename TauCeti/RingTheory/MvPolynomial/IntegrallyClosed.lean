/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Polynomial rings over an integrally closed domain are integrally closed

If `R` is an integrally closed domain, then so is the polynomial ring `MvPolynomial σ R` in any
set of variables (Stacks, Lemma 10.37.8 (030A), for one variable). Mathlib provides the
one-variable instance for `R[X]`; this file gives the multivariable one, by the same argument.
Over the fraction field `K` of `R`, the ring `MvPolynomial σ K` is a unique factorization domain,
hence integrally closed, and an element of `MvPolynomial σ K` integral over `MvPolynomial σ R`
has coefficients integral over `R` (Mathlib's `MvPolynomial.isIntegral_iff_isIntegral_coeff`),
hence in `R`.

## Main results

* `TauCeti.MvPolynomial.isIntegrallyClosed`: `MvPolynomial σ R` is integrally closed when `R` is an
  integrally closed domain.

## References

* [Stacks Project, Lemma 10.37.8](https://stacks.math.columbia.edu/tag/030A)
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

end TauCeti.MvPolynomial
