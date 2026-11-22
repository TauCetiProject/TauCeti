/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Algebra
public import TauCeti.GroupTheory.MonoidLocalization.Divisibility

/-!
# Squarefreeness and relative primality in localizations

If `S` is a localization of a commutative semiring `R`, then `S[X]` is a localization of `R[X]`.
So when `R[X]` is a decomposition monoid, relative primality, and with cancellation also
squarefreeness, pass from `R[X]` to `S[X]` (`IsRelPrime.map_localization_map`,
`Squarefree.map_localization_map`), by the monoid statements
`Submonoid.LocalizationMap.map_isRelPrime` and `Submonoid.LocalizationMap.map_squarefree`.
The main case is a GCD domain `R` and its fraction field: there `R[X]` is a GCD monoid by
Mathlib's form of Gauss's lemma. No primitivity is assumed: a constant factor of a polynomial
over `R` may become a unit over `S`, so these implications only lose information. Over `K[X]`
for a field `K`, a principal ideal domain, relative primality is the same as `IsCoprime`, which
makes resultants of the images nonzero; this is how the members of a squarefree basis are shown
to have nonzero pairwise resultants (`Finset.IsSquarefreeBasis.resultant_ne_zero`).

These facts complement Mathlib's
`Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map` and
`Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`.
-/

public section

open Polynomial

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
/-- If polynomials over `R` form a cancellative decomposition monoid, as over a GCD domain, a
squarefree polynomial over `R` stays squarefree over every localization of `R`, in particular
over the fraction field. -/
theorem Squarefree.map_localization_map [IsCancelMulZero R[X]] [DecompositionMonoid R[X]]
    (M : Submonoid R) [IsLocalization M S] {p : R[X]} (hp : Squarefree p) :
    Squarefree (p.map (algebraMap R S)) :=
  (IsLocalization.toLocalizationMap (M.map C) S[X]).map_squarefree hp

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
/-- If polynomials over `R` form a decomposition monoid, as over a GCD domain, relatively prime
polynomials over `R` stay relatively prime over every localization of `R`, in particular over
the fraction field. -/
theorem IsRelPrime.map_localization_map [DecompositionMonoid R[X]] (M : Submonoid R)
    [IsLocalization M S] {p q : R[X]} (h : IsRelPrime p q) :
    IsRelPrime (p.map (algebraMap R S)) (q.map (algebraMap R S)) :=
  (IsLocalization.toLocalizationMap (M.map C) S[X]).map_isRelPrime h
