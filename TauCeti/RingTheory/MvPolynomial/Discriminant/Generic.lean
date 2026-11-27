/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Vieta

import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.FreeMonic

/-!
# Primality and squareness of the generic monic discriminant

Let `R` be a commutative ring. A monic polynomial of degree `m` over `R` has `m` free lower
coefficients, represented universally by `Polynomial.freeMonic R m` over `MvPolynomial (Fin m) R`.
Via Vieta's formulas and the fundamental theorem of symmetric polynomials, `MvPolynomial (Fin m) R`
embeds `R`-algebraically onto the symmetric polynomials in `m` root variables, sending
`(Polynomial.freeMonic R m).discr` to the square `δ ^ 2` of the Vandermonde alternant.

When `(2 : R) = 0`, the Vandermonde alternant is symmetric and hence descends to a square root of
`(Polynomial.freeMonic R m).discr` (`Polynomial.isSquare_discr_freeMonic_of_two_eq_zero`). Combining
this with `Polynomial.prime_discr_freeMonic`, over an integral domain `R` with `2 ≤ m` the
discriminant `(Polynomial.freeMonic R m).discr` is prime if and only if `(2 : R) ≠ 0`
(`Polynomial.prime_discr_freeMonic_iff`).

## Main results

* `MvPolynomial.map_vietaAlgHom_freeMonic`: `Polynomial.freeMonic R m` maps along
  `MvPolynomial.vietaAlgHom R m` to `∏ j, (X - C (X j))`.
* `MvPolynomial.vietaAlgHom_discr_freeMonic`: `MvPolynomial.vietaAlgHom` sends
  `(Polynomial.freeMonic R m).discr` to the square of the Vandermonde alternant.
* `Polynomial.isSquare_discr_freeMonic_of_two_eq_zero`, `Polynomial.prime_discr_freeMonic_iff`:
  squareness when `2 = 0` and characterization of when `(Polynomial.freeMonic R m).discr` is prime
  for `2 ≤ m`.

## References

* S. Lang, *Algebra*, Revised Third Edition, GTM 211, Springer (2002), Chapter IV, §8.
* I. M. Gelfand, M. M. Kapranov, A. V. Zelevinsky, *Discriminants, Resultants, and
  Multidimensional Determinants*, Birkhäuser (1994), Chapter 12, §1.B.
-/

public section

open Finset MvPolynomial Polynomial

namespace Polynomial

section FreeMonicPrime

/-- Mapping `Polynomial.freeMonic R m` along `MvPolynomial.vietaAlgHom` factors it into linear
root factors `∏ j, (Polynomial.X - Polynomial.C (MvPolynomial.X j))`. -/
theorem _root_.MvPolynomial.map_vietaAlgHom_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    (freeMonic R m).map (vietaAlgHom R m).toRingHom =
      ∏ j : Fin m, (Polynomial.X - Polynomial.C (MvPolynomial.X j)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  let P : Polynomial (MvPolynomial (Fin m) R) :=
    ∏ j : Fin m, (Polynomial.X - Polynomial.C (MvPolynomial.X j))
  have hmon : P.Monic :=
    monic_prod_of_monic Finset.univ _ fun j _ ↦ monic_X_sub_C _
  have hdeg : P.natDegree = m := by
    simp [P, natDegree_finsetProd_X_sub_C_eq_card]
  have hv_eq : vietaAlgHom R m = MvPolynomial.aeval (fun k : Fin m ↦ P.coeff k) := by
    refine MvPolynomial.algHom_ext fun k : Fin m ↦ ?_
    rw [MvPolynomial.aeval_X, vietaAlgHom_X]
  rw [hv_eq]
  exact map_aeval_coeff_freeMonic hmon hdeg

/-- Applying `MvPolynomial.vietaAlgHom` to `(Polynomial.freeMonic R m).discr` yields the square of
the Vandermonde alternant `TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ))`. -/
theorem _root_.MvPolynomial.vietaAlgHom_discr_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    vietaAlgHom R m (freeMonic R m).discr =
      TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ^ 2 := by
  have h := congrArg Polynomial.discr (map_vietaAlgHom_freeMonic R m)
  rw [(monic_freeMonic R m).discr_map, discr_prod_X_sub_C_eq_sq] at h
  have h' : vietaAlgHom R m (freeMonic R m).discr =
      (∏ i : Fin m, ∏ j ∈ Ioi i, (MvPolynomial.X i - MvPolynomial.X j :
        MvPolynomial (Fin m) R)) ^ 2 := by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  exact h'.trans (TauCeti.alternant_fin_val_sq m).symm

/-- When `(2 : R) = 0`, the discriminant of `Polynomial.freeMonic R m` is a square in
`MvPolynomial (Fin m) R`. -/
theorem isSquare_discr_freeMonic_of_two_eq_zero {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    (m : ℕ) : IsSquare (freeMonic R m).discr := by
  -- When `2 = 0`, `-1 = 1`, so the Vandermonde alternant is invariant under every permutation of
  -- the roots and descends along `vietaAlgHom` to a square root of the discriminant.
  obtain ⟨s, hs⟩ := mem_range_vietaAlgHom_iff.mpr
    (TauCeti.isSymmetric_alternant_of_two_eq_zero h2 (fun j : Fin m ↦ (j : ℕ)))
  refine ⟨s, vietaAlgHom_injective R m ?_⟩
  rw [vietaAlgHom_discr_freeMonic, map_mul, ← sq, hs]

/-- Over an integral domain `R` and for `m ≥ 2`, the discriminant of `Polynomial.freeMonic R m`
is prime if and only if `(2 : R) ≠ 0`. -/
theorem prime_discr_freeMonic_iff {R : Type*} [CommRing R] [IsDomain R] {m : ℕ} (hm : 2 ≤ m) :
    Prime (freeMonic R m).discr ↔ (2 : R) ≠ 0 :=
  ⟨fun hp h2 ↦ (isSquare_discr_freeMonic_of_two_eq_zero h2 m).not_prime hp,
    fun h2 ↦ prime_discr_freeMonic h2 hm⟩

end FreeMonicPrime

end Polynomial
