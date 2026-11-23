/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Alternant
public import TauCeti.RingTheory.Polynomial.Vieta

import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Prime.Lemmas
import TauCeti.RingTheory.MvPolynomial.IrreducibleQuadratic
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import TauCeti.RingTheory.Polynomial.Resultant.WeightedHomogeneous

/-!
# Weighted homogeneity and primality of the generic monic discriminant

Let `R` be a commutative ring. A monic polynomial of degree `m` over `R` has `m` free lower
coefficients, represented universally by `Polynomial.freeMonic R m` over `MvPolynomial (Fin m) R`.
Under uniform scaling `rᵢ ↦ t rᵢ` of the roots, the elementary symmetric coefficient `aₖ` of
`X ^ (m - k)` acquires weight `k`, and over any commutative ring `R` and degree `m` the universal
monic discriminant `(Polynomial.freeMonic R m).discr` is weighted homogeneous of weight
`m * (m - 1)`. Over a unique factorization domain `R` and for `2 ≤ m`,
`(Polynomial.freeMonic R m).discr` is prime if and only if `(2 : R) ≠ 0` (and is a square when
`(2 : R) = 0`), so under those hypotheses the repeated-root locus where the generic monic
discriminant vanishes is an irreducible weighted-homogeneous hypersurface of weight `m * (m - 1)`.

1. **Weighted homogeneity.** Specializing `Polynomial.isWeightedHomogeneous_discr` to the
   universal monic polynomial `Polynomial.freeMonic R m` shows that
   `(Polynomial.freeMonic R m).discr` is weighted homogeneous of weight `m * (m - 1)` when `X k` is
   given weight `m - k` (`Polynomial.isWeightedHomogeneous_discr_freeMonic`).

2. **Primality of the generic monic discriminant.** Via Vieta's formulas and the fundamental
   theorem of symmetric polynomials, `MvPolynomial (Fin m) R` embeds `R`-algebraically onto the
   symmetric polynomials in `m` root variables, sending `(Polynomial.freeMonic R m).discr` to the
   square `δ ^ 2` of the Vandermonde product `δ = ∏_{i < j} (X i - X j)`. Over a unique
   factorization domain `R` with `2 ≤ m`, the linear factors `X i - X j` (`i < j`) are pairwise
   non-associated primes permuted transitively on ordered pairs of distinct indices by
   `Equiv.Perm (Fin m)`. Any symmetric factor of `δ ^ 2` divisible by one root difference is
   therefore divisible by `δ`, whereas permuting two variables negates `δ` and rules out symmetric
   unit multiples of `δ` whenever `(2 : R) ≠ 0`. Conversely, when `(2 : R) = 0`, `δ` is symmetric
   and the generic monic discriminant is a square
   (`Polynomial.isSquare_discr_freeMonic_of_two_eq_zero`). Hence `(Polynomial.freeMonic R m).discr`
   is prime if and only if `(2 : R) ≠ 0` (`Polynomial.prime_discr_freeMonic_iff`).

## Main results

* `Polynomial.isWeightedHomogeneous_discr_freeMonic`: weighted homogeneity of the universal monic
  discriminant.
* `MvPolynomial.vietaAlgHom_discr_freeMonic`: `MvPolynomial.vietaAlgHom` sends
  `(Polynomial.freeMonic R m).discr` to the square of the Vandermonde alternant.
* `Polynomial.isSquare_discr_freeMonic_of_two_eq_zero`,
  `Polynomial.prime_discr_freeMonic`, `Polynomial.prime_discr_freeMonic_iff`: squareness when
  `2 = 0` and unique factorization primality of `(Polynomial.freeMonic R m).discr` when `2 ≤ m`.

## References

* S. Lang, *Algebra*, Revised Third Edition, GTM 211, Springer (2002), Chapter IV, §8.
* I. M. Gelfand, M. M. Kapranov, A. V. Zelevinsky, *Discriminants, Resultants, and
  Multidimensional Determinants*, Birkhäuser (1994), Chapter 12, §1.B.
-/

public section

open Finset MvPolynomial Polynomial

/-! ### Weighted homogeneity of discriminants -/

namespace Polynomial

/-- The discriminant of `Polynomial.freeMonic R m` is weighted homogeneous of weight `m * (m - 1)`
when the variable `X i` (the coefficient in degree `i`) is given weight `m - i`. -/
theorem isWeightedHomogeneous_discr_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    (freeMonic R m).discr.IsWeightedHomogeneous (fun i : Fin m ↦ m - (i : ℕ)) (m * (m - 1)) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (freeMonic R m).discr 0]
    exact isWeightedHomogeneous_zero R _ _
  let w : Fin m → ℕ := fun i ↦ m - (i : ℕ)
  have h := isWeightedHomogeneous_discr (w := w) (1 : ℕ) (p := freeMonic R m) fun i ↦ by
    rw [natDegree_freeMonic, coeff_freeMonic, smul_eq_mul, mul_one]
    split_ifs with hi him
    · exact isWeightedHomogeneous_X R w ⟨i, hi⟩
    · rw [him, Nat.sub_self]; exact isWeightedHomogeneous_one R w
    · exact isWeightedHomogeneous_zero R w (m - i)
  rw [natDegree_freeMonic] at h
  simpa [w] using h

/-! ### Primality of the generic monic discriminant -/

section FreeMonicPrime

/-- Applying `MvPolynomial.vietaAlgHom` to `(Polynomial.freeMonic R m).discr` yields the square of
the Vandermonde alternant `TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ))`. -/
theorem _root_.MvPolynomial.vietaAlgHom_discr_freeMonic (R : Type*) [CommRing R] (m : ℕ) :
    vietaAlgHom R m (freeMonic R m).discr =
      TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ^ 2 := by
  have h := congrArg Polynomial.discr (map_vietaAlgHom_freeMonic R m)
  rw [(monic_freeMonic R m).discr_map, discr_prod_X_sub_C_eq_sq, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom] at h
  exact h.trans (TauCeti.alternant_fin_val_sq m).symm

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

/-- **Primality of the generic monic discriminant.** Over any unique factorization domain `R` in
which `2 ≠ 0`, the discriminant of `Polynomial.freeMonic R m` is prime in `MvPolynomial (Fin m) R`
for every `m ≥ 2`. -/
theorem prime_discr_freeMonic {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (h2 : (2 : R) ≠ 0) {m : ℕ} (hm : 2 ≤ m) :
    Prime (freeMonic R m).discr := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ < i₁ := Fin.mk_lt_mk.mpr (by omega)
  have hdvd_vand : MvPolynomial.X i₁ - MvPolynomial.X i₀ ∣
      TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) := by
    rw [TauCeti.alternant_fin_val_eq_vandermonde]
    exact dvd_trans
      (Finset.dvd_prod_of_mem (fun j ↦ MvPolynomial.X j - MvPolynomial.X i₀) (mem_Ioi.mpr h01))
      (Finset.dvd_prod_of_mem
        (fun i ↦ ∏ j ∈ Ioi i, (MvPolynomial.X j - MvPolynomial.X i)) (mem_univ i₀))
  refine ⟨fun hu ↦ ?_, fun f g hfg ↦ ?_⟩
  · have hu' : IsUnit (TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ^ 2) := by
      rw [← vietaAlgHom_discr_freeMonic]
      exact hu.map (vietaAlgHom R m)
    have hv_unit : IsUnit (TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ))) :=
      (isUnit_pow_iff (by decide : 2 ≠ 0)).mp hu'
    exact (irreducible_X_sub_X h01.ne').not_isUnit (isUnit_of_dvd_unit hdvd_vand hv_unit)
  · have hprod : vietaAlgHom R m f * vietaAlgHom R m g =
        TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ^ 2 := by
      rw [← map_mul, ← hfg, vietaAlgHom_discr_freeMonic]
    rcases TauCeti.isUnit_or_alternant_fin_val_dvd_of_isSymmetric_of_dvd_sq
      (isSymmetric_vietaAlgHom f) ⟨vietaAlgHom R m g, hprod.symm⟩ with hf | ⟨q₁, hq₁⟩
    · exact Or.inl (isUnit_of_isUnit_vietaAlgHom hf)
    rcases TauCeti.isUnit_or_alternant_fin_val_dvd_of_isSymmetric_of_dvd_sq
      (isSymmetric_vietaAlgHom g) ⟨vietaAlgHom R m f, by rw [mul_comm, hprod]⟩ with
        hg | ⟨q₂, hq₂⟩
    · exact Or.inr (isUnit_of_isUnit_vietaAlgHom hg)
    have hne0 : TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ≠ 0 :=
      TauCeti.alternant_ne_zero_of_injective Fin.val_injective
    have hmul : TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ^ 2 * (q₁ * q₂) =
        TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ^ 2 * 1 := by
      calc TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ^ 2 * (q₁ * q₂)
        _ = (TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) * q₁) *
              (TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) * q₂) := by ring
        _ = vietaAlgHom R m f * vietaAlgHom R m g := by rw [← hq₁, ← hq₂]
        _ = TauCeti.alternant (Fin m) R (fun j ↦ (j : ℕ)) ^ 2 * 1 := by rw [hprod, mul_one]
    have hq₁_unit : IsUnit q₁ :=
      IsUnit.of_mul_eq_one q₂ (mul_left_cancel₀ (pow_ne_zero 2 hne0) hmul)
    obtain ⟨r, hr, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hq₁_unit
    exact absurd (hq₁ ▸ isSymmetric_vietaAlgHom f)
      (TauCeti.not_isSymmetric_alternant_mul_C h2 (by simpa using hm) Fin.val_injective hr.ne_zero)

/-- Over a unique factorization domain `R` and for `m ≥ 2`, the discriminant of
`Polynomial.freeMonic R m` is prime if and only if `(2 : R) ≠ 0`. -/
theorem prime_discr_freeMonic_iff {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {m : ℕ} (hm : 2 ≤ m) :
    Prime (freeMonic R m).discr ↔ (2 : R) ≠ 0 :=
  ⟨fun hp h2 ↦ (isSquare_discr_freeMonic_of_two_eq_zero h2 m).not_prime hp,
    fun h2 ↦ prime_discr_freeMonic h2 hm⟩

end FreeMonicPrime

end Polynomial
