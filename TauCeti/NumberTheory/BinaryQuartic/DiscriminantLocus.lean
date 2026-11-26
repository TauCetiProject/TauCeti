/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Cubic.DiscriminantLocus
public import TauCeti.NumberTheory.BinaryQuartic.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.Polynomial.Primitive

/-!
# The discriminant locus of binary quartic forms

The discriminant `Δ` of the binary quartic form `a x⁴ + b x³ y + c x² y² + d x y³ + e y⁴`
(`TauCeti.BinaryQuartic.disc`, with `27 Δ = 4 I³ − J²`) is recorded here as the polynomial
`TauCeti.BinaryQuartic.discPoly R` in the five coefficient variables `a = X 0`, …, `e = X 4`. This
file proves the facts about it that make the locus `V(Δ, ∂Δ/∂e)` small:

* `Δ` is primitive: a constant dividing it is a unit
  (`TauCeti.BinaryQuartic.isUnit_of_C_dvd_discPoly`);
* as a polynomial in `e` over `R[a, b, c, d]` it is a cubic, with leading coefficient `256 a³`
  (nonzero when `256 ≠ 0` in `R`) and constant term `d² Disc(a, b, c, d)`, where `Disc` is the
  binary cubic discriminant
  (`TauCeti.BinaryQuartic.finSuccEquiv'_last_discPoly`); the constant term is the identity
  `Δ(a, b, c, d, 0) = d² Disc(a, b, c, d)` (`TauCeti.BinaryQuartic.disc_eq_sq_mul_discr`);
* over a field in which `2` and `3` are nonzero, `Δ` and `∂Δ/∂e` have no common factor other than
  units (`TauCeti.BinaryQuartic.isRelPrime_discPoly_pderiv`).

These are the inputs to the geometric sieve for strongly divisible discriminants of binary
quartic forms: the reduction of a form whose discriminant is strongly divisible by `p²` lies on
`V(Δ, ∂Δ/∂e)`, and primitivity over `ℤ` together with coprimality over `ℚ` is what makes that
subscheme of `𝔸⁵_ℤ` have codimension two.

## Implementation notes

The coprimality is certified by one specialization: at `(a, b, c, d) = (1, 0, 0, 1)` the pair
becomes `(256 e³ − 27, 768 e²)`, which is coprime in `K[e]`, while the leading coefficient
`256 a³` stays nonzero, so any common factor is free of `e`; such a factor divides both `256 a³`
and `d² Disc(a, b, c, d)`, which have no common prime factor.

## References

* M. Bhargava, A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), §2.6.
* M. Bhargava, *The geometric sieve and the density of squarefree values of invariant
  polynomials*, arXiv:1402.0031, proof of Lemma 3.6.
-/

public section

open MvPolynomial

namespace TauCeti.BinaryQuartic

variable {R : Type*} [CommRing R]

/-- A binary quartic form divisible by `x`, `x (a x³ + b x² y + c x y² + d y³)`, has discriminant
`d²` times the discriminant of the binary cubic form `a x³ + b x² y + c x y² + d y³`. -/
theorem disc_eq_sq_mul_discr {f : BinaryQuartic R} (hf : f 4 = 0) :
    disc f = f 3 ^ 2 * Cubic.discr ⟨f 0, f 1, f 2, f 3⟩ := by
  rw [disc_def, hf, Cubic.discr]
  ring

variable (R) in
/-- The discriminant of the binary quartic form `a x⁴ + b x³ y + c x² y² + d x y³ + e y⁴`, as a
polynomial in the coefficients `a = X 0`, …, `e = X 4`: `BinaryQuartic.disc` of the generic
form. -/
noncomputable def discPoly : MvPolynomial (Fin 5) R :=
  disc X

/-- The generic quartic discriminant is `BinaryQuartic.disc` of the generic form `X`. -/
theorem discPoly_def : discPoly R = disc X := (rfl)

/-- Evaluating the generic discriminant at a binary quartic form gives its discriminant. -/
@[simp]
theorem eval_discPoly (f : BinaryQuartic R) : eval f (discPoly R) = disc f := by
  rw [discPoly_def, ← disc_comp]
  congr
  funext i
  simp

/-- The generic discriminant is compatible with maps of the coefficient ring. -/
@[simp]
theorem map_discPoly {S : Type*} [CommRing S] (φ : R →+* S) :
    map φ (discPoly R) = discPoly S := by
  rw [discPoly_def, ← disc_comp]
  congr
  funext i
  simp

/-- **The quartic discriminant is primitive.** A constant dividing `discPoly R` is a unit. -/
theorem isUnit_of_C_dvd_discPoly {r : R} (h : C r ∣ discPoly R) : IsUnit r := by
  -- `r` divides the values `256` at `(a, b, c, d, e) = (1, 0, 0, 0, 1)` and `−27` at
  -- `(1, 0, 0, 1, 0)`, and `1 = 19 · 27 − 2 · 256`.
  obtain ⟨g, hg⟩ := h
  have h1 := congrArg (eval ![1, 0, 0, 0, 1]) hg
  have h2 := congrArg (eval ![1, 0, 0, 1, 0]) hg
  simp only [eval_discPoly, eval_mul, eval_C] at h1 h2
  norm_num [disc_def] at h1 h2
  refine isUnit_of_dvd_one ⟨-19 * eval ![1, 0, 0, 1, 0] g - 2 * eval ![1, 0, 0, 0, 1] g, ?_⟩
  linear_combination -19 * h2 - 2 * h1

/-- **The quartic discriminant as a polynomial in `e`.** Singling out the last coefficient `e`,
`Δ` is the cubic
`256 a³ e³ + (−192 a²bd − 128 a²c² + 144 ab²c − 27 b⁴) e²`
`+ (144 a²cd² − 6 ab²d² − 80 abc²d + 16 ac⁴ + 18 b³cd − 4 b²c³) e + d² Disc(a, b, c, d)`
over `R[a, b, c, d]`. -/
theorem finSuccEquiv'_last_discPoly :
    finSuccEquiv' R (Fin.last 4) (discPoly R) =
      Polynomial.C (256 * X 0 ^ 3) * Polynomial.X ^ 3 +
        Polynomial.C (-192 * X 0 ^ 2 * X 1 * X 3 - 128 * X 0 ^ 2 * X 2 ^ 2 +
          144 * X 0 * X 1 ^ 2 * X 2 - 27 * X 1 ^ 4) * Polynomial.X ^ 2 +
        Polynomial.C (144 * X 0 ^ 2 * X 2 * X 3 ^ 2 - 6 * X 0 * X 1 ^ 2 * X 3 ^ 2 -
          80 * X 0 * X 1 * X 2 ^ 2 * X 3 + 16 * X 0 * X 2 ^ 4 + 18 * X 1 ^ 3 * X 2 * X 3 -
          4 * X 1 ^ 2 * X 2 ^ 3) * Polynomial.X +
        Polynomial.C (X 3 ^ 2 * Cubic.discrPoly R) := by
  have h0 : finSuccEquiv' R (Fin.last 4) (X 0) = Polynomial.C (X 0) :=
    finSuccEquiv'_X_succAbove (Fin.last 4) 0
  have h1 : finSuccEquiv' R (Fin.last 4) (X 1) = Polynomial.C (X 1) :=
    finSuccEquiv'_X_succAbove (Fin.last 4) 1
  have h2 : finSuccEquiv' R (Fin.last 4) (X 2) = Polynomial.C (X 2) :=
    finSuccEquiv'_X_succAbove (Fin.last 4) 2
  have h3 : finSuccEquiv' R (Fin.last 4) (X 3) = Polynomial.C (X 3) :=
    finSuccEquiv'_X_succAbove (Fin.last 4) 3
  have h4 : finSuccEquiv' R (Fin.last 4) (X 4) = Polynomial.X :=
    finSuccEquiv'_X_self (Fin.last 4)
  simp only [discPoly_def, disc_def, Cubic.discrPoly_def, map_add, map_sub, map_mul, map_pow,
    map_ofNat, map_neg, h0, h1, h2, h3, h4]
  ring

/-- The leading coefficient `256 a³` of the quartic discriminant in `e` is nonzero when
`256 ≠ 0`. -/
private theorem C_256_mul_X_pow_ne_zero (h : (256 : R) ≠ 0) :
    (256 * X 0 ^ 3 : MvPolynomial (Fin 4) R) ≠ 0 :=
  fun h0 ↦ h (by simpa using congrArg (eval 1) h0)

/-- The quartic discriminant has degree three in `e` when `256 ≠ 0` in `R`. -/
theorem natDegree_finSuccEquiv'_last_discPoly (h : (256 : R) ≠ 0) :
    (finSuccEquiv' R (Fin.last 4) (discPoly R)).natDegree = 3 := by
  rw [finSuccEquiv'_last_discPoly]
  exact Polynomial.natDegree_cubic (C_256_mul_X_pow_ne_zero h)

/-- The leading coefficient of the quartic discriminant in `e` is `256 a³` when `256 ≠ 0` in
`R`. -/
theorem leadingCoeff_finSuccEquiv'_last_discPoly (h : (256 : R) ≠ 0) :
    (finSuccEquiv' R (Fin.last 4) (discPoly R)).leadingCoeff = 256 * X 0 ^ 3 := by
  rw [finSuccEquiv'_last_discPoly]
  exact Polynomial.leadingCoeff_cubic (C_256_mul_X_pow_ne_zero h)

/-- **The quartic discriminant locus has no divisorial part.** Over a field in which `2` and `3`
are nonzero, the binary quartic discriminant and its partial derivative in `e` have no common
factor other than units. -/
theorem isRelPrime_discPoly_pderiv {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    IsRelPrime (discPoly K) (pderiv (Fin.last 4) (discPoly K)) := by
  have h256 : (256 : K) ≠ 0 := by
    rw [show (256 : K) = 2 ^ 8 by norm_num]
    exact pow_ne_zero 8 h2
  have hlead : (finSuccEquiv' K (Fin.last 4) (discPoly K)).coeff 3 = 256 * X 0 ^ 3 := by
    have := leadingCoeff_finSuccEquiv'_last_discPoly h256
    rwa [Polynomial.leadingCoeff, natDegree_finSuccEquiv'_last_discPoly h256] at this
  have hconst : (finSuccEquiv' K (Fin.last 4) (discPoly K)).coeff 0 =
      X 3 ^ 2 * Cubic.discrPoly K := by
    rw [finSuccEquiv'_last_discPoly, Polynomial.coeff_zero_eq_eval_zero]
    simp
  -- The specialization at `(a, b, c, d) = (1, 0, 0, 1)`.
  have hspec : (finSuccEquiv' K (Fin.last 4) (discPoly K)).map (eval ![1, 0, 0, 1]) =
      256 * Polynomial.X ^ 3 - 27 := by
    rw [finSuccEquiv'_last_discPoly]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    simp [map_ofNat, Cubic.discr]
    ring
  refine IsRelPrime.of_map (finSuccEquiv' K (Fin.last 4)) ?_
  rw [finSuccEquiv'_pderiv]
  refine (Polynomial.isPrimitive_of_isRelPrime_coeff (i := 3) (j := 0) ?_)
    |>.isRelPrime_of_isCoprime_map (eval ![1, 0, 0, 1]) ?_ ?_
  · -- The coefficients `256 a³` and `d² Disc(a, b, c, d)` have no common factor, as
    -- `a ∤ d² Disc(a, b, c, d)`: the latter is `−3` at `(a, b, c, d) = (0, 1, 1, 1)`.
    have hu : IsUnit (256 : MvPolynomial (Fin 4) K) := by
      rw [← map_ofNat C 256]
      exact (Ne.isUnit h256).map C
    have hX : ¬ X 0 ∣ (X 3 ^ 2 * Cubic.discrPoly K : MvPolynomial (Fin 4) K) := by
      rintro ⟨s, hs⟩
      have hv : eval ![0, 1, 1, 1] (X 3 ^ 2 * Cubic.discrPoly K) = (-3 : K) := by
        simp [Cubic.discr]
        norm_num
      rw [hs, eval_mul, eval_X, Matrix.cons_val_zero, zero_mul] at hv
      exact h3 (by linear_combination hv)
    rw [hlead, hconst, isRelPrime_mul_unit_left_left hu]
    exact ((prime_X.irreducible.isRelPrime_iff_not_dvd).2 hX).pow_left
  · rw [leadingCoeff_finSuccEquiv'_last_discPoly h256]
    simpa using h256
  · have hderiv : Polynomial.derivative (256 * Polynomial.X ^ 3 - 27 : Polynomial K) =
        768 * Polynomial.X ^ 2 := by
      simp [map_ofNat]
      ring
    rw [← Polynomial.derivative_map, hspec, hderiv]
    -- Bézout for `(256 e³ − 27, 768 e²)`, with `c = 1/3`.
    set c : Polynomial K := Polynomial.C 3⁻¹
    have hc : 3 * c = 1 := by
      rw [← map_ofNat Polynomial.C 3, ← map_mul, mul_inv_cancel₀ h3, map_one]
    exact ⟨-c ^ 3, c ^ 4 * Polynomial.X,
      by linear_combination (9 * c ^ 2 + 3 * c + 1 + 256 * c ^ 3 * Polynomial.X ^ 3) * hc⟩

end TauCeti.BinaryQuartic
