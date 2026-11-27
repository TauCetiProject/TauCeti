/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import TauCeti.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.Polynomial.Primitive

/-!
# The discriminant locus of binary cubic forms

The discriminant of the binary cubic form `a x³ + b x² y + c x y² + d y³` is Mathlib's
`Cubic.discr`, the polynomial `b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd` in the coefficients. This file
records it as the polynomial `TauCeti.Cubic.discrPoly R` in the four coefficient variables
`a = X 0`, `b = X 1`, `c = X 2`, `d = X 3`, and proves the facts about it that make the locus
`V(Disc, ∂Disc/∂d)` small:

* `Disc` is primitive: a constant dividing it is a unit (`TauCeti.Cubic.isUnit_of_C_dvd_discrPoly`);
* as a polynomial in `d` over `R[a, b, c]` it is
  `−27a² d² + (18abc − 4b³) d + (b²c² − 4ac³)`
  (`TauCeti.Cubic.finSuccEquiv'_last_discrPoly`), of degree two with leading coefficient `−27a²`
  as soon as `27 ≠ 0` in `R`;
* over a field in which `2` and `3` are nonzero, `Disc` and `∂Disc/∂d` have no common factor
  other than units (`TauCeti.Cubic.isRelPrime_discrPoly_pderiv`).

These are the inputs to the geometric sieve for strongly divisible discriminants of binary cubic
forms: the reduction of a form whose discriminant is strongly divisible by `p²` lies on
`V(Disc, ∂Disc/∂d)`, and primitivity over `ℤ` together with coprimality over `ℚ` is what makes
that subscheme of `𝔸⁴_ℤ` have codimension two.

## Implementation notes

The coprimality is certified by one specialization: at `(a, b, c) = (1, 0, 1)` the pair becomes
`(−27d² − 4, −54d)`, which is coprime in `K[d]`, while the leading coefficient `−27a²` stays
nonzero, so any common factor is free of `d`; such a factor divides both `−27a²` and
`b²c² − 4ac³`, which have no common prime factor.

## References

* M. Bhargava, *The geometric sieve and the density of squarefree values of invariant
  polynomials*, arXiv:1402.0031, proof of Lemma 3.6.
* M. Bhargava, A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), §2.6.
-/

public section

open MvPolynomial

namespace TauCeti.Cubic

variable (R : Type*) [CommRing R]

/-- The discriminant `b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd` of the binary cubic form
`a x³ + b x² y + c x y² + d y³`, as a polynomial in the coefficients `a = X 0`, `b = X 1`,
`c = X 2`, `d = X 3`: Mathlib's `Cubic.discr` of the generic cubic. -/
noncomputable def discrPoly : MvPolynomial (Fin 4) R :=
  Cubic.discr ⟨X 0, X 1, X 2, X 3⟩

variable {R}

/-- The generic cubic discriminant, written out in the coefficient variables. -/
theorem discrPoly_def :
    discrPoly R = X 1 ^ 2 * X 2 ^ 2 - 4 * X 0 * X 2 ^ 3 - 4 * X 1 ^ 3 * X 3 -
      27 * X 0 ^ 2 * X 3 ^ 2 + 18 * X 0 * X 1 * X 2 * X 3 := (rfl)

/-- Evaluating the generic discriminant at a coefficient vector gives the discriminant of that
cubic. -/
@[simp]
theorem eval_discrPoly (v : Fin 4 → R) :
    eval v (discrPoly R) = Cubic.discr ⟨v 0, v 1, v 2, v 3⟩ := by
  simp [discrPoly_def, Cubic.discr]

/-- The generic discriminant is compatible with maps of the coefficient ring. -/
@[simp]
theorem map_discrPoly {S : Type*} [CommRing S] (φ : R →+* S) :
    map φ (discrPoly R) = discrPoly S := by
  simp [discrPoly_def]

/-- **The cubic discriminant is primitive.** A constant dividing `discrPoly R` is a unit. -/
theorem isUnit_of_C_dvd_discrPoly {r : R} (h : C r ∣ discrPoly R) : IsUnit r := by
  -- `r` divides the value `1` of the discriminant at `(a, b, c, d) = (0, 1, 1, 0)`.
  obtain ⟨g, hg⟩ := h
  have h1 := congrArg (eval ![0, 1, 1, 0]) hg
  simp only [eval_discrPoly, eval_mul, eval_C] at h1
  refine isUnit_of_dvd_one ⟨eval ![0, 1, 1, 0] g, ?_⟩
  rw [← h1]
  simp [Cubic.discr]

/-- **The cubic discriminant as a polynomial in `d`.** Singling out the last coefficient `d`,
`Disc = −27a² d² + (18abc − 4b³) d + (b²c² − 4ac³)` over `R[a, b, c]`. -/
theorem finSuccEquiv'_last_discrPoly :
    finSuccEquiv' R (Fin.last 3) (discrPoly R) =
      Polynomial.C (-27 * X 0 ^ 2) * Polynomial.X ^ 2 +
        Polynomial.C (18 * X 0 * X 1 * X 2 - 4 * X 1 ^ 3) * Polynomial.X +
        Polynomial.C (X 1 ^ 2 * X 2 ^ 2 - 4 * X 0 * X 2 ^ 3) := by
  have h0 : finSuccEquiv' R (Fin.last 3) (X 0) = Polynomial.C (X 0) :=
    finSuccEquiv'_X_succAbove (Fin.last 3) 0
  have h1 : finSuccEquiv' R (Fin.last 3) (X 1) = Polynomial.C (X 1) :=
    finSuccEquiv'_X_succAbove (Fin.last 3) 1
  have h2 : finSuccEquiv' R (Fin.last 3) (X 2) = Polynomial.C (X 2) :=
    finSuccEquiv'_X_succAbove (Fin.last 3) 2
  have h3 : finSuccEquiv' R (Fin.last 3) (X 3) = Polynomial.X :=
    finSuccEquiv'_X_self (Fin.last 3)
  simp only [discrPoly_def, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg, h0, h1, h2,
    h3]
  ring

/-- The leading coefficient `−27a²` of the cubic discriminant in `d` is nonzero when `27 ≠ 0`. -/
private theorem neg_27_mul_X_sq_ne_zero (h : (27 : R) ≠ 0) :
    (-27 * X 0 ^ 2 : MvPolynomial (Fin 3) R) ≠ 0 :=
  fun h0 ↦ h (by simpa using congrArg (eval 1) h0)

/-- The cubic discriminant has degree two in `d` when `27 ≠ 0` in `R`. -/
theorem natDegree_finSuccEquiv'_last_discrPoly (h : (27 : R) ≠ 0) :
    (finSuccEquiv' R (Fin.last 3) (discrPoly R)).natDegree = 2 := by
  rw [finSuccEquiv'_last_discrPoly]
  exact Polynomial.natDegree_quadratic (neg_27_mul_X_sq_ne_zero h)

/-- The leading coefficient of the cubic discriminant in `d` is `−27a²` when `27 ≠ 0` in `R`. -/
theorem leadingCoeff_finSuccEquiv'_last_discrPoly (h : (27 : R) ≠ 0) :
    (finSuccEquiv' R (Fin.last 3) (discrPoly R)).leadingCoeff = -27 * X 0 ^ 2 := by
  rw [finSuccEquiv'_last_discrPoly]
  exact Polynomial.leadingCoeff_quadratic (neg_27_mul_X_sq_ne_zero h)

/-- **The cubic discriminant locus has no divisorial part.** Over a field in which `2` and `3` are
nonzero, the cubic discriminant and its partial derivative in `d` have no common factor other than
units. -/
theorem isRelPrime_discrPoly_pderiv {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    IsRelPrime (discrPoly K) (pderiv (Fin.last 3) (discrPoly K)) := by
  have h27 : (27 : K) ≠ 0 := by
    rw [show (27 : K) = 3 ^ 3 by norm_num]
    exact pow_ne_zero 3 h3
  have hlead : (finSuccEquiv' K (Fin.last 3) (discrPoly K)).coeff 2 = -27 * X 0 ^ 2 := by
    have := Polynomial.coeff_natDegree (p := finSuccEquiv' K (Fin.last 3) (discrPoly K))
    rwa [natDegree_finSuccEquiv'_last_discrPoly h27,
      leadingCoeff_finSuccEquiv'_last_discrPoly h27] at this
  have hconst : (finSuccEquiv' K (Fin.last 3) (discrPoly K)).coeff 0 =
      X 1 ^ 2 * X 2 ^ 2 - 4 * X 0 * X 2 ^ 3 := by
    rw [finSuccEquiv'_last_discrPoly, Polynomial.coeff_zero_eq_eval_zero]
    simp
  -- The specialization at `(a, b, c) = (1, 0, 1)`.
  have hspec : (finSuccEquiv' K (Fin.last 3) (discrPoly K)).map (eval ![1, 0, 1]) =
      -27 * Polynomial.X ^ 2 - 4 := by
    rw [finSuccEquiv'_last_discrPoly]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    simp [map_ofNat]
    ring
  refine IsRelPrime.of_map (finSuccEquiv' K (Fin.last 3)) ?_
  rw [finSuccEquiv'_pderiv]
  refine (Polynomial.isPrimitive_of_isRelPrime_coeff (i := 2) (j := 0) ?_)
    |>.isRelPrime_of_isCoprime_map (eval ![1, 0, 1]) ?_ ?_
  · -- The coefficients `−27a²` and `b²c² − 4ac³` have no common factor, as `a ∤ b²c² − 4ac³`.
    have hu : IsUnit (-27 : MvPolynomial (Fin 3) K) := by
      rw [← map_ofNat C 27, ← map_neg]
      exact (Ne.isUnit (neg_ne_zero.2 h27)).map C
    have hX : ¬ X 0 ∣ (X 1 ^ 2 * X 2 ^ 2 - 4 * X 0 * X 2 ^ 3 : MvPolynomial (Fin 3) K) := by
      rintro ⟨s, hs⟩
      simpa using congrArg (eval ![0, 1, 1]) hs
    rw [hlead, hconst, isRelPrime_mul_unit_left_left hu]
    exact ((prime_X.irreducible.isRelPrime_iff_not_dvd).2 hX).pow_left
  · rw [leadingCoeff_finSuccEquiv'_last_discrPoly h27]
    simpa using h27
  · have hderiv : Polynomial.derivative (-27 * Polynomial.X ^ 2 - 4 : Polynomial K) =
        -54 * Polynomial.X := by
      simp
      ring
    rw [← Polynomial.derivative_map, hspec, hderiv]
    -- Bézout for `(−27d² − 4, −54d)`, with `c = 1/2`.
    set c : Polynomial K := Polynomial.C 2⁻¹
    have hc : 2 * c = 1 := by
      rw [← map_ofNat Polynomial.C 2, ← map_mul, mul_inv_cancel₀ h2, map_one]
    exact ⟨-c ^ 2, c ^ 3 * Polynomial.X,
      by linear_combination (2 * c + 1 - 27 * c ^ 2 * Polynomial.X ^ 2) * hc⟩

end TauCeti.Cubic
