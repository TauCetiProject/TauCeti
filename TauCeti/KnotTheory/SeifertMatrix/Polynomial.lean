/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Symmetric
public import TauCeti.KnotTheory.Alexander

/-!
# Polynomial descent of the Seifert Alexander invariant

The normalized Alexander polynomial of any even-size matrix is a polynomial in
`t + t⁻¹ - 2`. After writing `t = s²`, this is the square of the Conway variable
`z = s⁻¹ - s`. Thus the matrix invariant comes from an even ordinary polynomial
with coefficients in the original ring; integer matrices give integer coefficients.

These are algebraic existence results, using `TauCeti.KnotTheory.invert_alexander`
and the symmetric Laurent-polynomial theorem. Identifying this polynomial with a
diagram invariant additionally requires the geometric Seifert-matrix construction
and the skein comparison.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997),
  Chapter 8, Theorem 8.6 and the definition of the Conway polynomial on p. 83.
-/

public section

noncomputable section

open LaurentPolynomial
open TauCeti.KnotTheory
open scoped Polynomial

namespace Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized Alexander polynomial of an even-size matrix is a polynomial
in `t + t⁻¹ - 2`, over the original coefficient ring. -/
theorem exists_polynomial_eval₂_eq_alexander {g : ℕ} (V : Matrix ι ι R)
    (h : Fintype.card ι = 2 * g) :
    ∃ q : R[X], Polynomial.eval₂ C (T 1 + T (-1) - 2) q = alexander V :=
  exists_eval₂_add_T_neg_sub_two (invert_alexander V h)

/-- An even-size matrix has an even Conway polynomial: substituting `z = s⁻¹ - s`
in `q(z²)` gives its normalized Alexander polynomial at `t = s²`.
The same polynomial works for every coefficient homomorphism and unit parameter. -/
theorem exists_conwayPolynomial {g : ℕ} (V : Matrix ι ι R)
    (h : Fintype.card ι = 2 * g) :
    ∃ q : R[X], ∀ {S : Type*} [CommRing S] (f : R →+* S) (s : Sˣ),
      Polynomial.eval₂ f ((s⁻¹ : Sˣ).val - s.val) (q.comp (Polynomial.X ^ 2)) =
        LaurentPolynomial.eval₂ f (s ^ 2) (alexander V) := by
  obtain ⟨q, hq⟩ := exists_polynomial_eval₂_eq_alexander V h
  refine ⟨q, ?_⟩
  intro S _ f s
  rw [← hq, Polynomial.hom_eval₂, Polynomial.eval₂_comp]
  have hc : (LaurentPolynomial.eval₂ f (s ^ 2)).comp C = f := by
    ext r
    simp
  rw [hc]
  congr 1
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, map_sub, map_add, map_ofNat,
    LaurentPolynomial.eval₂_T, zpow_one, zpow_neg_one, Units.inv_pow_eq_pow_inv,
    Units.val_pow_eq_pow_val]
  have hs := s.inv_mul
  linear_combination -2 * hs

end Matrix

namespace TauCeti.KnotTheory

/-- The right-handed trefoil's Seifert invariant has Conway polynomial `1 + z²`. -/
theorem eval₂_conway_trefoil {S : Type*} [CommRing S] {s : Sˣ} :
    Polynomial.eval₂ (Int.castRingHom S) ((s⁻¹ : Sˣ).val - s.val)
      (1 + Polynomial.X ^ 2 : ℤ[X]) =
      LaurentPolynomial.eval₂ (Int.castRingHom S) (s ^ 2)
        (alexander trefoilSeifertMatrix) := by
  rw [alexander_trefoilSeifertMatrix]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, map_add, map_sub, map_one, LaurentPolynomial.eval₂_T,
    zpow_one, zpow_neg_one, Units.inv_pow_eq_pow_inv, Units.val_pow_eq_pow_val]
  have hs := s.inv_mul
  linear_combination -2 * hs

/-- The figure-eight's Seifert invariant has Conway polynomial `1 - z²`. -/
theorem eval₂_conway_figureEight {S : Type*} [CommRing S] {s : Sˣ} :
    Polynomial.eval₂ (Int.castRingHom S) ((s⁻¹ : Sˣ).val - s.val)
      (1 - Polynomial.X ^ 2 : ℤ[X]) =
      LaurentPolynomial.eval₂ (Int.castRingHom S) (s ^ 2)
        (alexander figureEightSeifertMatrix) := by
  rw [alexander_figureEightSeifertMatrix]
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, map_sub, map_add, map_neg, map_ofNat, LaurentPolynomial.eval₂_T,
    zpow_one, zpow_neg_one, Units.inv_pow_eq_pow_inv, Units.val_pow_eq_pow_val]
  have hs := s.inv_mul
  linear_combination 2 * hs

end TauCeti.KnotTheory
