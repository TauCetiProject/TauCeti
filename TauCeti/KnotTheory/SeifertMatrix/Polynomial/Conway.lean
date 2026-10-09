/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SeifertMatrix.Polynomial.Basic
public import TauCeti.KnotTheory.SeifertMatrix.Alexander
public import TauCeti.Algebra.Polynomial.Laurent.Injective
import TauCeti.Algebra.Polynomial.Laurent.Basic
import Mathlib.Algebra.Polynomial.Expand

/-!
# The canonical Conway polynomial of an even-size Seifert matrix

The normalized Alexander polynomial of an even-size matrix has a unique polynomial
expression in `t + t⁻¹ - 2`. Composing that expression with `X²` gives the Conway
polynomial, characterized by `∇(s⁻¹ - s) = Δ(s²)`. Uniqueness of substitution makes
this an invariant under S-equivalence, including moves that change the matrix size.

The construction works over every commutative ring, without division by two. For the
standard integral trefoil and figure-eight matrices it gives `1 + X²` and `1 - X²`.
It is an algebraic invariant of a chosen matrix; identification with a diagram polynomial
still requires a geometric Seifert presentation and the skein comparison.

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

/-- The canonical Conway polynomial of an even-size matrix. For a knot Seifert matrix
this is the even polynomial satisfying `∇(s⁻¹ - s) = Δ(s²)`. -/
def conwayPolynomial (V : Matrix ι ι R) (h : Even (Fintype.card ι)) : R[X] := by
  have hcard : Fintype.card ι = 2 * (Fintype.card ι / 2) := by
    obtain ⟨g, hg⟩ := h
    omega
  exact (V.exists_polynomial_eval₂_eq_alexander hcard).choose.comp (Polynomial.X ^ 2)

/-- Substituting the Conway variable in the canonical polynomial gives the normalized
Alexander polynomial at the square of the unit parameter, after any coefficient map. -/
theorem eval₂_conwayPolynomial {S : Type*} [CommRing S] (V : Matrix ι ι R)
    (h : Even (Fintype.card ι)) (f : R →+* S) (s : Sˣ) :
    Polynomial.eval₂ f ((s⁻¹ : Sˣ).val - s.val) (V.conwayPolynomial h) =
      LaurentPolynomial.eval₂ f (s ^ 2) (alexander V) := by
  have hcard : Fintype.card ι = 2 * (Fintype.card ι / 2) := by
    obtain ⟨g, hg⟩ := h
    omega
  rw [conwayPolynomial, Polynomial.eval₂_comp_X_sq_eq_laurent_eval₂,
    (V.exists_polynomial_eval₂_eq_alexander hcard).choose_spec]

/-- Substitution of the formal Conway variable characterizes the canonical polynomial.
This formulation suffices for uniqueness without testing numerical parameter values. -/
theorem conwayPolynomial_eq_iff (V : Matrix ι ι R) (h : Even (Fintype.card ι))
    (p : R[X]) :
    p = V.conwayPolynomial h ↔
      Polynomial.eval₂ C (T (-1) - T 1) p =
        LaurentPolynomial.eval₂ C ((isUnit_T (R := R) 1).unit ^ 2) (alexander V) := by
  have hu := TauCeti.val_isUnit_T_unit_inv_pow (R := R) 1 1
  simp only [pow_one, one_mul, Nat.cast_one] at hu
  have he := V.eval₂_conwayPolynomial h C (isUnit_T (R := R) 1).unit
  rw [hu, IsUnit.unit_spec] at he
  rw [← he]
  exact (eval₂_C_T_neg_sub_T_injective (R := R)).eq_iff.symm

/-- The empty matrix, corresponding to a disc Seifert surface, has Conway polynomial one. -/
@[simp]
theorem conwayPolynomial_of_isEmpty [IsEmpty ι] (V : Matrix ι ι R)
    (h : Even (Fintype.card ι)) : V.conwayPolynomial h = 1 := by
  apply Eq.symm
  apply (V.conwayPolynomial_eq_iff h _).mpr
  simp

/-- Every odd coefficient of the canonical Conway polynomial vanishes, even over
coefficient rings of characteristic two. -/
theorem coeff_conwayPolynomial_eq_zero_of_odd (V : Matrix ι ι R)
    (h : Even (Fintype.card ι)) (n : ℕ) (hn : Odd n) :
    (V.conwayPolynomial h).coeff n = 0 := by
  rw [conwayPolynomial, ← Polynomial.expand_eq_comp_X_pow,
    Polynomial.coeff_expand (by norm_num : 0 < 2)]
  simp only [hn.not_two_dvd_nat, ↓reduceIte]

/-- Substituting the negative variable preserves the canonical Conway polynomial. -/
@[simp]
theorem conwayPolynomial_comp_neg_X (V : Matrix ι ι R) (h : Even (Fintype.card ι)) :
    (V.conwayPolynomial h).comp (-Polynomial.X) = V.conwayPolynomial h := by
  rw [conwayPolynomial, Polynomial.comp_assoc]
  simp

/-- Equal normalized Alexander polynomials give equal canonical Conway polynomials.
The matrices may have different index types and different even sizes. -/
theorem conwayPolynomial_eq_of_alexander_eq {κ : Type*} [Fintype κ] [DecidableEq κ]
    (V : Matrix ι ι R) (W : Matrix κ κ R)
    (hV : Even (Fintype.card ι)) (hW : Even (Fintype.card κ))
    (h : alexander V = alexander W) :
    V.conwayPolynomial hV = W.conwayPolynomial hW := by
  apply (W.conwayPolynomial_eq_iff hW _).mpr
  rw [← h]
  exact (V.conwayPolynomial_eq_iff hV _).mp rfl

end Matrix

namespace TauCeti.KnotTheory

/-- The canonical Conway polynomial is invariant under S-equivalence of even integral
matrices, including sequences of enlargements and reductions. -/
theorem IntegralSquareMatrix.SEquivalent.conwayPolynomial_eq
    {V W : IntegralSquareMatrix} (h : V.SEquivalent W)
    (hV : Even (Fintype.card (Fin V.1))) (hW : Even (Fintype.card (Fin W.1))) :
    V.2.conwayPolynomial hV = W.2.conwayPolynomial hW :=
  V.2.conwayPolynomial_eq_of_alexander_eq W.2 hV hW h.alexander_eq

/-- The canonical Conway polynomial of the right-handed trefoil is `1 + X²`. -/
@[simp]
theorem conwayPolynomial_trefoilSeifertMatrix (h : Even (Fintype.card (Fin 2))) :
    trefoilSeifertMatrix.conwayPolynomial h = 1 + Polynomial.X ^ 2 := by
  apply Eq.symm
  apply (trefoilSeifertMatrix.conwayPolynomial_eq_iff h _).mpr
  have hu := TauCeti.val_isUnit_T_unit_inv_pow (R := ℤ) 1 1
  simp only [pow_one, one_mul, Nat.cast_one] at hu
  have hf : Int.castRingHom ℤ[T;T⁻¹] = C := RingHom.ext_int _ _
  simpa only [hf, hu, IsUnit.unit_spec] using
    (eval₂_conway_trefoilSeifertMatrix (s := (isUnit_T (R := ℤ) 1).unit))

/-- The canonical Conway polynomial of the figure-eight is `1 - X²`. -/
@[simp]
theorem conwayPolynomial_figureEightSeifertMatrix (h : Even (Fintype.card (Fin 2))) :
    figureEightSeifertMatrix.conwayPolynomial h = 1 - Polynomial.X ^ 2 := by
  apply Eq.symm
  apply (figureEightSeifertMatrix.conwayPolynomial_eq_iff h _).mpr
  have hu := TauCeti.val_isUnit_T_unit_inv_pow (R := ℤ) 1 1
  simp only [pow_one, one_mul, Nat.cast_one] at hu
  have hf : Int.castRingHom ℤ[T;T⁻¹] = C := RingHom.ext_int _ _
  simpa only [hf, hu, IsUnit.unit_spec] using
    (eval₂_conway_figureEightSeifertMatrix (s := (isUnit_T (R := ℤ) 1).unit))

end TauCeti.KnotTheory
