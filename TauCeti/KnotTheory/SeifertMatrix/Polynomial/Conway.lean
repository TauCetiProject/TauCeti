/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SeifertMatrix.Polynomial.Basic
public import TauCeti.KnotTheory.SeifertMatrix.Conway
public import TauCeti.KnotTheory.SeifertMatrix.Alexander
public import TauCeti.Algebra.Polynomial.Laurent.Injective
import TauCeti.Algebra.Polynomial.Laurent.Basic
import Mathlib.Algebra.Polynomial.Expand

/-!
# The canonical Conway polynomial of a Seifert matrix

The half-power determinant `det(s V - s⁻¹ Vᵀ)` of a square matrix of any size
has a unique polynomial expression in `z = s⁻¹ - s`. This file chooses that
polynomial and proves the diagonal-change skein formula. Odd sizes are needed
for links obtained by smoothing a crossing of a knot.

For even-size matrices, evaluation recovers the normalized Alexander polynomial
at `t = s²`, so the existing S-equivalence invariance and knot computations
remain valid. This is an algebraic invariant of a matrix; identification with a
diagram polynomial additionally requires the geometric Seifert construction.

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

/-- The canonical Conway polynomial of a square matrix, characterized by
`∇(s⁻¹ - s) = det(s V - s⁻¹ Vᵀ)`. Odd sizes, as well as even sizes, are allowed. -/
def conwayPolynomial (V : Matrix ι ι R) : R[X] :=
  V.exists_polynomial_eval₂_eq_seifertConwayDeterminant.choose

/-- Substitution of the formal Conway variable characterizes the canonical polynomial. -/
theorem conwayPolynomial_eq_iff (V : Matrix ι ι R) (p : R[X]) :
    p = V.conwayPolynomial ↔
      Polynomial.eval₂ C (T (-1) - T 1) p = V.seifertConwayDeterminant := by
  rw [← V.exists_polynomial_eval₂_eq_seifertConwayDeterminant.choose_spec]
  exact (eval₂_C_T_neg_sub_T_injective (R := R)).eq_iff.symm

/-- Substituting the formal Conway variable recovers the half-power determinant. -/
@[simp] theorem eval₂_C_conwayPolynomial (V : Matrix ι ι R) :
    Polynomial.eval₂ C (T (-1) - T 1) V.conwayPolynomial = V.seifertConwayDeterminant :=
  (V.conwayPolynomial_eq_iff _).mp rfl

/-- Substituting the Conway variable gives the half-power Seifert determinant,
after any coefficient homomorphism and at any unit parameter. -/
theorem eval₂_conwayPolynomial {S : Type*} [CommRing S] (V : Matrix ι ι R)
    (f : R →+* S) (s : Sˣ) :
    Polynomial.eval₂ f ((s⁻¹ : Sˣ).val - s.val) V.conwayPolynomial =
      ((s : S) • V.map f - (s⁻¹ : Sˣ).val • (V.map f)ᵀ).det := by
  have h := congrArg (eval₂ f s) ((V.conwayPolynomial_eq_iff _).mp rfl)
  rw [eval₂_seifertConwayDeterminant, Polynomial.hom_eval₂] at h
  have hcomp : (eval₂ f s).comp C = f := by ext r; simp
  simpa only [hcomp, map_sub, eval₂_T, zpow_neg_one, zpow_one] using h

/-- The half-power normalization differs from the integer-exponent Alexander
normalization by `s⁻¹` in odd size and by no factor in even size. -/
theorem eval₂_conwayPolynomial_eq_mul_alexander {S : Type*} [CommRing S]
    (V : Matrix ι ι R) (f : R →+* S) (s : Sˣ) :
    Polynomial.eval₂ f ((s⁻¹ : Sˣ).val - s.val) V.conwayPolynomial =
      (s ^ (-((Fintype.card ι % 2 : ℕ) : ℤ)) : Sˣ).val *
        LaurentPolynomial.eval₂ f (s ^ 2) (alexander V) := by
  have hmatrix : (s : S) • V.map f - (s⁻¹ : Sˣ).val • (V.map f)ᵀ =
      (s⁻¹ : Sˣ).val • ((s ^ 2 : Sˣ).val • V.map f - (V.map f)ᵀ) := by
    ext i j
    simp only [sub_apply, smul_apply, smul_eq_mul, transpose_apply,
      Units.val_pow_eq_pow_val, mul_sub]
    have hs := s.inv_mul
    linear_combination -(s : S) * V.map f i j * hs
  rw [eval₂_conwayPolynomial, hmatrix, det_smul, eval₂_alexander, ← mul_assoc]
  congr 1
  have hexp : -((Fintype.card ι : ℕ) : ℤ) =
      -((Fintype.card ι % 2 : ℕ) : ℤ) + 2 * -((Fintype.card ι / 2 : ℕ) : ℤ) := by omega
  have hunit : s⁻¹ ^ Fintype.card ι =
      s ^ (-((Fintype.card ι % 2 : ℕ) : ℤ)) *
        (s ^ 2) ^ (-((Fintype.card ι / 2 : ℕ) : ℤ)) := by
    rw [← zpow_natCast, inv_zpow, ← zpow_neg, hexp, zpow_add, zpow_mul]
    simp only [zpow_ofNat]
  exact (Units.val_pow_eq_pow_val _ _).symm.trans (congrArg Units.val hunit)

/-- For even-size matrices, evaluation of the Conway polynomial is the normalized
Alexander polynomial at the square of the unit parameter. -/
theorem eval₂_conwayPolynomial_eq_alexander {S : Type*} [CommRing S] (V : Matrix ι ι R)
    (h : Even (Fintype.card ι)) (f : R →+* S) (s : Sˣ) :
    Polynomial.eval₂ f ((s⁻¹ : Sˣ).val - s.val) V.conwayPolynomial =
      LaurentPolynomial.eval₂ f (s ^ 2) (alexander V) := by
  obtain ⟨g, hg⟩ := h
  have hmod : Fintype.card ι % 2 = 0 := by omega
  simp [eval₂_conwayPolynomial_eq_mul_alexander, hmod]

/-- The empty matrix, corresponding to a disc Seifert surface, has Conway polynomial one. -/
@[simp] theorem conwayPolynomial_of_isEmpty [IsEmpty ι] (V : Matrix ι ι R) :
    V.conwayPolynomial = 1 := by
  apply Eq.symm
  apply (V.conwayPolynomial_eq_iff _).mpr
  simp

/-- An even-size matrix has a Conway polynomial in `X²`, without a characteristic
restriction on the coefficient ring. -/
theorem exists_conwayPolynomial_eq_comp_X_sq (V : Matrix ι ι R)
    (h : Even (Fintype.card ι)) :
    ∃ q : R[X], V.conwayPolynomial = q.comp (Polynomial.X ^ 2) := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨q, hq⟩ := V.exists_conwayPolynomial (by omega : Fintype.card ι = 2 * g)
  refine ⟨q, ?_⟩
  apply (eval₂_C_T_neg_sub_T_injective (R := R))
  have hu := TauCeti.val_isUnit_T_unit_inv_pow (R := R) 1 1
  simp only [pow_one, one_mul, Nat.cast_one] at hu
  simpa only [hu, IsUnit.unit_spec] using
    (V.eval₂_conwayPolynomial_eq_alexander ⟨g, hg⟩ C (isUnit_T (R := R) 1).unit).trans
      (hq C (isUnit_T (R := R) 1).unit).symm

/-- Every odd coefficient of the canonical Conway polynomial vanishes, even over
coefficient rings of characteristic two. -/
theorem coeff_conwayPolynomial_eq_zero_of_odd (V : Matrix ι ι R)
    (h : Even (Fintype.card ι)) (n : ℕ) (hn : Odd n) :
    V.conwayPolynomial.coeff n = 0 := by
  obtain ⟨q, hq⟩ := exists_conwayPolynomial_eq_comp_X_sq V h
  rw [hq, ← Polynomial.expand_eq_comp_X_pow,
    Polynomial.coeff_expand (by norm_num : 0 < 2)]
  simp only [hn.not_two_dvd_nat, ↓reduceIte]

/-- Substituting the negative variable preserves the canonical Conway polynomial. -/
@[simp]
theorem conwayPolynomial_comp_neg_X (V : Matrix ι ι R) (h : Even (Fintype.card ι)) :
    V.conwayPolynomial.comp (-Polynomial.X) = V.conwayPolynomial := by
  obtain ⟨q, hq⟩ := exists_conwayPolynomial_eq_comp_X_sq V h
  rw [hq, Polynomial.comp_assoc]
  simp

/-- Equal normalized Alexander polynomials and equal size parity give equal Conway
polynomials. The matrices may have different index types and different sizes. -/
theorem conwayPolynomial_eq_of_alexander_eq {κ : Type*} [Fintype κ] [DecidableEq κ]
    (V : Matrix ι ι R) (W : Matrix κ κ R)
    (hcard : Fintype.card ι % 2 = Fintype.card κ % 2)
    (h : alexander V = alexander W) :
    V.conwayPolynomial = W.conwayPolynomial := by
  apply eval₂_C_T_neg_sub_T_injective (R := R)
  have hu := TauCeti.val_isUnit_T_unit_inv_pow (R := R) 1 1
  simp only [pow_one, one_mul, Nat.cast_one] at hu
  have hV := V.eval₂_conwayPolynomial_eq_mul_alexander C (isUnit_T (R := R) 1).unit
  have hW := W.eval₂_conwayPolynomial_eq_mul_alexander C (isUnit_T (R := R) 1).unit
  rw [h, hcard] at hV
  simpa only [hu, IsUnit.unit_spec] using hV.trans hW.symm

/-- Changing the last diagonal entry by `r` changes the Conway polynomial by
`-r X` times the polynomial of the deleted minor. In particular, decreasing it
by one gives the usual positive Conway skein factor `X`. -/
theorem conwayPolynomial_add_diagonal_single {n : ℕ}
    (V : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (r : R) :
    (V + diagonal (Pi.single (Fin.last n) r)).conwayPolynomial - V.conwayPolynomial =
      -Polynomial.C r * Polynomial.X *
        (V.submatrix Fin.castSucc Fin.castSucc).conwayPolynomial := by
  apply eval₂_C_T_neg_sub_T_injective (R := R)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_neg,
    Polynomial.eval₂_C, Polynomial.eval₂_X,
    eval₂_C_conwayPolynomial]
  rw [seifertConwayDeterminant_add_diagonal_single]
  ring

end Matrix

namespace TauCeti.KnotTheory

/-- The canonical Conway polynomial is invariant under S-equivalence of integral
matrices of any size, including odd sizes and enlargements and reductions. -/
theorem IntegralSquareMatrix.SEquivalent.conwayPolynomial_eq
    {V W : IntegralSquareMatrix} (h : V.SEquivalent W) :
    V.2.conwayPolynomial = W.2.conwayPolynomial := by
  exact V.2.conwayPolynomial_eq_of_alexander_eq W.2
    (by simpa using h.size_mod_two_eq) h.alexander_eq

/-- The canonical Conway polynomial of the right-handed trefoil is `1 + X²`. -/
@[simp]
theorem conwayPolynomial_trefoilSeifertMatrix :
    trefoilSeifertMatrix.conwayPolynomial = 1 + Polynomial.X ^ 2 := by
  apply Eq.symm
  apply eval₂_C_T_neg_sub_T_injective (R := ℤ)
  have he := trefoilSeifertMatrix.eval₂_conwayPolynomial_eq_alexander
    (by norm_num) C (isUnit_T (R := ℤ) 1).unit
  have hu := TauCeti.val_isUnit_T_unit_inv_pow (R := ℤ) 1 1
  simp only [pow_one, one_mul, Nat.cast_one] at hu
  have hf : Int.castRingHom ℤ[T;T⁻¹] = C := RingHom.ext_int _ _
  simpa only [hf, hu, IsUnit.unit_spec] using
    (eval₂_conway_trefoilSeifertMatrix (s := (isUnit_T (R := ℤ) 1).unit)).trans he.symm

/-- The canonical Conway polynomial of the figure-eight is `1 - X²`. -/
@[simp]
theorem conwayPolynomial_figureEightSeifertMatrix :
    figureEightSeifertMatrix.conwayPolynomial = 1 - Polynomial.X ^ 2 := by
  apply Eq.symm
  apply eval₂_C_T_neg_sub_T_injective (R := ℤ)
  have he := figureEightSeifertMatrix.eval₂_conwayPolynomial_eq_alexander
    (by norm_num) C (isUnit_T (R := ℤ) 1).unit
  have hu := TauCeti.val_isUnit_T_unit_inv_pow (R := ℤ) 1 1
  simp only [pow_one, one_mul, Nat.cast_one] at hu
  have hf : Int.castRingHom ℤ[T;T⁻¹] = C := RingHom.ext_int _ _
  simpa only [hf, hu, IsUnit.unit_spec] using
    (eval₂_conway_figureEightSeifertMatrix (s := (isUnit_T (R := ℤ) 1).unit)).trans he.symm

end TauCeti.KnotTheory
