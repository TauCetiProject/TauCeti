/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Jones.Basic
public import TauCeti.KnotTheory.PDCode.Oriented.CrossingInsertion
import Mathlib.Tactic.LinearCombination

/-!
# The oriented Jones skein relation

Insert a positive or negative crossing between any two distinct arcs of an oriented code.
Their Jones polynomials satisfy
`t⁻¹ V₊ - t V₋ = (t^(1/2) - t^(-1/2)) V₀`, where `V₀` is the oriented smoothing.
The Laurent generator is `T = t^(1/2)`, so the coefficients are `T (-2)`, `T 2`,
and `T 1 - T (-1)`.

This gives the diagram algorithm's skein identity for crossings whose four arc ends are
attached to other crossings. Crossing-free circles are retained throughout. It does not
provide crossing deletion or a skein uniqueness theorem for arbitrary diagrams.

The proof uses `PDCode.kauffmanBracket_insertCrossing` and the existing injective
substitution `T ↦ A⁻²` relating the Jones state sum to the normalized bracket.

Reference: W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175 (1997),
Chapter 3, Proposition 3.7.
-/

public section

namespace TauCeti.OrientedPDCode

open LaurentPolynomial

variable {n : ℕ} (D : OrientedPDCode n) (p q : Fin (4 * n))
  (hqp : q ≠ p) (hqe : q ≠ D.edgePair.val p)

/-- The writhe-normalized bracket satisfies the oriented skein relation at an inserted
crossing, over every commutative ring and without dividing by the loop value. -/
theorem normalizedKauffmanBracket_insertCrossing_skein {R : Type*} [CommRing R] (a : Rˣ) :
    (a : R) ^ 4 *
        (D.insertCrossing p q
          (D.orientation p ^^ D.orientation q) hqp hqe).normalizedKauffmanBracket a -
      (↑(a⁻¹) : R) ^ 4 *
        (D.insertCrossing p q
          (!(D.orientation p ^^ D.orientation q)) hqp hqe).normalizedKauffmanBracket a =
    ((↑(a⁻¹) : R) ^ 2 - (a : R) ^ 2) * (D.orientedSmoothing p q).normalizedKauffmanBracket a := by
  have hpos (w : ℤ) : ((-a ^ 3) ^ (-(w + 1)) : Rˣ) =
      (-a ^ 3) ^ (-w) * (-(a⁻¹) ^ 3) := by
    simp [zpow_add, inv_neg, inv_pow, mul_comm]
  have hneg (w : ℤ) : ((-a ^ 3) ^ (-(w + -1)) : Rˣ) =
      (-a ^ 3) ^ (-w) * (-a ^ 3) := by
    simp [zpow_add, mul_comm]
  have hc : (a : R) ^ 3 * (↑(a⁻¹) : R) ^ 3 = 1 := by
    rw [← mul_pow, a.mul_inv, one_pow]
  simp only [normalizedKauffmanBracket_def, writhe_insertCrossing,
    writhe_orientedSmoothing, insertCrossing_toPDCode, orientedSmoothing_toPDCode]
  generalize hs : (D.orientation p ^^ D.orientation q) = b
  cases b <;> simp only [Bool.not_false, Bool.not_true, ↓reduceIte, hpos, hneg,
    Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val, Bool.false_eq_true, Bool.true_eq_false,
    PDCode.kauffmanBracket_insertCrossing hqp hqe, Bool.cond_true, Bool.cond_false]
  · linear_combination
      ((↑(a⁻¹) : R) ^ 2 - (a : R) ^ 2) * (↑((-a ^ 3) ^ (-D.writhe)) : R) *
        (D.toPDCode.reconnect p (D.edgePair.val q)).kauffmanBracket a * hc
  · linear_combination
      ((↑(a⁻¹) : R) ^ 2 - (a : R) ^ 2) * (↑((-a ^ 3) ^ (-D.writhe)) : R) *
        (D.toPDCode.reconnect p q).kauffmanBracket a * hc

/-- **The Jones skein relation** for a crossing inserted between distinct diagram arcs.
The first insertion has positive sign, the second negative sign, and the right side uses
their orientation-preserving smoothing. Here `T = t^(1/2)`. -/
theorem jonesPolynomial_insertCrossing_skein :
    T (-2) * (D.insertCrossing p q (D.orientation p ^^ D.orientation q) hqp hqe).jonesPolynomial -
      T 2 * (D.insertCrossing p q (!(D.orientation p ^^ D.orientation q)) hqp hqe).jonesPolynomial =
    (T 1 - T (-1)) * (D.orientedSmoothing p q).jonesPolynomial := by
  refine eval₂_C_inv_pow_injective two_ne_zero ?_
  rw [← Subsingleton.elim (Int.castRingHom ℤ[T;T⁻¹]) C]
  simp only [map_sub, map_mul, eval₂_jonesPolynomial]
  simp only [eval₂_T, zpow_neg, zpow_ofNat, ← inv_pow, inv_inv,
    ← pow_mul, Units.val_pow_eq_pow_val]
  norm_num only
  exact D.normalizedKauffmanBracket_insertCrossing_skein p q hqp hqe
    (isUnit_T (R := ℤ) 1).unit

end TauCeti.OrientedPDCode
