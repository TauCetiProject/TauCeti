/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Chain.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Binary
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.SquareClass
public import TauCeti.RingTheory.Henselian.BinaryForm

/-!
# Unimodular diagonal forms over Henselian local rings

Over a Henselian local ring with finite residue field and with two invertible, diagonal forms
with unit coefficients are classified by their rank and their determinant modulo unit squares.
In positive rank, every such form is isometric to the form with all coefficients equal to one
except for the last, which is the product of the original coefficients.

The binary representation normal form supplies the elementary integral changes of basis: every
binary unit form represents one, so `⟨a, b⟩` is isometric to `⟨1, a * b⟩`. Iterating these changes
uses the existing diagonal-chain API. In particular, the equivalences are over the coefficient ring,
rather than merely over its fraction field.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 92:1--92:2.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

open QuadraticMap

namespace TauCeti

variable {R : Type*} [CommRing R] [HenselianLocalRing R]
  [Finite (IsLocalRing.ResidueField R)]

/-- A binary form with unit coefficients over a finite-residue Henselian local ring with two
invertible is isometric, integrally, to `⟨1, a * b⟩`. -/
theorem equivalent_binary_one_mul_of_isUnit_two (h2 : IsUnit (2 : R)) (a b : Rˣ) :
    (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![(1 : R), (a * b : Rˣ)]) := by
  obtain ⟨x, y, hxy⟩ := exists_mul_sq_add_mul_sq_eq_of_isUnit h2 a.isUnit b.isUnit isUnit_one
  have h : (weightedSumSquares R ![(a : R), (b : R)]).Equivalent
      (weightedSumSquares R ![((1 : Rˣ) : R), (a : R) * (b : R) * (1 : Rˣ)]) :=
    ⟨(isometryEquivBinaryNormalForm (a : R) (b : R) x y 1 hxy).symm⟩
  simpa only [Units.val_one, mul_one, Units.val_mul] using h

/-- The elementary binary changes of basis reduce a positive-rank unit diagonal form to ones
followed by its determinant. -/
private theorem diagonalChain_snoc_prod_of_isUnit_two (h2 : IsUnit (2 : R)) {n : ℕ}
    (w : Fin (n + 1) → Rˣ) :
    DiagonalChain w (Fin.snoc (fun _ : Fin n ↦ 1) (∏ i, w i)) := by
  induction n with
  | zero =>
      convert DiagonalChain.refl w using 1
      ext i
      fin_cases i
      simp [Fin.snoc]
  | succ n ih =>
      let v : Fin (n + 1) → Rˣ := Fin.cons (w 0 * w 1) (fun i ↦ w i.succ.succ)
      have hs : BinaryStep w (Fin.cons 1 v) := by
        refine BinaryStep.of_pair 0 1 (by simp) ?_ ?_
        · intro k hk0 hk1
          revert hk0 hk1
          refine Fin.cases (by simp) (fun j ↦ ?_) k
          refine Fin.cases (by simp) (fun j _ _ ↦ by simp [v]) j
        · simpa [v] using equivalent_binary_one_mul_of_isUnit_two h2 (w 0) (w 1)
      have hp : (∏ i, v i) = ∏ i, w i := by
        simp [v, Fin.prod_univ_succ, mul_assoc]
      refine (DiagonalChain.binary hs).trans ?_
      convert (ih v).cons 1 using 1
      rw [Fin.cons_snoc_eq_snoc_cons, hp]
      congr 1
      ext i
      refine Fin.cases (by simp) (fun j ↦ by simp) i

/-- A positive-rank unit diagonal form over a finite-residue Henselian local ring with two
invertible is isometric to ones followed by its determinant. -/
theorem equivalent_weightedSumSquares_snoc_prod_of_isUnit_two (h2 : IsUnit (2 : R)) {n : ℕ}
    (w : Fin (n + 1) → Rˣ) :
    (weightedSumSquares R w).Equivalent
      (weightedSumSquares R (Fin.snoc (fun _ : Fin n ↦ (1 : Rˣ)) (∏ i, w i))) := by
  simpa only [weightedSumSquares_units] using
    (diagonalChain_snoc_prod_of_isUnit_two h2 w).equivalent

/-- Two unit diagonal forms of the same rank over a finite-residue Henselian local ring with
two invertible are isometric exactly when their determinants agree modulo unit squares. -/
theorem equivalent_weightedSumSquares_iff_isSquare_prod_mul_prod_of_isUnit_two
    (h2 : IsUnit (2 : R)) {n : ℕ} (w v : Fin n → Rˣ) :
    (weightedSumSquares R w).Equivalent (weightedSumSquares R v) ↔
      IsSquare ((∏ i, w i) * ∏ i, v i) := by
  let := h2.invertible
  refine ⟨isSquare_prod_mul_prod_of_equivalent, fun h ↦ ?_⟩
  cases n with
  | zero =>
      have hv : w = v := Subsingleton.elim _ _
      rw [hv]
  | succ n =>
      refine (equivalent_weightedSumSquares_snoc_prod_of_isUnit_two h2 w).trans
        ((equivalent_weightedSumSquares_of_isSquare_div ?_).trans
          (equivalent_weightedSumSquares_snoc_prod_of_isUnit_two h2 v).symm)
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa [div_eq_mul_inv, pow_two, mul_assoc] using h.div (IsSquare.sq (∏ i, v i))
      · simp

end TauCeti
