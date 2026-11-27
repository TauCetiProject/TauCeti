/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.Algebra.MvPolynomial.SchwartzZippel
import TauCeti.Algebra.Polynomial.Bivariate.Basic
import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# Bivariate Schwartz–Zippel bound on linear grids

A bivariate polynomial `F : K[X][X]` is evaluated at a point `(x, y) : K × K` via
`F.evalEval y x = (F.map (evalRingHom y)).eval x`, so `F.natDegree` bounds the first-coordinate
(outer) degree and `∀ i, (F.coeff i).natDegree ≤ b` bounds the second-coordinate (inner) degree.
Pulling `F` back along a `2 × 2` matrix `M` with nonzero determinant over an integral domain into
`MvPolynomial (Fin 2) K` (`MvPolynomial.linearSubst` composed with
`Polynomial.Bivariate.equivMvPolynomial`) transports
`MvPolynomial.card_filter_piFinset_eval_eq_zero_le` to a zero-count bound on the image of a
Cartesian grid `S × S` under `Matrix.toLinProd M`
(`Polynomial.card_filter_evalEval_eq_zero_linearGrid_le`), and via
`Polynomial.Bivariate.totalDegree_equivMvPolynomial_le` to the separate-degree bound
`Polynomial.card_filter_evalEval_eq_zero_linearGrid_le_of_natDegree_le`.

## Main results

* `Polynomial.card_filter_evalEval_eq_zero_linearGrid_le`: total-degree Schwartz–Zippel zero bound
  for a nonzero bivariate polynomial on `(S ×ˢ S).image (Matrix.toLinProd M)` for a `2 × 2`
  matrix `M` with nonzero determinant over an integral domain.
* `Polynomial.card_filter_evalEval_eq_zero_linearGrid_le_of_natDegree_le`: separate-degree corollary
  bounded by `S.card * (a + b)` when `F.natDegree ≤ a` and `∀ i, (F.coeff i).natDegree ≤ b`.
-/

public section

open Finset
open scoped Matrix

namespace Polynomial

/-- **Bivariate Schwartz–Zippel bound on a linear grid (total-degree form).** Over an integral
domain `K`, evaluate `F : K[X][X]` at `(x, y)` via
`F.evalEval y x = (F.map (evalRingHom y)).eval x`. If `F ≠ 0` and `M` is a `2 × 2` matrix with
nonzero determinant, then the number of zeros of `F` on `(S ×ˢ S).image (Matrix.toLinProd M)`
is at most `S.card * (Bivariate.equivMvPolynomial K F).totalDegree`. -/
theorem card_filter_evalEval_eq_zero_linearGrid_le {K : Type*} [CommRing K] [IsDomain K]
    [DecidableEq K] {S : Finset K} {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det ≠ 0) {F : K[X][X]} (hF : F ≠ 0) :
    (((S ×ˢ S).image (Matrix.toLinProd M)).filter
      fun p : K × K ↦ F.evalEval p.2 p.1 = 0).card ≤
      S.card * (Bivariate.equivMvPolynomial K F).totalDegree := by
  let M' : Matrix (Fin 2) (Fin 2) K := M.submatrix (Equiv.swap 0 1) id
  let P' : MvPolynomial (Fin 2) K := MvPolynomial.linearSubst M' (Bivariate.equivMvPolynomial K F)
  have hdet' : M'.det ≠ 0 := by
    dsimp only [M']
    rw [Matrix.det_permute (Equiv.swap 0 1) M, Equiv.Perm.sign_swap (by decide)]
    simp [hdet]
  have hP'_ne : P' ≠ 0 := fun h0 ↦
    hF ((Bivariate.equivMvPolynomial K).injective
      (MvPolynomial.linearSubst_injective hdet' (by simpa [P'] using h0)))
  let e := finTwoArrowEquiv K
  have heval : ∀ v : Fin 2 → K,
      MvPolynomial.eval v P' =
        F.evalEval (Matrix.toLinProd M (e v)).2 (Matrix.toLinProd M (e v)).1 := by
    intro v
    dsimp only [P']
    rw [MvPolynomial.eval_linearSubst, Bivariate.eval_equivMvPolynomial]
    have hmul : M' *ᵥ v = (M *ᵥ v) ∘ Equiv.swap 0 1 := by
      simpa [M'] using Matrix.submatrix_mulVec_equiv M v (Equiv.swap 0 1) (Equiv.refl _)
    rw [Matrix.toLinProd_finTwoArrowEquiv]
    simp [hmul]
  have hcard_le :
      (((S ×ˢ S).image (Matrix.toLinProd M)).filter
        fun p : K × K ↦ F.evalEval p.2 p.1 = 0).card ≤
      ((Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun v ↦
        MvPolynomial.eval v P' = 0).card := by
    rw [Finset.filter_image]
    refine Finset.card_image_le.trans_eq ?_
    refine Finset.card_equiv e.symm ?_
    intro q
    simp [e, Fin.forall_fin_two, heval]
  have hnat_le :
      ((Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun v ↦
        MvPolynomial.eval v P' = 0).card ≤ S.card * P'.totalDegree := by
    simpa using MvPolynomial.card_filter_piFinset_eval_eq_zero_le hP'_ne S
  have hdeg_le : P'.totalDegree ≤ (Bivariate.equivMvPolynomial K F).totalDegree :=
    MvPolynomial.totalDegree_linearSubst_le M' _
  exact hcard_le.trans (hnat_le.trans (Nat.mul_le_mul_left S.card hdeg_le))

/-- **Bivariate Schwartz–Zippel bound on a linear grid (separate-degree form).** Over an integral
domain `K`, if `F : K[X][X]` is nonzero with `F.natDegree ≤ a` and `∀ i, (F.coeff i).natDegree ≤ b`,
and `M` is a `2 × 2` matrix with nonzero determinant, then the number of zeros of `F` on
`(S ×ˢ S).image (Matrix.toLinProd M)` is at most `S.card * (a + b)`. -/
theorem card_filter_evalEval_eq_zero_linearGrid_le_of_natDegree_le {K : Type*} [CommRing K]
    [IsDomain K] [DecidableEq K] {S : Finset K} {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det ≠ 0) {F : K[X][X]} (hF : F ≠ 0) {a b : ℕ}
    (ha : F.natDegree ≤ a) (hb : ∀ i, (F.coeff i).natDegree ≤ b) :
    (((S ×ˢ S).image (Matrix.toLinProd M)).filter
      fun p : K × K ↦ F.evalEval p.2 p.1 = 0).card ≤ S.card * (a + b) :=
  (card_filter_evalEval_eq_zero_linearGrid_le hdet hF).trans
    (Nat.mul_le_mul_left S.card (Bivariate.totalDegree_equivMvPolynomial_le F ha hb))

end Polynomial
