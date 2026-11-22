/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.Algebra.MvPolynomial.SchwartzZippel
import TauCeti.Algebra.Polynomial.Bivariate.Basic
import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# Bivariate Schwartz–Zippel bound on linear grids

A bivariate polynomial `F : K[X][X]` is evaluated at a point `(x, y) : K × K` as
`(F.map (evalRingHom y)).eval x`, so `F.natDegree` bounds the first-coordinate (outer) degree and
`∀ i, (F.coeff i).natDegree ≤ b` bounds the second-coordinate (inner) degree. Pulling `F` back
along a `2 × 2` matrix `M` with nonzero determinant over an integral domain into
`MvPolynomial (Fin 2) K` (`MvPolynomial.linearSubst` composed with
`Polynomial.Bivariate.equivMvPolynomial`) transports
`MvPolynomial.card_filter_piFinset_eval_eq_zero_le` to a zero-count bound on the image of a
Cartesian grid `S × S` (`Polynomial.card_filter_eval_eq_zero_linearGrid_le`).

## Main results

* `Polynomial.card_filter_eval_eq_zero_linearGrid_le`: Schwartz–Zippel zero bound for a nonzero
  bivariate polynomial on the image of a Cartesian grid `S × S` under a `2 × 2` matrix with
  nonzero determinant over an integral domain.
-/

public section

open Finset

namespace Polynomial

/-- **Bivariate Schwartz–Zippel bound on a linear grid.** Over an integral domain `K`, evaluate
`F : K[X][X]` at `(x, y)` by `(F.map (evalRingHom y)).eval x`, so `a` bounds the
first-coordinate (outer) natural degree `F.natDegree` and `b` bounds the second-coordinate (inner)
coefficient natural degrees `(F.coeff i).natDegree`. If `F ≠ 0` and `M` is a `2 × 2` matrix with
nonzero determinant, then the number of zeros of `F` on the image of the Cartesian grid `S × S`
under `M` is at most `S.card * (a + b)`. -/
theorem card_filter_eval_eq_zero_linearGrid_le {K : Type*} [CommRing K] [IsDomain K]
    [DecidableEq K] {S : Finset K} {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det ≠ 0) {F : K[X][X]} (hF : F ≠ 0) {a b : ℕ}
    (ha : F.natDegree ≤ a) (hb : ∀ i, (F.coeff i).natDegree ≤ b) :
    (((S ×ˢ S).image fun q : K × K ↦
        (M 0 0 * q.1 + M 0 1 * q.2, M 1 0 * q.1 + M 1 1 * q.2)).filter
      fun p : K × K ↦ (F.map (evalRingHom p.2)).eval p.1 = 0).card ≤ S.card * (a + b) := by
  let M' : Matrix (Fin 2) (Fin 2) K := M.submatrix (Equiv.swap 0 1) id
  let P' : MvPolynomial (Fin 2) K := MvPolynomial.linearSubst M' (Bivariate.equivMvPolynomial K F)
  have hdet' : M'.det ≠ 0 := by
    dsimp only [M']
    rw [Matrix.det_permute (Equiv.swap 0 1) M, Equiv.Perm.sign_swap (by decide)]
    simp [hdet]
  have hP'_ne : P' ≠ 0 := fun h0 ↦
    hF ((Bivariate.equivMvPolynomial K).injective
      (MvPolynomial.linearSubst_injective hdet' (by simpa [P'] using h0)))
  have heval : ∀ v : Fin 2 → K, MvPolynomial.eval v P' =
      (F.map (evalRingHom (M 1 0 * v 0 + M 1 1 * v 1))).eval (M 0 0 * v 0 + M 0 1 * v 1) := by
    intro v
    dsimp only [P']
    rw [MvPolynomial.eval_linearSubst, Bivariate.eval_equivMvPolynomial]
    simp [M', Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hcard_le :
      (((S ×ˢ S).image fun q : K × K ↦
          (M 0 0 * q.1 + M 0 1 * q.2, M 1 0 * q.1 + M 1 1 * q.2)).filter
        fun p : K × K ↦ (F.map (evalRingHom p.2)).eval p.1 = 0).card ≤
      ((Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun v ↦
        MvPolynomial.eval v P' = 0).card := by
    refine Finset.card_le_card_of_surjOn
      (fun v : Fin 2 → K ↦ (M 0 0 * v 0 + M 0 1 * v 1, M 1 0 * v 0 + M 1 1 * v 1)) ?_
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp hp.1
    rw [Finset.mem_product] at hqS
    refine ⟨![q.1, q.2], Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr (Fin.forall_fin_two.mpr hqS), ?_⟩), rfl⟩
    rw [heval]
    exact hp.2
  have hnat_le :
      ((Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun v ↦
        MvPolynomial.eval v P' = 0).card ≤ S.card * P'.totalDegree := by
    simpa using MvPolynomial.card_filter_piFinset_eval_eq_zero_le hP'_ne S
  have hdeg_le : P'.totalDegree ≤ a + b :=
    (MvPolynomial.totalDegree_linearSubst_le M' _).trans
      (Bivariate.totalDegree_equivMvPolynomial_le F ha hb)
  exact hcard_le.trans (hnat_le.trans (Nat.mul_le_mul_left S.card hdeg_le))

end Polynomial
