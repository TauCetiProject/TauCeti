/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `MvPolynomial.eq_of_eval_eq_on_gl`, the Zariski density of the invertible matrices, together with
-- the `GL` notation and the coercion of an element of `GL m k` to a matrix.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.MvPolynomial
public import Mathlib.LinearAlgebra.Multilinear.Basic
-- `Matrix.single`, the matrix units in which the arguments are expanded.
public import Mathlib.Data.Matrix.Basis

/-!
# A multilinear form on matrices is determined on the diagonal by the invertible matrices

Let `Θ` be a multilinear form in `ι` matrix arguments over a field `K`. Its **diagonal**
`Y ↦ Θ (Y, …, Y)` is a polynomial function of the entries of `Y`: expanding each argument in the
matrix units `Matrix.single i j 1` writes it as a sum, over the functions `a : ι → m × m`, of the
constant `Θ (fun i => single (a i).1 (a i).2 1)` times the monomial `∏ᵢ Y (a i).1 (a i).2`. That is
`MultilinearMap.exists_mvPolynomial_eval_eq_apply_const` below.

Over an *infinite* field the invertible matrices are Zariski dense, so such a polynomial function
vanishes everywhere as soon as it vanishes on `GL m K` (`MvPolynomial.eq_of_eval_eq_on_gl`). Hence a
multilinear form whose diagonal kills every invertible matrix has zero diagonal:
`MultilinearMap.apply_const_eq_zero_of_eq_zero_on_gl`.

This is the form in which density is used to pass from the invertible diagonal operators `g^{⊗ι}`
on a tensor power to all of them; the argument is stated here on matrices, where the ambient
polynomial ring `MvPolynomial (m × m) K` and the density statement live.

## Main results

* `MultilinearMap.exists_mvPolynomial_eval_eq_apply_const`: the diagonal of a multilinear form on
  matrices is the evaluation of a polynomial in the matrix entries.
* `MultilinearMap.apply_const_eq_zero_of_eq_zero_on_gl`: over an infinite field, a multilinear form
  on matrices whose diagonal vanishes on the invertible matrices has vanishing diagonal.
-/

public section

open Matrix MvPolynomial

namespace MultilinearMap

universe u v w

variable {ι : Type u} {m : Type v} {K : Type w} [Finite ι]

section CommSemiring

variable [Finite m] [CommSemiring K]

/-- **The diagonal of a multilinear form on matrices is a polynomial in the matrix entries.**
Expanding each of the `ι` arguments in the matrix units, the value `Θ (Y, …, Y)` is a sum of
constants times monomials `∏ᵢ Y (a i).1 (a i).2` indexed by the functions `a : ι → m × m`. -/
theorem exists_mvPolynomial_eval_eq_apply_const
    (Θ : MultilinearMap K (fun _ : ι => Matrix m m K) K) :
    ∃ P : MvPolynomial (m × m) K, ∀ Y : Matrix m m K,
      MvPolynomial.eval (fun p : m × m => Y p.1 p.2) P = Θ fun _ => Y := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype m
  refine ⟨∑ a : ι → m × m, C (Θ fun i => single (a i).1 (a i).2 1) * ∏ i, X (a i), fun Y => ?_⟩
  have hY : ∑ p : m × m, Y p.1 p.2 • single p.1 p.2 (1 : K) = Y := by
    simp only [smul_single, smul_eq_mul, mul_one]
    rw [Fintype.sum_prod_type]
    exact (matrix_eq_sum_single Y).symm
  have hexp : (Θ fun _ => Y) =
      ∑ a : ι → m × m, (∏ i, Y (a i).1 (a i).2) * Θ fun i => single (a i).1 (a i).2 1 := by
    have hstep : (Θ fun _ : ι => ∑ p : m × m, Y p.1 p.2 • single p.1 p.2 (1 : K)) =
        ∑ a : ι → m × m, (∏ i, Y (a i).1 (a i).2) * Θ fun i => single (a i).1 (a i).2 1 := by
      rw [Θ.map_sum]
      exact Finset.sum_congr rfl fun a _ => by
        rw [Θ.map_smul_univ (fun i => Y (a i).1 (a i).2), smul_eq_mul]
    rwa [hY] at hstep
  rw [hexp]
  simp only [_root_.map_sum, _root_.map_mul, eval_C, _root_.map_prod, eval_X]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end CommSemiring

section Field

variable [Fintype m] [DecidableEq m] [Field K] [Infinite K]

/-- **A multilinear form on matrices whose diagonal vanishes on the invertible matrices has
vanishing diagonal.** The diagonal is a polynomial function of the matrix entries, and over an
infinite field the invertible matrices are Zariski dense. -/
theorem apply_const_eq_zero_of_eq_zero_on_gl (Θ : MultilinearMap K (fun _ : ι => Matrix m m K) K)
    (h : ∀ g : GL m K, (Θ fun _ => (g : Matrix m m K)) = 0) (Y : Matrix m m K) :
    (Θ fun _ => Y) = 0 := by
  obtain ⟨P, hP⟩ := Θ.exists_mvPolynomial_eval_eq_apply_const
  have hzero : P = 0 := MvPolynomial.eq_of_eval_eq_on_gl fun g => by simp [hP, h g]
  rw [← hP Y, hzero, _root_.map_zero]

end Field

end MultilinearMap
