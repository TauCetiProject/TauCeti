/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.Algebra.Polynomial.Eval.AlgebraMap

/-!
# Multilinear maps along polynomial paths

Let `A` be an algebra over a field `R` of characteristic zero, possibly noncommutative, and let
`φ` be an `R`-multilinear map on `A`. A family `p` of polynomials with coefficients in `A` gives a
polynomial path `t ↦ (p l)(t)` in each argument, where `t ∈ R` is evaluated through the central
embedding `algebraMap R A`. Along such paths `t ↦ φ((p l)(t))` is a polynomial function of `t`,
and its derivative is given by the Leibniz rule
`∑ₖ φ((p 0)(t), …, (p k)′(t), …)`, that is, by `MultilinearMap.linearDeriv` at `(p l)(t)` in the
direction `(p l)′(t)`.

This file proves the resulting **zero-derivative principle**: if this derivative vanishes for every
`t`, then `φ((p l)(t))` does not depend on `t`. It is the algebraic form of homotopy invariance
used for multilinear invariants evaluated along polynomial families, such as the pairing of cyclic
cocycles with polynomial paths of idempotents.

## Main results

* `MultilinearMap.apply_eval_algebraMap_eq_of_linearDeriv_eq_zero`: a multilinear map is constant
  along polynomial paths whose Leibniz derivative vanishes identically.
-/

public section

open Polynomial

namespace MultilinearMap

variable {R A M ι : Type*} [Fintype ι] [DecidableEq ι] [Field R] [CharZero R]
  [Semiring A] [Algebra R A] [AddCommGroup M] [Module R M]

/-- **Zero-derivative principle for multilinear maps along polynomial paths.** If the Leibniz
derivative `φ.linearDeriv ((p l)(t)) ((p l)′(t)) = ∑ₖ φ((p 0)(t), …, (p k)′(t), …)` of
`t ↦ φ((p l)(t))` vanishes at every scalar `t`, then `φ((p l)(t))` takes the same value at all
scalars. -/
theorem apply_eval_algebraMap_eq_of_linearDeriv_eq_zero
    (φ : MultilinearMap R (fun _ : ι ↦ A) M) (p : ι → A[X])
    (h : ∀ t : R, φ.linearDeriv (fun l ↦ (p l).eval (algebraMap R A t))
      (fun l ↦ (p l).derivative.eval (algebraMap R A t)) = 0) (s t : R) :
    φ (fun l ↦ (p l).eval (algebraMap R A s)) = φ (fun l ↦ (p l).eval (algebraMap R A t)) := by
  let S := Fintype.piFinset fun l ↦ Finset.range ((p l).natDegree + 1)
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff R]
  intro ℓ
  -- Under a linear functional `ℓ`, the value along the path is the scalar polynomial `P`.
  let c : (ι → ℕ) → R := fun σ ↦ ℓ (φ fun l ↦ (p l).coeff (σ l))
  let P : R[X] := ∑ σ ∈ S, C (c σ) * ∏ l, X ^ σ l
  have hP (r : R) : P.eval r = ℓ (φ fun l ↦ (p l).eval (algebraMap R A r)) := by
    simp_rw [eval_algebraMap_eq_sum_range, φ.map_sum_finset, φ.map_smul_univ]
    simp only [P, S, c, _root_.map_sum, _root_.map_smul, smul_eq_mul, eval_finsetSum, eval_mul,
      eval_C, eval_prod, eval_pow, eval_X]
    exact Finset.sum_congr rfl fun σ _ ↦ mul_comm _ _
  -- Its derivative is the Leibniz sum, so it vanishes at every scalar.
  have hP' (r : R) : P.derivative.eval r = ℓ (φ.linearDeriv (fun l ↦ (p l).eval (algebraMap R A r))
      (fun l ↦ (p l).derivative.eval (algebraMap R A r))) := by
    rw [linearDeriv_apply]
    have hupd (k : ι) : Function.update (fun l ↦ (p l).eval (algebraMap R A r)) k
        ((p k).derivative.eval (algebraMap R A r)) = fun l ↦
          ∑ i ∈ Finset.range ((p l).natDegree + 1),
            (if l = k then (i : R) * r ^ (i - 1) else r ^ i) • (p l).coeff i := by
      funext l
      by_cases hl : l = k
      · subst hl
        simp [derivative_eval_algebraMap_eq_sum_range]
      · simp [hl, eval_algebraMap_eq_sum_range]
    have hprod (k : ι) (σ : ι → ℕ) :
        ∏ l, (if l = k then (σ l : R) * r ^ (σ l - 1) else r ^ σ l) =
          (σ k * r ^ (σ k - 1)) * ∏ l ∈ Finset.univ.erase k, r ^ σ l := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
      congr 1
      · simp
      · exact Finset.prod_congr rfl fun l hl ↦ by simp [Finset.ne_of_mem_erase hl]
    simp_rw [hupd, φ.map_sum_finset, φ.map_smul_univ, hprod, _root_.map_sum, _root_.map_smul]
    rw [Finset.sum_comm]
    simp only [P, derivative_sum, derivative_C_mul, derivative_prod_finset, derivative_X_pow,
      eval_finsetSum, eval_mul, eval_C, eval_prod, eval_pow, eval_X, Finset.mul_sum, smul_eq_mul]
    exact Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun k _ ↦ by
      simp only [c]
      ring
  have hd : P.derivative = 0 := Polynomial.funext fun r ↦ by simp [hP', h]
  rw [map_sub, ← hP, ← hP, eq_C_of_derivative_eq_zero hd, eval_C, eval_C, sub_self]

end MultilinearMap
