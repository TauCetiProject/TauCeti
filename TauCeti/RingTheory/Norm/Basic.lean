/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic

/-!
# Norms of negatives and of shifted power-basis generators

Two elementary evaluations of the algebra norm `Algebra.norm R` of a finite free `R`-algebra `S`.

* `Algebra.norm_neg`: `N(-x) = (-1) ^ [S : R] * N(x)`. It converts between the two sign
  conventions `ζ - 1` and `1 - ζ` for norms of cyclotomic elements.
* `PowerBasis.norm_algebraMap_sub_gen`: for a power basis with generator `x`,
  `N(r - x) = f(r)`, where `f` is the minimal polynomial of `x` over `R`. This is the
  characteristic-polynomial form of Mathlib's `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`,
  which is the case `r = 0` up to the sign `(-1) ^ deg f`.
-/

public section

open Polynomial

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]

/-- The norm of `-x` is `(-1) ^ [S : R]` times the norm of `x`. -/
theorem Algebra.norm_neg [Module.Free R S] (x : S) :
    Algebra.norm R (-x) = (-1) ^ Module.finrank R S * Algebra.norm R x := by
  rw [← neg_one_mul, ← map_one (algebraMap R S), ← map_neg, map_mul, Algebra.norm_algebraMap]

/-- For a power basis with generator `x`, the norm of `r - x` is the value at `r` of the minimal
polynomial of `x`: the matrix of multiplication by `x` has the minimal polynomial as its
characteristic polynomial. -/
theorem PowerBasis.norm_algebraMap_sub_gen (pb : PowerBasis R S) (r : R) :
    Algebra.norm R (algebraMap R S r - pb.gen) = (minpoly R pb.gen).eval r := by
  rw [Algebra.norm_eq_matrix_det pb.basis, map_sub, AlgHom.commutes, ← charpoly_leftMulMatrix,
    Matrix.eval_charpoly]
  simp [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def]
