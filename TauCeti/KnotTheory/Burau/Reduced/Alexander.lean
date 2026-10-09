/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Burau.Alexander
public import TauCeti.KnotTheory.Burau.Reduced.Basic
public import TauCeti.LinearAlgebra.Matrix.InvariantReduction
import Mathlib.Tactic.DSimpPercent

/-!
# The reduced Burau determinant and the braid Alexander polynomial

For an `(n + 1)`-strand braid, the determinant of its reduced Burau matrix minus the
identity is the geometric sum `1 + t + ⋯ + t^n`, times `t⁻ⁿ` times the corner-minor
Alexander invariant. This identifies the reduced determinant algorithm with the existing
unreduced algorithm, with its exact unit factor. It does not identify either algorithm
with a geometric knot's Seifert matrix.

The identity holds over every commutative ring at a unit parameter. It does not divide by
the geometric sum: in particular it remains valid at roots of unity and in positive
characteristic. Over a field where the sum is nonzero, it gives the usual quotient formula.

The calculation uses the existing Burau-column intertwining identity and Mathlib's
rank-one determinant formula through `Matrix.det_of_intertwining_of_mulVec_eq_zero`.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82,
  Princeton University Press (1974), Chapter 3.
* A. Conway, *Burau maps and twisted Alexander polynomials*, Proceedings of the Edinburgh
  Mathematical Society 61 (2018), 479–497, introduction (the classical Burau formula).
-/

public section

open Matrix

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The reduced Burau determinant is the geometric sum times the existing braid Alexander
invariant, with unit factor `t⁻ⁿ`. This equality remains valid when the geometric sum is zero. -/
@[simp] theorem det_reducedBurauCol_sub_one (b : BraidGroup (n + 1)) (t : Rˣ) :
    -- Normalize dimension arithmetic in implicit coercion and instance arguments too.
    (dsimp% only [Nat.add_one_sub_one]
      ((reducedBurauCol (n + 1) t b : Matrix (Fin (n + 1 - 1)) (Fin (n + 1 - 1)) R) - 1).det) =
      (∑ i : Fin (n + 1), (t : R) ^ (i : ℕ)) *
        ((t⁻¹ : Rˣ) : R) ^ n * (MarkovBraid.mk n b).burauAlexander t := by
  let A := (burau (n + 1) t b : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1
  let C := burauColMatrix (n + 1) (t : R)
  let X := (reducedBurauCol (n + 1) t b : Matrix (Fin (n + 1 - 1)) (Fin (n + 1 - 1)) R) - 1
  have hAX : A * C = C * X := by
    simp only [A, C, X, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      burau_mul_burauColMatrix]
  have h := Matrix.det_of_intertwining_of_mulVec_eq_zero A C X
    (fun _ => 1) (fun i => (t : R) ^ (i : ℕ))
    (burau_sub_one_mulVec_one t b) rfl
    (geom_vecMul_burauColMatrix_eq_zero (n + 1) (t : R))
    (by
      dsimp only [C]
      rw [det_burauColMatrix_submatrix_castSucc]
      exact t.isUnit.pow n) hAX
  simp only [dotProduct, mul_one, Fin.val_last] at h
  have hcancel : ((t⁻¹ : Rˣ) : R) ^ n * (t : R) ^ n = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  rw [MarkovBraid.burauAlexander_def]
  -- Multiply by the inverse unit rather than cancelling the geometric sum.
  have h' := congrArg (fun r : R => ((t⁻¹ : Rˣ) : R) ^ n * r) h
  simpa only [← mul_assoc, hcancel, one_mul, mul_comm, mul_left_comm, A, X] using h'

end TauCeti.KnotTheory
