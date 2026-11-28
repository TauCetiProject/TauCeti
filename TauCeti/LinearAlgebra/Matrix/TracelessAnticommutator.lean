/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring

/-!
# The traceless anticommutator of square matrices

For matrix size `d`, subtracting `(2 * Ring.inverse d) tr(XY)` times the identity from
`XY + YX` gives a symmetric bilinear operation. If `d` is a unit, the result has trace zero.
For nonunit `d`, the operation reduces to `XY + YX`.
Conjugation by any invertible matrix preserves the operation.
-/

public section

namespace Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

/-- The anticommutator with its scalar trace correction. The correction vanishes when the matrix
size is a nonunit. -/
noncomputable def tracelessAnticommutator (X Y : Matrix ι ι K) : Matrix ι ι K :=
  X * Y + Y * X - ((2 * Ring.inverse (Fintype.card ι : K)) * trace (X * Y)) • 1

/-- The traceless anticommutator is the sum of the two products minus the scalar trace
correction. -/
theorem tracelessAnticommutator_def (X Y : Matrix ι ι K) :
    tracelessAnticommutator X Y =
      X * Y + Y * X - ((2 * Ring.inverse (Fintype.card ι : K)) * trace (X * Y)) • 1 := by
  unfold tracelessAnticommutator
  rfl

/-- The scalar correction removes the trace whenever the matrix size is a unit. -/
@[simp]
theorem trace_tracelessAnticommutator [Invertible (Fintype.card ι : K)] (X Y : Matrix ι ι K) :
    trace (tracelessAnticommutator X Y) = 0 := by
  simp only [tracelessAnticommutator, trace_sub, trace_add, trace_smul, trace_one,
    trace_mul_comm Y X, smul_eq_mul]
  have hn := Ring.mul_inverse_cancel (Fintype.card ι : K) (isUnit_of_invertible _)
  calc
    _ = trace (X * Y) + trace (X * Y) -
        2 * trace (X * Y) * ((Fintype.card ι : K) * Ring.inverse (Fintype.card ι : K)) := by ring
    _ = 0 := by rw [hn]; ring

/-- The traceless anticommutator is symmetric in its arguments. -/
theorem tracelessAnticommutator_comm (X Y : Matrix ι ι K) :
    tracelessAnticommutator X Y = tracelessAnticommutator Y X := by
  simp only [tracelessAnticommutator, trace_mul_comm Y X, add_comm]

/-- Additivity in the first argument. -/
theorem tracelessAnticommutator_add_left (X Y Z : Matrix ι ι K) :
    tracelessAnticommutator (X + Y) Z =
      tracelessAnticommutator X Z + tracelessAnticommutator Y Z := by
  simp only [tracelessAnticommutator, add_mul, mul_add, trace_add, mul_add, add_smul]
  abel

/-- Scalar compatibility in the first argument. -/
theorem tracelessAnticommutator_smul_left (a : K) (X Y : Matrix ι ι K) :
    tracelessAnticommutator (a • X) Y = a • tracelessAnticommutator X Y := by
  simp only [tracelessAnticommutator, Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_add,
    smul_sub, smul_smul]
  congr 2
  ring

/-- Additivity in the second argument. -/
theorem tracelessAnticommutator_add_right (X Y Z : Matrix ι ι K) :
    tracelessAnticommutator X (Y + Z) =
      tracelessAnticommutator X Y + tracelessAnticommutator X Z := by
  rw [tracelessAnticommutator_comm X, tracelessAnticommutator_add_left,
    tracelessAnticommutator_comm Y X, tracelessAnticommutator_comm Z X]

/-- Scalar compatibility in the second argument. -/
theorem tracelessAnticommutator_smul_right (a : K) (X Y : Matrix ι ι K) :
    tracelessAnticommutator X (a • Y) = a • tracelessAnticommutator X Y := by
  rw [tracelessAnticommutator_comm X, tracelessAnticommutator_smul_left,
    tracelessAnticommutator_comm Y X]

/-- Conjugation by an invertible matrix preserves the traceless anticommutator. -/
theorem tracelessAnticommutator_units_smul (g : ConjAct (Matrix ι ι K)ˣ) (X Y : Matrix ι ι K) :
    tracelessAnticommutator (g • X) (g • Y) = g • tracelessAnticommutator X Y := by
  have htrace : trace (g • (X * Y)) = trace (X * Y) := by
    rw [ConjAct.units_smul_def]
    exact trace_units_conj (ConjAct.ofConjAct g) (X * Y)
  have hscalar (c : K) :
      g • (c • (1 : Matrix ι ι K)) =
        c • (1 : Matrix ι ι K) := by
    -- The conjugation action fixes scalars, since it fixes `1`.
    rw [smul_comm, MulDistribMulAction.smul_one]
  simp only [tracelessAnticommutator, ← smul_mul', smul_add, smul_sub, htrace, hscalar]

end Matrix
