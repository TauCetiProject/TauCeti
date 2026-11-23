/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The traceless anticommutator of three-by-three matrices

The anticommutator of two matrices has trace twice the trace of the product. On three-by-three
matrices the identity has trace three, so subtracting `(2 / 3) tr(XY)` times the identity
leaves a trace-zero matrix. Conjugation by any invertible matrix preserves this operation.
-/

public section

namespace Matrix

variable {K : Type*} [Field K]

/-- The traceless part of the anticommutator of two three-by-three matrices. -/
def tracelessAnticommutator (X Y : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  X * Y + Y * X - ((2 / 3 : K) * trace (X * Y)) • 1

/-- The traceless anticommutator has the displayed formula. -/
theorem tracelessAnticommutator_apply (X Y : Matrix (Fin 3) (Fin 3) K) :
    tracelessAnticommutator X Y =
      X * Y + Y * X - ((2 / 3 : K) * trace (X * Y)) • 1 :=
  (rfl)

/-- The scalar correction removes the full trace of the anticommutator. -/
@[simp]
theorem trace_tracelessAnticommutator [NeZero (3 : K)] (X Y : Matrix (Fin 3) (Fin 3) K) :
    trace (tracelessAnticommutator X Y) = 0 := by
  simp only [tracelessAnticommutator, trace_sub, trace_add, trace_smul, trace_one,
    Fintype.card_fin, trace_mul_comm Y X, smul_eq_mul]
  field_simp [NeZero.ne (3 : K)]
  ring

/-- The traceless anticommutator is symmetric in its arguments. -/
theorem tracelessAnticommutator_comm (X Y : Matrix (Fin 3) (Fin 3) K) :
    tracelessAnticommutator X Y = tracelessAnticommutator Y X := by
  simp only [tracelessAnticommutator, trace_mul_comm Y X, add_comm]

/-- Additivity in the first argument. -/
theorem tracelessAnticommutator_add_left (X Y Z : Matrix (Fin 3) (Fin 3) K) :
    tracelessAnticommutator (X + Y) Z =
      tracelessAnticommutator X Z + tracelessAnticommutator Y Z := by
  simp only [tracelessAnticommutator, add_mul, mul_add, trace_add, mul_add, add_smul]
  abel

/-- Scalar compatibility in the first argument. -/
theorem tracelessAnticommutator_smul_left (a : K) (X Y : Matrix (Fin 3) (Fin 3) K) :
    tracelessAnticommutator (a • X) Y = a • tracelessAnticommutator X Y := by
  simp only [tracelessAnticommutator, Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_add,
    smul_sub, smul_smul]
  congr 2
  ring

/-- Additivity in the second argument. -/
theorem tracelessAnticommutator_add_right (X Y Z : Matrix (Fin 3) (Fin 3) K) :
    tracelessAnticommutator X (Y + Z) =
      tracelessAnticommutator X Y + tracelessAnticommutator X Z := by
  rw [tracelessAnticommutator_comm X, tracelessAnticommutator_add_left,
    tracelessAnticommutator_comm Y, tracelessAnticommutator_comm Z]

/-- Scalar compatibility in the second argument. -/
theorem tracelessAnticommutator_smul_right (a : K) (X Y : Matrix (Fin 3) (Fin 3) K) :
    tracelessAnticommutator X (a • Y) = a • tracelessAnticommutator X Y := by
  rw [tracelessAnticommutator_comm X, tracelessAnticommutator_smul_left,
    tracelessAnticommutator_comm Y]

/-- Conjugation by an invertible matrix preserves the traceless anticommutator. -/
theorem tracelessAnticommutator_conj (g : (Matrix (Fin 3) (Fin 3) K)ˣ)
    (X Y : Matrix (Fin 3) (Fin 3) K) :
    tracelessAnticommutator ((g : Matrix (Fin 3) (Fin 3) K) * X *
      ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K))
      ((g : Matrix (Fin 3) (Fin 3) K) * Y * ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K)) =
      (g : Matrix (Fin 3) (Fin 3) K) * tracelessAnticommutator X Y *
        ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K) := by
  have hsmul (A : Matrix (Fin 3) (Fin 3) K) :
      (g : Matrix (Fin 3) (Fin 3) K) * A * ((g⁻¹ : _) : Matrix (Fin 3) (Fin 3) K) =
        ConjAct.toConjAct g • A := by
    simp [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  have htrace : trace (ConjAct.toConjAct g • (X * Y)) = trace (X * Y) := by
    rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
    exact trace_units_conj g (X * Y)
  have hscalar (c : K) :
      ConjAct.toConjAct g • (c • (1 : Matrix (Fin 3) (Fin 3) K)) =
        c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    -- The conjugation action fixes scalars, since it fixes `1`.
    rw [smul_comm, MulDistribMulAction.smul_one]
  rw [hsmul X, hsmul Y, hsmul (tracelessAnticommutator X Y)]
  simp only [tracelessAnticommutator, ← smul_mul', smul_add, smul_sub, htrace, hscalar]

end Matrix
