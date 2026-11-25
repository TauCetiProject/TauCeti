/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.Matrix.Charpoly.FinTwo
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Examples of the rank-two trace identity

* For `g = diag(2, 3)` and `h = 1` over `ℚ`, the identity
  `det g * tr (g⁻¹ h) - tr g * tr h + tr (g h) = 0` reads `6 * (1/2 + 1/3) - 5 * 2 + 5 = 0`,
  while the variant with `tr (g h⁻¹)` in place of `tr (g⁻¹ h)` gives `6 * 5 - 5 * 2 + 5 = 25`.
* For the trivial representation `1 ⊕ 1` the identity reads `2 - 4 + 2 = 0`.
* Over `𝔽₂` the unipotent matrix `(1 1; 0 1)` has the trace and determinant of `1`, so the same
  characteristic polynomial, without being conjugate to `1`.
-/

open Matrix

/-! ### The numerical witness -/

example :
    let g : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 3]
    g.det * (g⁻¹ * 1).trace - g.trace * (1 : Matrix (Fin 2) (Fin 2) ℚ).trace + (g * 1).trace
      = 0 := by
  norm_num [inv_def, adjugate_fin_two, det_fin_two, trace_fin_two]

example :
    let g : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 3]
    g.det * (g * 1⁻¹).trace - g.trace * (1 : Matrix (Fin 2) (Fin 2) ℚ).trace + (g * 1).trace
      = 25 := by
  norm_num [det_fin_two, trace_fin_two]

/-! ### The trivial representation -/

example (A : Type*) [CommRing A] :
    (1 : Matrix (Fin 2) (Fin 2) A).det * (1 : Matrix (Fin 2) (Fin 2) A).trace
      - (1 : Matrix (Fin 2) (Fin 2) A).trace * (1 : Matrix (Fin 2) (Fin 2) A).trace
      + (1 : Matrix (Fin 2) (Fin 2) A).trace = 0 := by
  simp only [det_one, trace_one, Fintype.card_fin]
  norm_num

/-! ### Equal traces and determinants without conjugacy over `𝔽₂` -/

example : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2)).charpoly =
    (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)).charpoly := by
  rw [charpoly_eq_charpoly_iff_fin_two]
  refine ⟨?_, ?_⟩
  · rw [trace_fin_two_of, trace_one]
    decide
  · rw [det_fin_two_of, det_one]
    decide

example (P : GL (Fin 2) (ZMod 2)) :
    (P : Matrix (Fin 2) (Fin 2) (ZMod 2)) * 1 * ((P⁻¹ : GL (Fin 2) (ZMod 2)) : Matrix _ _ _) ≠
      !![1, 1; 0, 1] := by
  rw [mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  intro h
  simpa using congrFun (congrFun h 0) 1
