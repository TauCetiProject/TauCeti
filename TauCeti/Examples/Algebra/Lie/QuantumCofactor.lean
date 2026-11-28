/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.ZMod.Basic
public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Vector
import Mathlib.Tactic.FinCases

/-!
# A quantum cofactor contraction in characteristic two

The upper-left matrix units in a three-dimensional matrix algebra act on the extra bottom
row by the vector commutator law. At spectral parameter `0`, the signed cofactor contraction
with a one-entry row tuple is a nonzero matrix unit. This example checks the spectral shift
without a torsion-free coefficient hypothesis.
-/

public section

namespace TauCeti.Examples

open Matrix

/-- The first-row cofactor contraction at parameter zero gives the matrix unit at `(2, 1)`. -/
theorem quantumCofactor_eq_single_mod_two :
    let E : Matrix (Fin 2) (Fin 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
      of fun i j ↦ single i.castSucc j.castSucc 1
    let y (j : Fin 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) := single 2 j.castSucc 1
    y 0 * E.quantumMinor (0 : ZMod 2) (fun _ : Fin 1 ↦ 0) (fun _ : Fin 1 ↦ 1) -
      y 1 * E.quantumMinor (0 : ZMod 2) (fun _ : Fin 1 ↦ 0) (fun _ : Fin 1 ↦ 0) = y 1 := by
  intro E y
  have h := E.sum_vector_mul_quantumMinor_eq y (0 : ZMod 2) (fun _ : Fin 1 ↦ 0) id (by
    intro i j k
    fin_cases i
    fin_cases j <;> fin_cases k <;>
      simp [Ring.lie_def, E, y, Fin.castSucc])
  calc
    _ = ∑ j : Fin 2, (-1 : ℤ) ^ j.val •
        (E.quantumMinor ((0 : ZMod 2) - 1) (fun _ : Fin 1 ↦ 0) (j.removeNth id) * y j) := by
      convert h using 1 <;> simp [Fin.sum_univ_two, Fin.removeNth, Fin.succAbove, sub_eq_add_neg]
    _ = _ := by
      simp [Fin.sum_univ_two, Fin.removeNth, Fin.succAbove, E, y, Fin.castSucc, add_mul,
        ZMod.neg_eq_self_mod_two]

end TauCeti.Examples
