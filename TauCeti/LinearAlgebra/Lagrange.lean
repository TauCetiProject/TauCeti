/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# Top derivative of a corrected Lagrange interpolant

`Lagrange.iterate_derivative_interpolate_add_C_mul_nodal` prescribes the top derivative of an
interpolant by adding a constant multiple of the node polynomial. It holds over any field,
including for repeated nodes, and supplies the algebraic step in interpolation remainder formulas.
-/

public section

open Finset Polynomial

namespace Lagrange

/-- Adding `c` times the node polynomial to the interpolant gives a polynomial whose `#s`-th
formal derivative is the constant `c * (#s)!`, even when nodes are repeated. -/
theorem iterate_derivative_interpolate_add_C_mul_nodal {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (v : ι → F) (r : ι → F) (c : F) :
    derivative^[s.card] (interpolate s v r + C c * nodal s v) =
      C (c * (s.card.factorial : F)) := by
  have hp : derivative^[s.card] (interpolate s v r) = 0 := by
    apply iterate_derivative_eq_zero_of_degree_lt
    rw [interpolate_eq_sum]
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 ?_)
    intro i hi
    refine (degree_mul_le_of_le degree_C_le le_rfl).trans_lt ?_
    rw [← nodal_eq, degree_nodal, zero_add]
    exact_mod_cast card_erase_lt_of_mem hi
  -- The top derivative uses Mathlib's `hasseDeriv_natDegree_eq_C` and
  -- `factorial_smul_hasseDeriv` for the monic node polynomial.
  have hhasse : hasseDeriv s.card (nodal s v) = C 1 := by
    rw [← natDegree_nodal (s := s) (v := v), hasseDeriv_natDegree_eq_C,
      nodal_monic.leadingCoeff]
  rw [iterate_map_add derivative, hp, zero_add, iterate_derivative_C_mul,
    ← factorial_smul_hasseDeriv, LinearMap.smul_apply, hhasse]
  simp [nsmul_eq_mul, C_mul]

end Lagrange
