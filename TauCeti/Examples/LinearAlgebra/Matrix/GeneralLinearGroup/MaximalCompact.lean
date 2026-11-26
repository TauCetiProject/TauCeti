/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MaximalCompact
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Compact subgroups meet the positive upper-triangular group trivially: checks

Checks for `Matrix.GeneralLinearGroup.inf_posUpperTriangularGroup_eq_bot_of_isCompact`.

* `n = 0`: the general linear group is trivial, so both subgroups are `⊥`.
* `n = 1`: `A N` is the group `ℝ_{>0}` of positive real scalars in `ℂˣ`, and the circle group
  `U(1)` meets it trivially.
* `n = 2`, `K = U(2)`: the unitary group meets `A N` trivially.
* Positivity is load-bearing: `diag(1, -1)` is unitary and upper triangular with real diagonal,
  but it is not the identity, so a compact subgroup can meet the group of all invertible upper
  triangular matrices nontrivially.

## Main declarations

* `TauCeti.CompactPosUpperTriangular.diagOneNegOne`: the invertible matrix `diag(1, -1)`.
* `TauCeti.CompactPosUpperTriangular.diagOneNegOne_mem_inf`: it is unitary and upper triangular.
* `TauCeti.CompactPosUpperTriangular.diagOneNegOne_ne_one`: it is not the identity.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition, Birkhäuser (1996),
  Chapter VI, §4, Theorem 6.46 (the compact/triangular intersection in the Iwasawa decomposition).
-/

public noncomputable section

open Matrix Matrix.GeneralLinearGroup
open scoped ComplexOrder

namespace TauCeti.CompactPosUpperTriangular

/-- For `n = 0` every subgroup of the trivial group `GL (Fin 0) ℂ` meets `A N` trivially. -/
example (K : Subgroup (GL (Fin 0) ℂ)) : K ⊓ posUpperTriangularGroup (Fin 0) ℂ = ⊥ :=
  Subsingleton.elim _ _

/-- For `n = 1`, `A N` consists of the positive real scalars. -/
example (g : GL (Fin 1) ℂ) : g ∈ posUpperTriangularGroup (Fin 1) ℂ ↔ 0 < g 0 0 := by
  simp [PosUpperTriangularGroup.mem_iff, Matrix.IsUpperTriangular, Matrix.BlockTriangular,
    Fin.forall_fin_one]

/-- For `n = 1`, the circle group `U(1)` meets the positive real scalars trivially. -/
example : unitarySubgroup (GL (Fin 1) ℂ) ⊓ posUpperTriangularGroup (Fin 1) ℂ = ⊥ :=
  inf_posUpperTriangularGroup_eq_bot_of_isCompact isCompact_unitarySubgroup

/-- For `K = U(2)`, `K ∩ A N = {1}`. -/
example : unitarySubgroup (GL (Fin 2) ℂ) ⊓ posUpperTriangularGroup (Fin 2) ℂ = ⊥ :=
  inf_posUpperTriangularGroup_eq_bot_of_isCompact isCompact_unitarySubgroup

/-- The invertible diagonal matrix `diag(1, -1)`. -/
def diagOneNegOne : GL (Fin 2) ℂ := diagGL ![1, -1]

/-- The matrix `diag(1, -1)` is unitary and upper triangular. -/
theorem diagOneNegOne_mem_inf :
    diagOneNegOne ∈ unitarySubgroup (GL (Fin 2) ℂ) ⊓ upperTriangularGroup (Fin 2) ℂ := by
  refine ⟨mem_unitarySubgroup_GL_iff_mem_unitaryGroup.mpr ?_, ?_⟩
  · rw [mem_unitaryGroup_iff, diagOneNegOne, diagGL_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [diagOneNegOne, ← UpperTriangularGroup.coe_diagonalHom]
    exact (UpperTriangularGroup.diagonalHom _).property

/-- The matrix `diag(1, -1)` is not the identity, so positivity of the diagonal is needed. -/
theorem diagOneNegOne_ne_one : diagOneNegOne ≠ 1 := by
  intro h
  have h11 := congrArg (fun g : GL (Fin 2) ℂ ↦ (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1) h
  norm_num [diagOneNegOne, diagGL_coe] at h11

end TauCeti.CompactPosUpperTriangular
