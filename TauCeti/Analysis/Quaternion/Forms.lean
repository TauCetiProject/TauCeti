/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The quaternionic forms `dq` and `Dq`

In the coordinates `q = t + i x + j y + k z` of `ℍ`, read on the integration domain `Fin 4 → ℝ`
in the order `(t, x, y, z)`, this file defines the constant quaternion-valued `1`-form

`dq = dt + i dx + j dy + k dz`

and the constant quaternion-valued `3`-form

`Dq = dx∧dy∧dz − i dt∧dy∧dz − j dt∧dz∧dx − k dt∧dx∧dy`.

Both forms are constant, so each is given by its value at every base point: a continuous real
linear map for `dq` and a continuous real alternating map for `Dq`. The form `Dq` is the surface
element of quaternionic analysis: classically, for `f` of class `C¹`, `d (Dq * f)` and
`d (f * Dq)` are the left and right Cauchy–Riemann–Fueter operators of `f` times the volume form,
and `Dq` is the form integrated over boundaries in the Cauchy–Fueter theorems. Quaternion
coefficients act on these forms on either
side through the module structures of `ℍ` and `ℍᵐᵒᵖ` on the target, so that
`(a • Dq) v = a * Dq v` and `(MulOpposite.op a • Dq) v = Dq v * a`; the order is part of every
statement.

On the coordinate triple obtained by deleting the `i`-th direction, `Dq` takes the value
`(-1) ^ i` times the `i`-th unit `1, i, j, k`. More intrinsically, `Dq` is the quaternionic
interior product of the volume form: for every `w`, the real inner product of `dq w` with
`Dq v` is the determinant of the `4 × 4` matrix with rows `w, v 0, v 1, v 2`. Quaternion
conjugation of the tangent vectors pulls `Dq` back to `-star Dq`.

## Main declarations

* `TauCeti.Quaternion.dq`: the `1`-form `dq`, the inverse of the coordinate map `ℍ → (Fin 4 → ℝ)`.
* `TauCeti.Quaternion.Dq`: the `3`-form `Dq`, as a continuous alternating map.
* `TauCeti.Quaternion.Dq_apply`: `Dq v` is the sum over the four coordinates `i` of
  `(-1) ^ i` times the `3 × 3` minor of `v` omitting coordinate `i`, times the `i`-th unit.
* `TauCeti.Quaternion.Dq_succAbove`: the value of `Dq` on the coordinate triple omitting the
  `i`-th direction is `(-1) ^ i` times the `i`-th unit.
* `TauCeti.Quaternion.inner_dq_Dq`: `⟪dq w, Dq v⟫_ℝ = det (w, v 0, v 1, v 2)`.
* `TauCeti.Quaternion.Dq_star`: the pullback of `Dq` under quaternion conjugation is `-star Dq`.

## References

* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225,
  for the forms `dq` and `Dq`.
* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, the form `dX` and equation (18) for the
  `3`-form, there called `Dx`.
-/

public section

open scoped Quaternion RealInnerProductSpace

namespace TauCeti.Quaternion

/-! ### The `1`-form `dq` -/

/-- The constant quaternion-valued `1`-form `dq = dt + i dx + j dy + k dz` on the coordinate space
`Fin 4 → ℝ`: it sends `h` to `h 0 + i * h 1 + j * h 2 + k * h 3`, the quaternion with coordinates
`h`. -/
noncomputable def dq : (Fin 4 → ℝ) →L[ℝ] ℍ :=
  (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.toContinuousLinearEquiv

theorem dq_apply (h : Fin 4 → ℝ) : dq h = ⟨h 0, h 1, h 2, h 3⟩ :=
  (rfl)

@[simp]
theorem re_dq (h : Fin 4 → ℝ) : (dq h).re = h 0 :=
  (rfl)

@[simp]
theorem imI_dq (h : Fin 4 → ℝ) : (dq h).imI = h 1 :=
  (rfl)

@[simp]
theorem imJ_dq (h : Fin 4 → ℝ) : (dq h).imJ = h 2 :=
  (rfl)

@[simp]
theorem imK_dq (h : Fin 4 → ℝ) : (dq h).imK = h 3 :=
  (rfl)

/-- `dq` sends the `i`-th coordinate vector to the `i`-th unit of `1, i, j, k`. -/
theorem dq_single (i : Fin 4) (r : ℝ) :
    dq (Pi.single i r) = r • QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i := by
  rw [QuaternionAlgebra.basisOneIJK, Module.Basis.coe_ofEquivFun, ← map_smul, ← Pi.single_smul',
    smul_eq_mul, mul_one]
  rfl

/-- `dq` is the inverse of the coordinate map `QuaternionAlgebra.linearEquivTuple`. -/
theorem coe_dq : ⇑dq = (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm :=
  (rfl)

/-! ### The `3`-form `Dq` -/

/-- The real `3`-form on `Fin 4 → ℝ` omitting the coordinate `i`: the determinant of the
`3 × 3` matrix of the remaining coordinates of three vectors. These are `dx∧dy∧dz`,
`dt∧dy∧dz`, `dt∧dx∧dz` and `dt∧dx∧dy`. -/
noncomputable def minorForm (i : Fin 4) : (Fin 4 → ℝ) [⋀^Fin 3]→L[ℝ] ℝ :=
  AlternatingMap.toContinuousAlternatingMap
    (Matrix.detRowAlternating.compLinearMap (LinearMap.funLeft ℝ ℝ i.succAbove))

theorem minorForm_apply (i : Fin 4) (v : Fin 3 → Fin 4 → ℝ) :
    minorForm i v = (Matrix.of fun r c ↦ v r (i.succAbove c)).det := by
  rw [minorForm, AlternatingMap.coe_toContinuousAlternatingMap,
    AlternatingMap.compLinearMap_apply]
  -- `Matrix.det` is `Matrix.detRowAlternating` evaluated on the rows of the matrix.
  rfl

/-- The constant quaternion-valued `3`-form
`Dq = dx∧dy∧dz − i dt∧dy∧dz − j dt∧dz∧dx − k dt∧dx∧dy` on the coordinate space `Fin 4 → ℝ`.
Its `i`-th coefficient is `(-1) ^ i` times the `i`-th unit `1, i, j, k`, against the real
`3`-form omitting the coordinate `i`. -/
noncomputable def Dq : (Fin 4 → ℝ) [⋀^Fin 3]→L[ℝ] ℍ :=
  ∑ i : Fin 4,
    (minorForm i).smulRight ((-1 : ℝ) ^ (i : ℕ) • QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i)


/-- `Dq v` is the sum over the coordinates `i` of `(-1) ^ i` times the minor of `v` omitting
coordinate `i`, times the `i`-th unit of `1, i, j, k`. -/
theorem Dq_apply (v : Fin 3 → Fin 4 → ℝ) :
    Dq v = ∑ i : Fin 4,
      ((-1 : ℝ) ^ (i : ℕ) * minorForm i v) • QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i := by
  simp only [Dq, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smulRight_apply,
    mul_comm _ (minorForm _ v), mul_smul]

/-- The real part of `Dq` is `dx∧dy∧dz`. -/
@[simp]
theorem re_Dq (v : Fin 3 → Fin 4 → ℝ) : (Dq v).re = minorForm 0 v := by
  norm_num [Dq_apply, Fin.sum_univ_four, ← dq_single, Pi.single_apply]

/-- The `i`-component of `Dq` is `-dt∧dy∧dz`. -/
@[simp]
theorem imI_Dq (v : Fin 3 → Fin 4 → ℝ) : (Dq v).imI = -minorForm 1 v := by
  norm_num [Dq_apply, Fin.sum_univ_four, ← dq_single, Pi.single_apply]

/-- The `j`-component of `Dq` is `-dt∧dz∧dx = dt∧dx∧dz`. -/
@[simp]
theorem imJ_Dq (v : Fin 3 → Fin 4 → ℝ) : (Dq v).imJ = minorForm 2 v := by
  norm_num [Dq_apply, Fin.sum_univ_four, ← dq_single, Pi.single_apply]

/-- The `k`-component of `Dq` is `-dt∧dx∧dy`. -/
@[simp]
theorem imK_Dq (v : Fin 3 → Fin 4 → ℝ) : (Dq v).imK = -minorForm 3 v := by
  norm_num [Dq_apply, Fin.sum_univ_four, ← dq_single, Pi.single_apply]

/-- On the coordinate triple obtained by deleting the `i`-th direction, `Dq` takes the value
`(-1) ^ i` times the `i`-th unit of `1, i, j, k`: so `Dq (e_x, e_y, e_z) = 1`,
`Dq (e_t, e_y, e_z) = -i`, `Dq (e_t, e_x, e_z) = j` and `Dq (e_t, e_x, e_y) = -k`. -/
theorem Dq_succAbove (i : Fin 4) :
    Dq (fun r ↦ Pi.single (i.succAbove r) 1) =
      (-1 : ℝ) ^ (i : ℕ) • QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i := by
  rw [← dq_single]
  fin_cases i <;> ext <;>
    norm_num [minorForm_apply, Matrix.det_fin_three, Pi.single_apply, Fin.succAbove]

/-- `Dq` is the quaternionic interior product of the volume form: the real inner product of
`dq w` with `Dq v` is the determinant of the matrix with rows `w, v 0, v 1, v 2`. -/
theorem inner_dq_Dq (w : Fin 4 → ℝ) (v : Fin 3 → Fin 4 → ℝ) :
    ⟪dq w, Dq v⟫ = (Matrix.of (Fin.cons w v : Fin 4 → Fin 4 → ℝ)).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four, Quaternion.inner_def]
  simp [minorForm_apply, Matrix.submatrix, Fin.succAbove]
  ring

/-- Conjugating the tangent vectors pulls `Dq` back to `-star Dq`: if `dq (w r)` is the conjugate of
`dq (v r)` for each `r`, then `Dq w = -star (Dq v)`. -/
theorem Dq_star {v w : Fin 3 → Fin 4 → ℝ} (h : ∀ r, dq (w r) = star (dq (v r))) :
    Dq w = -star (Dq v) := by
  have h0 r : w r 0 = v r 0 := by simpa using congrArg QuaternionAlgebra.re (h r)
  have h1 r : w r 1 = -v r 1 := by simpa using congrArg QuaternionAlgebra.imI (h r)
  have h2 r : w r 2 = -v r 2 := by simpa using congrArg QuaternionAlgebra.imJ (h r)
  have h3 r : w r 3 = -v r 3 := by simpa using congrArg QuaternionAlgebra.imK (h r)
  ext <;> simp [minorForm_apply, Matrix.det_fin_three, Fin.succAbove, h0, h1, h2, h3]
  ring

end TauCeti.Quaternion
