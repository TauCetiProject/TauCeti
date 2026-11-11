/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# Alternating area and conormals in dimension two

If a linear functional annihilates a tangent vector, contracting an alternating area form
with two transverse vectors changes by the same factor as their values under that functional.
This identity proves that an induced boundary orientation is independent of the inward field.
-/

public section
noncomputable section
open Set
namespace ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Area contractions and transverse conormal values have the same ratio. -/
theorem apply_pair_mul_apply_eq (hE : Module.finrank ℝ E = 2)
    (A : E [⋀^Fin 2]→L[ℝ] ℝ) (L : E →L[ℝ] ℝ) {u W W' : E}
    (hLu : L u = 0) (hLW : L W ≠ 0) :
    A ![W', u] * L W = A ![W, u] * L W' := by
  by_cases hu : u = 0
  · subst u
    have hz (z : E) : A ![z, 0] = 0 := A.map_coord_zero 1 rfl
    rw [hz, hz, zero_mul, zero_mul]
  have hli : LinearIndependent ℝ ![u, W] := by
    rw [LinearIndependent.pair_iff' hu]
    intro a ha
    have h := congrArg L ha
    rw [map_smul, hLu, smul_zero] at h
    exact hLW h.symm
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simpa using hE.symm)
  have hB : (B : Fin 2 → E) = ![u, W] :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hrepr : W' = (B.repr W') 0 • u + (B.repr W') 1 • W := by
    have h := B.sum_repr W'
    rw [Fin.sum_univ_two] at h
    simpa only [hB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using h.symm
  have hL : L W' = (B.repr W') 1 * L W := by
    conv_lhs => rw [hrepr]
    rw [map_add, map_smul, map_smul, hLu, smul_zero, zero_add, smul_eq_mul]
  have hA : A ![W', u] = (B.repr W') 1 * A ![W, u] := by
    change A.curryLeft W' ![u] = _
    conv_lhs => rw [hrepr]
    rw [map_add, map_smul, map_smul, add_apply, smul_apply, smul_apply]
    simp only [curryLeft_apply_apply]
    have hz : A ![u, u] = 0 := A.map_eq_zero_of_eq _ (by rfl) (by decide : (0 : Fin 2) ≠ 1)
    rw [hz, smul_zero, zero_add, smul_eq_mul]
  rw [hL, hA]
  ring
/-- The complementary basis vector gives the exact coordinate face sign. -/
theorem apply_pair_basis_rev (A : E [⋀^Fin 2]→L[ℝ] ℝ)
    (B : Module.Basis (Fin 2) ℝ E) (i : Fin 2) (w : E) :
    A ![w, B i.rev] = (-1 : ℝ) ^ i.val * (B.repr w) i * A B := by
  rw [apply_eq_det_mul A B]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  fin_cases i <;> simp [Module.Basis.repr_self]

end ContinuousAlternatingMap
