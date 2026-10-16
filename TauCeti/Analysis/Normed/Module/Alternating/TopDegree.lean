/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# Top-degree continuous alternating forms

Top-degree real alternating forms are determined by their basis coefficient. Pullback by a
continuous linear endomorphism multiplies that coefficient by the signed determinant.
-/

public section

noncomputable section

open Set

namespace ContinuousAlternatingMap

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]

/-- A top-degree alternating form is determined by its scalar coefficient in a basis. -/
theorem apply_eq_det_mul (ω : E [⋀^ι]→L[ℝ] ℝ) (b : Module.Basis ι ℝ E) (v : ι → E) :
    ω v = b.det v * ω b := by
  have h := congrArg (fun f : E [⋀^ι]→ₗ[ℝ] ℝ ↦ f v) (ω.toAlternatingMap.eq_smul_basis_det b)
  simpa only [coe_toAlternatingMap, _root_.smul_apply, smul_eq_mul, mul_comm] using h

omit [Fintype ι] [DecidableEq ι] in
/-- Pullback of a top-degree coefficient multiplies by the signed real determinant. -/
theorem compContinuousLinearMap_apply_basis [Finite ι] (ω : E [⋀^ι]→L[ℝ] ℝ)
    (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E) :
    (ω.compContinuousLinearMap A) b = A.toLinearMap.det * ω b := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [compContinuousLinearMap_apply, apply_eq_det_mul ω b]
  have hd := b.det_comp A.toLinearMap b
  simp only [ContinuousLinearMap.coe_coe, b.det_self, mul_one] at hd
  rw [hd]

end ContinuousAlternatingMap
