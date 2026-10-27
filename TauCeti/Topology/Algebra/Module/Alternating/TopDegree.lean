/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# Top-degree continuous alternating forms

Top-degree scalar-valued continuous alternating forms over a commutative ring are determined
by their basis coefficient. Pullback by a continuous linear endomorphism multiplies that
coefficient by its determinant. Above the top degree, continuous alternating maps on a
finite-dimensional space over a division ring vanish. No compatibility between the topology and
the module structure is required for those statements.
-/

public section

namespace ContinuousAlternatingMap

variable {R E ι : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup E] [Module R E] [TopologicalSpace E] [Fintype ι] [DecidableEq ι]

/-- A top-degree alternating form is determined by its scalar coefficient in a basis. -/
theorem apply_eq_det_mul (ω : E [⋀^ι]→L[R] R) (b : Module.Basis ι R E) (v : ι → E) :
    ω v = b.det v * ω b := by
  have h := congrArg (fun f : E [⋀^ι]→ₗ[R] R ↦ f v) (ω.toAlternatingMap.eq_smul_basis_det b)
  simpa only [coe_toAlternatingMap, _root_.smul_apply, smul_eq_mul, mul_comm] using h

omit [Fintype ι] [DecidableEq ι] in
/-- Pullback of a top-degree coefficient multiplies by the determinant. -/
theorem compContinuousLinearMap_apply_basis [Finite ι] (ω : E [⋀^ι]→L[R] R)
    (b : Module.Basis ι R E) (A : E →L[R] E) :
    (ω.compContinuousLinearMap A) b = A.toLinearMap.det * ω b := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [compContinuousLinearMap_apply, apply_eq_det_mul ω b]
  simp only [← ContinuousLinearMap.coe_coe A, b.det_comp, b.det_self, mul_one]

section AboveTopDegree

variable {K E F ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [AddCommGroup F] [Module K F] [TopologicalSpace F]

/-- A continuous alternating map in more variables than the dimension of its domain is zero. -/
theorem eq_zero_of_finrank_lt [Module.Finite K E] [Fintype ι] (f : E [⋀^ι]→L[K] F)
    (h : Module.finrank K E < Fintype.card ι) : f = 0 := by
  ext v
  exact f.toAlternatingMap.map_linearDependent v fun hv ↦ hv.fintype_card_le_finrank.not_gt h

end AboveTopDegree

end ContinuousAlternatingMap
