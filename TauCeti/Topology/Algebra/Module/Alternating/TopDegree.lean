/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Algebra.Module.Alternating.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Top-degree continuous alternating forms

Top-degree scalar-valued continuous alternating forms over a commutative ring are determined
by their basis coefficient. Pullback by a continuous linear endomorphism multiplies that
coefficient by its determinant. Above the top degree, continuous alternating maps on a
finite-dimensional space over a division ring vanish. No compatibility between the topology and
the module structure is required for those statements.

Over a complete nontrivially normed field, evaluation on a basis identifies the space of
top-degree forms with the scalar field as a continuous linear equivalence. Its inverse
multiplies the continuous determinant form of that basis. This construction needs only a
Hausdorff topological vector space, with no choice of norm or inner product.
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

namespace TauCeti

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [T2Space E] [ContinuousSMul 𝕜 E]
  [Fintype ι] [DecidableEq ι]

/-- The determinant form of a basis as a continuous alternating map. -/
noncomputable def _root_.Module.Basis.continuousDet (b : Module.Basis ι 𝕜 E) :
    E [⋀^ι]→L[𝕜] 𝕜 :=
  { b.det with
    cont := by
      convert b.continuous_toMatrix.matrix_det using 1
      exact funext b.det_apply }

@[simp]
theorem _root_.Module.Basis.continuousDet_apply (b : Module.Basis ι 𝕜 E) (v : ι → E) :
    b.continuousDet v = b.det v := by rfl

@[simp]
theorem _root_.Module.Basis.continuousDet_toAlternatingMap (b : Module.Basis ι 𝕜 E) :
    b.continuousDet.toAlternatingMap = b.det := by rfl

/-- Evaluation on a basis is a continuous linear equivalence from top-degree forms to scalars.
The inverse sends `c` to `c` times the determinant form of the basis. -/
noncomputable def _root_.Module.Basis.topFormEquiv (b : Module.Basis ι 𝕜 E) :
    (E [⋀^ι]→L[𝕜] 𝕜) ≃L[𝕜] 𝕜 where
  toLinearEquiv :=
    { toFun := fun ω ↦ ω b
      invFun := fun c ↦ c • b.continuousDet
      left_inv := by
        intro ω
        ext v
        simpa only [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
          Module.Basis.continuousDet_apply, mul_comm] using (ω.apply_eq_det_mul b v).symm
      right_inv := by intro c; simp [Module.Basis.det_self]
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  continuous_toFun := (ContinuousAlternatingMap.apply 𝕜 E 𝕜 b).continuous
  continuous_invFun := continuous_id.smul continuous_const

@[simp]
theorem _root_.Module.Basis.topFormEquiv_apply (b : Module.Basis ι 𝕜 E)
    (ω : E [⋀^ι]→L[𝕜] 𝕜) : b.topFormEquiv ω = ω b := by rfl

/-- The inverse scalar coordinate map multiplies the continuous determinant form. -/
theorem _root_.Module.Basis.topFormEquiv_symm_eq_smul (b : Module.Basis ι 𝕜 E) (c : 𝕜) :
    b.topFormEquiv.symm c = c • b.continuousDet := by rfl

@[simp]
theorem _root_.Module.Basis.topFormEquiv_symm_apply (b : Module.Basis ι 𝕜 E)
    (c : 𝕜) (v : ι → E) : b.topFormEquiv.symm c v = c * b.det v := by
  simp [Module.Basis.topFormEquiv_symm_eq_smul]

end TauCeti
