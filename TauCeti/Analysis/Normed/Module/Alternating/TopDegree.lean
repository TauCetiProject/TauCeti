/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Alternating.Topology
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# Scalar coordinates for top-degree continuous alternating forms

Over a complete nontrivially normed field, evaluation on a basis identifies the space of
top-degree forms with the scalar field as a continuous linear equivalence. Its inverse
multiplies the continuous determinant form of that basis. This construction needs only a
Hausdorff topological vector space, with no choice of norm or inner product.
-/

public section

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
