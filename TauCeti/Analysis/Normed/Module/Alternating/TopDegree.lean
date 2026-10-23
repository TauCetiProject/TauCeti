/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Scalar coordinates for top-degree forms

Evaluation on a basis identifies top-degree continuous alternating scalar forms with the
scalar field, as a continuous linear equivalence. Its inverse multiplies the determinant form
of that basis. This gives scalar coordinates for top-degree test forms without choosing an
inner product or restricting to positive dimension.

The algebraic input is Mathlib's `AlternatingMap.eq_smul_basis_det`, through
`ContinuousAlternatingMap.apply_eq_det_mul`.
-/

public section

namespace TauCeti

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Fintype ι] [DecidableEq ι]

/-- Evaluation on a basis is a continuous linear equivalence from top-degree forms to scalars.
The inverse sends `c` to `c` times the determinant form of the basis. -/
noncomputable def _root_.Module.Basis.topFormEquiv (b : Module.Basis ι 𝕜 E) :
    (E [⋀^ι]→L[𝕜] 𝕜) ≃L[𝕜] 𝕜 := by
  let δ : E [⋀^ι]→L[𝕜] 𝕜 :=
    { b.det with
      cont := by
        convert b.continuous_toMatrix.matrix_det using 1
        exact funext b.det_apply }
  have hδ (v : ι → E) : δ v = b.det v := by rfl
  exact
    { toLinearEquiv :=
        { toFun := fun ω ↦ ω b
          invFun := fun c ↦ c • δ
          left_inv := by
            intro ω
            ext v
            simpa only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, hδ, mul_comm] using
              (ω.apply_eq_det_mul b v).symm
          right_inv := by intro c; simp [hδ, Module.Basis.det_self]
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      continuous_toFun := (ContinuousAlternatingMap.apply 𝕜 E 𝕜 b).continuous
      continuous_invFun := continuous_id.smul continuous_const }

@[simp]
theorem _root_.Module.Basis.topFormEquiv_apply (b : Module.Basis ι 𝕜 E)
    (ω : E [⋀^ι]→L[𝕜] 𝕜) : b.topFormEquiv ω = ω b := by rfl

@[simp]
theorem _root_.Module.Basis.topFormEquiv_symm_apply (b : Module.Basis ι 𝕜 E)
    (c : 𝕜) (v : ι → E) : b.topFormEquiv.symm c v = c * b.det v := by rfl

end TauCeti
