/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangyang Li
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Paraboloid.SecondFundamentalForm
public import TauCeti.Analysis.InnerProductSpace.Normalize

/-!
# The upward unit normal of the paraboloid

Normalize the Cartesian graph normal and show that the resulting field is a smooth unit
normal at every point, including the vertex.

Adapted from Yangyang Li's formalization in ColdingMinicozziTheory,
[commit 234e55b3](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/234e55b3).
-/

public noncomputable section

open scoped ContDiff InnerProductSpace

namespace TauCeti.Manifold

local notation "V₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The upward unit normal to the Cartesian paraboloid. -/
def paraboloidUnitNormal (x : V₂) : E₃ :=
  NormedSpace.normalize (paraboloidNormal x)

/-- The explicit expression for the upward unit normal. -/
theorem paraboloidUnitNormal_apply (x : V₂) :
    paraboloidUnitNormal x = (√(1 + 4 * ‖x‖ ^ 2))⁻¹ • paraboloidNormal x := by
  have hn : ‖paraboloidNormal x‖ = √(1 + 4 * ‖x‖ ^ 2) := by
    rw [← norm_paraboloidNormal_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [paraboloidUnitNormal, NormedSpace.normalize, hn]

/-- The upward Cartesian unit normal has length one. -/
@[simp]
theorem norm_paraboloidUnitNormal (x : V₂) : ‖paraboloidUnitNormal x‖ = 1 :=
  NormedSpace.norm_normalize (paraboloidNormal_ne_zero x)

/-- The upward unit normal is orthogonal to the differential of the graph. -/
@[simp]
theorem inner_paraboloidUnitNormal_fderiv_paraboloidGraph (x w : V₂) :
    ⟪paraboloidUnitNormal x, fderiv ℝ paraboloidGraph x w⟫_ℝ = 0 := by
  simp [paraboloidUnitNormal, NormedSpace.normalize, real_inner_smul_left]

/-- The upward unit normal is smooth in the Cartesian coordinates. -/
theorem contDiff_paraboloidUnitNormal : ContDiff ℝ ∞ paraboloidUnitNormal := by
  have hnormal : ContDiff ℝ ∞ paraboloidNormal := by
    have h : paraboloidNormal = fun x ↦
        (-2 * x 0) • EuclideanSpace.basisFun (Fin 3) ℝ 0 +
        (-2 * x 1) • EuclideanSpace.basisFun (Fin 3) ℝ 1 +
        EuclideanSpace.basisFun (Fin 3) ℝ 2 := by
      funext x
      ext i
      fin_cases i <;> simp [EuclideanSpace.basisFun_apply]
    rw [h]
    have hp (i : Fin 2) : ContDiff ℝ ∞ (fun x : V₂ ↦ x i) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).contDiff
    exact (((contDiff_const.mul (hp 0)).smul contDiff_const).add
      ((contDiff_const.mul (hp 1)).smul contDiff_const)).add contDiff_const
  exact contDiff_iff_contDiffAt.2 fun x ↦
    (NormedSpace.contDiffAt_normalize (paraboloidNormal_ne_zero x)).comp x hnormal.contDiffAt

end TauCeti.Manifold
