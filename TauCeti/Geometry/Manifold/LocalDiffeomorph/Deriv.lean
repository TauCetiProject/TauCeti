/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Local diffeomorphisms of the scalar field

A `C^n` function `g : 𝕂 → 𝕂`, `1 ≤ n`, whose derivative vanishes nowhere is a `C^n` local
diffeomorphism of `𝕂` (`TauCeti.isLocalDiffeomorph_of_deriv_ne_zero`): its differential at each
point is multiplication by the nonzero number `deriv g x`, so the inverse function theorem for
manifolds (`TauCeti.isLocalDiffeomorph_of_mfderiv_eq`) applies. The logistic sigmoid, a
diffeomorphism of `ℝ` onto `(0, 1)`, is an example.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕂 : Type*} [RCLike 𝕂] {n : WithTop ℕ∞}

/-- **The inverse function theorem in one variable**: a `C^n` function `𝕂 → 𝕂`, `1 ≤ n`, whose
derivative vanishes nowhere is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_of_deriv_ne_zero {g : 𝕂 → 𝕂} (hg : ContDiff 𝕂 n g) (hn : 1 ≤ n)
    (hg' : ∀ x, deriv g x ≠ 0) : IsLocalDiffeomorph 𝓘(𝕂) 𝓘(𝕂) n g := by
  refine isLocalDiffeomorph_of_mfderiv_eq hg.contMDiff hn fun y =>
    ⟨ContinuousLinearEquiv.unitsEquivAut 𝕂 (Units.mk0 _ (hg' y)), ?_⟩
  -- The differential is multiplication by `deriv g y`, computed on `𝕂` rather than on the
  -- tangent spaces, which are only definitionally `𝕂`.
  have key : ((ContinuousLinearEquiv.unitsEquivAut 𝕂 (Units.mk0 _ (hg' y)) : 𝕂 →L[𝕂] 𝕂) :
      TangentSpace 𝓘(𝕂) y →L[𝕂] TangentSpace 𝓘(𝕂) (g y)) = mfderiv 𝓘(𝕂) 𝓘(𝕂) g y := by
    rw [(hg.differentiable (zero_lt_one.trans_le hn).ne' y).hasFDerivAt.hasMFDerivAt.mfderiv]
    refine ContinuousLinearMap.ext_ring ?_
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquivAut_apply, one_mul,
      Units.val_mk0, fderiv_apply_one_eq_deriv]
  exact key

/-- The logistic sigmoid `x ↦ 1 / (1 + exp (-x))` is a `C^n` local diffeomorphism of `ℝ` for every
`n ≥ 1`. -/
theorem isLocalDiffeomorph_sigmoid (hn : 1 ≤ n) :
    IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) n Real.sigmoid := by
  refine isLocalDiffeomorph_of_deriv_ne_zero (contDiff_sigmoid.of_le le_top) hn fun x => ?_
  rw [Real.deriv_sigmoid]
  exact mul_ne_zero (Real.sigmoid_pos x).ne' (sub_ne_zero.2 (Real.sigmoid_lt_one x).ne')

end TauCeti
