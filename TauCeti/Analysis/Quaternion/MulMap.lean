/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Topology.Algebra.Module.Determinant
import TauCeti.Algebra.Quaternion.MulMatrix
import TauCeti.Analysis.Normed.Operator.Mul

/-!
# Determinants of bounded quaternion multiplication

For a quaternion `a`, left multiplication `L_a = ContinuousLinearMap.mul ℝ ℍ a` and right
multiplication `R_a = (ContinuousLinearMap.mul ℝ ℍ).flip a` are the real-linear maps
`q ↦ a * q` and `q ↦ q * a` of the four-dimensional real space `ℍ`; they are the real Fréchet
derivatives of functions with a right, respectively left, quotient derivative. Both have
determinant `‖a‖ ^ 4`, the square of `normSq a = ‖a‖ ^ 2`: this is the Jacobian of the linear
changes of variables `q ↦ a * q` and `q ↦ q * a` of `ℍ`, nonnegative for every `a`.

The remaining identities for these maps hold in every normed algebra and are stated there:
the composition rules `L_{ab} = L_a ∘ L_b` and `R_{ab} = R_b ∘ R_a`
(`ContinuousLinearMap.mul_apply_mul`, `ContinuousLinearMap.flip_mul_apply_mul`), the commutation
of `L_a` with `R_b` (`ContinuousLinearMap.commute_mul_apply_flip_mul_apply`), the inverses
`L_a⁻¹ = L_{a⁻¹}` and `R_a⁻¹ = R_{a⁻¹}` (`ContinuousLinearMap.inverse_mul_apply`,
`ContinuousLinearMap.inverse_flip_mul_apply`), and the operator norms `‖L_a‖ = ‖R_a‖ = ‖a‖`
(`ContinuousLinearMap.opNorm_mul_apply`,
`ContinuousLinearMap.opNorm_mul_flip_apply_of_normOneClass`; since `ℍ` is also a C⋆-ring,
Mathlib's `ContinuousLinearMap.opNorm_mul_flip_apply` gives the latter too). Pointwise,
`‖a * q‖ = ‖a‖ * ‖q‖` and `‖q * a‖ = ‖q‖ * ‖a‖` are `norm_mul`.

## Main results

* `Quaternion.det_mul_apply`: `det L_a = ‖a‖ ^ 4`.
* `Quaternion.det_flip_mul_apply`: `det R_a = ‖a‖ ^ 4`.

## References

* Igor Frenkel and Matvei Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.1, for the multiplicativity of the norm.
-/

public section

open scoped Quaternion

namespace Quaternion

/-- The determinant of the real-linear map `q ↦ a * q` of `ℍ` is `‖a‖ ^ 4`. -/
theorem det_mul_apply (a : ℍ) : (ContinuousLinearMap.mul ℝ ℍ a).det = ‖a‖ ^ 4 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_mul_eq_mulLeft, det_mulLeft,
    normSq_eq_norm_mul_self]
  ring

/-- The determinant of the real-linear map `q ↦ q * a` of `ℍ` is `‖a‖ ^ 4`. -/
theorem det_flip_mul_apply (a : ℍ) : ((ContinuousLinearMap.mul ℝ ℍ).flip a).det = ‖a‖ ^ 4 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_flip_mul_eq_mulRight, det_mulRight,
    normSq_eq_norm_mul_self]
  ring

end Quaternion
