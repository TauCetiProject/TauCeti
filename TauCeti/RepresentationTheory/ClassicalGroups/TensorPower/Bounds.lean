/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Kronecker.OperatorNorm
public import TauCeti.RepresentationTheory.ClassicalGroups.TensorPower.Form

/-!
# Bounds for the standard Hermitian form on tensor powers

Applying a matrix to every factor of a tensor of degree `d` increases its squared length by at
most the `2d`-th power of the matrix's Euclidean operator norm. The bound holds for all tensors,
not only pure tensors, and for singular matrices as well.
-/

public section

open Matrix
open scoped Matrix.Norms.L2Operator TensorProduct

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {n d : ℕ}

/-- The squared length for the standard Hermitian form is the sum of squared coordinate norms
in the monomial basis. -/
theorem re_tensorPowerForm_apply_self (x : ⨂[𝕜]^d (Fin n → 𝕜)) :
    RCLike.re (tensorPowerForm n d x x) = ∑ w, ‖(tensorPowerBasis 𝕜 n d).repr x w‖ ^ 2 := by
  rw [tensorPowerForm_apply, ← RCLike.reLm_coe, map_sum]
  simp only [RCLike.reLm_coe, RCLike.star_def, RCLike.conj_mul, RCLike.re_ofReal_pow]

/-- Applying `A` in every tensor factor increases squared length by at most `‖A‖^(2*d)`. -/
theorem re_tensorPowerForm_map_apply_self_le (A : Matrix (Fin n) (Fin n) 𝕜)
    (x : ⨂[𝕜]^d (Fin n → 𝕜)) :
    let y := PiTensorProduct.map (fun _ : Fin d ↦ A.mulVecLin) x
    RCLike.re (tensorPowerForm n d y y) ≤ ‖A‖ ^ (2 * d) * RCLike.re (tensorPowerForm n d x x) := by
  dsimp only
  have hrepr := LinearMap.toMatrix_mulVec_repr (tensorPowerBasis 𝕜 n d) (tensorPowerBasis 𝕜 n d)
    (PiTensorProduct.map (fun _ : Fin d ↦ A.mulVecLin)) x
  rw [A.toMatrix_piTensorProductMap_tensorPowerBasis] at hrepr
  simp only [re_tensorPowerForm_apply_self, ← hrepr]
  refine ((A.kroneckerPower (Fin d)).sum_norm_sq_mulVec_le
    ((tensorPowerBasis 𝕜 n d).repr x)).trans ?_
  rw [mul_comm 2, pow_mul]
  gcongr
  simpa only [Fintype.card_fin] using A.l2_opNorm_kroneckerPower_le (κ := Fin d)

end TauCeti
