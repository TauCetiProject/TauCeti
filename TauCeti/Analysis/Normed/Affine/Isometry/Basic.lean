/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Affine isometries

For a scalar `c` and an affine isometry `e : V ≃ᵃⁱ[𝕜] V₂` between normed spaces, the affine
isometry `TauCeti.dilateConj c e` has the linear part of `e` and translation part `c • e 0`. For
`c ≠ 0` it is the conjugate `y ↦ c • e (c⁻¹ • y)` of `e` by the dilations by `c`.

The derivative of an affine isometry equivalence has norm at most one.

## Main declarations

* `TauCeti.dilateConj`: the dilation conjugate of an affine isometry.
* `TauCeti.dilateConj_smul`: `dilateConj c e (c • y) = c • e y`.
* `TauCeti.dilateConj_symm_apply`: the inverse of `dilateConj c e`, written out pointwise.
* `AffineIsometryEquiv.norm_fderiv_le`: the derivative of an affine isometry equivalence has norm
  at most one.
-/

public section

noncomputable section

namespace AffineIsometryEquiv

/-- The Fréchet derivative of an affine isometry equivalence has norm at most one. -/
theorem norm_fderiv_le {𝕜 W W₂ : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedAddCommGroup W₂] [NormedSpace 𝕜 W₂]
    (e : W ≃ᵃⁱ[𝕜] W₂) (x : W) : ‖fderiv 𝕜 e x‖ ≤ 1 := by
  simpa using norm_fderiv_le_of_lipschitz 𝕜 e.lipschitzWith (x₀ := x)

end AffineIsometryEquiv

namespace TauCeti

variable {𝕜 V V₂ : Type*} [NormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₂]

/-- The affine isometry with the linear part of `e` and translation part `c • e 0`. For `c ≠ 0`
it is the conjugate `y ↦ c • e (c⁻¹ • y)` of `e` by the dilation by `c`; for `c = 0` it is the
linear part of `e`. -/
def dilateConj (c : 𝕜) (e : V ≃ᵃⁱ[𝕜] V₂) : V ≃ᵃⁱ[𝕜] V₂ :=
  e.linearIsometryEquiv.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd 𝕜 V₂ (c • e 0))

/-- The dilation conjugate of `e` sends `c • y` to `c • e y`. -/
@[simp]
theorem dilateConj_smul (c : 𝕜) (e : V ≃ᵃⁱ[𝕜] V₂) (y : V) :
    dilateConj c e (c • y) = c • e y := by
  have he : e y = e.linearIsometryEquiv y + e 0 := by simpa using e.map_vadd 0 y
  simp [dilateConj, he, smul_add, add_comm]

/-- The inverse of the dilation conjugate of `e` by `c ≠ 0` is the dilation conjugate of
`e.symm`, written out pointwise. -/
theorem dilateConj_symm_apply {c : 𝕜} (hc : c ≠ 0) (e : V ≃ᵃⁱ[𝕜] V₂) (z : V₂) :
    (dilateConj c e).symm z = c • e.symm (c⁻¹ • z) := by
  rw [AffineIsometryEquiv.symm_apply_eq, dilateConj_smul, AffineIsometryEquiv.apply_symm_apply,
    smul_inv_smul₀ hc]

end TauCeti
