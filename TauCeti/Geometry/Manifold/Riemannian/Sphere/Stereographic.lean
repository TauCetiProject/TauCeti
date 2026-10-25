/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The round metric in stereographic coordinates

Let `v` be a unit vector of a real inner product space `E` of dimension `n + 1`. Mathlib's
stereographic projection `stereographic' n v` from `v` is a chart of the unit sphere `Sⁿ` with
values in `ℝⁿ`; it projects onto the hyperplane orthogonal to `v` through `-v`, so its inverse is

`σ⁻¹(w) = (‖w‖² + 4)⁻¹ (4 w + (‖w‖² - 4) v)`

(`stereoInvFunAux`), up to the linear isometry of `(ℝ ∙ v)ᗮ` with `ℝⁿ` used by
`stereographic'`. This file proves that `σ⁻¹` is conformal, and computes its conformal factor:
for `w`, `a`, `b` orthogonal to `v`,

`⟪dσ⁻¹_w a, dσ⁻¹_w b⟫ = (4 / (‖w‖² + 4))² ⟪a, b⟫`.

Equivalently, the round metric of the sphere (`TauCeti.sphereRoundMetric`) reads in the
stereographic chart as `(4 / (‖y‖² + 4))²` times the Euclidean metric of `ℝⁿ`. For the more common
projection onto the equatorial hyperplane, which is `y ↦ σ⁻¹(2 y)`, the factor is the familiar
`(2 / (1 + ‖y‖²))²`.

## Main results

* `TauCeti.fderiv_stereoInvFunAux_apply`: the differential of `σ⁻¹`.
* `TauCeti.inner_fderiv_stereoInvFunAux`: the conformal factor of `σ⁻¹` on the hyperplane
  orthogonal to `v`.
* `TauCeti.inner_mfderiv_stereographic'_symm`: the round metric pulled back along the inverse of
  the stereographic chart `stereographic' n v`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  (stereographic coordinates on the round sphere).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 3.
-/

public section

open Bundle Metric Module
open scoped InnerProductSpace Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {v : E}

/-- The differential at `w` of the inverse `stereoInvFunAux v` of stereographic projection, which
is `w ↦ (‖w‖² + 4)⁻¹ (4 w + (‖w‖² - 4) v)`. -/
theorem fderiv_stereoInvFunAux_apply (v w a : E) :
    fderiv ℝ (stereoInvFunAux v) w a =
      (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • a + (2 * ⟪w, a⟫_ℝ) • v) -
        (2 * ⟪w, a⟫_ℝ / (‖w‖ ^ 2 + 4) ^ 2) • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v) := by
  have hs : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  have hn := (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h := ((hasDerivAt_inv hs).comp_hasFDerivAt w (hn.add_const 4)).smul
    (((hasFDerivAt_id w).const_smul (4 : ℝ)).add ((hn.sub_const 4).smul_const v))
  rw [(h.congr_of_eventuallyEq (.of_forall fun _ ↦ rfl) :
    HasFDerivAt (stereoInvFunAux v) _ w).fderiv]
  simp only [Function.comp_apply, smul_add, neg_smul, Pi.add_apply, Pi.smul_apply, id_eq,
    add_apply, smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    coe_innerSL_apply, nsmul_eq_mul, Nat.cast_ofNat, neg_apply, smul_eq_mul]
  module

/-- **Inverse stereographic projection is conformal.** For a unit vector `v` and vectors `w`, `a`,
`b` orthogonal to `v`, the differential of `σ⁻¹ = stereoInvFunAux v` at `w` satisfies
`⟪dσ⁻¹_w a, dσ⁻¹_w b⟫ = (4 / (‖w‖² + 4))² ⟪a, b⟫`. -/
theorem inner_fderiv_stereoInvFunAux (hv : ‖v‖ = 1) {w a b : E} (hw : w ∈ (ℝ ∙ v)ᗮ)
    (ha : a ∈ (ℝ ∙ v)ᗮ) (hb : b ∈ (ℝ ∙ v)ᗮ) :
    ⟪fderiv ℝ (stereoInvFunAux v) w a, fderiv ℝ (stereoInvFunAux v) w b⟫_ℝ =
      (4 / (‖w‖ ^ 2 + 4)) ^ 2 * ⟪a, b⟫_ℝ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hw ha hb
  have hs : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  rw [fderiv_stereoInvFunAux_apply, fderiv_stereoInvFunAux_apply]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hv,
    real_inner_comm v, real_inner_comm w a, hw, ha, hb]
  field_simp
  ring

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- **The round metric in stereographic coordinates.** Pulled back along the inverse of the
stereographic chart `stereographic' n v` of the unit sphere, the round metric is
`(4 / (‖y‖² + 4))²` times the Euclidean metric of `ℝⁿ` at `y`. -/
theorem inner_mfderiv_stereographic'_symm (v : sphere (0 : E) 1)
    (y a b : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm y a)
        (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm y b) =
      (4 / (‖y‖ ^ 2 + 4)) ^ 2 * inner ℝ a b := by
  set U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere v)).repr
  have hsymm : MDifferentiableAt (𝓡 n) (𝓡 n) (stereographic' n v).symm y :=
    mdifferentiableAt_atlas_symm (e := stereographic' n v) (Exists.intro v rfl) (by simp)
  -- Read in `E`, the inverse chart is `σ⁻¹` precomposed with the isometry `U.symm`.
  have hfun : ((↑) : sphere (0 : E) 1 → E) ∘ (stereographic' n v).symm =
      stereoInvFunAux (v : E) ∘ ((↑) : (ℝ ∙ (v : E))ᗮ → E) ∘ U.symm := by
    funext y
    simp [stereographic'_symm_apply, smul_add, U]
  have hd (c : TangentSpace (𝓡 n) y) :
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) _
          (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm y c) =
        fderiv ℝ (stereoInvFunAux (v : E)) (U.symm y) (U.symm c) := by
    rw [← mvfderiv_comp_apply y ((contMDiff_coe_sphere _).mdifferentiableAt one_ne_zero) hsymm,
      hfun, mvfderiv_eq_fderiv]
    have hL : HasFDerivAt (((↑) : (ℝ ∙ (v : E))ᗮ → E) ∘ U.symm)
        ((ℝ ∙ (v : E))ᗮ.subtypeL.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap) y :=
      ((ℝ ∙ (v : E))ᗮ.subtypeL.comp
        U.symm.toContinuousLinearEquiv.toContinuousLinearMap).hasFDerivAt
    rw [(((contDiff_stereoInvFunAux (m := 1)).differentiable one_ne_zero _).hasFDerivAt.comp y
      hL).fderiv]
    -- `NormedSpace.fromTangentSpace y` is the identity of the model space, by definition.
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, Submodule.subtypeL_apply]
    rfl
  rw [inner_tangentSpace_sphere, hd a, hd b,
    inner_fderiv_stereoInvFunAux (norm_eq_of_mem_sphere v) (U.symm y).2 (U.symm a).2 (U.symm b).2,
    Submodule.norm_coe, LinearIsometryEquiv.norm_map, ← Submodule.coe_inner,
    LinearIsometryEquiv.inner_map_map]

end TauCeti
