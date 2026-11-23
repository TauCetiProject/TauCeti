/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Orientation

/-!
# Regular and critical levels of functions on the real line

Two functions on `ℝ` test the regular-level and boundary-face API of
`TauCeti.Geometry.Manifold.RegularValue.Scalar`.

**The coordinate on an interval.** Every value of the coordinate function `x ↦ x` is regular
(`TauCeti.isRegularValue_id`), so for `a < b` the band `[a, b]` carries the atlas
`TauCeti.scalarRegularBandChartedSpace`. Orient `ℝ` by its standard orientation
`TauCeti.Manifold.Orientation.real`, the band by the induced orientation and its boundary
`{a, b}` by the outward-first orientation `TauCeti.boundaryOrientation`. Then the outgoing
endpoint `b` is positively oriented
(`TauCeti.orientationAt_boundaryOrientation_scalarRegularBand_id_of_eq_right`) and the incoming
endpoint `a` negatively oriented
(`TauCeti.orientationAt_boundaryOrientation_scalarRegularBand_id_of_eq_left`). The derivative of
the coordinate is positive on the outward vectors at `b` and negative on those at `a`, and the
signs agree with those of the closed interval `Icc a b` with its own atlas
(`TauCeti.orientationAt_boundaryOrientation_interval_right` and
`TauCeti.orientationAt_boundaryOrientation_interval_left`).

**The square at its minimum.** The derivative of `x ↦ x²` vanishes at `0`, so `0` is not a
regular value (`TauCeti.not_isRegularValue_sq_zero`). Its level is the single point `0`, and the
conclusion of the regular-level theorem fails there for every atlas of the expected dimension
`1 - 1 = 0`: the derivative of the inclusion of a zero-dimensional manifold has range `0`, while the
kernel of the derivative of `x²` at `0` is all of `ℝ`
(`TauCeti.range_mfderiv_coe_ne_ker_mfderiv_sq`).
-/

public section

open Set Module
open scoped Manifold

namespace TauCeti

/-! ### The band of the coordinate function -/

section Band

variable {a b : ℝ} (hab : a < b)

/-- **The outgoing endpoint of an interval is positively oriented.** Orient the band `[a, b]` of
the coordinate function on `ℝ` by the standard orientation of `ℝ`, and its boundary by the
outward-first orientation. Then the endpoint `b` is positively oriented. -/
theorem orientationAt_boundaryOrientation_scalarRegularBand_id_of_eq_right :
    letI := scalarRegularBandChartedSpace contMDiff_id (finrank_self ℝ)
      (isRegularValue_id a) (isRegularValue_id b) hab
    letI := isManifold_scalarRegularBand (finrank_self ℝ)
      (isRegularValue_id a) (isRegularValue_id b) le_rfl contMDiff_id hab
    letI := isManifold_boundary (n := 0) (k := 1) ((id : ℝ → ℝ) ⁻¹' Icc a b)
    ∀ x : (𝓡∂ (0 + 1)).boundary ((id : ℝ → ℝ) ⁻¹' Icc a b), (x : ℝ) = b →
      (boundaryOrientation (n := 0) (Manifold.Orientation.real.scalarRegularBand contMDiff_id
          (finrank_self ℝ) (isRegularValue_id a) (isRegularValue_id b)
          hab)).orientationAt x =
        (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.orientation := by
  intro x hx
  let e := NormedSpace.fromTangentSpace (𝕜 := ℝ) (x : ℝ)
  -- The unit vector `1` points out of the band at `b`, and as a basis of the tangent line of `ℝ`
  -- it is positively oriented.
  refine ((boundaryOrientation_scalarRegularBand_spec_of_eq_right _ _ _ _ _ hab x hx
    (v := e.symm 1) ?_ (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis
    ((Basis.singleton (Fin 1) ℝ).map e.symm.toLinearEquiv) ?_).2
      (Manifold.Orientation.orientation_map_fromTangentSpace_symm_singleton _)).symm
  · simp [e]
  · funext i
    rw [Fin.fin_one_eq_zero i]
    simp [e]

/-- **The incoming endpoint of an interval is negatively oriented.** Orient the band `[a, b]` of
the coordinate function on `ℝ` by the standard orientation of `ℝ`, and its boundary by the
outward-first orientation. Then the endpoint `a` is negatively oriented. -/
theorem orientationAt_boundaryOrientation_scalarRegularBand_id_of_eq_left :
    letI := scalarRegularBandChartedSpace contMDiff_id (finrank_self ℝ)
      (isRegularValue_id a) (isRegularValue_id b) hab
    letI := isManifold_scalarRegularBand (finrank_self ℝ)
      (isRegularValue_id a) (isRegularValue_id b) le_rfl contMDiff_id hab
    letI := isManifold_boundary (n := 0) (k := 1) ((id : ℝ → ℝ) ⁻¹' Icc a b)
    ∀ x : (𝓡∂ (0 + 1)).boundary ((id : ℝ → ℝ) ⁻¹' Icc a b), (x : ℝ) = a →
      (boundaryOrientation (n := 0) (Manifold.Orientation.real.scalarRegularBand contMDiff_id
          (finrank_self ℝ) (isRegularValue_id a) (isRegularValue_id b)
          hab)).orientationAt x =
        -(EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.orientation := by
  intro x hx
  let e := NormedSpace.fromTangentSpace (𝕜 := ℝ) (x : ℝ)
  -- The vector `-1` points out of the band at `a`, and as a basis of the tangent line of `ℝ` it is
  -- negatively oriented.
  let e' := ((Basis.singleton (Fin 1) ℝ).map e.symm.toLinearEquiv).unitsSMul
    (Function.update (1 : Fin 1 → ℝˣ) 0 (-1))
  have hspec := boundaryOrientation_scalarRegularBand_spec_of_eq_left
    Manifold.Orientation.real contMDiff_id (finrank_self ℝ) (isRegularValue_id a)
    (isRegularValue_id b) hab x hx (v := -e.symm 1) (by simp [e])
    (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis e' (by
      funext i
      rw [Fin.fin_one_eq_zero i]
      simp [e', e, Basis.unitsSMul_apply])
  rw [Basis.orientation_neg_single,
    Manifold.Orientation.orientation_map_fromTangentSpace_symm_singleton] at hspec
  refine (Basis.orientation_ne_iff_eq_neg _ _).1 fun h ↦ ?_
  exact Module.Ray.ne_neg_self _ (hspec.1 h.symm).symm

end Band

/-! ### The square at its critical level -/

section Square

/-- The derivative of `x ↦ x²` vanishes at `0`, so `0` is not a regular value. -/
theorem not_isRegularValue_sq_zero : ¬IsRegularValue 𝓘(ℝ) 𝓘(ℝ) (fun x : ℝ ↦ x ^ 2) 0 := by
  rw [isRegularValue_iff_notMem_image_criticalPoints, criticalPoints_pow le_rfl]
  simp

/-- **The square has no regular level at `0`.** For every atlas on the level `{x | x² = 0}` of the
expected dimension `1 - 1 = 0`, the derivative of the inclusion into `ℝ` does not have range the
kernel of the derivative of `x²`: the range is `0`, and the kernel is all of `ℝ`. -/
theorem range_mfderiv_coe_ne_ker_mfderiv_sq (c : ChartedSpace (Fin 0 → ℝ) {x : ℝ // x ^ 2 = 0})
    (x : {x : ℝ // x ^ 2 = 0}) :
    (mfderiv 𝓘(ℝ, Fin 0 → ℝ) 𝓘(ℝ) (Subtype.val : {x : ℝ // x ^ 2 = 0} → ℝ) x).range ≠
      (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun y : ℝ ↦ y ^ 2) x).ker := by
  have : Subsingleton (TangentSpace 𝓘(ℝ, Fin 0 → ℝ) x) :=
    inferInstanceAs (Subsingleton (Fin 0 → ℝ))
  have hx : (x : ℝ) = 0 := pow_eq_zero_iff two_ne_zero |>.1 x.property
  have hd : mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun y : ℝ ↦ y ^ 2) x = 0 :=
    mem_criticalPoints_iff_mfderiv_eq_zero.1 (by simp [criticalPoints_pow le_rfl, hx])
  rw [hd, Subsingleton.elim (mfderiv _ _ _ x) 0]
  simp only [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, LinearMap.ker_zero]
  exact (bot_ne_top : (⊥ : Submodule ℝ ℝ) ≠ ⊤)

end Square

end TauCeti
