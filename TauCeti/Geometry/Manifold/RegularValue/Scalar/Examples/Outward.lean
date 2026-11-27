/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Examples.Sphere
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Outward

/-!
# The outward criterion on the closed unit ball and on a half-space

A regular domain `{ρ ≥ 0}` is the regular sublevel `{φ ≤ 0}` of `φ = -ρ`, and a tangent vector at
a boundary point points outward exactly when `dφ(dj v) > 0`
(`TauCeti.isOutwardPointing_scalarRegularSublevel_iff_mfderiv`). Two examples fix the sign.

* **The closed unit ball** `{‖x‖² ≤ 1}` in a real inner product space of dimension `n + 1`, the
  sublevel of `‖x‖²` at the regular value `1`, that is `φ = ‖x‖² - 1`: at a point `x` of the unit
  sphere, `dφ(w) = 2 ⟪x, w⟫`, so `v` points outward iff
  `⟪x, dj v⟫ > 0` (`TauCeti.isOutwardPointing_normSqSublevel_iff`). The vector over the radius `x`
  points outward and the one over `-x` does not
  (`TauCeti.isOutwardPointing_normSqSublevel_of_mfderiv_eq_self`,
  `TauCeti.not_isOutwardPointing_normSqSublevel_of_mfderiv_eq_neg_self`).
* **The half-space** `{x₀ ≥ 0}` in `ℝⁿ⁺¹`, with `ρ = x₀` and `φ = -x₀`: `v` points outward iff
  `(dj v)₀ < 0` (`TauCeti.isOutwardPointing_halfSpaceSublevel_iff`), so the vector over `-e₀`
  points outward and the one over `e₀` does not
  (`TauCeti.isOutwardPointing_halfSpaceSublevel_of_mfderiv_eq_neg_single`,
  `TauCeti.not_isOutwardPointing_halfSpaceSublevel_of_mfderiv_eq_single`).

Reading the criterion with `ρ` in place of `φ` would make the radius inward on the sphere and `e₀`
outward on the half-space.
-/

public section

open Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

section Ball

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (finrank ℝ E = n + 1)]

attribute [local instance] normSqSublevelChartedSpace

/-- **The outward criterion on the closed unit ball.** At a point `x` of the unit sphere, a tangent
vector `v` of the closed unit ball `{‖x‖² ≤ 1}`, with its sublevel atlas, points outward iff
`⟪x, dj v⟫ > 0`, where `j` is the inclusion. -/
theorem isOutwardPointing_normSqSublevel_iff {x : {x : E | ‖x‖ ^ 2 ≤ 1}}
    (hx : ‖(x : E)‖ ^ 2 = 1) (v : TangentSpace (𝓡∂ (n + 1)) x) :
    IsOutwardPointing x v ↔
      0 < ⟪(x : E),
        mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | ‖x‖ ^ 2 ≤ 1} → E) x v⟫ := by
  rw [isOutwardPointing_scalarRegularSublevel_iff_mfderiv _ Fact.out _ hx, mvfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply, fderiv_norm_sq_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, nsmul_eq_mul,
    Nat.cast_ofNat, NormedSpace.fromTangentSpace]
  exact ⟨fun h ↦ pos_of_mul_pos_right h zero_le_two, fun h ↦ mul_pos zero_lt_two h⟩

/-- On the closed unit ball, the tangent vector over the radius `x` at a point `x` of the unit
sphere points outward. -/
theorem isOutwardPointing_normSqSublevel_of_mfderiv_eq_self {x : {x : E | ‖x‖ ^ 2 ≤ 1}}
    (hx : ‖(x : E)‖ ^ 2 = 1) {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | ‖x‖ ^ 2 ≤ 1} → E) x v = (x : E)) :
    IsOutwardPointing x v := by
  rw [isOutwardPointing_normSqSublevel_iff hx, hv, real_inner_self_eq_norm_sq, hx]
  exact one_pos

/-- On the closed unit ball, the tangent vector over `-x` at a point `x` of the unit sphere does
not point outward. -/
theorem not_isOutwardPointing_normSqSublevel_of_mfderiv_eq_neg_self {x : {x : E | ‖x‖ ^ 2 ≤ 1}}
    (hx : ‖(x : E)‖ ^ 2 = 1) {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : {x : E | ‖x‖ ^ 2 ≤ 1} → E) x v = -(x : E)) :
    ¬IsOutwardPointing x v := by
  rw [isOutwardPointing_normSqSublevel_iff hx, hv, inner_neg_right, real_inner_self_eq_norm_sq,
    hx]
  norm_num

end Ball

section HalfSpace

variable {n : ℕ}

/-- The function `x ↦ -x₀` on `ℝⁿ⁺¹` is `C^k` for every `k`. -/
theorem contMDiff_neg_apply_zero {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ) k
      (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ -x 0) :=
  (EuclideanSpace.proj (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).contDiff.neg
    |>.contMDiff

/-- The derivative of `x ↦ -x₀` on `ℝⁿ⁺¹` is `w ↦ -w₀`. -/
private theorem fderiv_neg_apply_zero_apply (x w : EuclideanSpace ℝ (Fin (n + 1))) :
    fderiv ℝ (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ -x 0) x w = -w 0 := by
  have h : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ -x 0)
      (-(EuclideanSpace.proj (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)) x :=
    (ContinuousLinearMap.hasFDerivAt
      (EuclideanSpace.proj (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)).neg
  rw [h.fderiv, neg_apply, PiLp.proj_apply]

/-- Every value of `x ↦ -x₀` on `ℝⁿ⁺¹` is regular: its derivative is the nonzero linear form
`w ↦ -w₀`. -/
theorem isRegularValue_neg_apply_zero (c : ℝ) :
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ)
      (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ -x 0) c := by
  rw [isRegularValue_iff]
  intro x _
  rw [isRegularPoint_iff_surjective_fderiv]
  intro t
  refine ⟨EuclideanSpace.single 0 (-t), ?_⟩
  rw [fderiv_neg_apply_zero_apply]
  simp

variable (n) in
/-- The sublevel atlas `TauCeti.scalarRegularSublevelChartedSpace` of the half-space
`{-x₀ ≤ 0} = {x₀ ≥ 0}` in `ℝⁿ⁺¹`, modelled on `EuclideanHalfSpace (n + 1)`. -/
noncomputable abbrev halfSpaceSublevelChartedSpace :
    ChartedSpace (EuclideanHalfSpace (n + 1)) {x : EuclideanSpace ℝ (Fin (n + 1)) | -x 0 ≤ 0} :=
  scalarRegularSublevelChartedSpace contMDiff_neg_apply_zero (isRegularValue_neg_apply_zero 0)
    finrank_euclideanSpace_fin

attribute [local instance] halfSpaceSublevelChartedSpace

/-- **The outward criterion on a half-space.** At a point `x` of the hyperplane `{x₀ = 0}`, a
tangent vector `v` of the half-space `{-x₀ ≤ 0} = {x₀ ≥ 0}`, with its sublevel atlas, points
outward iff `(dj v)₀ < 0`, where `j` is the inclusion. -/
theorem isOutwardPointing_halfSpaceSublevel_iff
    {x : {x : EuclideanSpace ℝ (Fin (n + 1)) | -x 0 ≤ 0}}
    (hx : -(x : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0) (v : TangentSpace (𝓡∂ (n + 1)) x) :
    IsOutwardPointing x v ↔
      WithLp.ofLp (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : {x : EuclideanSpace ℝ (Fin (n + 1)) | -x 0 ≤ 0} → _) x v) 0 < 0 := by
  rw [isOutwardPointing_scalarRegularSublevel_iff_mfderiv _ finrank_euclideanSpace_fin _ hx,
    mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, fderiv_neg_apply_zero_apply]
  simp only [NormedSpace.fromTangentSpace, neg_pos]
  exact Iff.rfl

/-- On the half-space `{x₀ ≥ 0}`, the tangent vector over `-e₀` at a point of the hyperplane
`{x₀ = 0}` points outward. -/
theorem isOutwardPointing_halfSpaceSublevel_of_mfderiv_eq_neg_single
    {x : {x : EuclideanSpace ℝ (Fin (n + 1)) | -x 0 ≤ 0}}
    (hx : -(x : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0) {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : {x : EuclideanSpace ℝ (Fin (n + 1)) | -x 0 ≤ 0} → _) x v =
        -EuclideanSpace.single 0 1) :
    IsOutwardPointing x v := by
  rw [isOutwardPointing_halfSpaceSublevel_iff hx, hv]
  simp

/-- On the half-space `{x₀ ≥ 0}`, the tangent vector over `e₀` at a point of the hyperplane
`{x₀ = 0}` does not point outward. -/
theorem not_isOutwardPointing_halfSpaceSublevel_of_mfderiv_eq_single
    {x : {x : EuclideanSpace ℝ (Fin (n + 1)) | -x 0 ≤ 0}}
    (hx : -(x : EuclideanSpace ℝ (Fin (n + 1))) 0 = 0) {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : {x : EuclideanSpace ℝ (Fin (n + 1)) | -x 0 ≤ 0} → _) x v =
        EuclideanSpace.single 0 1) :
    ¬IsOutwardPointing x v := by
  rw [isOutwardPointing_halfSpaceSublevel_iff hx, hv]
  simp

end HalfSpace

end TauCeti
