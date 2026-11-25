/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.Riemannian.Induced
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.OutwardUnitNormal

/-!
# The Euclidean metric on a closed interval

The closed interval `[a, b]`, for `a < b`, is an analytic manifold with boundary modelled on the
half-line `𝓡∂ 1` (Mathlib's `instIccChartedSpace`), and the differential of its inclusion into `ℝ`
is invertible at every point, including both endpoints
(`TauCeti.isInvertible_mfderiv_subtypeVal_Icc`). The *Euclidean metric* of the interval is the
Riemannian metric induced by this inclusion: the inner product of two tangent vectors is the
product of their images in `ℝ`. This file installs it as the `RiemannianBundle` instance on the
tangent bundle of `[a, b]`, together with its analyticity, so that the interval is a
one-dimensional Riemannian manifold with boundary.

For this metric the unit tangent vector `1` (the image of `1 ∈ ℝ`, Mathlib's `oneTangentSpaceIcc`)
has norm one, and the outward unit normal is `-1` at the left endpoint and `+1` at the right
endpoint (`TauCeti.outwardUnitNormal_Icc_bot`, `TauCeti.outwardUnitNormal_Icc_top`), although both
preferred charts read the inward direction as `+e₀`: the chart at the right endpoint is a
reflection.

## Main definitions

* `TauCeti.iccEuclideanMetric`: the analytic Euclidean metric on `[a, b]`.
* `TauCeti.instRiemannianBundleIcc`, `TauCeti.instIsContMDiffRiemannianBundleIcc` and
  `TauCeti.instIsContinuousRiemannianBundleIcc`: the corresponding instances.

## Main statements

* `TauCeti.inner_tangentSpace_Icc`: the inner product of two tangent vectors is the product of
  their images in `ℝ`.
* `TauCeti.norm_tangentSpace_Icc`: the norm of a tangent vector is the absolute value of its image
  in `ℝ`.
* `TauCeti.outwardUnitNormal_Icc_bot`, `TauCeti.outwardUnitNormal_Icc_top`: the outward unit
  normal at the two endpoints.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {a b : ℝ} [Fact (a < b)]

/-- The differential of the inclusion of `[a, b]` into `ℝ`, read in `ℝ`, is injective at every
point, including both endpoints. -/
theorem injective_mvfderiv_subtypeVal_Icc (x : Icc a b) :
    Function.Injective (mvfderiv (𝓡∂ 1) (Subtype.val : Icc a b → ℝ) x) := by
  obtain ⟨e, he⟩ := isInvertible_mfderiv_subtypeVal_Icc x
  exact injective_mvfderiv_iff.2 (he ▸ e.injective)

/-- The **Euclidean metric** on the closed interval `[a, b]`: the analytic Riemannian metric
induced by the inclusion into `ℝ`. -/
def iccEuclideanMetric :
    ContMDiffRiemannianMetric (𝓡∂ 1) ω (EuclideanSpace ℝ (Fin 1))
      (fun x : Icc a b ↦ TangentSpace (𝓡∂ 1) x) :=
  inducedRiemannianMetric (n := ω) (Subtype.val : Icc a b → ℝ) contMDiff_subtypeVal_Icc
    injective_mvfderiv_subtypeVal_Icc

/-- The closed interval is a Riemannian manifold with boundary for its Euclidean metric. -/
instance instRiemannianBundleIcc :
    RiemannianBundle (fun x : Icc a b ↦ TangentSpace (𝓡∂ 1) x) :=
  ⟨(iccEuclideanMetric (a := a) (b := b)).toRiemannianMetric⟩

/-- The Euclidean metric on the closed interval is analytic. -/
instance instIsContMDiffRiemannianBundleIcc :
    IsContMDiffRiemannianBundle (𝓡∂ 1) ω (EuclideanSpace ℝ (Fin 1))
      (fun x : Icc a b ↦ TangentSpace (𝓡∂ 1) x) :=
  Bundle.instIsContMDiffRiemannianBundle (iccEuclideanMetric (a := a) (b := b))

/-- The Euclidean metric on the closed interval is continuous. -/
instance instIsContinuousRiemannianBundleIcc :
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1))
      (fun x : Icc a b ↦ TangentSpace (𝓡∂ 1) x) :=
  Bundle.instIsContinuousRiemannianBundle
    (iccEuclideanMetric (a := a) (b := b)).toContinuousRiemannianMetric

/-- The inner product of two tangent vectors of `[a, b]` is the product of their images in `ℝ`
under the differential of the inclusion. -/
@[simp]
theorem inner_tangentSpace_Icc (x : Icc a b) (v w : TangentSpace (𝓡∂ 1) x) :
    inner ℝ v w =
      mvfderiv (𝓡∂ 1) (Subtype.val : Icc a b → ℝ) x v *
        mvfderiv (𝓡∂ 1) (Subtype.val : Icc a b → ℝ) x w := by
  have h : inner ℝ v w = inner ℝ (mvfderiv (𝓡∂ 1) (Subtype.val : Icc a b → ℝ) x v)
      (mvfderiv (𝓡∂ 1) (Subtype.val : Icc a b → ℝ) x w) :=
    inducedRiemannianMetric_inner _ _ _ x v w
  rw [h, RCLike.inner_apply, conj_trivial, mul_comm]

/-- The norm of a tangent vector of `[a, b]` is the absolute value of its image in `ℝ` under the
differential of the inclusion. -/
@[simp]
theorem norm_tangentSpace_Icc (x : Icc a b) (v : TangentSpace (𝓡∂ 1) x) :
    ‖v‖ = |mvfderiv (𝓡∂ 1) (Subtype.val : Icc a b → ℝ) x v| := by
  rw [norm_eq_sqrt_real_inner, inner_tangentSpace_Icc, Real.sqrt_mul_self_eq_abs]

/-- The differential of the inclusion of `[a, b]` into `ℝ`, read in `ℝ`, sends the unit tangent
vector `1` to `1 ∈ ℝ`. -/
-- Priority `high` so that `simp` evaluates this before reading `mvfderiv` as `mfderiv`
-- (`mvfderiv_apply_eq_mfderiv_apply`), whose value `1` lies in a tangent space of `ℝ` rather than
-- in `ℝ`.
@[simp high]
theorem mvfderiv_subtypeVal_Icc_one (x : Icc a b) :
    mvfderiv (𝓡∂ 1) (Subtype.val : Icc a b → ℝ) x 1 = 1 := by
  rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_subtypeVal_Icc_one]
  rfl

/-- The unit tangent vector `1` of `[a, b]`, the image of `1 ∈ ℝ`, has norm one. -/
theorem norm_one_tangentSpace_Icc (x : Icc a b) : ‖(1 : TangentSpace (𝓡∂ 1) x)‖ = 1 := by
  simp

/-! ### The outward unit normal at the endpoints -/

section Endpoints

open Fact.Manifold
open scoped IccZeroAddOne

/-- The Euclidean metric of the interval, on the tangent spaces of the charts
`IccZeroAddOne.instChartedSpace`. -/
local instance instRiemannianBundleIccZeroAddOne :
    RiemannianBundle (fun x : Icc a b ↦ TangentSpace (𝓡∂ (0 + 1)) x) :=
  instRiemannianBundleIcc

/-- A tangent vector at a boundary point of `[a, b]` with norm one and outward is the outward
unit normal: the boundary manifold is zero-dimensional, so orthogonality is automatic. -/
private theorem eq_outwardUnitNormal_Icc {q : (𝓡∂ (0 + 1)).boundary (Icc a b)}
    {v : TangentSpace (𝓡∂ (0 + 1)) (q : Icc a b)} (hv : ‖v‖ = 1)
    (ho : IsOutwardPointing (q : Icc a b) v) : v = outwardUnitNormal q := by
  refine eq_outwardUnitNormal_iff.mpr ⟨hv, ho, fun w ↦ ?_⟩
  -- The boundary is modelled on `EuclideanSpace ℝ (Fin 0)`, so its tangent spaces are trivial.
  have : Subsingleton (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) q) :=
    inferInstanceAs (Subsingleton (EuclideanSpace ℝ (Fin 0)))
  have hw : w = 0 := Subsingleton.elim w 0
  rw [hw, map_zero, inner_zero_right]

/-- The outward unit normal of `[a, b]` at the left endpoint is `-1`, minus the image of
`1 ∈ ℝ`. -/
theorem outwardUnitNormal_Icc_bot :
    outwardUnitNormal (⟨⊥, Icc_isBoundaryPoint_bot⟩ : (𝓡∂ (0 + 1)).boundary (Icc a b)) =
      -(1 : TangentSpace (𝓡∂ 1) (⊥ : Icc a b)) := by
  have hab : ((⊥ : Icc a b) : ℝ) < b := Fact.out (p := a < b)
  refine (eq_outwardUnitNormal_Icc (by rw [norm_neg, norm_one_tangentSpace_Icc]) ?_).symm
  rw [isOutwardPointing_iff_proj Icc_isBoundaryPoint_bot]
  -- The boundary API reads tangent vectors in the model `𝓡∂ (0 + 1)`, the unit vector `1` lives
  -- in `𝓡∂ 1`, and both are `EuclideanSpace ℝ (Fin 1)` only after reducing `0 + 1` to `1`, which
  -- `rw` and `simp` do not see. `change` states the normal coordinate of `-1` in `𝓡∂ 1`;
  -- `EuclideanSpace.proj 0` is `fun v ↦ v 0` by `EuclideanSpace.coe_proj`.
  change -(WithLp.ofLp (p := 2) (1 : TangentSpace (𝓡∂ 1) (⊥ : Icc a b)) 0) < 0
  rw [one_tangentSpace_Icc_apply]
  simp only [hab, ↓reduceIte, neg_lt_zero, zero_lt_one]

/-- The outward unit normal of `[a, b]` at the right endpoint is `+1`, the image of `1 ∈ ℝ`,
although the preferred chart there reads it as `-e₀`. -/
theorem outwardUnitNormal_Icc_top :
    outwardUnitNormal (⟨⊤, Icc_isBoundaryPoint_top⟩ : (𝓡∂ (0 + 1)).boundary (Icc a b)) =
      (1 : TangentSpace (𝓡∂ 1) (⊤ : Icc a b)) := by
  have hab : ¬((⊤ : Icc a b) : ℝ) < b := lt_irrefl b
  refine (eq_outwardUnitNormal_Icc (norm_one_tangentSpace_Icc _) ?_).symm
  rw [isOutwardPointing_iff_proj Icc_isBoundaryPoint_top]
  -- As in `outwardUnitNormal_Icc_bot`, `change` reads the normal coordinate in `𝓡∂ 1`.
  change WithLp.ofLp (p := 2) (1 : TangentSpace (𝓡∂ 1) (⊤ : Icc a b)) 0 < 0
  rw [one_tangentSpace_Icc_apply]
  simp only [hab, ↓reduceIte, neg_lt_zero, zero_lt_one]

end Endpoints

end TauCeti
