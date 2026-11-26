/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.Instances.Icc.Boundary
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
* `TauCeti.IccZeroAddOne.instRiemannianBundle`,
  `TauCeti.IccZeroAddOne.instIsContMDiffRiemannianBundle` and
  `TauCeti.IccZeroAddOne.instIsContinuousRiemannianBundle`: the same instances, scoped in
  `TauCeti.IccZeroAddOne`, for the charts in the successor dimension `0 + 1` used by the boundary
  constructions (outward unit normal, second fundamental form), together with the unit tangent
  vector `1` there (`TauCeti.IccZeroAddOne.instOneTangentSpace`).

## Main statements

* `TauCeti.iccEuclideanMetric_inner`: the Euclidean metric evaluates the product of the images of
  two tangent vectors in `ℝ`.
* `TauCeti.inner_tangentSpace_Icc`: the inner product of two tangent vectors is the product of
  their images in `ℝ`.
* `TauCeti.norm_tangentSpace_Icc`: the norm of a tangent vector is the absolute value of its image
  in `ℝ`.
* `TauCeti.IccZeroAddOne.inner_tangentSpace`, `TauCeti.IccZeroAddOne.norm_tangentSpace`: the same
  statements for the charts in the successor dimension `0 + 1`.
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

/-- The Euclidean metric evaluates the product of the images of two tangent vectors in `ℝ` under
the differential of the inclusion. -/
@[simp]
theorem iccEuclideanMetric_inner (x : Icc a b) (v w : TangentSpace (𝓡∂ 1) x) :
    (iccEuclideanMetric (a := a) (b := b)).inner x v w =
      mvfderiv (𝓡∂ 1) (Subtype.val : Icc a b → ℝ) x v *
        mvfderiv (𝓡∂ 1) (Subtype.val : Icc a b → ℝ) x w := by
  rw [iccEuclideanMetric, inducedRiemannianMetric_inner, RCLike.inner_apply, conj_trivial,
    mul_comm]

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
        mvfderiv (𝓡∂ 1) (Subtype.val : Icc a b → ℝ) x w :=
  -- The inner product of the bundle instance `instRiemannianBundleIcc` is that of
  -- `iccEuclideanMetric` by definition.
  iccEuclideanMetric_inner x v w

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
  -- The tangent space `TangentSpace 𝓘(ℝ, ℝ) _` is `ℝ` by definition, and its `1` is `1 : ℝ`.
  rfl

/-- The unit tangent vector `1` of `[a, b]`, the image of `1 ∈ ℝ`, has norm one. -/
theorem norm_one_tangentSpace_Icc (x : Icc a b) : ‖(1 : TangentSpace (𝓡∂ 1) x)‖ = 1 := by
  simp

/-! ### The Euclidean metric in the successor dimension `0 + 1` -/

namespace IccZeroAddOne

/-- The Euclidean metric of the interval, on the tangent spaces of the charts
`instChartedSpaceIccZeroAddOne` used by the boundary constructions. -/
scoped instance instRiemannianBundle :
    RiemannianBundle (fun x : Icc a b ↦ TangentSpace (𝓡∂ (0 + 1)) x) :=
  instRiemannianBundleIcc

/-- The Euclidean metric of the interval is analytic for the charts
`instChartedSpaceIccZeroAddOne`. -/
scoped instance instIsContMDiffRiemannianBundle :
    IsContMDiffRiemannianBundle (𝓡∂ (0 + 1)) ω (EuclideanSpace ℝ (Fin (0 + 1)))
      (fun x : Icc a b ↦ TangentSpace (𝓡∂ (0 + 1)) x) :=
  instIsContMDiffRiemannianBundleIcc

/-- The Euclidean metric of the interval is continuous for the charts
`instChartedSpaceIccZeroAddOne`. -/
scoped instance instIsContinuousRiemannianBundle :
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (0 + 1)))
      (fun x : Icc a b ↦ TangentSpace (𝓡∂ (0 + 1)) x) :=
  instIsContinuousRiemannianBundleIcc

/-- The unit tangent vector `1` of `[a, b]`, the image of `1 ∈ ℝ`, on the tangent spaces of the
charts `instChartedSpaceIccZeroAddOne`. -/
scoped instance instOneTangentSpace (x : Icc a b) : One (TangentSpace (𝓡∂ (0 + 1)) x) :=
  inferInstanceAs (One (TangentSpace (𝓡∂ 1) x))

/-- The inner product of two tangent vectors of `[a, b]` for the charts
`instChartedSpaceIccZeroAddOne` is the product of their images in `ℝ`. -/
@[scoped simp]
theorem inner_tangentSpace (x : Icc a b) (v w : TangentSpace (𝓡∂ (0 + 1)) x) :
    inner ℝ v w =
      mvfderiv (𝓡∂ (0 + 1)) (Subtype.val : Icc a b → ℝ) x v *
        mvfderiv (𝓡∂ (0 + 1)) (Subtype.val : Icc a b → ℝ) x w :=
  inner_tangentSpace_Icc x v w

/-- The norm of a tangent vector of `[a, b]` for the charts `instChartedSpaceIccZeroAddOne` is
the absolute value of its image in `ℝ`. -/
@[scoped simp]
theorem norm_tangentSpace (x : Icc a b) (v : TangentSpace (𝓡∂ (0 + 1)) x) :
    ‖v‖ = |mvfderiv (𝓡∂ (0 + 1)) (Subtype.val : Icc a b → ℝ) x v| :=
  norm_tangentSpace_Icc x v

/-- The differential of the inclusion of `[a, b]` into `ℝ`, for the charts
`instChartedSpaceIccZeroAddOne`, sends the unit tangent vector `1` to `1 ∈ ℝ`. -/
-- Priority `high` for the same reason as `mvfderiv_subtypeVal_Icc_one`.
@[scoped simp high]
theorem mvfderiv_subtypeVal_one (x : Icc a b) :
    mvfderiv (𝓡∂ (0 + 1)) (Subtype.val : Icc a b → ℝ) x 1 = 1 :=
  mvfderiv_subtypeVal_Icc_one x

/-- The unit tangent vector `1` of `[a, b]` has norm one for the charts
`instChartedSpaceIccZeroAddOne`. -/
theorem norm_one_tangentSpace (x : Icc a b) : ‖(1 : TangentSpace (𝓡∂ (0 + 1)) x)‖ = 1 := by
  simp

/-- The normal coordinate of the unit tangent vector `1` of `[a, b]` in the preferred chart at
`x`, read as the boundary constructions read it: `+1` in the translation chart and `-1` in the
reflection chart at the right endpoint. -/
theorem proj_one_tangentSpace (x : Icc a b) :
    EuclideanSpace.proj 0 (1 : TangentSpace (𝓡∂ (0 + 1)) x) = if (x : ℝ) < b then 1 else -1 := by
  rw [EuclideanSpace.coe_proj]
  -- `Fin (0 + 1)` reduces to `Fin 1`, so the tangent spaces for the charts `𝓡∂ (0 + 1)` and
  -- `𝓡∂ 1` and their unit vectors `1` (`instOneTangentSpace`) agree by definition.
  exact one_tangentSpace_Icc_apply x 0

end IccZeroAddOne

/-! ### The outward unit normal at the endpoints -/

section Endpoints

open Fact.Manifold
open scoped IccZeroAddOne

/-- The outward unit normal of `[a, b]` at the left endpoint is `-1`, minus the image of
`1 ∈ ℝ`. -/
theorem outwardUnitNormal_Icc_bot :
    outwardUnitNormal (⟨⊥, Icc_isBoundaryPoint_bot⟩ : (𝓡∂ (0 + 1)).boundary (Icc a b)) =
      -(1 : TangentSpace (𝓡∂ (0 + 1)) (⊥ : Icc a b)) := by
  have hab : ((⊥ : Icc a b) : ℝ) < b := by
    rw [Set.Icc.coe_bot]
    exact Fact.out
  refine (eq_outwardUnitNormal_iff_of_dim_one.2
    ⟨by rw [norm_neg, IccZeroAddOne.norm_one_tangentSpace], ?_⟩).symm
  rw [isOutwardPointing_neg_iff_proj Icc_isBoundaryPoint_bot, IccZeroAddOne.proj_one_tangentSpace]
  simp only [hab, ↓reduceIte, zero_lt_one]

/-- The outward unit normal of `[a, b]` at the right endpoint is `+1`, the image of `1 ∈ ℝ`,
although the preferred chart there reads it as `-e₀`. -/
theorem outwardUnitNormal_Icc_top :
    outwardUnitNormal (⟨⊤, Icc_isBoundaryPoint_top⟩ : (𝓡∂ (0 + 1)).boundary (Icc a b)) =
      (1 : TangentSpace (𝓡∂ (0 + 1)) (⊤ : Icc a b)) := by
  have hab : ¬((⊤ : Icc a b) : ℝ) < b := by
    rw [Set.Icc.coe_top]
    exact lt_irrefl b
  refine (eq_outwardUnitNormal_iff_of_dim_one.2 ⟨IccZeroAddOne.norm_one_tangentSpace _, ?_⟩).symm
  rw [isOutwardPointing_iff_proj Icc_isBoundaryPoint_top, IccZeroAddOne.proj_one_tangentSpace]
  simp only [hab, ↓reduceIte, neg_lt_zero, zero_lt_one]

end Endpoints

end TauCeti
