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
  intro v w h
  rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply] at h
  obtain ⟨e, he⟩ := isInvertible_mfderiv_subtypeVal_Icc x
  rw [← he] at h
  exact e.injective h

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

/-- The unit tangent vector `1` of `[a, b]`, the image of `1 ∈ ℝ`, has norm one. -/
theorem norm_one_tangentSpace_Icc (x : Icc a b) : ‖(1 : TangentSpace (𝓡∂ 1) x)‖ = 1 := by
  rw [norm_tangentSpace_Icc, mvfderiv_apply_eq_mfderiv_apply, mfderiv_subtypeVal_Icc_one]
  exact abs_one

/-! ### The outward unit normal at the endpoints -/

section Endpoints

open Fact.Manifold

/-- The interval charts, with the model dimension written as the successor `0 + 1` used by the
boundary constructions. -/
@[reducible] local instance instChartedSpaceIccZeroAddOne :
    ChartedSpace (EuclideanHalfSpace (0 + 1)) (Icc a b) :=
  instIccChartedSpace a b

/-- The interval is a `C¹` manifold for the charts `instChartedSpaceIccZeroAddOne`. -/
local instance instIsManifoldIccZeroAddOne : IsManifold (𝓡∂ (0 + 1)) 1 (Icc a b) :=
  instIsManifoldIcc a b

/-- The Euclidean metric of the interval, on the tangent spaces of the charts
`instChartedSpaceIccZeroAddOne`. -/
local instance instRiemannianBundleIccZeroAddOne :
    RiemannianBundle (fun x : Icc a b ↦ TangentSpace (𝓡∂ (0 + 1)) x) :=
  instRiemannianBundleIcc

/-- A tangent vector at a boundary point of `[a, b]` with norm one and outward is the outward
unit normal: the boundary manifold is zero-dimensional, so orthogonality is automatic. -/
private theorem eq_outwardUnitNormal_Icc {q : (𝓡∂ (0 + 1)).boundary (Icc a b)}
    {v : TangentSpace (𝓡∂ (0 + 1)) (q : Icc a b)} (hv : ‖v‖ = 1)
    (ho : IsOutwardPointing (q : Icc a b) v) : v = outwardUnitNormal q := by
  refine eq_outwardUnitNormal_iff.mpr ⟨hv, ho, fun w ↦ ?_⟩
  have hw : w = 0 := Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) w 0
  rw [hw, map_zero, inner_zero_right]

/-- The outward unit normal of `[a, b]` at the left endpoint is `-1`, minus the image of
`1 ∈ ℝ`. -/
theorem outwardUnitNormal_Icc_bot :
    outwardUnitNormal (⟨⊥, Icc_isBoundaryPoint_bot⟩ : (𝓡∂ (0 + 1)).boundary (Icc a b)) =
      -(1 : TangentSpace (𝓡∂ 1) (⊥ : Icc a b)) := by
  have hab : ((⊥ : Icc a b) : ℝ) < b := Fact.out (p := a < b)
  refine (eq_outwardUnitNormal_Icc (by rw [norm_neg, norm_one_tangentSpace_Icc]) ?_).symm
  rw [isOutwardPointing_iff_proj Icc_isBoundaryPoint_bot]
  change -(WithLp.ofLp (p := 2) (1 : TangentSpace (𝓡∂ 1) (⊥ : Icc a b)) 0) < 0
  rw [one_tangentSpace_Icc_apply]
  simp only [hab, ↓reduceIte]
  norm_num

/-- The outward unit normal of `[a, b]` at the right endpoint is `+1`, the image of `1 ∈ ℝ`,
although the preferred chart there reads it as `-e₀`. -/
theorem outwardUnitNormal_Icc_top :
    outwardUnitNormal (⟨⊤, Icc_isBoundaryPoint_top⟩ : (𝓡∂ (0 + 1)).boundary (Icc a b)) =
      (1 : TangentSpace (𝓡∂ 1) (⊤ : Icc a b)) := by
  have hab : ¬((⊤ : Icc a b) : ℝ) < b := lt_irrefl b
  refine (eq_outwardUnitNormal_Icc (norm_one_tangentSpace_Icc _) ?_).symm
  rw [isOutwardPointing_iff_proj Icc_isBoundaryPoint_top]
  change WithLp.ofLp (p := 2) (1 : TangentSpace (𝓡∂ 1) (⊤ : Icc a b)) 0 < 0
  rw [one_tangentSpace_Icc_apply]
  simp only [hab, ↓reduceIte]
  norm_num

end Endpoints

end TauCeti
