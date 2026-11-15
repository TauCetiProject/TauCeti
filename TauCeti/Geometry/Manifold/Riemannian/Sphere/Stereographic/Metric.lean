/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Conformal
import TauCeti.Analysis.InnerProductSpace.Nondegenerate
import TauCeti.Topology.Algebra.Module.BilinearForm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Stereographic metric and Christoffel formula

The coordinate metric with scale `s` is `(2s / (s² + ‖x‖²))²` times the Euclidean
inner product. Scale one gives equatorial stereographic coordinates; scale two gives
Mathlib's coordinates. For `s ≠ 0`, this is the round unit-sphere metric pulled back by
`y ↦ σ⁻¹((2 / s) • y)`, where `σ` is Mathlib's stereographic projection, up to the
linear isometry identifying the coordinate space with the projection hyperplane.
`metric_two_apply_eq_inner_mfderiv` identifies scale two with the inverse chart's pullback.

Its Christoffel bilinear map is
`-2 / (s² + ‖x‖²) • (⟪x,v⟫u + ⟪x,u⟫v - ⟪u,v⟫x)`.
This expresses the Levi-Civita connection in these coordinates for computations of
geodesics and second fundamental forms on the sphere.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 3.
-/

public noncomputable section

open Bundle
open scoped InnerProductSpace Manifold

namespace TauCeti.Manifold.SphereStereographic

variable {E : Type*} [NormedAddCommGroup E]

private theorem denom_ne_zero {s : ℝ} (hs : s ≠ 0) (x : E) : s ^ 2 + ‖x‖ ^ 2 ≠ 0 :=
  ne_of_gt (by positivity)

private theorem conformalFactor_ne_zero {s : ℝ} (hs : s ≠ 0) (x : E) :
    (2 * s / (s ^ 2 + ‖x‖ ^ 2)) ^ 2 ≠ 0 :=
  pow_ne_zero 2 (div_ne_zero (mul_ne_zero two_ne_zero hs) (denom_ne_zero hs x))

variable [InnerProductSpace ℝ E]

-- Cache the bilinear-space instance so typeclass search resolves bounded scalar multiplication
-- in the operator-valued differentiation and smoothness proofs below.
/-- The canonical normed additive group of real bilinear forms, cached for metric regularity. -/
local instance metricBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The canonical normed space of real bilinear forms, cached for metric regularity. -/
local instance metricBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The spherical coordinate metric, with equatorial scale one and Mathlib scale two. -/
def metric (s : ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (2 * s / (s ^ 2 + ‖x‖ ^ 2)) ^ 2 • innerSL ℝ

/-- The coordinate metric evaluated on two vectors. -/
@[simp]
theorem metric_apply (s : ℝ) (x u v : E) :
    metric s x u v = (2 * s / (s ^ 2 + ‖x‖ ^ 2)) ^ 2 * inner ℝ u v := by
  simp [metric, innerSL_apply_apply ℝ]

/-- The stereographic coordinate metric is symmetric. -/
theorem isSymm_toBilinForm_metric (s : ℝ) (x : E) : (metric s x).toBilinForm.IsSymm := by
  apply ContinuousLinearMap.isSymm_toBilinForm_iff.mpr
  intro u v
  simp [real_inner_comm]

/-- At nonzero scale, the stereographic metric is positive on nonzero vectors. -/
theorem metric_apply_self_pos {s : ℝ} (hs : s ≠ 0) (x : E) {u : E} (hu : u ≠ 0) :
    0 < metric s x u u := by
  rw [metric_apply]
  exact mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (conformalFactor_ne_zero hs x)))
    (real_inner_self_pos.mpr hu)

/-- A nonzero stereographic scale gives a nondegenerate metric everywhere. -/
theorem nondegenerate_toBilinForm_metric {s : ℝ} (hs : s ≠ 0) (x : E) :
    (metric s x).toBilinForm.Nondegenerate := by
  unfold metric
  exact nondegenerate_toBilinForm_smul_innerSL (conformalFactor_ne_zero hs x)

private theorem hasFDerivAt_conformalFactor {s : ℝ} (hs : s ≠ 0) (x : E) :
    HasFDerivAt (fun y : E ↦ (2 * s / (s ^ 2 + ‖y‖ ^ 2)) ^ 2)
      ((-16 * s ^ 2 / (s ^ 2 + ‖x‖ ^ 2) ^ 3) • innerSL ℝ x) x := by
  have hd := denom_ne_zero hs x
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add (s ^ 2)
  have hf := (((hasDerivAt_inv hd).comp_hasFDerivAt x hn).const_mul (2 * s)).pow 2
  convert hf using 1
  · funext y
    simp [div_eq_mul_inv]
  · ext u
    simp [innerSL_apply_apply ℝ]
    field_simp
    ring

/-- The full stereographic metric has the displayed continuous linear differential. -/
theorem hasFDerivAt_metric {s : ℝ} (hs : s ≠ 0) (x : E) :
    HasFDerivAt (metric s)
      (((-16 * s ^ 2 / (s ^ 2 + ‖x‖ ^ 2) ^ 3) • innerSL ℝ x).smulRight (innerSL ℝ)) x := by
  unfold metric
  exact (hasFDerivAt_conformalFactor hs x).smul_const
    (F := E →L[ℝ] E →L[ℝ] ℝ) (innerSL ℝ)

/-- The stereographic coordinate metric is smooth at every nonzero scale. -/
theorem contDiff_metric {s : ℝ} (hs : s ≠ 0) {n : WithTop ℕ∞} :
    ContDiff ℝ n (metric (E := E) s) := by
  unfold metric
  exact ((contDiff_const.div (contDiff_const.add (contDiff_norm_sq ℝ))
    (denom_ne_zero hs)).pow 2).smul_const
      (F := E →L[ℝ] E →L[ℝ] ℝ) (innerSL ℝ)

/-- The differential of the full coordinate metric, including its conformal factor. -/
theorem fderiv_metric {s : ℝ} (hs : s ≠ 0) (x u v w : E) :
    fderiv ℝ (metric s) x u v w =
      (-16 * s ^ 2 / (s ^ 2 + ‖x‖ ^ 2) ^ 3) * inner ℝ x u * inner ℝ v w := by
  rw [(hasFDerivAt_metric hs x).fderiv]
  simp [innerSL_apply_apply ℝ]

/-- Scale two is the round sphere metric pulled back by Mathlib's inverse stereographic chart. -/
theorem metric_two_apply_eq_inner_mfderiv {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (v : Metric.sphere (0 : E) 1) (y a b : EuclideanSpace ℝ (Fin n)) :
    metric 2 y a b =
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm y a)
        (mfderiv (𝓡 n) (𝓡 n) (stereographic' n v).symm y b) := by
  rw [TauCeti.inner_mfderiv_stereographic'_symm, metric_apply]
  norm_num [add_comm]

/-- The Christoffel bilinear map of the actual stereographic coordinate metric. -/
theorem christoffelSecondKind_metric [FiniteDimensional ℝ E]
    {s : ℝ} (hs : s ≠ 0) (x u v : E) :
    christoffelSecondKind (metric s) x u v =
      (-2 / (s ^ 2 + ‖x‖ ^ 2)) •
        (inner ℝ x v • u + inner ℝ x u • v - inner ℝ u v • x) := by
  unfold metric
  rw [christoffelSecondKind_smul_innerSL (hasFDerivAt_conformalFactor hs x).differentiableAt
    (conformalFactor_ne_zero hs x)]
  apply ext_inner_right ℝ
  intro w
  simp [inner_sub_left, inner_add_left, real_inner_smul_left,
    (hasFDerivAt_conformalFactor hs x).fderiv, innerSL_apply_apply ℝ]
  field_simp
  ring

end TauCeti.Manifold.SphereStereographic
