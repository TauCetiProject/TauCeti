/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Stereographic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
import TauCeti.Topology.Algebra.Module.BilinearForm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Stereographic metric and Christoffel formula

The coordinate metric with scale `s` is `(2s / (s² + ‖x‖²))²` times the Euclidean
inner product. Scale one gives equatorial stereographic coordinates; scale two gives
Mathlib's coordinates. Its Christoffel bilinear map is
`-2 / (s² + ‖x‖²) • (⟪x,v⟫u + ⟪x,u⟫v - ⟪u,v⟫x)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 3.
-/

public noncomputable section

open scoped InnerProductSpace

namespace TauCeti.Manifold.SphereStereographic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def euclideanForm : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ

/-- The spherical coordinate metric, with equatorial scale one and Mathlib scale two. -/
def metric (s : ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (2 * s / (s ^ 2 + ‖x‖ ^ 2)) ^ 2 • euclideanForm

/-- The coordinate metric evaluated on two vectors. -/
@[simp]
theorem metric_apply (s : ℝ) (x u v : E) :
    metric s x u v = (2 * s / (s ^ 2 + ‖x‖ ^ 2)) ^ 2 * inner ℝ u v := by
  rfl

/-- A nonzero stereographic scale gives a nondegenerate metric everywhere. -/
theorem metric_nondegenerate [FiniteDimensional ℝ E] {s : ℝ} (hs : s ≠ 0) (x : E) :
    (metric s x).toBilinForm.Nondegenerate := by
  have hd : s ^ 2 + ‖x‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hc : (2 * s / (s ^ 2 + ‖x‖ ^ 2)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (div_ne_zero (mul_ne_zero two_ne_zero hs) hd)
  apply (metric s x).nondegenerate_toBilinForm_iff_injective.mpr
  intro u v h
  apply ext_inner_right ℝ
  intro w
  exact mul_left_cancel₀ hc (by simpa only [metric_apply] using DFunLike.congr_fun h w)

/-- The differential of the full coordinate metric, including its conformal factor. -/
theorem fderiv_metric {s : ℝ} (hs : s ≠ 0) (x u v w : E) :
    fderiv ℝ (metric s) x u v w =
      (-16 * s ^ 2 / (s ^ 2 + ‖x‖ ^ 2) ^ 3) * inner ℝ x u * inner ℝ v w := by
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  have hd : s ^ 2 + ‖x‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hn := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add (s ^ 2)
  have hf := (((hasDerivAt_inv hd).comp_hasFDerivAt x hn).const_mul (2 * s)).pow 2
  have hb (a b : E) : (euclideanForm : E →L[ℝ] E →L[ℝ] ℝ) a b = inner ℝ a b := rfl
  have hg := (hf.smul_const (euclideanForm (E := E))).congr_of_eventuallyEq
    (f₁ := metric s) (.of_forall fun _ ↦ rfl)
  rw [hg.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, hb,
    _root_.innerSL_apply_apply, smul_eq_mul, Function.comp_apply, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Nat.cast_ofNat]
  field_simp [hd]
  ring

/-- The Christoffel bilinear map of the actual stereographic coordinate metric. -/
theorem christoffelSecondKind_metric [FiniteDimensional ℝ E]
    {s : ℝ} (hs : s ≠ 0) (x u v : E) :
    christoffelSecondKind (metric s) x u v =
      (-2 / (s ^ 2 + ‖x‖ ^ 2)) •
        (inner ℝ x v • u + inner ℝ x u • v - inner ℝ u v • x) := by
  have hd : s ^ 2 + ‖x‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hc : (2 * s / (s ^ 2 + ‖x‖ ^ 2)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (div_ne_zero (mul_ne_zero two_ne_zero hs) hd)
  apply ext_inner_right ℝ
  intro w
  apply mul_left_cancel₀ hc
  have h := apply_christoffelSecondKind (metric_nondegenerate hs x) u v w
  simp only [metric_apply, christoffelFirstKind_apply, fderiv_metric hs] at h
  rw [h]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
  field_simp
  ring

end TauCeti.Manifold.SphereStereographic
