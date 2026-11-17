/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Curve.OrientedNormal

/-!
# Reparametrization of signed geodesic curvature

The geodesic curvature relative to a chosen normal field is invariant under regular
reparametrization. The chain rule for the covariant acceleration gives
`D_t (γ ∘ φ)' = φ'' γ' + (φ')² D_t γ'`. The first term is orthogonal to the chosen normal,
and the factor `(φ')²` in the second term cancels the same factor in the squared speed.
This statement holds in any dimension and also at points where the velocity of `γ` vanishes.

On an oriented surface, an orientation-preserving regular reparametrization preserves signed
geodesic curvature relative to the oriented unit normal, while an orientation-reversing one
negates it. In particular, the affine parameter reflection `r ↦ γ (d - r)` negates this curvature
without any regularity assumption on the original curve.

The signed density `k_g ‖γ'‖` pulls back by the parameter derivative, including where that
derivative vanishes. Its integral change-of-variables laws are in
`TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature.Integral`. The volume-form formula,
`C^n` regularity,
continuity, and oriented-unit-normal germ-invariance and periodicity results are in
`TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature.OrientedNormal`.
General germ invariance and the arbitrary-normal reparametrization, reflection, translation and
periodicity laws live in `TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature`.

## Main results

* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal_comp`: the sign law for a general
  reparametrization, including at zero derivative.
* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal_comp_const_sub`: reflecting a curve
  changes the sign of its curvature relative to the oriented unit normal.
* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp`:
  the signed density pulls back by the derivative, including at critical points.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 9.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {φ : ℝ → ℝ} {t : ℝ}

/-- Reparametrization multiplies signed geodesic curvature relative to the oriented unit
normal by the sign of the derivative. At zero derivative both sides vanish. -/
theorem geodesicCurvature_orientedUnitNormal_comp (o : Orientation I M (Fin 2))
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t)) (hφ : DifferentiableAt ℝ φ t)
    (hφ' : DifferentiableAt ℝ (deriv φ) t) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t =
      (SignType.sign (deriv φ t) : ℝ) *
        geodesicCurvature γ (orientedUnitNormal o γ) (φ t) := by
  by_cases hφ₀ : deriv φ t = 0
  · rw [geodesicCurvature_def,
      curveVelocity_comp hφ.hasDerivAt
        (hγ.mdifferentiableAt two_ne_zero)]
    simp [hφ₀]
  · have hcomp := geodesicCurvature_comp (orientedUnitNormal o γ) hγ hφ' hφ₀
      (inner_orientedUnitNormal_curveVelocity o γ (φ t))
    rw [geodesicCurvature_def,
      orientedUnitNormal_comp o (hγ.mdifferentiableAt two_ne_zero)
        hφ, real_inner_smul_right, mul_div_assoc]
    rw [geodesicCurvature_def] at hcomp
    rw [hcomp]

/-- An orientation-preserving regular reparametrization preserves signed geodesic curvature
relative to the oriented unit normal. -/
theorem geodesicCurvature_orientedUnitNormal_comp_of_deriv_pos (o : Orientation I M (Fin 2))
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t)) (hφ' : DifferentiableAt ℝ (deriv φ) t)
    (hφ₀ : 0 < deriv φ t) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t =
      geodesicCurvature γ (orientedUnitNormal o γ) (φ t) := by
  rw [geodesicCurvature_orientedUnitNormal_comp o hγ
    (differentiableAt_of_deriv_ne_zero hφ₀.ne') hφ']
  simp [hφ₀]

/-- An orientation-reversing regular reparametrization negates signed geodesic curvature
relative to the oriented unit normal. -/
theorem geodesicCurvature_orientedUnitNormal_comp_of_deriv_neg (o : Orientation I M (Fin 2))
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t)) (hφ' : DifferentiableAt ℝ (deriv φ) t)
    (hφ₀ : deriv φ t < 0) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t =
      -geodesicCurvature γ (orientedUnitNormal o γ) (φ t) := by
  rw [geodesicCurvature_orientedUnitNormal_comp o hγ
    (differentiableAt_of_deriv_ne_zero hφ₀.ne) hφ']
  simp [hφ₀]

/-- Reflecting the parameter via `r ↦ γ (d - r)` negates signed geodesic curvature relative to
the oriented unit normal, without any regularity assumption on the original curve. -/
theorem geodesicCurvature_orientedUnitNormal_comp_const_sub
    (o : Orientation I M (Fin 2)) (γ : ℝ → M) (d t : ℝ) :
    geodesicCurvature (fun r ↦ γ (d - r))
      (orientedUnitNormal o (fun r ↦ γ (d - r))) t =
        -geodesicCurvature γ (orientedUnitNormal o γ) (d - t) := by
  calc
    _ = geodesicCurvature (fun r ↦ γ (d - r))
        (fun r ↦ -orientedUnitNormal o γ (d - r)) t :=
      geodesicCurvature_congr_normal (orientedUnitNormal_comp_const_sub o γ d t)
    _ = -geodesicCurvature γ (orientedUnitNormal o γ) (d - t) := by
      rw [geodesicCurvature_fun_neg, geodesicCurvature_comp_const_sub]

variable (o : Orientation I M (Fin 2))

/-- On an oriented surface, the geodesic-curvature density relative to the oriented unit normal
pulls back by the derivative of a change of parameter. The curve is `C²` at the image parameter,
and both the parameter change and its derivative are differentiable at the tested parameter.
This formula applies to either sign of the derivative, including zero. -/
theorem geodesicCurvature_orientedUnitNormal_mul_norm_curveVelocity_comp
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (φ t))
    (hφ : DifferentiableAt ℝ φ t) (hφ' : DifferentiableAt ℝ (deriv φ) t) :
    geodesicCurvature (γ ∘ φ) (orientedUnitNormal o (γ ∘ φ)) t * ‖curveVelocity I (γ ∘ φ) t‖ =
      geodesicCurvature γ (orientedUnitNormal o γ) (φ t) * ‖curveVelocity I γ (φ t)‖ *
        deriv φ t := by
  rw [geodesicCurvature_orientedUnitNormal_comp o hγ hφ hφ',
    curveVelocity_comp hφ.hasDerivAt (hγ.mdifferentiableAt two_ne_zero),
    norm_smul, Real.norm_eq_abs]
  rw [mul_mul_mul_comm, sign_mul_abs]
  ring

end TauCeti.Manifold
