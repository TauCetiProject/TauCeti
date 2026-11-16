/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Euclidean
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# Jacobi fields in an inner-product space

A finite-dimensional real inner-product space `F` with its standard metric has vanishing
Christoffel map and vanishing curvature. Along every curve, the Levi-Civita covariant derivative
of a field is therefore its ordinary derivative, also within a parameter set. Along an affine
geodesic `t ↦ p + t • v` the Jacobi equation `D_t² J + R(J, γ') γ' = 0` becomes `J'' = 0`.

Every affine field `t ↦ u + t • w` is thus a Jacobi field along every affine geodesic, with
initial value `u` and initial covariant derivative `w`; this includes `u = w = 0` and the constant
geodesic `v = 0`. A quadratic field `t ↦ t² • e` has Jacobi residual `2 • e` at every time, so it
is not a Jacobi field when `e ≠ 0`, although it vanishes at `t = 0`.

## Main results

* `TauCeti.Manifold.isJacobiFieldOn_add_smul_model_space`: affine fields are Jacobi fields along
  affine geodesics.
* `TauCeti.Manifold.alongCurveWithin_add_smul_model_space`: their covariant derivative is `w`.
* `TauCeti.Manifold.not_isJacobiFieldOn_sq_smul_model_space`: the field `t ↦ t² • e`, whose
  Jacobi residual is `2 • e`, is not a Jacobi field for `e ≠ 0`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  §14 (the Jacobi equation).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private theorem curvatureTensor_apply_model_space (x : F) (u v w : TangentSpace 𝓘(ℝ, F) x) :
    (leviCivitaConnection 𝓘(ℝ, F) F).curvatureTensor x u v w = 0 := by
  rw [curvatureTensor_leviCivitaConnection_model_space]
  rfl

/-- The covariant derivative of the affine field `t ↦ u + t • w` along any curve is `w`. -/
theorem alongCurveWithin_add_smul_model_space (γ : ℝ → F) (u w : F) (t : ℝ) :
    alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ
      (fun r ↦ (u + r • w : TangentSpace 𝓘(ℝ, F) (γ r))) univ t = w := by
  rw [alongCurveWithin_leviCivitaConnection_model_space γ (fun r ↦ u + r • w), derivWithin_univ]
  have h := (((hasDerivAt_id t).smul_const w).const_add u).deriv
  rw [one_smul] at h
  exact h

/-- The affine field `t ↦ u + t • w` is a Jacobi field along every affine geodesic
`t ↦ p + t • v`, including the zero field and the constant geodesic. -/
theorem isJacobiFieldOn_add_smul_model_space (p v u w : F) :
    IsJacobiFieldOn 𝓘(ℝ, F) (fun t ↦ p + t • v)
      (fun t ↦ (u + t • w : TangentSpace 𝓘(ℝ, F) (p + t • v))) univ := by
  have hD : alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) (fun r ↦ p + r • v)
      (fun r ↦ (u + r • w : TangentSpace 𝓘(ℝ, F) (p + r • v))) univ = fun _ ↦ w :=
    funext (alongCurveWithin_add_smul_model_space _ u w)
  refine ⟨(isGeodesicCurveOnFrom_add_smul p v).isGeodesicCurveOn, ?_, fun t _ ↦ ?_⟩
  · rw [contMDiffOn_univ]
    have hpair := contMDiff_iff_contDiff.mpr
      ((show ContDiff ℝ 2 fun t : ℝ ↦ p + t • v by fun_prop).prodMk
        (show ContDiff ℝ 2 fun t : ℝ ↦ u + t • w by fun_prop))
    rw [modelWithCornersSelf_prod] at hpair
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, F)) (n := 2)).comp hpair
  · have hc : (leviCivitaConnection 𝓘(ℝ, F) F).curvatureTensor (p + t • v) (u + t • w)
        (curveVelocityWithin 𝓘(ℝ, F) (fun r ↦ p + r • v) univ t)
        (curveVelocityWithin 𝓘(ℝ, F) (fun r ↦ p + r • v) univ t) = 0 :=
      curvatureTensor_apply_model_space _ _ _ _
    rw [hD, hc, add_zero,
      alongCurveWithin_leviCivitaConnection_model_space (fun r ↦ p + r • v) (fun _ : ℝ ↦ w)]
    exact congrFun (derivWithin_const (𝕜 := ℝ) univ w) t

/-- The quadratic field `t ↦ t² • e` has Jacobi residual `2 • e` at every time along every
affine geodesic. -/
private theorem jacobiResidual_sq_smul_model_space (p v e : F) (t : ℝ) :
    alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) (fun r ↦ p + r • v)
        (alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) (fun r ↦ p + r • v)
          (fun r ↦ (r ^ 2 • e : TangentSpace 𝓘(ℝ, F) (p + r • v))) univ) univ t +
      (leviCivitaConnection 𝓘(ℝ, F) F).curvatureTensor (p + t • v) (t ^ 2 • e)
        (curveVelocityWithin 𝓘(ℝ, F) (fun r ↦ p + r • v) univ t)
        (curveVelocityWithin 𝓘(ℝ, F) (fun r ↦ p + r • v) univ t) = (2 : ℝ) • e := by
  have hD : alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) (fun r ↦ p + r • v)
      (fun r ↦ (r ^ 2 • e : TangentSpace 𝓘(ℝ, F) (p + r • v))) univ =
      fun r ↦ (2 * r) • e := by
    funext r
    rw [alongCurveWithin_leviCivitaConnection_model_space _ (fun r ↦ r ^ 2 • e), derivWithin_univ]
    have h := ((hasDerivAt_pow 2 r).smul_const e).deriv
    norm_num at h
    exact h
  have hc : (leviCivitaConnection 𝓘(ℝ, F) F).curvatureTensor (p + t • v) (t ^ 2 • e)
      (curveVelocityWithin 𝓘(ℝ, F) (fun r ↦ p + r • v) univ t)
      (curveVelocityWithin 𝓘(ℝ, F) (fun r ↦ p + r • v) univ t) = 0 :=
    curvatureTensor_apply_model_space _ _ _ _
  rw [hD, hc, add_zero,
    alongCurveWithin_leviCivitaConnection_model_space _ (fun r ↦ (2 * r) • e), derivWithin_univ]
  have h := (((hasDerivAt_id t).const_mul (2 : ℝ)).smul_const e).deriv
  rw [mul_one] at h
  exact h

/-- A quadratic field `t ↦ t² • e` with `e ≠ 0` is not a Jacobi field along any affine geodesic,
although it vanishes at `t = 0`. -/
theorem not_isJacobiFieldOn_sq_smul_model_space (p v : F) {e : F} (he : e ≠ 0) :
    ¬IsJacobiFieldOn 𝓘(ℝ, F) (fun t ↦ p + t • v)
      (fun t ↦ (t ^ 2 • e : TangentSpace 𝓘(ℝ, F) (p + t • v))) univ := fun hJ ↦
  he <| (smul_eq_zero.mp ((jacobiResidual_sq_smul_model_space p v e 0).symm.trans
    (hJ.equation 0 (mem_univ 0)))).resolve_left two_ne_zero

end TauCeti.Manifold
