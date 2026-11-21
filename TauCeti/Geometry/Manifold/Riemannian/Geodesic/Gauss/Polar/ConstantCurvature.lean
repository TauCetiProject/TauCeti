/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Polar.Jacobian
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Metric

/-!
# The polar Jacobian in constant curvature

For a unit radial vector `v` and an angular vector `w ⊥ v`, constant sectional curvature `κ`
along the radial segment gives `polarJacobian p v w r = |curvatureSine κ r| * ‖w‖`.
This follows from the constant-curvature norm formula for the exponential differential and
the scaling law of the model sine. It includes zero and negative radii and conjugate vectors;
only membership in the exponential domain is required, without completeness or injectivity.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (Jacobi fields in constant curvature).
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v w : TangentSpace I p} {κ r : ℝ}

/-- In constant sectional curvature along the radial segment, the polar Jacobian for a unit
radial vector and an orthogonal angular vector is the absolute model sine times the angular
norm. The formula holds at every radius in the exponential domain, including conjugate radii. -/
theorem polarJacobian_of_inner_eq_zero_of_hasSectionalCurvatureAt
    (hmem : r • v ∈ expDomain I M p)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (t • (r • v))) κ)
    (hv : ‖v‖ = 1) (hvw : ⟪v, w⟫_ℝ = 0) :
    polarJacobian (I := I) p v w r = |curvatureSine κ r| * ‖w‖ := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have hw : ⟪w, r • v⟫_ℝ = 0 := by
    simp only [real_inner_smul_right, inner_eq_zero_symm.mpr hvw, mul_zero]
  have hscale : r * curvatureSine (κ * r ^ 2) 1 = curvatureSine κ r := by
    have hs := curvatureSine_div_sq_mul (κ * r ^ 2) r 1
    rw [mul_div_cancel_right₀ _ (pow_ne_zero 2 hr), mul_one] at hs
    exact hs.symm
  rw [polarJacobian_eq_abs_mul,
    norm_mfderiv_riemannianExp_of_inner_eq_zero_of_hasSectionalCurvatureAt hmem hK w hw,
    norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs, ← mul_assoc, ← abs_mul, hscale]

end TauCeti.Manifold
