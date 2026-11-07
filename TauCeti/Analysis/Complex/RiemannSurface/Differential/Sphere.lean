/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical

/-!
# A canonical divisor on the Riemann sphere

The differential `dz` of the affine coordinate on `OnePoint ℂ` has no zeros or poles at
finite points and has a double pole at infinity. In the coordinate `w = 1/z` it is
`-w⁻² dw`. Thus its divisor is `-2[∞]`, an explicit canonical divisor of degree `-2`.
This is the sphere contribution in the canonical-divisor form of Riemann–Hurwitz.

The affine coordinate itself is assigned the value zero at infinity. Its manifold
differential there is likewise a junk value; meromorphy, order and divisor only depend
on punctured neighbourhoods, so the double pole is retained.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, GTM 81, §§9 and 17
  (meromorphic differentials and the canonical divisor of the sphere).
-/

public noncomputable section

open Filter Function OnePoint Set Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open AlgebraicGeometry WeilDivisor

/-- The meromorphic differential `dz` on the sphere, obtained by differentiating the
affine coordinate. Its value at infinity is irrelevant to its meromorphic germ. -/
def sphereCoordinateDifferential : OneForm (OnePoint ℂ) :=
  mvfderiv 𝓘(ℂ) (affineChart : OnePoint ℂ → ℂ)

/-- In the affine chart the coefficient of `dz` is the constant one. -/
@[simp]
theorem coeff_sphereCoordinateDifferential_affineChart :
    sphereCoordinateDifferential.coeff affineChart = fun _ => 1 := by
  funext z
  have he : affineChart ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 (OnePoint ℂ) := by
    simpa only [chartAt_coe] using
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) (z : OnePoint ℂ))
  rw [sphereCoordinateDifferential, OneForm.coeff_mvfderiv he (by simp)
    (mdifferentiableAt_of_mem_maximalAtlas he (by simp))]
  simp [comp_def]

/-- The differential `dz` is holomorphic at every finite point of the sphere. -/
theorem holomorphicAt_sphereCoordinateDifferential_coe (z : ℂ) :
    sphereCoordinateDifferential.HolomorphicAt (z : OnePoint ℂ) := by
  rw [OneForm.holomorphicAt_def, chartAt_coe,
    coeff_sphereCoordinateDifferential_affineChart]
  exact analyticAt_const

/-- The differential `dz` has order zero at every finite point. -/
@[simp]
theorem order_sphereCoordinateDifferential_coe (z : ℂ) :
    sphereCoordinateDifferential.order (z : OnePoint ℂ) = 0 := by
  rw [OneForm.order_def, chartAt_coe, coeff_sphereCoordinateDifferential_affineChart]
  rw [_root_.meromorphicOrderAt_const]
  norm_num

/-- In the inverted coordinate, `dz = -w⁻² dw`, so `dz` has a double pole at infinity. -/
@[simp]
theorem order_sphereCoordinateDifferential_infty :
    sphereCoordinateDifferential.order ∞ = (-2 : ℤ) := by
  exact OneForm.order_mvfderiv (by norm_num : (-1 : ℤ) ≠ 0)
    meromorphicOrderAt_affineChart_infty

/-- The differential `dz` is meromorphic everywhere on the sphere. -/
theorem meromorphicAt_sphereCoordinateDifferential (x : OnePoint ℂ) :
    sphereCoordinateDifferential.MeromorphicAt x :=
  OneForm.meromorphicAt_mvfderiv (meromorphicAt_affineChart x)

/-- The differential `dz` has finite order at every point. -/
theorem order_sphereCoordinateDifferential_ne_top (x : OnePoint ℂ) :
    sphereCoordinateDifferential.order x ≠ ⊤ := by
  induction x using OnePoint.rec <;> simp

/-- The divisor of `dz` on the sphere is `-2[∞]`. -/
@[simp]
theorem divisor_sphereCoordinateDifferential :
    sphereCoordinateDifferential.divisor = (-2 : ℤ) • ofPoint (∞ : OnePoint ℂ) := by
  classical
  apply WeilDivisor.ext
  intro x
  rw [OneForm.coeff_divisor meromorphicAt_sphereCoordinateDifferential]
  induction x using OnePoint.rec with
  | infty => simp only [order_sphereCoordinateDifferential_infty, WithTop.untop₀_coe,
      coeff_zsmul, coeff_ofPoint_self, mul_one]
  | coe z => simp only [order_sphereCoordinateDifferential_coe, WithTop.untop₀_zero,
      coeff_zsmul, coeff_ofPoint_of_ne (coe_ne_infty z), mul_zero]

/-- The sphere has the explicit canonical divisor `-2[∞]`. -/
theorem isCanonicalDivisor_neg_two_infty :
    IsCanonicalDivisor ((-2 : ℤ) • ofPoint (∞ : OnePoint ℂ)) := by
  rw [← divisor_sphereCoordinateDifferential]
  exact isCanonicalDivisor_divisor meromorphicAt_sphereCoordinateDifferential
    order_sphereCoordinateDifferential_ne_top

/-- The explicit canonical divisor of the sphere has degree `-2`. -/
theorem degree_divisor_sphereCoordinateDifferential :
    WeilDivisor.degree sphereCoordinateDifferential.divisor = -2 := by
  simp [divisor_sphereCoordinateDifferential, degree_ofPoint]

end TauCeti.RiemannSurface
