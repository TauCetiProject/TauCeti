/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Base change of affine elliptic curves

Mathlib carries ellipticity through `WeierstrassCurve.map`. This module exposes the same instance
for the canonical affine base-change spelling `W⁄A`, so consumers of the point and function-field
base-change APIs do not have to unfold that abbreviation to recover the instance.

This is infrastructure for the base-change lane of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 0.5.
-/

public section

open Polynomial

open _root_.WeierstrassCurve

section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {W : _root_.WeierstrassCurve.Affine R} [W.IsElliptic]

/-- **Base change preserves ellipticity**, in the `(W⁄A).toAffine` spelling used by the affine
point API. -/
instance _root_.WeierstrassCurve.Affine.instIsEllipticBaseChange : (W⁄A).toAffine.IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

end

/-- **The `y`-coordinate is integral over the base ring** once the `x`-coordinate comes from it:
fixing `x` leaves the Weierstrass equation a monic quadratic in `y` with coefficients in the
base. No field or nonsingularity hypothesis is used. -/
theorem isIntegral_y_of_equation_of_mem_range_x {F : Type*} [CommRing F] (W : WeierstrassCurve F)
    {Ω : Type*} [CommRing Ω] [Algebra F Ω] {x y : Ω}
    (heq : (W.baseChange Ω).toAffine.Equation x y) {x₀ : F} (hx : algebraMap F Ω x₀ = x) :
    IsIntegral F y := by
  refine ⟨X ^ 2 + C (W.a₁ * x₀ + W.a₃) * X -
    C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆), by monicity!, ?_⟩
  have h := ((W.baseChange Ω).toAffine.equation_iff' x y).mp heq
  rw [← hx] at h
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, map_add, map_mul,
    map_pow]
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h
  linear_combination h

end
