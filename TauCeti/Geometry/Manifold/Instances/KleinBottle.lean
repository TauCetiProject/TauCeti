/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Instances.MappingTorus
public import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# The Klein bottle

The Klein bottle is the quotient of the cylinder `ℝ × S¹` by `(t + 1, z) ∼ (t, conj z)`, the smooth
mapping torus of complex conjugation of the unit circle `S¹ ⊆ ℂ` (`TauCeti.KleinBottle`). Writing
`z = e^{iθ}`, it is `([0, 1] × S¹) / ((1, e^{iθ}) ∼ (0, e^{-iθ}))`. As a smooth mapping torus it is
a smooth surface modelled on `𝓘(ℝ).prod (𝓡 1)`, whose charts are those of the cylinder pushed
forward along the quotient map `(t, z) ↦ [t, z]`, a smooth local diffeomorphism
(`TauCeti.SmoothMappingTorus.isLocalDiffeomorph_uncurry_mk`).

Conjugation is the restriction to the circle of the linear isometry `Complex.conjLIE`
(`TauCeti.conjCircleDiffeomorph`), whose underlying function is `TauCeti.conjSphere`. It fixes
the two points `1` and `-1`, so the orbits of the suspension flow through `[0, 1]` and `[0, -1]`
close up after one turn.

## Main definitions

* `TauCeti.conjCircleDiffeomorph`: complex conjugation of the unit circle.
* `TauCeti.KleinBottle`: the Klein bottle, the mapping torus of `TauCeti.conjCircleDiffeomorph`.
* `TauCeti.KleinBottle.mk`: the class `[t, z]` of a point of the cylinder.

## Main results

* `TauCeti.mfderiv_conjCircleDiffeomorph_one`: conjugation acts by `-1` on the tangent line of the
  circle at its fixed point `1`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

noncomputable section

open Metric Module
open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-- **Complex conjugation of the unit circle** `S¹ ⊆ ℂ`, as a smooth diffeomorphism: the
restriction of the linear isometry `Complex.conjLIE`. -/
abbrev conjCircleDiffeomorph : sphere (0 : ℂ) 1 ≃ₘ⟮𝓡 1, 𝓡 1⟯ sphere (0 : ℂ) 1 :=
  Complex.conjLIE.unitSphereDiffeomorph ∞

/-- As a function, complex conjugation of the unit circle is `TauCeti.conjSphere`. -/
theorem coe_conjCircleDiffeomorph : ⇑conjCircleDiffeomorph = conjSphere :=
  funext fun z ↦ Subtype.ext (by simp)

/-- Complex conjugation fixes the point `1` of the unit circle. -/
@[simp]
theorem conjCircleDiffeomorph_one : conjCircleDiffeomorph 1 = 1 :=
  Subtype.ext (by simp [Metric.unitSphere.coe_one])

/-- Complex conjugation fixes the point `-1` of the unit circle. -/
@[simp]
theorem conjCircleDiffeomorph_neg_one : conjCircleDiffeomorph (-1) = -1 :=
  Subtype.ext (by simp [Metric.unitSphere.coe_one])

/-- **Complex conjugation reverses the tangent line of the circle at its fixed point `1`**: its
differential there is `-1`. Read in `ℂ`, the tangent line at `1` is the imaginary axis, which
conjugation negates. -/
@[simp]
theorem mfderiv_conjCircleDiffeomorph_one (w : TangentSpace (𝓡 1) (1 : sphere (0 : ℂ) 1)) :
    mfderiv (𝓡 1) (𝓡 1) conjCircleDiffeomorph 1 w = -w := by
  have hcoe : ⇑conjCircleDiffeomorph = LinearIsometryEquiv.unitSphereEquiv Complex.conjLIE :=
    LinearIsometryEquiv.coe_unitSphereDiffeomorph _
  rw [hcoe]
  have h := LinearIsometryEquiv.mvfderiv_coe_sphere_unitSphereEquiv (n := 1) (k := 1)
    Complex.conjLIE 1 w
  have hfix : LinearIsometryEquiv.unitSphereEquiv Complex.conjLIE (1 : sphere (0 : ℂ) 1) = 1 :=
    hcoe ▸ conjCircleDiffeomorph_one
  rw [hfix] at h
  -- Read in `ℂ`, the tangent vector `w` at `1` is orthogonal to `1`, so it is imaginary and
  -- conjugation negates it.
  have hw : mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) 1 w ∈
      (ℝ ∙ ((1 : sphere (0 : ℂ) 1) : ℂ))ᗮ :=
    range_mvfderiv_subtypeVal (n := 1) (1 : sphere (0 : ℂ) 1) ▸ LinearMap.mem_range_self _ w
  generalize hz : mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) 1 w = z at h hw
  have hre : z.re = 0 := by
    have := Submodule.mem_orthogonal_singleton_iff_inner_right.1 hw
    rwa [Complex.inner, Metric.unitSphere.coe_one, map_one, mul_one] at this
  apply injective_mvfderiv_subtypeVal_sphere (n := 1) (1 : sphere (0 : ℂ) 1)
  rw [map_neg, hz]
  refine h.trans (Complex.ext ?_ ?_) <;> simp [hre]

/-- The **Klein bottle**: the quotient of the cylinder `ℝ × S¹` by `(t + 1, z) ∼ (t, conj z)`, the
smooth mapping torus of complex conjugation of the unit circle. -/
abbrev KleinBottle : Type :=
  SmoothMappingTorus conjCircleDiffeomorph

namespace KleinBottle

/-- The class `[t, z]` in the Klein bottle of a point `(t, z)` of the cylinder `ℝ × S¹`. -/
abbrev mk (t : ℝ) (z : sphere (0 : ℂ) 1) : KleinBottle :=
  SmoothMappingTorus.mk _ t z

end KleinBottle

end TauCeti
