/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.LieGroup
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Pullback

/-!
# The invariant differential of a complex elliptic curve

On the points `E(ℂ)` of a complex elliptic curve, the local parameter `t = -X / Y`
(`WeierstrassCurve.Projective.Point.localParameter`) is holomorphic wherever `Y ≠ 0`, in particular
near the origin `O = [0 : 1 : 0]`
(`WeierstrassCurve.Projective.Point.contMDiffAt_localParameter_zero`, in
`TauCeti.AlgebraicGeometry.EllipticCurve.Projective.ComplexManifold`). Translating a tangent vector
at `P` to the origin and applying the differential of `t` there gives the normalized invariant
differential `ω` of `E(ℂ)`: at `P` it is the differential of `Q ↦ t (Q - P)`. It is invariant
under translations.

This file only defines `ω` and proves its translation invariance. The results that use the
exponential map are in `TauCeti.Analysis.SpecialFunctions.Elliptic.Exponential`: its pullback
along the exponential map is `dz`
(`WeierstrassCurve.Projective.pullback_invariantDifferential_exp`), it is holomorphic
(`WeierstrassCurve.Projective.holomorphicAt_invariantDifferential`) and vanishes nowhere
(`WeierstrassCurve.Projective.invariantDifferential_ne_zero`), and on affine coordinate
neighbourhoods where `2y + a₁x + a₃ ≠ 0` it is `dx / (2y + a₁x + a₃)`
(`WeierstrassCurve.Projective.invariantDifferential_eq_inv_smul_mvfderiv`).

## Main definitions

* `WeierstrassCurve.Projective.invariantDifferential`: the normalized invariant differential of
  `E(ℂ)`.

## Main results

* `WeierstrassCurve.Projective.invariantDifferential_zero`: at the origin the invariant
  differential is the differential of the local parameter.
* `WeierstrassCurve.Projective.pullback_invariantDifferential_add_right`: translations preserve it.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §III.5 and §IV.1.
-/

public section

open scoped Manifold ContDiff Topology

namespace WeierstrassCurve.Projective

variable (W : Projective ℂ) [W.IsElliptic]

/-- The normalized invariant differential on `E(ℂ)`: translate a tangent vector to the origin
and apply the differential of the local parameter `-X / Y` there. Its pullback along the
exponential map is `dz` (`WeierstrassCurve.Projective.pullback_invariantDifferential_exp`, in
`TauCeti.Analysis.SpecialFunctions.Elliptic.Exponential`). -/
noncomputable def invariantDifferential : TauCeti.RiemannSurface.OneForm W.Point := fun P ↦
  mvfderiv 𝓘(ℂ) (fun Q : W.Point ↦ (Q - P).localParameter) P

/-- At `P`, the invariant differential is the differential of `Q ↦ t (Q - P)`, for the local
parameter `t`. -/
theorem invariantDifferential_apply (P : W.Point) :
    W.invariantDifferential P = mvfderiv 𝓘(ℂ) (fun Q : W.Point ↦ (Q - P).localParameter) P :=
  (rfl)

/-- At the origin, the invariant differential is the differential of the local parameter. -/
theorem invariantDifferential_zero :
    W.invariantDifferential 0 = mvfderiv 𝓘(ℂ) Point.localParameter 0 := by
  simp only [invariantDifferential_apply, sub_zero]

/-- Translation preserves the invariant differential. -/
@[simp]
theorem pullback_invariantDifferential_add_right (P : W.Point) :
    W.invariantDifferential.pullback (fun Q ↦ Q + P) = W.invariantDifferential := by
  funext Q
  apply ContinuousLinearMap.ext
  intro v
  have hplus : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun R : W.Point ↦ R + P) Q :=
    (contMDiff_id.add contMDiff_const).mdifferentiableAt (n := 1) one_ne_zero
  have hsub : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun R : W.Point ↦ (R - (Q + P)).localParameter) (Q + P) :=
    ((Point.contMDiffAt_localParameter_zero (W := W) 1).mdifferentiableAt
      one_ne_zero).comp_of_eq (Q + P)
        ((contMDiff_id.sub contMDiff_const).mdifferentiableAt (n := 1) one_ne_zero)
        (sub_self _)
  have heq : (fun R : W.Point ↦ (R - (Q + P)).localParameter) ∘ (fun R ↦ R + P) =
      fun R ↦ (R - Q).localParameter := by
    funext R
    simp only [Function.comp_apply]
    exact congrArg Point.localParameter (by abel)
  rw [TauCeti.RiemannSurface.OneForm.pullback_apply, invariantDifferential_apply,
    invariantDifferential_apply, ← mvfderiv_comp_apply Q hsub hplus, heq]

end WeierstrassCurve.Projective
