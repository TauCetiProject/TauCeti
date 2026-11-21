/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.LieGroup
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.LocalParameter
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Pullback

/-!
# The invariant differential of a complex elliptic curve

On the points `E(ℂ)` of a complex elliptic curve, the local parameter `t = -X / Y`
(`WeierstrassCurve.Projective.Point.localParameter`) is holomorphic wherever `Y ≠ 0`, in particular
near the origin `O = [0 : 1 : 0]`. Translating a tangent vector at `P` to the origin and applying
the differential of `t` there gives the normalized invariant differential `ω` of `E(ℂ)`: at `P`
it is the differential of `Q ↦ t (Q - P)`. It is invariant under translations.

Its pullback along the exponential map is `dz`
(`WeierstrassCurve.Projective.pullback_invariantDifferential_exp`), from which it is holomorphic
and vanishes nowhere, and on affine coordinate neighbourhoods it is `dx / (2y + a₁x + a₃)`
(`WeierstrassCurve.Projective.invariantDifferential_eq_inv_smul_mvfderiv`).

## Main definitions

* `WeierstrassCurve.Projective.invariantDifferential`: the normalized invariant differential of
  `E(ℂ)`.

## Main results

* `WeierstrassCurve.Projective.Point.contMDiffAt_localParameter_mk`: the local parameter is
  holomorphic at the points `[X : Y : Z]` with `Y ≠ 0`.
* `WeierstrassCurve.Projective.Point.eventually_contMDiffAt_localParameter` and
  `WeierstrassCurve.Projective.Point.contMDiffAt_localParameter_zero`: in particular it is
  holomorphic near the origin.
* `WeierstrassCurve.Projective.invariantDifferential_zero`: at the origin the invariant
  differential is the differential of the local parameter.
* `WeierstrassCurve.Projective.pullback_invariantDifferential_add`: translations preserve it.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, §III.5 and §IV.1.
-/

public section

open scoped Manifold ContDiff Topology

namespace WeierstrassCurve.Projective

namespace Point

variable {W : Projective ℂ} [W.IsElliptic]

omit [W.IsElliptic] in
/-- Representatives of the same point are proportional, so whether `Y ≠ 0` does not depend on
the representative. -/
private theorem apply_one_ne_zero_of_mk_eq {P Q : Fin 3 → ℂ} {hP : W.NonsingularLift ⟦P⟧}
    {hQ : W.NonsingularLift ⟦Q⟧} (h : Point.mk hQ = Point.mk hP) (hY : P 1 ≠ 0) : Q 1 ≠ 0 := by
  obtain ⟨u, hu⟩ := Quotient.exact (congrArg Point.point h)
  rw [← hu]
  simp [Units.smul_def, hY]

/-- **The local parameter is holomorphic where `Y ≠ 0`.** Near such a point it is `-X / Y` for
holomorphic homogeneous coordinates with `Y ≠ 0`. -/
theorem contMDiffAt_localParameter_mk {P : Fin 3 → ℂ} (hP : W.NonsingularLift ⟦P⟧)
    (hY : P 1 ≠ 0) (r : ℕ∞ω) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) r (localParameter : W.Point → ℂ) (Point.mk hP) := by
  obtain ⟨s, hs, h⟩ := exists_contMDiffAt_mk_eq (Point.mk hP)
  have hY' : s (Point.mk hP) 1 ≠ 0 := apply_one_ne_zero_of_mk_eq h.self_of_nhds.choose_spec hY
  have hd : ContDiffAt ℂ r (fun v : Fin 3 → ℂ ↦ -(v 0 / v 1)) (s (Point.mk hP)) :=
    ((contDiffAt_apply ℂ (fun _ ↦ ℂ) _ _).div (contDiffAt_apply ℂ (fun _ ↦ ℂ) _ _) hY').neg
  refine (hd.comp_contMDiffAt (hs.of_le le_top)).congr_of_eventuallyEq ?_
  filter_upwards [h] with Q ⟨hQ, hQs⟩
  conv_lhs => rw [← hQs]
  rw [localParameter_mk, Function.comp_apply]

/-- **The local parameter is holomorphic near the origin**, where `Y ≠ 0`. -/
theorem eventually_contMDiffAt_localParameter (r : ℕ∞ω) :
    ∀ᶠ P in 𝓝 (0 : W.Point), ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) r (localParameter : W.Point → ℂ) P := by
  obtain ⟨s, hs, h⟩ := exists_contMDiffAt_mk_eq (0 : W.Point)
  -- The coordinates `s 0` represent `[0 : 1 : 0]`, so their `Y`-coordinate is nonzero.
  have hY : s 0 1 ≠ 0 :=
    apply_one_ne_zero_of_mk_eq (h.self_of_nhds.choose_spec.trans zero_def) (by simp)
  filter_upwards [h, ((continuous_apply 1).continuousAt.comp hs.continuousAt).eventually_ne hY]
    with P ⟨hP, hPs⟩ hP1
  rw [← hPs]
  exact contMDiffAt_localParameter_mk _ hP1 r

/-- **The local parameter at the origin is holomorphic there.** -/
theorem contMDiffAt_localParameter_zero (r : ℕ∞ω) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) r (localParameter : W.Point → ℂ) 0 :=
  (eventually_contMDiffAt_localParameter r).self_of_nhds

end Point

variable (W : Projective ℂ) [W.IsElliptic]

/-- The normalized invariant differential on `E(ℂ)`: translate a tangent vector to the origin
and apply the differential of the local parameter `-X / Y` there. Its pullback along the
exponential map is `dz` (`WeierstrassCurve.Projective.pullback_invariantDifferential_exp`). -/
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
theorem pullback_invariantDifferential_add (P : W.Point) :
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
