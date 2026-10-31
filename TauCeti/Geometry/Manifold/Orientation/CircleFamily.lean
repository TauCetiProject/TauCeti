/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.CircleFamily
public import TauCeti.Geometry.Manifold.Orientation.TopForm

/-!
# The orientation of the family of positive-period circles

The total family `C = {(p, x) : p > 0, x ∈ AddCircle p}` (`TauCeti.CircleFamily`) carries the
nowhere-vanishing total form `dp ∧ η` (`TauCeti.CircleFamily.totalForm`), the wedge of the
differential of the period with the time form `η` of the family. Its orientation
`TauCeti.CircleFamily.orientation` is the one on which `dp ∧ η` is positive.

This orientation is compatible with the positive orientations of the individual circles
(`AddCircle.orientation`), on which the time form `dt_p` is positive, and with the real cover.

* **Base followed by fiber.** At a point of the circle of period `p`, a tangent basis whose second
  vector is tangent to that circle, the image of `w ∈ T AddCircle p`, is positive exactly when
  `dp(b₀) * dt_p(w) > 0`. So a basis made of a vector increasing the period followed by a positive
  tangent vector of the circle is positive.
* **The real cover.** The covering map `Q(p, t) = (p, [t]_p)` from `ℝ_{>0} × ℝ` sends a basis
  `(v, w)` to a positive basis exactly when `v.1 * w.2 - w.1 * v.2 > 0`, that is, exactly when
  `(v, w)` is positive for the coordinate orientation `dp ∧ dt` of `ℝ_{>0} × ℝ`.

## Main declarations

* `TauCeti.CircleFamily.orientation`: the orientation of the family on which `dp ∧ η` is positive.
* `TauCeti.CircleFamily.orientation_eq_orientationAt_orientation_iff`: a tangent basis is positive
  exactly when the total form is positive on it.
* `TauCeti.CircleFamily.orientation_eq_orientationAt_orientation_iff_of_mfderiv_mk`: the base
  direction followed by a fiber direction.
* `TauCeti.CircleFamily.orientation_eq_orientationAt_orientation_iff_of_mfderiv_representative`:
  the images of tangent bases of the real cover.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15 (orientations from nonvanishing top forms).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace CircleFamily

/-- The **positive orientation** of the family of positive-period circles: the orientation on which
the nowhere-vanishing total form `dp ∧ η` is positive. -/
protected def orientation : Manifold.Orientation (𝓘(ℝ).prod 𝓘(ℝ)) CircleFamily (Fin 2) :=
  Manifold.Orientation.ofTopForm (by simp) totalForm.1 (totalForm.isSmoothForm.of_le zero_le)
    totalForm_apply_ne_zero

/-- A tangent basis of the family is positive for `TauCeti.CircleFamily.orientation` exactly when
the total form `dp ∧ η` is positive on it. -/
theorem orientation_eq_orientationAt_orientation_iff {z : CircleFamily}
    (b : Module.Basis (Fin 2) ℝ (TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) z)) :
    b.orientation = CircleFamily.orientation.orientationAt z ↔ 0 < totalForm.1 z b :=
  Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff _ _ _ b

/-- A tangent basis is positive for the orientation of the family when it is positive for the
total form, read as a pair of tangent vectors. -/
private theorem orientation_eq_orientationAt_orientation_iff_eval₂ {z : CircleFamily}
    (b : Module.Basis (Fin 2) ℝ (TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) z)) :
    b.orientation = CircleFamily.orientation.orientationAt z ↔
      0 < SmoothBundleForm.eval₂ totalForm z (b 0) (b 1) := by
  have hb : (⇑b : Fin 2 → TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) z) = ![b 0, b 1] := by
    ext i
    fin_cases i <;> rfl
  rw [orientation_eq_orientationAt_orientation_iff, SmoothBundleForm.eval₂_apply, ← hb]

/-- **Base followed by fiber.** At a point `x` of the circle of period `p`, a tangent basis whose
second vector is the image of a tangent vector `w` of `AddCircle p` is positive exactly when
`dp(b₀) * dt_p(w) > 0`. -/
theorem orientation_eq_orientationAt_orientation_iff_of_mfderiv_mk {p : PositivePeriod}
    {x : AddCircle (p : ℝ)} (b : Module.Basis (Fin 2) ℝ (TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) (mk p x)))
    {w : TangentSpace 𝓘(ℝ) x} (hb : b 1 = mfderiv 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (mk p) x w) :
    b.orientation = CircleFamily.orientation.orientationAt (mk p x) ↔
      0 < mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
          fun z : CircleFamily ↦ (z.period : ℝ)) (mk p x) ![b 0] *
        (AddCircle.timeForm (p : ℝ)).1 x ![w] := by
  rw [orientation_eq_orientationAt_orientation_iff_eval₂, hb, eval₂_totalForm_mfderiv_mk]

/-- **The real cover.** The covering map `Q(p, t) = (p, [t]_p)` sends a tangent basis `(v, w)` of
`ℝ_{>0} × ℝ` to a positive basis exactly when `v.1 * w.2 - w.1 * v.2 > 0`, that is, exactly when
`(v, w)` is positive for the coordinate area form `dp ∧ dt`. -/
theorem orientation_eq_orientationAt_orientation_iff_of_mfderiv_representative
    {y : PositivePeriod × ℝ}
    (b : Module.Basis (Fin 2) ℝ (TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) (representative y)))
    {v w : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) y}
    (hv : b 0 = mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) representative y v)
    (hw : b 1 = mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) representative y w) :
    b.orientation = CircleFamily.orientation.orientationAt (representative y) ↔
      0 < v.1 * w.2 - w.1 * v.2 := by
  rw [orientation_eq_orientationAt_orientation_iff_eval₂, hv, hw,
    eval₂_totalForm_mfderiv_representative]

end CircleFamily

end TauCeti
