/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# The Gromov–Lawson bending curve

In the Gromov–Lawson surgery construction, a sphere `S^k` of codimension `q = n - k ≥ 3` in a
Riemannian `n`-manifold `M` of positive scalar curvature is replaced by a handle. Let `r` be the
distance to `S^k`. Inside `M × ℝ`, with the product metric `g + dt²`, one considers the
hypersurface `T = {(x, t) | (r x, t) ∈ γ}` for a curve `γ` in the `(r, t)` half-plane. The curve
starts as the `r`-axis `t = 0`, so that `T` agrees with `M × {0}` away from `S^k`, and bends until
it becomes the vertical line `r = r_∞`, along which `T` is the cylinder `∂(tube of radius r_∞) × ℝ`.

Write `θ` for the angle between the normal of `γ` and the `t`-axis (equivalently, the angle from
the `-r` direction to the tangent of `γ`) and `k` for the curvature of `γ`. Among the principal
curvatures of the distance tube at radius `r`, `q - 1` are `-1/r + O(1)` and the remaining `n - q`
are `O(1)`. With these estimates the Gauss equation gives the scalar curvature of the induced metric
on `T` as `R_M` plus the bending term
`(q - 1) (q - 2) sin² θ / r² - 2 (q - 1) k sin θ / r`
plus an error bounded by `C sin θ (sin θ / r + sin θ + k)` for a constant `C` depending only on the
geometry of the tube, when `k ≥ 0`. So if `R_M ≥ R₀ > 0` on the tube, the induced metric has
positive scalar curvature as soon as the curve satisfies
`0 < R₀ + (q - 1) (q - 2) sin² θ / r² - 2 (q - 1) k sin θ / r - C sin θ (sin θ / r + sin θ + k)`
along its whole length. That curvature computation is not carried out here. This file constructs
the curves, for all `q ≥ 3`, `R₀ > 0`, `C` and every tube radius.

The curve is given by a parametrisation `u ↦ (r u, h u)` with velocity `v u (-cos θ u, sin θ u)`
for a positive speed `v`, so that its curvature is `θ' / v`. The predicate
`TauCeti.IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v` records the shape of the curve and the
inequality above, and `TauCeti.exists_isGromovLawsonBendingCurve` constructs one.

The construction has three stages. First a small-angle bend from `0` to an angle `θ₀`, in which
the curvature is so small that the bending term is dominated by `R₀`; then a straight segment at
angle `θ₀`, along which `r` shrinks; then a final bend from `θ₀` to `π / 2`. In the final bend
`sin θ ≥ sin θ₀` stays bounded below and the curvature is at most a small multiple of
`sin θ / r`, so the negative term `2 (q - 1) k sin θ / r` is dominated by the positive term
`(q - 1) (q - 2) sin² θ / r²`. Since the dominant terms scale like `r⁻²`, the final bend has to
shrink `r` by a factor depending on `θ₀`. Taking the speed proportional to `r` makes this
automatic: `r u = r₁ exp (-∫₀ᵘ w cos θ)` for a positive weight `w`, which stays positive however
far the curve bends.

## Main definitions

* `TauCeti.IsGromovLawsonBendingCurve`: a Gromov–Lawson bending curve.

## Main results

* `TauCeti.exists_isGromovLawsonBendingCurve`: a Gromov–Lawson bending curve exists for every
  codimension `q ≥ 3`, lower bound `R₀ > 0`, error constant `C` and tube radius `r₀ > 0`.
* `TauCeti.IsGromovLawsonBendingCurve.mono`: a bending curve for some constants is one for a
  larger lower bound, a smaller error constant and a larger tube radius.
* `TauCeti.IsGromovLawsonBendingCurve.exists_radius_eq`: a bending curve ends in a vertical line
  `r = ρ` with `0 < ρ < r₀`.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A.
* J. Rosenberg, S. Stolz, *Metrics of positive scalar curvature and connections with surgery*,
  Surveys on surgery theory, Vol. 2, Ann. of Math. Stud. 149 (2001), 353–386, Section 3.
-/

public section

noncomputable section

open Real Set Filter
open scoped ContDiff

namespace TauCeti

/-- `IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v` states that `u ↦ (r u, h u)` is a
Gromov–Lawson bending curve in the half-plane of the distance `r > 0` to a core sphere of
codimension `q` and the cylinder coordinate `h`: its velocity is `v u (-cos θ u, sin θ u)` for a
smooth speed `v > 0` and a smooth nondecreasing angle `θ`. For `u ≤ 0` it runs along the `r`-axis,
from `r = ∞` down to the radius `r 0 < r₀`, so it only bends inside the tube of radius `r₀`;
eventually it is a vertical line `θ = π / 2` traversed upwards. Along the whole curve, with
curvature `k = θ' / v`,
`0 < R₀ + (q - 1) (q - 2) sin² θ / r² - 2 (q - 1) k sin θ / r - C sin θ (sin θ / r + sin θ + k)`.
This is the inequality which, as explained in the module docstring, makes the hypersurface swept
out by the curve have positive scalar curvature when the ambient scalar curvature is at least `R₀`
on the tube of radius `r₀` and `C` controls the principal curvature errors of the tube. -/
structure IsGromovLawsonBendingCurve (q : ℕ) (R₀ C r₀ : ℝ) (r h θ v : ℝ → ℝ) : Prop where
  contDiff_angle : ContDiff ℝ ∞ θ
  contDiff_speed : ContDiff ℝ ∞ v
  speed_pos (u : ℝ) : 0 < v u
  hasDerivAt_radius (u : ℝ) : HasDerivAt r (-(v u * cos (θ u))) u
  hasDerivAt_height (u : ℝ) : HasDerivAt h (v u * sin (θ u)) u
  monotone_angle : Monotone θ
  angle_of_nonpos {u : ℝ} (hu : u ≤ 0) : θ u = 0
  height_of_nonpos {u : ℝ} (hu : u ≤ 0) : h u = 0
  radius_pos (u : ℝ) : 0 < r u
  radius_zero_lt : r 0 < r₀
  tendsto_radius_atBot : Tendsto r atBot atTop
  exists_angle_eq : ∃ b, ∀ u, b ≤ u → θ u = π / 2
  tendsto_height_atTop : Tendsto h atTop atTop
  scalar_pos (u : ℝ) :
    0 < R₀ + ((q : ℝ) - 1) * ((q : ℝ) - 2) * sin (θ u) ^ 2 / r u ^ 2
      - 2 * ((q : ℝ) - 1) * (deriv θ u / v u) * sin (θ u) / r u
      - C * sin (θ u) * (sin (θ u) / r u + sin (θ u) + deriv θ u / v u)

namespace IsGromovLawsonBendingCurve

variable {q : ℕ} {R₀ C r₀ : ℝ} {r h θ v : ℝ → ℝ}

/-- The radius of a bending curve is smooth. -/
theorem contDiff_radius (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) :
    ContDiff ℝ ∞ r := by
  have hd : deriv r = fun u ↦ -(v u * cos (θ u)) :=
    funext fun u ↦ (hγ.hasDerivAt_radius u).deriv
  exact contDiff_infty_iff_deriv.2 ⟨fun u ↦ (hγ.hasDerivAt_radius u).differentiableAt,
    hd ▸ (hγ.contDiff_speed.mul (contDiff_cos.comp hγ.contDiff_angle)).neg⟩

/-- The height of a bending curve is smooth. -/
theorem contDiff_height (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) :
    ContDiff ℝ ∞ h := by
  have hd : deriv h = fun u ↦ v u * sin (θ u) :=
    funext fun u ↦ (hγ.hasDerivAt_height u).deriv
  exact contDiff_infty_iff_deriv.2 ⟨fun u ↦ (hγ.hasDerivAt_height u).differentiableAt,
    hd ▸ hγ.contDiff_speed.mul (contDiff_sin.comp hγ.contDiff_angle)⟩

/-- The angle of a bending curve is nonnegative. -/
theorem angle_nonneg (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) (u : ℝ) : 0 ≤ θ u :=
  hγ.angle_of_nonpos (min_le_right u 0) ▸ hγ.monotone_angle (min_le_left u 0)

/-- The angle of a bending curve is at most `π / 2`. -/
theorem angle_le_pi_div_two (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) (u : ℝ) :
    θ u ≤ π / 2 := by
  obtain ⟨b, hb⟩ := hγ.exists_angle_eq
  exact hb _ (le_max_right u b) ▸ hγ.monotone_angle (le_max_left u b)

/-- The curvature `θ' / v` of a bending curve is nonnegative. -/
theorem deriv_angle_div_speed_nonneg (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v)
    (u : ℝ) : 0 ≤ deriv θ u / v u :=
  div_nonneg hγ.monotone_angle.deriv_nonneg (hγ.speed_pos u).le

/-- The radius of a bending curve is nonincreasing. -/
theorem antitone_radius (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) : Antitone r := by
  refine antitone_of_deriv_nonpos (fun u ↦ (hγ.hasDerivAt_radius u).differentiableAt) fun u ↦ ?_
  rw [(hγ.hasDerivAt_radius u).deriv, neg_nonpos]
  exact mul_nonneg (hγ.speed_pos u).le <| cos_nonneg_of_mem_Icc
    ⟨by linarith [hγ.angle_nonneg u, pi_pos], hγ.angle_le_pi_div_two u⟩

/-- A point of a bending curve outside the tube of radius `r₀` lies on the initial horizontal
part `u < 0`. -/
theorem neg_of_le_radius (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) {u : ℝ}
    (hu : r₀ ≤ r u) : u < 0 := by
  by_contra! h0
  exact (hγ.radius_zero_lt.trans_le hu).not_ge (hγ.antitone_radius h0)

/-- A bending curve ends in a vertical line `r = ρ`, traversed upwards, for some radius
`0 < ρ < r₀`. -/
theorem exists_radius_eq (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) :
    ∃ b ρ, 0 < ρ ∧ ρ < r₀ ∧ ∀ u, b ≤ u → θ u = π / 2 ∧ r u = ρ := by
  obtain ⟨b, hb⟩ := hγ.exists_angle_eq
  refine ⟨max b 0, r (max b 0), hγ.radius_pos _,
    (hγ.antitone_radius (le_max_right b 0)).trans_lt hγ.radius_zero_lt, fun u hu ↦
      ⟨hb u ((le_max_left b 0).trans hu), ?_⟩⟩
  refine constant_of_has_deriv_right_zero (hγ.contDiff_radius.continuous.continuousOn)
    (fun x hx ↦ ?_) u ⟨hu, le_rfl⟩
  have hx : θ x = π / 2 := hb x ((le_max_left b 0).trans hx.1)
  simpa [hx] using (hγ.hasDerivAt_radius x).hasDerivWithinAt

/-- A bending curve for the constants `R₀`, `C` and `r₀` is also one for a larger lower bound
`R₀'`, a smaller error constant `C'` and a larger tube radius `r₀'`. -/
theorem mono (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) {R₀' C' r₀' : ℝ}
    (hR : R₀ ≤ R₀') (hC : C' ≤ C) (hr : r₀ ≤ r₀') :
    IsGromovLawsonBendingCurve q R₀' C' r₀' r h θ v :=
  { hγ with
    radius_zero_lt := hγ.radius_zero_lt.trans_le hr
    scalar_pos u := by
      have hs : 0 ≤ sin (θ u) := sin_nonneg_of_nonneg_of_le_pi (hγ.angle_nonneg u)
        (by linarith [hγ.angle_le_pi_div_two u, pi_pos])
      have := mul_nonneg (sub_nonneg.2 hC) (mul_nonneg hs (add_nonneg (add_nonneg
        (div_nonneg hs (hγ.radius_pos u).le) hs) (hγ.deriv_angle_div_speed_nonneg u)))
      nlinarith [hγ.scalar_pos u] }

end IsGromovLawsonBendingCurve

/-! ### The construction -/

/-- The quadratic inequality behind the bending curve: for `r` small compared to `1 / C`, the
bending inequality follows from `3 m k s / r < R₀ + m (m - 1) s² / (2 r²)`, where `m = q - 1`. -/
private theorem bending_pos {q R₀ C r s k : ℝ} (hq : 3 ≤ q) (hC : 0 ≤ C) (hr : 0 < r)
    (hCr : 2 * (C + 1) * r ≤ 1) (hs : 0 ≤ s) (hk : 0 ≤ k)
    (h : 3 * (q - 1) * k * s / r < R₀ + (q - 1) * (q - 2) * s ^ 2 / (2 * r ^ 2)) :
    0 < R₀ + (q - 1) * (q - 2) * s ^ 2 / r ^ 2 - 2 * (q - 1) * k * s / r
      - C * s * (s / r + s + k) := by
  set x := r⁻¹ with hx_def
  have hx : 2 * (C + 1) ≤ x :=
    calc 2 * (C + 1) = 2 * (C + 1) * r * x := by rw [hx_def, mul_inv_cancel_right₀ hr.ne']
      _ ≤ 1 * x := by gcongr
      _ = x := one_mul x
  have hxr : ∀ a : ℝ, a / r = a * x := fun a ↦ by rw [div_eq_mul_inv]
  have hxr2 : ∀ a : ℝ, a / r ^ 2 = a * x ^ 2 := fun a ↦ by rw [div_eq_mul_inv, inv_pow]
  have hxr2' : ∀ a : ℝ, a / (2 * r ^ 2) = a * x ^ 2 / 2 := fun a ↦ by
    rw [mul_comm, ← div_div, hxr2]
  rw [hxr, hxr2'] at h
  rw [hxr, hxr2, hxr]
  have hA : 0 ≤ (q - 1) * (q - 2) * x ^ 2 / 2 - C * x - C := by
    nlinarith [mul_le_mul_of_nonneg_left hx (by linarith : (0 : ℝ) ≤ x),
      mul_nonneg (by nlinarith : (0 : ℝ) ≤ (q - 1) * (q - 2) - 2) (sq_nonneg x)]
  have hB : 0 ≤ (q - 1) * x - C := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg s) hA, mul_nonneg (mul_nonneg hk hs) hB]

/-- The angle of the constructed bending curve: a smooth step from `0` to `θ₀` on `[0, 1]`,
followed by a smooth step from `θ₀` to `π / 2` on `[2, 3]`. -/
private def bendAngle (θ₀ u : ℝ) : ℝ :=
  θ₀ * smoothTransition u + (π / 2 - θ₀) * smoothTransition (u - 2)

/-- The weight of the constructed bending curve, the ratio of its speed to its radius: `1` up to
`u = 1` and `W` from `u = 2`. -/
private def bendWeight (W u : ℝ) : ℝ :=
  1 + (W - 1) * smoothTransition (u - 1)

/-- The logarithm of `r₁ / r` along the constructed bending curve. -/
private def bendLogRadius (θ₀ W u : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..u, bendWeight W τ * cos (bendAngle θ₀ τ)

/-- The radius of the constructed bending curve. -/
private def bendRadius (r₁ θ₀ W u : ℝ) : ℝ :=
  r₁ * exp (-bendLogRadius θ₀ W u)

/-- The speed of the constructed bending curve, proportional to its radius. -/
private def bendSpeed (r₁ θ₀ W u : ℝ) : ℝ :=
  bendWeight W u * bendRadius r₁ θ₀ W u

/-- The height of the constructed bending curve. -/
private def bendHeight (r₁ θ₀ W u : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..u, bendSpeed r₁ θ₀ W τ * sin (bendAngle θ₀ τ)

section Construction

variable {r₁ θ₀ W : ℝ}

private theorem contDiff_bendAngle : ContDiff ℝ ∞ (bendAngle θ₀) :=
  (contDiff_const.mul smoothTransition.contDiff).add
    (contDiff_const.mul (smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)))

private theorem hasDerivAt_bendAngle (u : ℝ) :
    HasDerivAt (bendAngle θ₀)
      (θ₀ * deriv smoothTransition u + (π / 2 - θ₀) * deriv smoothTransition (u - 2)) u := by
  have hd := (smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
  exact ((hd u).hasDerivAt.const_mul θ₀).add
    (((hd (u - 2)).hasDerivAt.comp_sub_const u 2).const_mul _)

private theorem bendAngle_of_nonpos {u : ℝ} (hu : u ≤ 0) : bendAngle θ₀ u = 0 := by
  simp [bendAngle, smoothTransition.zero_of_nonpos hu,
    smoothTransition.zero_of_nonpos (by linarith : u - 2 ≤ 0)]

private theorem bendAngle_of_le_two {u : ℝ} (hu : u ≤ 2) :
    bendAngle θ₀ u = θ₀ * smoothTransition u := by
  simp [bendAngle, smoothTransition.zero_of_nonpos (by linarith : u - 2 ≤ 0)]

private theorem bendAngle_of_three_le {u : ℝ} (hu : 3 ≤ u) : bendAngle θ₀ u = π / 2 := by
  simp only [bendAngle, smoothTransition.one_of_one_le (by linarith : 1 ≤ u),
    smoothTransition.one_of_one_le (by linarith : 1 ≤ u - 2)]
  ring

private theorem bendAngle_nonneg (h₀ : 0 ≤ θ₀) (h₁ : θ₀ ≤ π / 2) (u : ℝ) :
    0 ≤ bendAngle θ₀ u :=
  add_nonneg (mul_nonneg h₀ (smoothTransition.nonneg _))
    (mul_nonneg (by linarith) (smoothTransition.nonneg _))

private theorem bendAngle_le (h₀ : 0 ≤ θ₀) (h₁ : θ₀ ≤ π / 2) (u : ℝ) :
    bendAngle θ₀ u ≤ π / 2 := by
  have := mul_le_of_le_one_right h₀ (smoothTransition.le_one u)
  have := mul_le_of_le_one_right (by linarith : 0 ≤ π / 2 - θ₀) (smoothTransition.le_one (u - 2))
  rw [bendAngle]
  linarith

private theorem le_bendAngle (h₁ : θ₀ ≤ π / 2) {u : ℝ} (hu : 2 ≤ u) : θ₀ ≤ bendAngle θ₀ u := by
  rw [bendAngle, smoothTransition.one_of_one_le (by linarith : 1 ≤ u)]
  nlinarith [mul_nonneg (by linarith : 0 ≤ π / 2 - θ₀) (smoothTransition.nonneg (u - 2))]

private theorem cos_bendAngle_nonneg (h₀ : 0 ≤ θ₀) (h₁ : θ₀ ≤ π / 2) (u : ℝ) :
    0 ≤ cos (bendAngle θ₀ u) :=
  cos_nonneg_of_mem_Icc ⟨by linarith [bendAngle_nonneg h₀ h₁ u, pi_pos], bendAngle_le h₀ h₁ u⟩

private theorem contDiff_bendWeight : ContDiff ℝ ∞ (bendWeight W) :=
  contDiff_const.add
    (contDiff_const.mul (smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)))

private theorem bendWeight_of_le_one {u : ℝ} (hu : u ≤ 1) : bendWeight W u = 1 := by
  simp [bendWeight, smoothTransition.zero_of_nonpos (by linarith : u - 1 ≤ 0)]

private theorem bendWeight_of_two_le {u : ℝ} (hu : 2 ≤ u) : bendWeight W u = W := by
  simp [bendWeight, smoothTransition.one_of_one_le (by linarith : 1 ≤ u - 1)]

private theorem one_le_bendWeight (hW : 1 ≤ W) (u : ℝ) : 1 ≤ bendWeight W u := by
  rw [bendWeight]
  nlinarith [mul_nonneg (by linarith : 0 ≤ W - 1) (smoothTransition.nonneg (u - 1))]

private theorem continuous_bendLogRadius_integrand :
    Continuous fun τ ↦ bendWeight W τ * cos (bendAngle θ₀ τ) :=
  contDiff_bendWeight.continuous.mul (continuous_cos.comp contDiff_bendAngle.continuous)

private theorem hasDerivAt_bendLogRadius (u : ℝ) :
    HasDerivAt (bendLogRadius θ₀ W) (bendWeight W u * cos (bendAngle θ₀ u)) u :=
  (continuous_bendLogRadius_integrand.integral_hasStrictDerivAt 0 u).hasDerivAt

private theorem contDiff_bendLogRadius : ContDiff ℝ ∞ (bendLogRadius θ₀ W) := by
  have hd : deriv (bendLogRadius θ₀ W) = fun u ↦ bendWeight W u * cos (bendAngle θ₀ u) :=
    funext fun u ↦ (hasDerivAt_bendLogRadius u).deriv
  exact contDiff_infty_iff_deriv.2 ⟨fun u ↦ (hasDerivAt_bendLogRadius u).differentiableAt,
    hd ▸ contDiff_bendWeight.mul (contDiff_cos.comp contDiff_bendAngle)⟩

private theorem bendLogRadius_of_nonpos {u : ℝ} (hu : u ≤ 0) : bendLogRadius θ₀ W u = u := by
  rw [bendLogRadius, intervalIntegral.integral_congr (g := fun _ ↦ (1 : ℝ)),
    intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  intro τ hτ
  rw [uIcc_of_ge hu] at hτ
  simp [bendWeight_of_le_one (by linarith [hτ.2] : τ ≤ 1), bendAngle_of_nonpos hτ.2]

private theorem bendLogRadius_nonneg (h₀ : 0 ≤ θ₀) (h₁ : θ₀ ≤ π / 2) (hW : 1 ≤ W) {u : ℝ}
    (hu : 0 ≤ u) : 0 ≤ bendLogRadius θ₀ W u :=
  intervalIntegral.integral_nonneg hu fun τ _ ↦
    mul_nonneg (by linarith [one_le_bendWeight hW τ]) (cos_bendAngle_nonneg h₀ h₁ τ)

private theorem bendLogRadius_le_one {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) :
    bendLogRadius θ₀ W u ≤ 1 := by
  calc bendLogRadius θ₀ W u ≤ ∫ _ in (0 : ℝ)..u, (1 : ℝ) := by
        refine intervalIntegral.integral_mono_on hu₀
          (continuous_bendLogRadius_integrand.intervalIntegrable _ _) intervalIntegrable_const
          fun τ hτ ↦ ?_
        rw [bendWeight_of_le_one (hτ.2.trans hu₁), one_mul]
        exact cos_le_one _
    _ ≤ 1 := by simpa using hu₁

private theorem bendLogRadius_of_three_le {u : ℝ} (hu : 3 ≤ u) :
    bendLogRadius θ₀ W u = bendLogRadius θ₀ W 3 := by
  rw [bendLogRadius, ← intervalIntegral.integral_add_adjacent_intervals (b := 3)
    (continuous_bendLogRadius_integrand.intervalIntegrable _ _)
    (continuous_bendLogRadius_integrand.intervalIntegrable _ _),
    intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) (a := 3), intervalIntegral.integral_zero,
    add_zero, bendLogRadius]
  intro τ hτ
  rw [uIcc_of_le hu] at hτ
  simp [bendAngle_of_three_le hτ.1]

private theorem hasDerivAt_bendRadius (u : ℝ) :
    HasDerivAt (bendRadius r₁ θ₀ W) (-(bendSpeed r₁ θ₀ W u * cos (bendAngle θ₀ u))) u := by
  refine (((hasDerivAt_bendLogRadius u).neg.exp).const_mul r₁).congr_deriv ?_
  simp only [bendSpeed, bendRadius, Pi.neg_apply]
  ring

private theorem bendRadius_pos (hr₁ : 0 < r₁) (u : ℝ) : 0 < bendRadius r₁ θ₀ W u :=
  mul_pos hr₁ (exp_pos _)

private theorem contDiff_bendSpeed : ContDiff ℝ ∞ (bendSpeed r₁ θ₀ W) :=
  contDiff_bendWeight.mul (contDiff_const.mul contDiff_bendLogRadius.neg.exp)

private theorem continuous_bendHeight_integrand :
    Continuous fun τ ↦ bendSpeed r₁ θ₀ W τ * sin (bendAngle θ₀ τ) :=
  contDiff_bendSpeed.continuous.mul (continuous_sin.comp contDiff_bendAngle.continuous)

private theorem bendHeight_of_nonpos {u : ℝ} (hu : u ≤ 0) : bendHeight r₁ θ₀ W u = 0 := by
  rw [bendHeight, intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)),
    intervalIntegral.integral_zero]
  intro τ hτ
  rw [uIcc_of_ge hu] at hτ
  simp [bendAngle_of_nonpos hτ.2]

private theorem bendHeight_of_three_le {u : ℝ} (hu : 3 ≤ u) :
    bendHeight r₁ θ₀ W u = bendHeight r₁ θ₀ W 3 + (u - 3) * (W * bendRadius r₁ θ₀ W 3) := by
  rw [bendHeight, ← intervalIntegral.integral_add_adjacent_intervals (b := 3)
    (continuous_bendHeight_integrand.intervalIntegrable _ _)
    (continuous_bendHeight_integrand.intervalIntegrable _ _),
    intervalIntegral.integral_congr (g := fun _ ↦ W * bendRadius r₁ θ₀ W 3) (a := 3),
    intervalIntegral.integral_const, smul_eq_mul, bendHeight]
  intro τ hτ
  rw [uIcc_of_le hu] at hτ
  simp [bendSpeed, bendRadius, bendAngle_of_three_le hτ.1,
    bendWeight_of_two_le (by linarith [hτ.1] : 2 ≤ τ), bendLogRadius_of_three_le hτ.1]

private theorem monotone_bendAngle (h₀ : 0 ≤ θ₀) (h₁ : θ₀ ≤ π / 2) : Monotone (bendAngle θ₀) :=
  monotone_of_deriv_nonneg (fun u ↦ (hasDerivAt_bendAngle u).differentiableAt) fun u ↦ by
    rw [(hasDerivAt_bendAngle u).deriv]
    exact add_nonneg (mul_nonneg h₀ smoothTransition.monotone.deriv_nonneg)
      (mul_nonneg (by linarith) smoothTransition.monotone.deriv_nonneg)

private theorem bendRadius_zero : bendRadius r₁ θ₀ W 0 = r₁ := by
  simp [bendRadius, bendLogRadius]

private theorem bendRadius_le (hr₁ : 0 < r₁) (h₀ : 0 ≤ θ₀) (h₁ : θ₀ ≤ π / 2) (hW : 1 ≤ W)
    {u : ℝ} (hu : 0 ≤ u) : bendRadius r₁ θ₀ W u ≤ r₁ :=
  mul_le_of_le_one_right hr₁.le
    (exp_le_one_iff.2 (neg_nonpos.2 (bendLogRadius_nonneg h₀ h₁ hW hu)))

private theorem tendsto_bendRadius_atBot (hr₁ : 0 < r₁) :
    Tendsto (bendRadius r₁ θ₀ W) atBot atTop := by
  refine Tendsto.congr' ?_
    ((tendsto_exp_atTop.comp tendsto_neg_atBot_atTop).const_mul_atTop hr₁)
  filter_upwards [eventually_le_atBot 0] with u hu
  simp [bendRadius, bendLogRadius_of_nonpos hu]

private theorem tendsto_bendHeight_atTop (hr₁ : 0 < r₁) (hW : 1 ≤ W) :
    Tendsto (bendHeight r₁ θ₀ W) atTop atTop := by
  have hc : 0 < W * bendRadius r₁ θ₀ W 3 := mul_pos (by linarith) (bendRadius_pos hr₁ 3)
  refine tendsto_atTop_atTop.2 fun b ↦ ⟨max 3 (3 + (b - bendHeight r₁ θ₀ W 3) /
    (W * bendRadius r₁ θ₀ W 3)), fun a ha ↦ ?_⟩
  rw [bendHeight_of_three_le (le_of_max_le_left ha)]
  have := (div_le_iff₀ hc).1 (le_sub_iff_add_le'.2 (le_of_max_le_right ha))
  linarith

/-- The first stage: during the small-angle bend `[0, 1]` the bending term is at most `R₀ / 2`. -/
private theorem bend_first_le {q R₀ K : ℝ} (hq : 3 ≤ q) (hR₀ : 0 ≤ R₀) (hr₁ : 0 < r₁)
    (h₀ : 0 ≤ θ₀) (h₁ : θ₀ ≤ π / 2) (hK : ∀ x, deriv smoothTransition x ≤ K)
    (hθ₀ : 6 * (q - 1) * K * θ₀ ≤ R₀ * (r₁ * exp (-1)) ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    3 * (q - 1) * (θ₀ * deriv smoothTransition u / bendSpeed r₁ θ₀ W u)
      * sin (bendAngle θ₀ u) / bendRadius r₁ θ₀ W u ≤ R₀ / 2 := by
  have hR := bendRadius_pos hr₁ (θ₀ := θ₀) (W := W) u
  have ha := smoothTransition.monotone.deriv_nonneg (x := u)
  rcases le_or_gt u 1 with hu₁ | hu₁
  · have hρ : r₁ * exp (-1) ≤ bendRadius r₁ θ₀ W u :=
      mul_le_mul_of_nonneg_left (exp_le_exp.2 (neg_le_neg (bendLogRadius_le_one hu hu₁)))
        hr₁.le
    have hs₀ : 0 ≤ sin (bendAngle θ₀ u) :=
      sin_nonneg_of_nonneg_of_le_pi (bendAngle_nonneg h₀ h₁ u)
        (by linarith [bendAngle_le h₀ h₁ u, pi_pos])
    have has : deriv smoothTransition u * sin (bendAngle θ₀ u) ≤ K := by
      nlinarith [hK u, sin_le_one (bendAngle θ₀ u)]
    have hL : 3 * (q - 1) * (θ₀ * deriv smoothTransition u / bendSpeed r₁ θ₀ W u)
        * sin (bendAngle θ₀ u) / bendRadius r₁ θ₀ W u =
        3 * (q - 1) * θ₀ * (deriv smoothTransition u * sin (bendAngle θ₀ u)) /
          bendRadius r₁ θ₀ W u ^ 2 := by
      rw [bendSpeed, bendWeight_of_le_one hu₁]
      field_simp
    rw [hL, div_le_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left has (by nlinarith : 0 ≤ 3 * (q - 1) * θ₀)
    have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hρ 2) hR₀
    nlinarith
  · rw [smoothTransition.deriv_of_one_lt hu₁]
    simp only [mul_zero, zero_div, zero_mul]
    linarith

/-- The final bend: from `u = 2` on, the bending term is at most the positive term
`(q - 1) (q - 2) sin² θ / (2 r²)`. -/
private theorem bend_second_le {q K : ℝ} (hq : 3 ≤ q) (hr₁ : 0 < r₁) (h₀ : 0 < θ₀)
    (h₁ : θ₀ ≤ π / 2) (hW : 1 ≤ W) (hK : ∀ x, deriv smoothTransition x ≤ K)
    (hWθ₀ : 3 * π * K ≤ W * sin θ₀) (u : ℝ) :
    3 * (q - 1) * ((π / 2 - θ₀) * deriv smoothTransition (u - 2) / bendSpeed r₁ θ₀ W u)
      * sin (bendAngle θ₀ u) / bendRadius r₁ θ₀ W u ≤
      (q - 1) * (q - 2) * sin (bendAngle θ₀ u) ^ 2 / (2 * bendRadius r₁ θ₀ W u ^ 2) := by
  have hR := bendRadius_pos hr₁ (θ₀ := θ₀) (W := W) u
  have hs₀ : 0 ≤ sin (bendAngle θ₀ u) :=
    sin_nonneg_of_nonneg_of_le_pi (bendAngle_nonneg h₀.le h₁ u)
      (by linarith [bendAngle_le h₀.le h₁ u, pi_pos])
  have hq₂ : 0 ≤ (q - 1) * (q - 2) := by nlinarith
  rcases lt_or_ge u 2 with hu | hu
  · rw [smoothTransition.deriv_of_neg (by linarith)]
    simp only [mul_zero, zero_div, zero_mul]
    positivity
  have hb := smoothTransition.monotone.deriv_nonneg (x := u - 2)
  have hs : sin θ₀ ≤ sin (bendAngle θ₀ u) :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (bendAngle_le h₀.le h₁ u)
      (le_bendAngle h₁ hu)
  have key : 6 * ((π / 2 - θ₀) * deriv smoothTransition (u - 2)) ≤
      (q - 2) * (W * sin (bendAngle θ₀ u)) := by
    nlinarith [mul_le_mul_of_nonneg_left (hK (u - 2)) (by linarith : 0 ≤ π / 2 - θ₀),
      mul_le_mul_of_nonneg_right (by linarith : π / 2 - θ₀ ≤ π / 2) (hb.trans (hK (u - 2))),
      mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ W),
      mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ q - 2)
        (mul_nonneg (by linarith : 0 ≤ W) hs₀)]
  have hL : 3 * (q - 1) * ((π / 2 - θ₀) * deriv smoothTransition (u - 2) /
      bendSpeed r₁ θ₀ W u) * sin (bendAngle θ₀ u) / bendRadius r₁ θ₀ W u =
      3 * (q - 1) * ((π / 2 - θ₀) * deriv smoothTransition (u - 2)) * sin (bendAngle θ₀ u) /
        (W * bendRadius r₁ θ₀ W u ^ 2) := by
    rw [bendSpeed, bendWeight_of_two_le hu]
    field_simp
  rw [hL, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left key
    (mul_nonneg (mul_nonneg (by linarith : 0 ≤ q - 1) hs₀) (sq_nonneg (bendRadius r₁ θ₀ W u)))
  nlinarith

/-- The constructed curve satisfies the bending inequality. -/
private theorem bend_scalar_pos {q R₀ C K : ℝ} (hq : 3 ≤ q) (hR₀ : 0 < R₀) (hC : 0 ≤ C)
    (hr₁ : 0 < r₁) (hCr₁ : 2 * (C + 1) * r₁ ≤ 1) (h₀ : 0 < θ₀) (h₁ : θ₀ ≤ π / 2) (hW : 1 ≤ W)
    (hK : ∀ x, deriv smoothTransition x ≤ K)
    (hθ₀ : 6 * (q - 1) * K * θ₀ ≤ R₀ * (r₁ * exp (-1)) ^ 2) (hWθ₀ : 3 * π * K ≤ W * sin θ₀)
    (u : ℝ) :
    0 < R₀ + (q - 1) * (q - 2) * sin (bendAngle θ₀ u) ^ 2 / bendRadius r₁ θ₀ W u ^ 2
      - 2 * (q - 1) * (deriv (bendAngle θ₀) u / bendSpeed r₁ θ₀ W u) * sin (bendAngle θ₀ u)
        / bendRadius r₁ θ₀ W u
      - C * sin (bendAngle θ₀ u) * (sin (bendAngle θ₀ u) / bendRadius r₁ θ₀ W u
        + sin (bendAngle θ₀ u) + deriv (bendAngle θ₀) u / bendSpeed r₁ θ₀ W u) := by
  rcases lt_or_ge u 0 with hu | hu
  · simp [bendAngle_of_nonpos hu.le, hR₀]
  have hR := bendRadius_pos hr₁ (θ₀ := θ₀) (W := W) u
  have hv : 0 < bendSpeed r₁ θ₀ W u := mul_pos (by linarith [one_le_bendWeight hW u]) hR
  have hs₀ : 0 ≤ sin (bendAngle θ₀ u) :=
    sin_nonneg_of_nonneg_of_le_pi (bendAngle_nonneg h₀.le h₁ u)
      (by linarith [bendAngle_le h₀.le h₁ u, pi_pos])
  have hk : 0 ≤ deriv (bendAngle θ₀) u / bendSpeed r₁ θ₀ W u :=
    div_nonneg (monotone_bendAngle h₀.le h₁).deriv_nonneg hv.le
  refine bending_pos hq hC hR ((mul_le_mul_of_nonneg_left (bendRadius_le hr₁ h₀.le h₁ hW hu)
    (by positivity)).trans hCr₁) hs₀ hk ?_
  rw [(hasDerivAt_bendAngle u).deriv, add_div, mul_add, add_mul, add_div]
  linarith [bend_first_le (W := W) hq hR₀.le hr₁ h₀.le h₁ hK hθ₀ hu,
    bend_second_le hq hr₁ h₀ h₁ hW hK hWθ₀ u]

end Construction

/-- **The Gromov–Lawson bending curve.** For every codimension `q ≥ 3`, lower bound `R₀ > 0` for
the ambient scalar curvature, error constant `C` and tube radius `r₀ > 0` there is a bending
curve: a smooth curve in the `(r, t)` half-plane which is the `r`-axis outside the tube of radius
`r₀`, ends in a vertical line, and along which
`0 < R₀ + (q - 1) (q - 2) sin² θ / r² - 2 (q - 1) k sin θ / r - C sin θ (sin θ / r + sin θ + k)`. -/
theorem exists_isGromovLawsonBendingCurve {q : ℕ} (hq : 3 ≤ q) {R₀ r₀ : ℝ} (hR₀ : 0 < R₀)
    (C : ℝ) (hr₀ : 0 < r₀) :
    ∃ r h θ v : ℝ → ℝ, IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v := by
  -- It suffices to treat `C ≥ 0`: a larger error constant gives a stronger inequality.
  wlog hC : 0 ≤ C generalizing C
  · obtain ⟨r, h, θ, v, hγ⟩ := this (max C 0) (le_max_right _ _)
    exact ⟨r, h, θ, v, hγ.mono le_rfl (le_max_left _ _) le_rfl⟩
  -- The construction bends by a small angle `θ₀` with curvature so small that the bending term
  -- stays below `R₀ / 2`, runs straight at the angle `θ₀`, and bends to `π / 2` with curvature
  -- at most `sin θ₀ / (6 r)`, where `(q - 1) (q - 2) sin² θ / r²` dominates.
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  -- A bound `K` for the derivative of the smooth transition function.
  obtain ⟨K₀, hK₀⟩ := ((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl)
    |>.bounded_above_of_compact_support smoothTransition.hasCompactSupport_deriv
  set K := max K₀ 1
  have hK : ∀ x, deriv smoothTransition x ≤ K := fun x ↦
    (le_abs_self _).trans (((Real.norm_eq_abs _).symm.trans_le (hK₀ x)).trans (le_max_left _ _))
  have hK₁ : 0 < K := one_pos.trans_le (le_max_right _ _)
  -- The radius `r₁ < r₀` at which the bending starts, small enough to absorb the errors.
  set r₁ := min (r₀ / 2) (1 / (2 * (C + 1)))
  have hr₁ : 0 < r₁ := lt_min (by positivity) (by positivity)
  have hCr₁ : 2 * (C + 1) * r₁ ≤ 1 :=
    calc 2 * (C + 1) * r₁ ≤ 2 * (C + 1) * (1 / (2 * (C + 1))) := by gcongr; exact min_le_right _ _
      _ = 1 := by field_simp
  -- The angle `θ₀` of the straight segment.
  set θ₀ := min 1 (R₀ * (r₁ * exp (-1)) ^ 2 / (6 * (q - 1) * K))
  have h6 : 0 < 6 * ((q : ℝ) - 1) * K := mul_pos (by linarith) hK₁
  have hθ₀ : 0 < θ₀ := lt_min one_pos (div_pos (by positivity) h6)
  have hθ₀π : θ₀ ≤ π / 2 := (min_le_left _ _).trans (by linarith [two_le_pi])
  have hθ₀R : 6 * (q - 1) * K * θ₀ ≤ R₀ * (r₁ * exp (-1)) ^ 2 := by
    rw [mul_comm]
    exact (le_div_iff₀ h6).1 (min_le_right _ _)
  -- The weight `W` of the final bend.
  have hsθ₀ : 0 < sin θ₀ := sin_pos_of_pos_of_lt_pi hθ₀ (by linarith [pi_pos])
  set W := 1 + 3 * π * K / sin θ₀
  have hW : 1 ≤ W := le_add_of_nonneg_right (by positivity)
  have hWθ₀ : 3 * π * K ≤ W * sin θ₀ := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ hsθ₀.ne']
    linarith
  refine ⟨bendRadius r₁ θ₀ W, bendHeight r₁ θ₀ W, bendAngle θ₀, bendSpeed r₁ θ₀ W,
    { contDiff_angle := contDiff_bendAngle
      contDiff_speed := contDiff_bendSpeed
      speed_pos u := mul_pos (by linarith [one_le_bendWeight hW u]) (bendRadius_pos hr₁ u)
      hasDerivAt_radius := hasDerivAt_bendRadius
      hasDerivAt_height u :=
        (continuous_bendHeight_integrand.integral_hasStrictDerivAt 0 u).hasDerivAt
      monotone_angle := monotone_bendAngle hθ₀.le hθ₀π
      angle_of_nonpos := bendAngle_of_nonpos
      height_of_nonpos := bendHeight_of_nonpos
      radius_pos := bendRadius_pos hr₁
      radius_zero_lt := by
        rw [bendRadius_zero]
        exact (min_le_left _ _).trans_lt (half_lt_self hr₀)
      tendsto_radius_atBot := tendsto_bendRadius_atBot hr₁
      exists_angle_eq := ⟨3, fun _ ↦ bendAngle_of_three_le⟩
      tendsto_height_atTop := tendsto_bendHeight_atTop hr₁ hW
      scalar_pos := bend_scalar_pos hq' hR₀ hC hr₁ hCr₁ hθ₀ hθ₀π hW hK hθ₀R hWθ₀ }⟩

end TauCeti
