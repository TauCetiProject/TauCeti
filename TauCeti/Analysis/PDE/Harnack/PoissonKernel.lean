/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Ball
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import TauCeti.Analysis.PDE.PoissonIntegral.Ball

/-!
# Harnack's inequality on balls with the Poisson-kernel constant

Let `E` be a real inner product space of finite dimension `n`, and let `u ≥ 0` be harmonic on the
open ball `B(c, R)`. This file proves **Harnack's inequality with the sharp constant**: for `x`,
`y` in the closed ball `closedBall c r` with `r < R`,

`u x ≤ ((R + r) / (R - r)) ^ n * u y`.

It follows from the two-sided comparison of `u` with its value at the centre: writing
`d = ‖x - c‖ < R`,

`(R - d) / R * (R / (R + d)) ^ (n - 1) * u c ≤ u x ≤ (R + d) / R * (R / (R - d)) ^ (n - 1) * u c`,

which is the form `R ^ (n - 2) (R - d) / (R + d) ^ (n - 1) u(c) ≤ u(x) ≤
R ^ (n - 2) (R + d) / (R - d) ^ (n - 1) u(c)` of Gilbarg–Trudinger. On a ball slightly smaller
than `B(c, R)`, the function `u` is the Poisson integral of its boundary values. On the boundary
sphere, the Poisson kernel with pole `x` lies between `(1 - t) / (1 + t) ^ (n - 1)` and
`(1 + t) / (1 - t) ^ (n - 1)` times the kernel with pole at the centre, where `t` is the
normalized distance of `x` from the centre
(`TauCeti.ballPoissonKernel_le_mul_ballPoissonKernel_zero`,
`TauCeti.mul_ballPoissonKernel_zero_le_ballPoissonKernel`). Integrating against the nonnegative
boundary values compares `u x` with the Poisson integral at the centre, which is `u c`. Letting
the smaller radius increase to `R` gives the comparison on `B(c, R)`.

The constant cannot be improved: for `n ≥ 1` and a point `ξ` of the unit sphere of `ℝⁿ`, the
Poisson kernel `TauCeti.ballPoissonKernel n · ξ` is positive and harmonic on the open unit ball,
and its values at `x = r ξ` and `y = -r ξ` have ratio exactly `((1 + r) / (1 - r)) ^ n`. At
`r = R / 4` the constant is `(5 / 3) ^ n`, below the constant `3 ^ n` of the mean-value form
`InnerProductSpace.HarmonicOnNhd.le_three_pow_mul_of_nonneg`, which needs harmonicity on the
ball of four times the radius. On the complex plane, `n = 2` gives the planar inequality
`InnerProductSpace.HarmonicOnNhd.harnack_inequality`.

## Main declarations

* `InnerProductSpace.HarmonicOnNhd.le_add_div_mul_div_sub_pow_mul_of_nonneg` and
  `InnerProductSpace.HarmonicOnNhd.sub_div_mul_div_add_pow_mul_le_of_nonneg`: the upper and lower
  comparison with the value at the centre.
* `InnerProductSpace.HarmonicOnNhd.le_add_div_sub_pow_mul_of_nonneg`: Harnack's inequality
  `u x ≤ ((R + r) / (R - r)) ^ n * u y` on the closed ball of radius `r < R`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 2 (Harnack's inequality, Theorem 2.5, and the Poisson integral formula).
* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, Chapter 3 (Harnack's
  inequality).
-/

public section

open InnerProductSpace Metric Module Set Filter Topology MeasureTheory

namespace TauCeti

/-- Harnack's comparison with the centre on the unit ball of `ℝⁿ`, for a function continuous on
the closed ball, harmonic in the open ball and nonnegative on the sphere. -/
private theorem le_mul_and_mul_le_of_harmonicOnNhd_ball_one {n : ℕ} (hn : n ≠ 0)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ContinuousOn u (closedBall 0 1))
    (hu : HarmonicOnNhd u (ball 0 1))
    (hnonneg : ∀ y ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1, 0 ≤ u y)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) :
    u x ≤ (1 + ‖x‖) / (1 - ‖x‖) ^ (n - 1) * u 0 ∧
      (1 - ‖x‖) / (1 + ‖x‖) ^ (n - 1) * u 0 ≤ u x := by
  have hP := eqOn_ballPoissonIntegral_of_harmonicOnNhd hn hc hu
  let g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ := fun y ↦ u y
  have hgi : Integrable g volume.toSphere :=
    (hc.comp_continuous continuous_subtype_val fun y ↦
      sphere_subset_closedBall y.2).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hKi := integrable_ballPoissonKernel_mul hgi (x := x)
  have hK0i := integrable_ballPoissonKernel_mul hgi (x := 0)
  have hux : u x = ∫ y, ballPoissonKernel n x y * g y ∂volume.toSphere := by
    rw [hP (mem_ball_zero_iff.mpr hx), ballPoissonIntegral_def]
  have hu0 : u 0 = ∫ y, ballPoissonKernel n 0 y * g y ∂volume.toSphere := by
    rw [hP (mem_ball_self one_pos), ballPoissonIntegral_def]
  rw [hux, hu0, ← integral_const_mul, ← integral_const_mul]
  -- Both bounds are the pointwise kernel comparison, integrated against `g ≥ 0`.
  refine ⟨integral_mono hKi (hK0i.const_mul _) fun y ↦ ?_,
    integral_mono (hK0i.const_mul _) hKi fun y ↦ ?_⟩
  · rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (ballPoissonKernel_le_mul_ballPoissonKernel_zero hx (norm_eq_of_mem_sphere y))
      (hnonneg y y.2)
  · rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_ballPoissonKernel_zero_le_ballPoissonKernel hx (norm_eq_of_mem_sphere y))
      (hnonneg y y.2)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {u : E → ℝ} {c x y : E} {r R : ℝ}

/-- Harnack's comparison with the centre on a closed ball `closedBall c ρ` inside the ball
`B(c, R)` on which `u` is harmonic and nonnegative, in the normalized form with
`t = ‖x - c‖ / ρ`. It is the unit-ball comparison transported along an isometry of `E` with
`ℝⁿ` and the homothety `y ↦ c + ρ • y`. -/
private theorem le_mul_and_mul_le_of_lt_of_lt (hn : finrank ℝ E ≠ 0)
    (hu : HarmonicOnNhd u (ball c R)) (hnonneg : ∀ z ∈ ball c R, 0 ≤ u z) {ρ : ℝ}
    (hxρ : dist x c < ρ) (hρR : ρ < R) :
    u x ≤ (1 + dist x c / ρ) / (1 - dist x c / ρ) ^ (finrank ℝ E - 1) * u c ∧
      (1 - dist x c / ρ) / (1 + dist x c / ρ) ^ (finrank ℝ E - 1) * u c ≤ u x := by
  have hρ : 0 < ρ := dist_nonneg.trans_lt hxρ
  let e := (stdOrthonormalBasis ℝ E).repr
  let v : EuclideanSpace ℝ (Fin (finrank ℝ E)) → ℝ := (fun z ↦ u (c + ρ • z)) ∘ e.symm
  -- `v` is harmonic on the ball of radius `R / ρ > 1`, which contains the closed unit ball.
  have hv : HarmonicOnNhd v (ball 0 (R / ρ)) := by
    have h₁ : HarmonicOnNhd (fun z ↦ u (c + ρ • z)) (ball 0 (R / ρ)) := by
      rw [harmonicOnNhd_comp_const_add_smul_ball_radius_iff c hρ.ne',
        Real.norm_of_nonneg hρ.le, mul_div_cancel₀ _ hρ.ne']
      exact hu
    have h₂ := (harmonicOnNhd_comp_linearIsometryEquiv_right_iff e.symm).2 h₁
    rwa [LinearIsometryEquiv.preimage_ball, LinearIsometryEquiv.symm_symm, map_zero] at h₂
  have hsub : closedBall (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1 ⊆ ball 0 (R / ρ) :=
    closedBall_subset_ball ((one_lt_div hρ).2 hρR)
  have hvc : ContinuousOn v (closedBall 0 1) := fun z hz ↦
    (hv z (hsub hz)).1.continuousAt.continuousWithinAt
  have hvn : ∀ z ∈ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E))) 1, 0 ≤ v z := by
    intro z hz
    refine hnonneg _ ?_
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le,
      LinearIsometryEquiv.norm_map, norm_eq_of_mem_sphere ⟨z, hz⟩, mul_one]
    exact hρR
  -- The point of the unit ball corresponding to `x`.
  set z := e (ρ⁻¹ • (x - c)) with hz
  have hzn : ‖z‖ = dist x c / ρ := by
    rw [hz, LinearIsometryEquiv.norm_map, norm_smul, norm_inv, Real.norm_of_nonneg hρ.le,
      dist_eq_norm, inv_mul_eq_div]
  have hvz : v z = u x := by
    simp [v, hz, smul_smul, mul_inv_cancel₀ hρ.ne']
  have hv0 : v 0 = u c := by simp [v]
  have h := le_mul_and_mul_le_of_harmonicOnNhd_ball_one hn hvc (hv.mono (ball_subset_ball
    ((one_lt_div hρ).2 hρR).le)) hvn (hzn ▸ (div_lt_one hρ).2 hxρ)
  rwa [hvz, hv0, hzn] at h

/-- Harnack's comparison with the centre on the ball `B(c, R)` itself, in the normalized form with
`t = ‖x - c‖ / R`: the comparison on the smaller balls `closedBall c ρ`, `ρ < R`, passes to the
limit `ρ → R`, since both bounds are continuous in `ρ`. -/
private theorem le_mul_and_mul_le (hu : HarmonicOnNhd u (ball c R))
    (hnonneg : ∀ z ∈ ball c R, 0 ≤ u z) (hx : x ∈ ball c R) :
    u x ≤ (1 + dist x c / R) / (1 - dist x c / R) ^ (finrank ℝ E - 1) * u c ∧
      (1 - dist x c / R) / (1 + dist x c / R) ^ (finrank ℝ E - 1) * u c ≤ u x := by
  have hdR : dist x c < R := mem_ball.mp hx
  have hR : 0 < R := dist_nonneg.trans_lt hdR
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · -- In dimension zero, `x = c`.
    have : Subsingleton E := Module.finrank_zero_iff.mp hn
    simp [Subsingleton.elim x c]
  have hev : ∀ᶠ ρ in 𝓝[<] R, ρ ∈ Ioo (dist x c) R := Ioo_mem_nhdsLT hdR
  have hq : ContinuousAt (fun ρ : ℝ ↦ dist x c / ρ) R :=
    continuousAt_const.div continuousAt_id hR.ne'
  have ht : dist x c / R < 1 := (div_lt_one hR).2 hdR
  have ht₀ : 0 ≤ dist x c / R := div_nonneg dist_nonneg hR.le
  have h₁ : ContinuousAt (fun ρ : ℝ ↦
      (1 + dist x c / ρ) / (1 - dist x c / ρ) ^ (finrank ℝ E - 1) * u c) R :=
    ((continuousAt_const.add hq).div ((continuousAt_const.sub hq).pow _)
      (pow_ne_zero _ (by simp only [Pi.sub_apply]; linarith))).mul continuousAt_const
  have h₂ : ContinuousAt (fun ρ : ℝ ↦
      (1 - dist x c / ρ) / (1 + dist x c / ρ) ^ (finrank ℝ E - 1) * u c) R :=
    ((continuousAt_const.sub hq).div ((continuousAt_const.add hq).pow _)
      (pow_ne_zero _ (by simp only [Pi.add_apply]; linarith))).mul continuousAt_const
  exact ⟨ge_of_tendsto (h₁.tendsto.mono_left nhdsWithin_le_nhds)
      (hev.mono fun ρ hρ ↦ (le_mul_and_mul_le_of_lt_of_lt hn hu hnonneg hρ.1 hρ.2).1),
    le_of_tendsto (h₂.tendsto.mono_left nhdsWithin_le_nhds)
      (hev.mono fun ρ hρ ↦ (le_mul_and_mul_le_of_lt_of_lt hn hu hnonneg hρ.1 hρ.2).2)⟩

/-- **Harnack's comparison with the centre, upper bound.** Let `u` be harmonic and nonnegative on
the ball `B(c, R)` of a real inner product space of finite dimension `n`. For `x ∈ B(c, R)` at
distance `d` from the centre,

`u x ≤ (R + d) / R * (R / (R - d)) ^ (n - 1) * u c`,

that is `u x ≤ R ^ (n - 2) (R + d) / (R - d) ^ (n - 1) * u c`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.le_add_div_mul_div_sub_pow_mul_of_nonneg
    (hu : HarmonicOnNhd u (ball c R)) (hnonneg : ∀ z ∈ ball c R, 0 ≤ u z) (hx : x ∈ ball c R) :
    u x ≤ (R + dist x c) / R * (R / (R - dist x c)) ^ (finrank ℝ E - 1) * u c := by
  have hdR : dist x c < R := mem_ball.mp hx
  have hR : 0 < R := dist_nonneg.trans_lt hdR
  have h := (le_mul_and_mul_le hu hnonneg hx).1
  have hsub : R - dist x c ≠ 0 := by linarith
  have heq : (1 + dist x c / R) / (1 - dist x c / R) ^ (finrank ℝ E - 1) =
      (R + dist x c) / R * (R / (R - dist x c)) ^ (finrank ℝ E - 1) := by
    rw [div_pow, one_add_div hR.ne', one_sub_div hR.ne', div_pow]
    field_simp
  rwa [heq] at h

/-- **Harnack's comparison with the centre, lower bound.** Let `u` be harmonic and nonnegative on
the ball `B(c, R)` of a real inner product space of finite dimension `n`. For `x ∈ B(c, R)` at
distance `d` from the centre,

`(R - d) / R * (R / (R + d)) ^ (n - 1) * u c ≤ u x`,

that is `R ^ (n - 2) (R - d) / (R + d) ^ (n - 1) * u c ≤ u x`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.sub_div_mul_div_add_pow_mul_le_of_nonneg
    (hu : HarmonicOnNhd u (ball c R)) (hnonneg : ∀ z ∈ ball c R, 0 ≤ u z) (hx : x ∈ ball c R) :
    (R - dist x c) / R * (R / (R + dist x c)) ^ (finrank ℝ E - 1) * u c ≤ u x := by
  have hdR : dist x c < R := mem_ball.mp hx
  have hR : 0 < R := dist_nonneg.trans_lt hdR
  have h := (le_mul_and_mul_le hu hnonneg hx).2
  have hadd : R + dist x c ≠ 0 := by linarith [dist_nonneg (x := x) (y := c)]
  have heq : (1 - dist x c / R) / (1 + dist x c / R) ^ (finrank ℝ E - 1) =
      (R - dist x c) / R * (R / (R + dist x c)) ^ (finrank ℝ E - 1) := by
    rw [div_pow, one_add_div hR.ne', one_sub_div hR.ne', div_pow]
    field_simp
  rwa [heq] at h

/-- **Harnack's inequality with the sharp constant.** Let `u` be harmonic and nonnegative on the
ball `B(c, R)` of a real inner product space of finite dimension `n`, and let `r < R`. For `x` and
`y` in the closed ball `closedBall c r`,

`u x ≤ ((R + r) / (R - r)) ^ n * u y`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.le_add_div_sub_pow_mul_of_nonneg
    (hu : HarmonicOnNhd u (ball c R)) (hnonneg : ∀ z ∈ ball c R, 0 ≤ u z) (hrR : r < R)
    (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    u x ≤ ((R + r) / (R - r)) ^ finrank ℝ E * u y := by
  have hdx : dist x c ≤ r := mem_closedBall.mp hx
  have hdy : dist y c ≤ r := mem_closedBall.mp hy
  have hr : 0 ≤ r := dist_nonneg.trans hdx
  have hR : 0 < R := hr.trans_lt hrR
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · -- In dimension zero, `x = y`.
    have : Subsingleton E := Module.finrank_zero_iff.mp hn
    simp [hn, Subsingleton.elim x y]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have huc : 0 ≤ u c := hnonneg c (mem_ball_self hR)
  -- The comparison with the centre, made uniform over the closed ball `closedBall c r`.
  have hux : u x ≤ (R + r) / R * (R / (R - r)) ^ k * u c := by
    refine (hu.le_add_div_mul_div_sub_pow_mul_of_nonneg hnonneg
      (closedBall_subset_ball hrR hx)).trans ?_
    rw [hk, Nat.add_sub_cancel]
    have : 0 < R - dist x c := by linarith
    gcongr
  have huy : (R - r) / R * (R / (R + r)) ^ k * u c ≤ u y := by
    refine le_trans ?_ (hu.sub_div_mul_div_add_pow_mul_le_of_nonneg hnonneg
      (closedBall_subset_ball hrR hy))
    rw [hk, Nat.add_sub_cancel]
    have : 0 < R + dist y c := by linarith [dist_nonneg (x := y) (y := c)]
    have : 0 ≤ (R - dist y c) / R := div_nonneg (by linarith) hR.le
    gcongr
  calc u x ≤ (R + r) / R * (R / (R - r)) ^ k * u c := hux
    _ = ((R + r) / (R - r)) ^ (k + 1) * ((R - r) / R * (R / (R + r)) ^ k * u c) := by
        have : R + r ≠ 0 := by linarith
        rw [div_pow, div_pow, div_pow]
        field_simp
        ring
    _ ≤ ((R + r) / (R - r)) ^ (k + 1) * u y := by gcongr
    _ = ((R + r) / (R - r)) ^ finrank ℝ E * u y := by rw [hk]

end TauCeti
