/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.BoundaryConcentration
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue

/-!
# The Poisson integral of the Euclidean unit ball and its boundary values

For boundary data `g` on the unit sphere `S` of `ℝⁿ`, the **Poisson integral**

`P[g](x) = ∫_S K(x, y) g(y) dσ(y)`

averages `g` against the Poisson kernel `K = TauCeti.ballPoissonKernel` of the unit ball, with
respect to the surface measure `σ = volume.toSphere` on `S`.  It is the candidate solution of the
Dirichlet problem `Δu = 0` in the ball, `u = g` on `S`.

This file proves that the Poisson kernel has **mass one**: `∫_S K(x, y) dσ(y) = 1` for every
pole `x` in the open ball (`n ≠ 0`).  For `x = r θ` with `‖θ‖ = 1` and a boundary point `y`, the
distances `‖r θ - y‖` and `‖r y - θ‖` agree, so `K(x, y) = K(r y, θ)`; the integral over `y` is
then the sphere integral of the function `K(·, θ)`, harmonic on the closed ball of radius
`r < 1`, and the mean-value property evaluates it as `σ(S) K(0, θ) = 1`.

With positivity of the kernel and its far-field bound, mass one makes the Poisson kernel an
approximate identity on the sphere: the Poisson integral of continuous boundary data tends to
`g z` as its argument tends to a boundary point `z` from inside the ball
(`TauCeti.tendsto_ballPoissonIntegral`).  This boundary attainment is one of the two halves of the
solution of the Dirichlet problem on the ball by the Poisson integral; the other is harmonicity of
`P[g]` in the open ball.

## Main declarations

* `TauCeti.integral_ballPoissonKernel`: the Poisson kernel of the ball has mass one.
* `TauCeti.ballPoissonIntegral`: the Poisson integral of boundary data on the unit sphere.
* `TauCeti.ballPoissonIntegral_const`, `TauCeti.ballPoissonIntegral_add`,
  `TauCeti.ballPoissonIntegral_smul`, `TauCeti.ballPoissonIntegral_mono`: the Poisson integral is
  a positive linear operator preserving constants.
* `TauCeti.tendsto_ballPoissonIntegral`: the Poisson integral of continuous boundary data attains
  the boundary values.

## References

The boundary argument and operator API are adapted from the planar formalization in
`TauCeti/Analysis/Complex/Poisson/Integral.lean`.

* L. C. Evans, *Partial Differential Equations*, Section 2.2.4, Theorem 15.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.5, Theorem 2.6.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace MeasureTheory Metric Set Filter

open scoped RealInnerProductSpace Topology

variable {n : ℕ}

/-- **The Poisson kernel of the ball has mass one.**  For a pole `x` in the open unit ball of
`ℝⁿ`, `n ≠ 0`, the Poisson kernel `K(x, ·)` integrates to one against the surface measure of the
unit sphere. -/
@[simp]
theorem integral_ballPoissonKernel (hn : n ≠ 0) {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) :
    ∫ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ballPoissonKernel n x y ∂volume.toSphere =
      1 := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    infer_instance
  set r := ‖x‖
  obtain ⟨θ, hθ, hxθ⟩ : ∃ θ : EuclideanSpace ℝ (Fin n), ‖θ‖ = 1 ∧ x = r • θ := by
    rcases eq_or_ne x 0 with rfl | h0
    · obtain ⟨θ, hθ⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin n)) zero_le_one
      exact ⟨θ, hθ, by simp [r]⟩
    · exact ⟨r⁻¹ • x, by simp [r, norm_smul, h0], by simp [r, smul_smul, h0]⟩
  -- Exchanging the roles of the directions `θ` and `y` turns `K(x, y)` into `K(r y, θ)`.
  have hswap (y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      ballPoissonKernel n x y =
        ballPoissonKernel n (0 + r • (y : EuclideanSpace ℝ (Fin n))) θ := by
    have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_eq_of_mem_sphere y
    have hdist : ‖x - y‖ = ‖r • (y : EuclideanSpace ℝ (Fin n)) - θ‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real, norm_sub_sq_real, hxθ,
        norm_smul, norm_smul, inner_smul_left, inner_smul_left, real_inner_comm, hθ, hy]
    rw [zero_add, ballPoissonKernel_def, ballPoissonKernel_def, hdist, norm_smul, hy, mul_one,
      Real.norm_of_nonneg (norm_nonneg x)]
  have hu : HarmonicOnNhd (fun z ↦ ballPoissonKernel n z θ)
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) := fun z hz ↦ by
    refine harmonicAt_ballPoissonKernel_left hθ fun hzθ ↦ ?_
    rw [mem_closedBall_zero_iff, hzθ, hθ] at hz
    exact hx.not_ge hz
  have hω := volume_real_unitBall_pos n
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [integral_congr_ae (ae_of_all _ hswap), hu.integral_toSphere_eq (norm_nonneg x),
    Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, ballPoissonKernel_def]
  simp only [norm_zero, zero_sub, norm_neg, hθ, one_pow, smul_eq_mul]
  field_simp
  norm_num

/-- The Poisson kernel with any pole times integrable boundary data is integrable on the
sphere. -/
theorem integrable_ballPoissonKernel_mul {g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ}
    (hg : Integrable g volume.toSphere) {x : EuclideanSpace ℝ (Fin n)} :
    Integrable (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ ballPoissonKernel n x y * g y)
      volume.toSphere := by
  by_cases hx : ‖x‖ = 1
  · simp [ballPoissonKernel_def, hx]
  · have hK := continuous_ballPoissonKernel_on_sphere x hx
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuousOn
    exact hg.bdd_mul hK.aestronglyMeasurable (ae_of_all _ fun y ↦ hC y (mem_univ y))

/-- The Poisson integral of boundary data `g` on the unit sphere of `ℝⁿ`,

`P[g](x) = ∫_S K(x, y) g(y) dσ(y)`,

where `K` is the Poisson kernel of the unit ball and `σ` is the surface measure of the unit
sphere `S`.  For continuous `g` it tends to `g z` at each boundary point `z`
(`TauCeti.tendsto_ballPoissonIntegral`). -/
def ballPoissonIntegral (g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ballPoissonKernel n x y * g y ∂volume.toSphere

/-- The defining formula for the Poisson integral of the ball. -/
theorem ballPoissonIntegral_def (g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ballPoissonIntegral g x =
      ∫ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ballPoissonKernel n x y * g y
        ∂volume.toSphere := by
  rw [ballPoissonIntegral]

/-- The Poisson integral of zero boundary data is zero. -/
@[simp] theorem ballPoissonIntegral_zero (x : EuclideanSpace ℝ (Fin n)) :
    ballPoissonIntegral (fun _ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ 0) x = 0 := by
  simp [ballPoissonIntegral_def]

/-- The Poisson integral is additive in integrable boundary data at every pole. -/
theorem ballPoissonIntegral_add {g₁ g₂ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ}
    (hg₁ : Integrable g₁ volume.toSphere) (hg₂ : Integrable g₂ volume.toSphere)
    {x : EuclideanSpace ℝ (Fin n)} :
    ballPoissonIntegral (g₁ + g₂) x = ballPoissonIntegral g₁ x + ballPoissonIntegral g₂ x := by
  simp only [ballPoissonIntegral_def, Pi.add_apply, mul_add]
  exact integral_add (integrable_ballPoissonKernel_mul hg₁)
    (integrable_ballPoissonKernel_mul hg₂)

/-- The Poisson integral commutes with real scalar multiplication of the boundary data. -/
@[simp] theorem ballPoissonIntegral_smul (a : ℝ) (g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ballPoissonIntegral (a • g) x = a • ballPoissonIntegral g x := by
  simp only [ballPoissonIntegral_def, Pi.smul_apply, smul_eq_mul, mul_left_comm _ a,
    integral_const_mul]

/-- The Poisson integral preserves constant boundary data at every point of the open unit
ball. -/
@[simp] theorem ballPoissonIntegral_const (hn : n ≠ 0) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ < 1) (a : ℝ) :
    ballPoissonIntegral (fun _ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ a) x = a := by
  rw [ballPoissonIntegral_def, integral_mul_const, integral_ballPoissonKernel hn hx, one_mul]

/-- In the open unit ball, subtracting a constant from the Poisson integral subtracts it from
the boundary data under the kernel. -/
theorem ballPoissonIntegral_sub_const (hn : n ≠ 0)
    {g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ} (hg : Integrable g volume.toSphere)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) (a : ℝ) :
    ballPoissonIntegral g x - a =
      ∫ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ballPoissonKernel n x y * (g y - a)
        ∂volume.toSphere := by
  conv_lhs => rw [← ballPoissonIntegral_const hn hx a]
  simp only [ballPoissonIntegral_def, mul_sub]
  exact (integral_sub (integrable_ballPoissonKernel_mul hg)
    (integrable_ballPoissonKernel_mul (integrable_const a))).symm

/-- The Poisson integral preserves order between integrable boundary data in the open unit
ball. -/
theorem ballPoissonIntegral_mono {g₁ g₂ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ}
    (hg₁ : Integrable g₁ volume.toSphere) (hg₂ : Integrable g₂ volume.toSphere)
    (hle : g₁ ≤ g₂) {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) :
    ballPoissonIntegral g₁ x ≤ ballPoissonIntegral g₂ x :=
  integral_mono (integrable_ballPoissonKernel_mul hg₁)
    (integrable_ballPoissonKernel_mul hg₂) fun y ↦
      mul_le_mul_of_nonneg_left (hle y) (ballPoissonKernel_pos_on_sphere x hx y).le

/-- Nonnegative boundary data have a nonnegative Poisson integral in the open unit ball. -/
theorem ballPoissonIntegral_nonneg {g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ}
    (hg : 0 ≤ g) {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) :
    0 ≤ ballPoissonIntegral g x :=
  integral_nonneg fun y ↦ mul_nonneg (ballPoissonKernel_pos_on_sphere x hx y).le (hg y)

/-- The pointwise estimate behind boundary recovery: where the data are `ε`-close to `g z`, the
integrand is at most `ε` times the kernel; elsewhere, at distance at least `δ` from `z`, the
far-field kernel bound and a global bound `C` on the data apply. -/
private theorem abs_ballPoissonKernel_mul_sub_le {g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {y z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1}
    {C ε δ : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε) (hx : ‖x‖ < 1)
    (hxz : dist x z ≤ δ / 2) (hC : |g y - g z| ≤ C)
    (hnear : dist y z < δ → |g y - g z| < ε) :
    |ballPoissonKernel n x y * (g y - g z)| ≤
      ε * ballPoissonKernel n x y +
        (1 - ‖x‖ ^ 2) /
          ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * (δ / 2) ^ n) * C := by
  have hK : 0 ≤ ballPoissonKernel n x y := (ballPoissonKernel_pos_on_sphere x hx y).le
  have hB : 0 ≤ (1 - ‖x‖ ^ 2) /
      ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * (δ / 2) ^ n) :=
    div_nonneg (by nlinarith [norm_nonneg x])
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg) (by positivity))
  rw [abs_mul, abs_of_nonneg hK]
  by_cases hyz : dist y z < δ
  · rw [mul_comm ε]
    exact (mul_le_mul_of_nonneg_left (hnear hyz).le hK).trans
      (le_add_of_nonneg_right (mul_nonneg hB ((abs_nonneg _).trans hC)))
  · have hKle := ballPoissonKernel_le_of_dist_le_half_of_le_dist hδ hx.le hxz
      (y := y) (by rw [← Subtype.dist_eq]; exact not_lt.mp hyz)
    exact (mul_le_mul hKle hC (abs_nonneg _) hB).trans
      (le_add_of_nonneg_left (mul_nonneg hε hK))

/-- **The Poisson integral attains continuous boundary values.**  For continuous data `g` on the
unit sphere of `ℝⁿ` and a point `z` of the sphere, the Poisson integral `P[g](x)` tends to `g z`
as `x` tends to `z` through the open unit ball. -/
theorem tendsto_ballPoissonIntegral {g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ}
    (hg : Continuous g) (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Tendsto (ballPoissonIntegral g) (𝓝[ball 0 1] (z : EuclideanSpace ℝ (Fin n)))
      (𝓝 (g z)) := by
  have hn : n ≠ 0 := by
    rintro rfl
    have hz := norm_eq_of_mem_sphere z
    simp [Subsingleton.elim (z : EuclideanSpace ℝ (Fin 0)) 0] at hz
  have hgi : Integrable g volume.toSphere :=
    hg.integrable_of_hasCompactSupport (.of_compactSpace g)
  -- Compactness of the sphere gives a global bound and uniform continuity of `g`.
  obtain ⟨C, hC⟩ :=
    isCompact_univ.exists_bound_of_continuousOn (hg.sub continuous_const).continuousOn
  have hgunif := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hg)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := hgunif (ε / 2) (half_pos hε)
  -- The far-field contribution `B x * C * σ(S)` tends to zero at the boundary point `z`.
  set σ := volume.toSphere.real (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
  let B : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ (1 - ‖x‖ ^ 2) /
    ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * (δ / 2) ^ n)
  have hBlim : Tendsto (fun x ↦ B x * C * σ) (𝓝[ball 0 1] (z : EuclideanSpace ℝ (Fin n)))
      (𝓝 0) := by
    have hcont : Continuous (fun x ↦ B x * C * σ) := by
      dsimp [B]
      fun_prop
    have hBz : B z * C * σ = 0 := by simp [B, norm_eq_of_mem_sphere z]
    simpa only [hBz] using (hcont.tendsto (z : EuclideanSpace ℝ (Fin n))).mono_left
      nhdsWithin_le_nhds
  have hsmall : ∀ᶠ x in 𝓝[ball 0 1] (z : EuclideanSpace ℝ (Fin n)), B x * C * σ < ε / 2 :=
    hBlim.eventually_lt_const (half_pos hε)
  have hnear : ∀ᶠ x in 𝓝[ball 0 1] (z : EuclideanSpace ℝ (Fin n)),
      dist x (z : EuclideanSpace ℝ (Fin n)) ≤ δ / 2 :=
    eventually_nhdsWithin_of_eventually_nhds (closedBall_mem_nhds _ (half_pos hδ))
  filter_upwards [self_mem_nhdsWithin, hsmall, hnear] with x hx hxsmall hxnear
  rw [mem_ball_zero_iff] at hx
  have hKi := integrableOn_univ.mp (integrableOn_ballPoissonKernel x hx.ne univ)
  -- Positivity and mass one turn the pointwise majorant into the required integral estimate.
  rw [Real.dist_eq, ballPoissonIntegral_sub_const hn hgi hx]
  calc |∫ y, ballPoissonKernel n x y * (g y - g z) ∂volume.toSphere|
      ≤ ∫ y, |ballPoissonKernel n x y * (g y - g z)| ∂volume.toSphere :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, (ε / 2 * ballPoissonKernel n x y + B x * C) ∂volume.toSphere :=
        integral_mono (integrable_ballPoissonKernel_mul (hgi.sub (integrable_const _))).abs
          ((hKi.const_mul _).add (integrable_const _)) fun y ↦
          abs_ballPoissonKernel_mul_sub_le hδ (half_pos hε).le hx hxnear (by simpa using hC y)
            fun hyz ↦ by simpa [Real.dist_eq] using hδg hyz
    _ = ε / 2 + B x * C * σ := by
        rw [integral_add (hKi.const_mul _) (integrable_const _), integral_const_mul,
          integral_ballPoissonKernel hn hx, integral_const, smul_eq_mul]
        ring
    _ < ε := by linarith

end TauCeti

end
