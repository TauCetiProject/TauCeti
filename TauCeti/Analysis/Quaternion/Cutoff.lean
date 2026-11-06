/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import TauCeti.Analysis.Quaternion.Integral
public import TauCeti.Analysis.Quaternion.Kernel

/-!
# The radial cutoff of the Cauchy–Fueter kernel and its mass

To prove the Cauchy–Fueter formula with the divergence theorem, the pole of the kernel
`G(q - q₀)` is removed by multiplying the kernel-weighted field `G(q - q₀) * eᵢ * f q` with
`ψ(‖q - q₀‖ / ε)`, where `ψ = TauCeti.cauchyFueterCutoff` is the smooth monotone cutoff
`s ↦ Real.smoothTransition (2 * s - 1)`, equal to `0` for `s ≤ 1 / 2` and to `1` for `1 ≤ s`.
The divergence of the cut-off field is then `G(q - q₀) * (∑ᵢ eᵢ ∂ᵢψ) * f q` plus `ψ` times the
divergence of the original field. This file defines the first factor as
`cauchyFueterCutoffDensity`, proves its nonnegativity and annular support, and computes its
total mass and integrability.

* `Quaternion.hasFDerivAt_cauchyFueterCutoff_norm_sub_div`: `q ↦ ψ(‖q - q₀‖ / ε)` is differentiable
  everywhere, with gradient `ε⁻¹ ψ'(‖q - q₀‖ / ε) (q - q₀) / ‖q - q₀‖`.
* `Quaternion.cauchyFueterKernel_mul_sum_fderiv_cauchyFueterCutoff`: hence
  `G(q - q₀) * ∑ᵢ (∂ᵢψ) eᵢ = ε⁻¹ ψ'(‖q - q₀‖ / ε) ‖q - q₀‖⁻³`, a real density supported on the
  annulus `ε / 2 ≤ ‖q - q₀‖ ≤ ε`.
* `Quaternion.integral_cauchyFueterCutoff_density`: the density above has total mass `2π²` for
  every `ε > 0` and `q₀`, the reciprocal of the normalization `1 / (2π²)` of the
  Cauchy–Fueter formula. It is computed with the polar formula
  `TauCeti.Quaternion.integral_fun_norm_dq_sub`, `∫ x, f ‖dq x - q₀‖ = 2π² ∫₀^∞ y³ f y`.

Integrals over the quaternions are taken on the coordinate space `Fin 4 → ℝ`, read as `ℍ`
through `dq`, with its product Lebesgue measure; no measure is placed on `ℍ` itself. Radial
variables are the Euclidean norm of `ℍ`, never the sup norm of the coordinate space.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Theorem 9, for the Cauchy–Fueter formula
  with normalization `1 / (2π²)`.
* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225.
-/

public section

open MeasureTheory Set Filter Real
open scoped Quaternion Topology RealInnerProductSpace

namespace TauCeti

open _root_.TauCeti.Quaternion

/-! ### The cutoff -/

/-- The radial cutoff `s ↦ Real.smoothTransition (2 * s - 1)` used to excise the pole of the
Cauchy–Fueter kernel: it is `0` for `s ≤ 1 / 2`, `1` for `1 ≤ s`, smooth and monotone. -/
noncomputable def cauchyFueterCutoff (s : ℝ) : ℝ :=
  Real.smoothTransition (2 * s - 1)

theorem cauchyFueterCutoff_apply (s : ℝ) :
    cauchyFueterCutoff s = Real.smoothTransition (2 * s - 1) :=
  (rfl)

@[simp]
theorem cauchyFueterCutoff_eq_zero_iff {s : ℝ} : cauchyFueterCutoff s = 0 ↔ s ≤ 1 / 2 := by
  rw [cauchyFueterCutoff_apply, Real.smoothTransition.zero_iff_nonpos]
  constructor <;> intro h <;> linarith

@[simp]
theorem cauchyFueterCutoff_eq_one_iff {s : ℝ} : cauchyFueterCutoff s = 1 ↔ 1 ≤ s := by
  rw [cauchyFueterCutoff_apply, Real.smoothTransition.eq_one_iff_one_le]
  constructor <;> intro h <;> linarith

theorem cauchyFueterCutoff_of_le {s : ℝ} (hs : s ≤ 1 / 2) : cauchyFueterCutoff s = 0 :=
  cauchyFueterCutoff_eq_zero_iff.2 hs

theorem cauchyFueterCutoff_of_one_le {s : ℝ} (hs : 1 ≤ s) : cauchyFueterCutoff s = 1 :=
  cauchyFueterCutoff_eq_one_iff.2 hs

theorem cauchyFueterCutoff_nonneg (s : ℝ) : 0 ≤ cauchyFueterCutoff s :=
  Real.smoothTransition.nonneg _

theorem cauchyFueterCutoff_le_one (s : ℝ) : cauchyFueterCutoff s ≤ 1 :=
  Real.smoothTransition.le_one _

theorem monotone_cauchyFueterCutoff : Monotone cauchyFueterCutoff := fun _ _ h ↦
  Real.smoothTransition.monotone (by linarith)

@[fun_prop]
theorem contDiff_cauchyFueterCutoff {n : ℕ∞} : ContDiff ℝ n cauchyFueterCutoff :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

@[fun_prop]
theorem differentiable_cauchyFueterCutoff : Differentiable ℝ cauchyFueterCutoff :=
  (contDiff_cauchyFueterCutoff (n := 1)).differentiable one_ne_zero

/-- The derivative of the cutoff vanishes below `1 / 2`, where the cutoff is constantly `0`. -/
theorem deriv_cauchyFueterCutoff_of_lt {s : ℝ} (hs : s < 1 / 2) :
    deriv cauchyFueterCutoff s = 0 := by
  rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ)), deriv_const]
  filter_upwards [Iio_mem_nhds hs] with t ht using cauchyFueterCutoff_of_le (le_of_lt ht)

/-- The derivative of the cutoff vanishes above `1`, where the cutoff is constantly `1`. -/
theorem deriv_cauchyFueterCutoff_of_one_lt {s : ℝ} (hs : 1 < s) :
    deriv cauchyFueterCutoff s = 0 := by
  rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (1 : ℝ)), deriv_const]
  filter_upwards [Ioi_mem_nhds hs] with t ht using cauchyFueterCutoff_of_one_le (le_of_lt ht)

/-- The cutoff rises from `0` to `1`, so its derivative has total integral `1`. -/
theorem integral_Ioi_deriv_cauchyFueterCutoff :
    ∫ s in Ioi (0 : ℝ), deriv cauchyFueterCutoff s = 1 := by
  have hlim : Tendsto cauchyFueterCutoff atTop (𝓝 1) :=
    tendsto_const_nhds.congr' <| (eventually_ge_atTop 1).mono fun s hs ↦
      (cauchyFueterCutoff_of_one_le hs).symm
  rw [integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun s _ ↦ (differentiable_cauchyFueterCutoff s).hasDerivAt)
    (fun _ _ ↦ monotone_cauchyFueterCutoff.deriv_nonneg) hlim,
    cauchyFueterCutoff_of_le (by norm_num), sub_zero]

/-! ### The cutoff density -/

/-- The real density produced by differentiating the radial cutoff against the
Cauchy–Fueter kernel. Its value at the pole is zero. -/
noncomputable def cauchyFueterCutoffDensity (ε : ℝ) (q q₀ : ℍ) : ℝ :=
  ε⁻¹ * deriv cauchyFueterCutoff (‖q - q₀‖ / ε) * (‖q - q₀‖ ^ 3)⁻¹

theorem cauchyFueterCutoffDensity_apply (ε : ℝ) (q q₀ : ℍ) :
    cauchyFueterCutoffDensity ε q q₀ =
      ε⁻¹ * deriv cauchyFueterCutoff (‖q - q₀‖ / ε) * (‖q - q₀‖ ^ 3)⁻¹ :=
  (rfl)

@[simp]
theorem cauchyFueterCutoffDensity_self (ε : ℝ) (q₀ : ℍ) :
    cauchyFueterCutoffDensity ε q₀ q₀ = 0 := by
  simp [cauchyFueterCutoffDensity_apply]

/-- The cutoff density is nonnegative for positive cutoff radius. -/
theorem cauchyFueterCutoffDensity_nonneg {ε : ℝ} (hε : 0 < ε) (q q₀ : ℍ) :
    0 ≤ cauchyFueterCutoffDensity ε q q₀ := by
  rw [cauchyFueterCutoffDensity_apply]
  exact mul_nonneg (mul_nonneg (inv_nonneg.2 hε.le)
    monotone_cauchyFueterCutoff.deriv_nonneg) (inv_nonneg.2 (by positivity))

/-- Outside the closed annulus of radii `ε / 2` and `ε`, the cutoff density vanishes. -/
theorem cauchyFueterCutoffDensity_eq_zero {ε : ℝ} (hε : 0 < ε) {q q₀ : ℍ}
    (hq : ‖q - q₀‖ < ε / 2 ∨ ε < ‖q - q₀‖) :
    cauchyFueterCutoffDensity ε q q₀ = 0 := by
  rcases hq with hq | hq
  · have hd : deriv cauchyFueterCutoff (‖q - q₀‖ / ε) = 0 :=
      deriv_cauchyFueterCutoff_of_lt ((div_lt_iff₀ hε).2 (by linarith))
    simp [cauchyFueterCutoffDensity_apply, hd]
  · have hd : deriv cauchyFueterCutoff (‖q - q₀‖ / ε) = 0 :=
      deriv_cauchyFueterCutoff_of_one_lt ((lt_div_iff₀ hε).2 (by simpa using hq))
    simp [cauchyFueterCutoffDensity_apply, hd]

/-! ### The gradient of the cutoff against the kernel -/

/-- The cutoff `q ↦ ψ(‖q - q₀‖ / ε)` is differentiable at every `q`, with gradient
`ε⁻¹ ψ'(‖q - q₀‖ / ε) (q - q₀) / ‖q - q₀‖`. At the pole both sides vanish, since the cutoff is
identically `0` near `q₀` (on the ball of radius `ε / 2` when `ε > 0`, everywhere otherwise). -/
theorem _root_.Quaternion.hasFDerivAt_cauchyFueterCutoff_norm_sub_div (q q₀ : ℍ) (ε : ℝ) :
    HasFDerivAt (fun p ↦ cauchyFueterCutoff (‖p - q₀‖ / ε))
      ((ε⁻¹ * deriv cauchyFueterCutoff (‖q - q₀‖ / ε) / ‖q - q₀‖) • innerSL ℝ (q - q₀)) q := by
  rcases eq_or_ne q q₀ with rfl | hq
  · simp only [sub_self, map_zero, smul_zero]
    refine (hasFDerivAt_const (0 : ℝ) q).congr_of_eventuallyEq ?_
    rcases le_or_gt ε 0 with hε | hε
    · exact Eventually.of_forall fun p ↦ cauchyFueterCutoff_of_le
        ((div_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hε).trans (by norm_num))
    filter_upwards [Metric.ball_mem_nhds q (half_pos hε)] with p hp
    rw [Metric.mem_ball, dist_eq_norm] at hp
    exact cauchyFueterCutoff_of_le (by rw [div_le_iff₀ hε]; linarith)
  · have hr : ‖q - q₀‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hq)
    have h₁ : HasFDerivAt (fun p ↦ √(‖p - q₀‖ ^ 2))
        ((1 / (2 * √(‖q - q₀‖ ^ 2))) • (2 • innerSL ℝ (q - q₀))) q := by
      have := ((hasFDerivAt_id q).sub_const q₀).norm_sq.sqrt (pow_ne_zero 2 hr)
      simpa using this
    simp only [Real.sqrt_sq (norm_nonneg _)] at h₁
    have h₂ : HasDerivAt (fun s ↦ cauchyFueterCutoff (s / ε))
        (deriv cauchyFueterCutoff (‖q - q₀‖ / ε) * (1 / ε)) ‖q - q₀‖ :=
      (differentiable_cauchyFueterCutoff _).hasDerivAt.comp _ ((hasDerivAt_id _).div_const ε)
    refine (h₂.comp_hasFDerivAt q h₁).congr_fderiv ?_
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp

/-- The gradient of the cutoff, multiplied on the left by the kernel, is the real density
`ε⁻¹ ψ'(‖q - q₀‖ / ε) ‖q - q₀‖⁻³`: here `∑ᵢ (∂ᵢψ) eᵢ` runs over the units `eᵢ = 1, i, j, k`,
and the identity uses `∑ᵢ (∂ᵢψ) eᵢ = ε⁻¹ ψ'(‖r‖ / ε) r / ‖r‖` and `G(r) * r = ‖r‖⁻²` for
`r = q - q₀`. This is the factor in the divergence of the cut-off kernel-weighted field
`G(q - q₀) * eᵢ * f q * ψ(‖q - q₀‖ / ε)` that does not involve the derivative of `f`. -/
theorem _root_.Quaternion.cauchyFueterKernel_mul_sum_fderiv_cauchyFueterCutoff (q q₀ : ℍ) (ε : ℝ) :
    cauchyFueterKernel q q₀ * ∑ i : Fin 4,
        fderiv ℝ (fun p ↦ cauchyFueterCutoff (‖p - q₀‖ / ε)) q (dq (Pi.single i 1)) •
          dq (Pi.single i 1) =
      (cauchyFueterCutoffDensity ε q q₀ : ℍ) := by
  simp only [cauchyFueterCutoffDensity_apply,
    (_root_.Quaternion.hasFDerivAt_cauchyFueterCutoff_norm_sub_div q q₀ ε).fderiv,
    FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, _root_.Quaternion.sum_inner_dq_single_smul, mul_smul_comm,
    _root_.Quaternion.cauchyFueterKernel_mul_sub, ← _root_.Quaternion.coe_smul]
  congr 1
  ring

/-! ### The mass of the cutoff density -/

/-- The mass of the cutoff density: for every `ε > 0` and every pole `q₀`, the integral of
`ε⁻¹ ψ'(‖dq x - q₀‖ / ε) ‖dq x - q₀‖⁻³` over the coordinate space is `2π²`, where
`ψ = cauchyFueterCutoff`. This is the reciprocal of the normalization of the Cauchy–Fueter
formula. -/
theorem _root_.Quaternion.integral_cauchyFueterCutoff_density (q₀ : ℍ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x : Fin 4 → ℝ, cauchyFueterCutoffDensity ε (dq x) q₀ = 2 * π ^ 2 := by
  simp only [cauchyFueterCutoffDensity_apply]
  rw [Quaternion.integral_fun_norm_dq_sub
    (fun y ↦ ε⁻¹ * deriv cauchyFueterCutoff (y / ε) * (y ^ 3)⁻¹) q₀]
  have h : ∫ y in Ioi (0 : ℝ), y ^ 3 • (ε⁻¹ * deriv cauchyFueterCutoff (y / ε) * (y ^ 3)⁻¹) =
      ∫ y in Ioi (0 : ℝ), ε⁻¹ * deriv cauchyFueterCutoff (ε⁻¹ * y) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have : y ≠ 0 := ne_of_gt hy
    simp only [smul_eq_mul]
    field_simp
  rw [h, integral_const_mul, integral_comp_mul_left_Ioi _ _ (inv_pos.2 hε), mul_zero,
    integral_Ioi_deriv_cauchyFueterCutoff]
  simp [hε.ne']

/-- The cutoff density is integrable on the real coordinate space. -/
theorem integrable_cauchyFueterCutoffDensity {ε : ℝ} (hε : 0 < ε) (q₀ : ℍ) :
    Integrable (fun x : Fin 4 → ℝ ↦ cauchyFueterCutoffDensity ε (dq x) q₀) := by
  -- The nonzero mass rules out the nonintegrable junk value of the Bochner integral.
  apply Integrable.of_integral_ne_zero
  rw [_root_.Quaternion.integral_cauchyFueterCutoff_density q₀ hε]
  positivity

end TauCeti
