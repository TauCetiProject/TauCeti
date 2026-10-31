/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.SobolevQuotient
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.PDE.Yamabe.Bubble.Decay

/-!
# Compactly supported Yamabe bubbles

Let `U_t = U_{t,b}` be the Euclidean Yamabe bubble of scale `t` centred at `b` in dimension
`n > 2`, and let `χ` be a cutoff with values in `[-1, 1]` that equals one on the ball of radius `r`
about `b`. This file bounds the errors made by replacing `U_t` with `χ U_t`, with their sharp
orders in the scale and explicit constants, for every `t > 0`:

* the critical mass satisfies `0 ≤ |Sⁿ| - ∫ |χ U_t| ^ pₙ ≤ (2 t / r) ^ n |Sⁿ|`;
* for compactly supported `C¹` cutoffs, the Dirichlet energy changes by at most
  `(2 t / r) ^ (n - 2) K`, where `K` depends only on `χ` and the bubble of scale `r`.

Consequently the Euclidean Sobolev quotient of `χ U_t` is `Y(Sⁿ) + O(t ^ (n - 2))` as `t → 0⁺`.
These are the cutoff errors in the test-function estimates for the Yamabe invariant: the term of
order `t ^ (n - 2)` is negligible against the curvature correction of order `t ⁴` in dimension
`n ≥ 7`, and comparable to it in dimension six.

All bounds come from comparing, outside the ball of radius `r`, the bubble of scale `t` with the
bubble of scale `r` (`TauCeti.Yamabe.bubble_rpow_criticalExponent_le_mul_of_le_norm_sub` and its
companions), so that no radial integration is needed beyond the exact values of the critical mass
and energy of a bubble.

Every nonempty open set contains a nonnegative smooth compactly supported test function with
positive critical mass and quotient below `Y(Sⁿ) + ε` for any `ε > 0`, as proved by
`TauCeti.Yamabe.exists_contDiff_hasCompactSupport_sobolev_quotient_lt`. No comparison with a
curved metric or manifold Yamabe invariant is asserted.

## Main declarations

* `TauCeti.Yamabe.abs_integral_cutoff_bubble_rpow_criticalExponent_sub_roundSphereVolume_le`:
  the critical mass error.
* `TauCeti.Yamabe.abs_integral_norm_fderiv_cutoff_bubble_sq_sub_le`: the Dirichlet energy error.
* `TauCeti.Yamabe.isBigO_cutoff_bubble_sobolev_quotient_sub_sphereYamabeConstant`: the Sobolev
  quotient of a cutoff bubble is `Y(Sⁿ) + O(t ^ (n - 2))`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3 and §6.
* T. Aubin, *Équations différentielles non linéaires et problème de Yamabe concernant la courbure
  scalaire*, J. Math. Pures Appl. 55 (1976), 269–296.
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open Filter InnerProductSpace MeasureTheory Metric Module Real Set Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma abs_mul_bubble_rpow_criticalExponent (c : ℝ) {t : ℝ} (ht : 0 < t) (b x : E) :
    |c * bubble t b x| ^ criticalExponent (finrank ℝ E) =
      |c| ^ criticalExponent (finrank ℝ E) * bubble t b x ^ criticalExponent (finrank ℝ E) := by
  rw [abs_mul, abs_of_pos (bubble_pos ht b x), Real.mul_rpow (abs_nonneg c) (bubble_pos ht b x).le]

/-! ### The critical mass -/

/-- Multiplying a bubble by a function with values in `[-1, 1]` does not increase its critical
mass, which is the area `|Sⁿ|` of the round sphere. -/
theorem integral_cutoff_bubble_rpow_criticalExponent_le_roundSphereVolume (hn : 2 < finrank ℝ E)
    {χ : E → ℝ} (hχ : ∀ x, |χ x| ≤ 1) {t : ℝ} (ht : 0 < t) (b : E) :
    ∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E) ≤
      roundSphereVolume (finrank ℝ E) := by
  rw [← integral_bubble_rpow_criticalExponent_eq_roundSphereVolume (by omega) hn.ne' ht b]
  refine integral_mono_of_nonneg (.of_forall fun x ↦ by positivity)
    (integrable_bubble_rpow_criticalExponent volume (by omega) hn.ne' ht b)
    (.of_forall fun x ↦ ?_)
  simp only [abs_mul_bubble_rpow_criticalExponent _ ht]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (bubble_pos ht b x).le _)
    (Real.rpow_le_one (abs_nonneg _) (hχ x) (criticalExponent_pos hn).le)

/-- The critical mass lost by multiplying a bubble of scale `t` by a measurable cutoff with values
in `[-1, 1]` that equals one on the ball of radius `r` about its centre is at most
`(2 t / r) ^ n |Sⁿ|`, for every `t > 0`. -/
theorem abs_integral_cutoff_bubble_rpow_criticalExponent_sub_roundSphereVolume_le
    (hn : 2 < finrank ℝ E) {χ : E → ℝ} (hχ : Measurable χ) (hχle : ∀ x, |χ x| ≤ 1) {b : E}
    {r : ℝ} (hr : 0 < r) (hχone : ∀ x ∈ ball b r, χ x = 1) {t : ℝ} (ht : 0 < t) :
    |(∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) -
      roundSphereVolume (finrank ℝ E)| ≤
      (2 * t / r) ^ finrank ℝ E * roundSphereVolume (finrank ℝ E) := by
  have hp := (criticalExponent_pos hn).le
  have hbase := integrable_bubble_rpow_criticalExponent volume (by omega) hn.ne' ht b
  have hcut : Integrable (fun x ↦ |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) := by
    refine hbase.mono' ?_ (.of_forall fun x ↦ ?_)
    · have hU : Measurable (bubble t b) :=
        (contDiff_bubble (m := 0) ht.ne' b).continuous.measurable
      exact (by fun_prop : Measurable fun x ↦
        |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity), abs_mul_bubble_rpow_criticalExponent _ ht]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (bubble_pos ht b x).le _)
        (Real.rpow_le_one (abs_nonneg _) (hχle x) hp)
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr
      (integral_cutoff_bubble_rpow_criticalExponent_le_roundSphereVolume hn hχle ht b))]
  nth_rewrite 1 [← integral_bubble_rpow_criticalExponent_eq_roundSphereVolume (by omega) hn.ne'
    ht b]
  rw [← integral_bubble_rpow_criticalExponent_eq_roundSphereVolume (by omega) hn.ne' hr b,
    ← integral_sub hbase hcut, ← integral_const_mul]
  refine integral_mono (hbase.sub hcut)
    ((integrable_bubble_rpow_criticalExponent volume (by omega) hn.ne' hr b).const_mul _)
    fun x ↦ ?_
  simp only [abs_mul_bubble_rpow_criticalExponent _ ht]
  by_cases hx : x ∈ ball b r
  · rw [hχone x hx, abs_one, Real.one_rpow, one_mul, sub_self]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (bubble_pos hr b x).le _)
  · have hx' : r ≤ ‖x - b‖ := by simpa [mem_ball, dist_eq_norm, not_lt] using hx
    calc
      _ ≤ bubble t b x ^ criticalExponent (finrank ℝ E) :=
        sub_le_self _ (mul_nonneg (by positivity) (Real.rpow_nonneg (bubble_pos ht b x).le _))
      _ ≤ _ := bubble_rpow_criticalExponent_le_mul_of_le_norm_sub hn.ne' ht hr hx'

/-- The critical mass of a bubble multiplied by a fixed measurable cutoff with values in `[-1, 1]`
and equal to one near its centre converges to the area of the round sphere. -/
theorem tendsto_integral_cutoff_bubble_rpow_criticalExponent (hn : 2 < finrank ℝ E)
    {χ : E → ℝ} (hχ : Measurable χ) (hχle : ∀ x, |χ x| ≤ 1)
    (b : E) (hχone : χ =ᶠ[𝓝 b] fun _ ↦ 1) :
    Tendsto (fun t : ℝ ↦ ∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E))
      (𝓝[>] 0) (𝓝 (roundSphereVolume (finrank ℝ E))) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hχone
  have hlim : Tendsto (fun t : ℝ ↦ (2 * t / r) ^ finrank ℝ E * roundSphereVolume (finrank ℝ E))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ ↦
        (2 * t / r) ^ finrank ℝ E * roundSphereVolume (finrank ℝ E) := by
      fun_prop
    simpa [zero_pow (show finrank ℝ E ≠ 0 by omega)] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ hlim)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact abs_integral_cutoff_bubble_rpow_criticalExponent_sub_roundSphereVolume_le hn hχ hχle hr
    hball ht

/-! ### The Dirichlet energy -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Outside the ball of radius `r`, the change of the squared differential of a bubble of scale `t`
under a cutoff with values in `[-1, 1]` is controlled by the bubble of scale `r`. -/
private lemma abs_norm_fderiv_cutoff_bubble_sq_sub_le (hn : 2 < finrank ℝ E) {χ : E → ℝ}
    {x : E} (hχ : DifferentiableAt ℝ χ x) (hχle : |χ x| ≤ 1) {b : E} {r t : ℝ} (hr : 0 < r)
    (ht : 0 < t) (hx : r ≤ ‖x - b‖) :
    |‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2 - ‖fderiv ℝ (bubble t b) x‖ ^ 2| ≤
      (2 * t / r) ^ (finrank ℝ E - 2) *
        (12 * ‖fderiv ℝ (bubble r b) x‖ ^ 2 + 2 * ‖fderiv ℝ χ x‖ ^ 2 * bubble r b x ^ 2) := by
  set A := ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖
  set B := ‖fderiv ℝ (bubble t b) x‖
  set c := ‖fderiv ℝ χ x‖
  set s := (2 * t / r) ^ (finrank ℝ E - 2)
  have hU := (bubble_pos ht b x).le
  have hmul : A = ‖χ x • fderiv ℝ (bubble t b) x + bubble t b x • fderiv ℝ χ x‖ :=
    congrArg norm (fderiv_fun_mul hχ ((contDiff_bubble (m := 1) ht.ne' b).differentiable_one x))
  have hA : A ≤ B + bubble t b x * c := by
    rw [hmul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hχle
    · rw [norm_smul, Real.norm_of_nonneg hU]
  have hB := norm_fderiv_bubble_sq_le_mul_of_le_norm_sub hn.le ht hr hx
  have hU2 := bubble_sq_le_mul_of_le_norm_sub hn.le ht hr hx
  have hA2 : A ^ 2 ≤ 2 * B ^ 2 + 2 * (bubble t b x ^ 2 * c ^ 2) := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hA 2, sq_nonneg (B - bubble t b x * c)]
  have hc2 : bubble t b x ^ 2 * c ^ 2 ≤ s * bubble r b x ^ 2 * c ^ 2 :=
    mul_le_mul_of_nonneg_right hU2 (sq_nonneg c)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg A, sq_nonneg B]

/-- Multiplying a bubble of scale `t` by a compactly supported `C¹` cutoff `χ` with values in
`[-1, 1]` that equals one on the ball of radius `r` about its centre changes its Dirichlet energy
by at most `(2 t / r) ^ (n - 2) ∫ (12 ‖dU_r‖² + 2 ‖dχ‖² U_r²)`, for every `t > 0`. The constant
depends only on the cutoff and the bubble `U_r` of scale `r`. -/
theorem abs_integral_norm_fderiv_cutoff_bubble_sq_sub_le (hn : 2 < finrank ℝ E) {χ : E → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (hχle : ∀ x, |χ x| ≤ 1) {b : E} {r : ℝ}
    (hr : 0 < r) (hχone : ∀ x ∈ ball b r, χ x = 1) {t : ℝ} (ht : 0 < t) :
    |(∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) -
      ∫ x, ‖fderiv ℝ (bubble t b) x‖ ^ 2| ≤
      (2 * t / r) ^ (finrank ℝ E - 2) *
        ∫ x, (12 * ‖fderiv ℝ (bubble r b) x‖ ^ 2 + 2 * ‖fderiv ℝ χ x‖ ^ 2 * bubble r b x ^ 2) := by
  have hcut : Integrable (fun x ↦ ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) := by
    have hcd : ContDiff ℝ 1 (fun y ↦ χ y * bubble t b y) := hχ.mul (contDiff_bubble ht.ne' b)
    have hcont : Continuous fun x ↦ ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2 :=
      (hcd.continuous_fderiv one_ne_zero).norm.pow 2
    have hcc : HasCompactSupport (fun y ↦ χ y * bubble t b y) := hχc.mul_right
    exact hcont.integrable_of_hasCompactSupport
      ((hcc.fderiv ℝ).comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp))
  have hcχ : Integrable (fun x ↦ ‖fderiv ℝ χ x‖ ^ 2 * bubble r b x ^ 2) := by
    have hcont : Continuous fun x ↦ ‖fderiv ℝ χ x‖ ^ 2 * bubble r b x ^ 2 :=
      ((hχ.continuous_fderiv one_ne_zero).norm.pow 2).mul
        ((contDiff_bubble (m := 0) hr.ne' b).continuous.pow 2)
    have hcc : HasCompactSupport fun x ↦ ‖fderiv ℝ χ x‖ ^ 2 :=
      (hχc.fderiv ℝ).comp_left (g := fun v ↦ ‖v‖ ^ 2) (by simp)
    exact hcont.integrable_of_hasCompactSupport hcc.mul_right
  have hbound : Integrable (fun x ↦
      12 * ‖fderiv ℝ (bubble r b) x‖ ^ 2 + 2 * ‖fderiv ℝ χ x‖ ^ 2 * bubble r b x ^ 2) :=
    ((integrable_norm_fderiv_bubble_sq volume hn hr b).const_mul 12).add
      (by simpa only [mul_assoc] using hcχ.const_mul 2)
  rw [← integral_sub hcut (integrable_norm_fderiv_bubble_sq volume hn ht b),
    ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono (hcut.sub
    (integrable_norm_fderiv_bubble_sq volume hn ht b)).abs (hbound.const_mul _) fun x ↦ ?_)
  by_cases hx : x ∈ ball b r
  · have hlocal : (fun y ↦ χ y * bubble t b y) =ᶠ[𝓝 x] bubble t b := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      simp [hχone y hy]
    simp only [hlocal.fderiv_eq, sub_self, abs_zero]
    positivity
  · exact abs_norm_fderiv_cutoff_bubble_sq_sub_le hn (hχ.differentiable_one x) (hχle x) hr ht
      (by simpa [mem_ball, dist_eq_norm, not_lt] using hx)

/-- The conformal Dirichlet energy of a bubble multiplied by a fixed compactly supported `C¹`
cutoff with values in `[-1, 1]` and equal to one near the centre converges to
`n (n - 1) |Sⁿ|`, the conformal energy of an uncut bubble, in dimension `n > 2`. -/
theorem tendsto_conformalCoefficient_mul_integral_norm_fderiv_cutoff_bubble_sq
    (hn : 2 < finrank ℝ E) {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) (hχle : ∀ x, |χ x| ≤ 1)
    (b : E) (hχone : χ =ᶠ[𝓝 b] fun _ ↦ 1) :
    Tendsto (fun t : ℝ ↦ conformalCoefficient (finrank ℝ E) *
      ∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2)
      (𝓝[>] 0) (𝓝 ((finrank ℝ E : ℝ) * (finrank ℝ E - 1) *
        roundSphereVolume (finrank ℝ E))) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hχone
  set K := ∫ x, (12 * ‖fderiv ℝ (bubble r b) x‖ ^ 2 + 2 * ‖fderiv ℝ χ x‖ ^ 2 * bubble r b x ^ 2)
  have hlim : Tendsto (fun t : ℝ ↦ (2 * t / r) ^ (finrank ℝ E - 2) * K) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ ↦ (2 * t / r) ^ (finrank ℝ E - 2) * K := by fun_prop
    simpa [zero_pow (show finrank ℝ E - 2 ≠ 0 by omega)] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto (fun t : ℝ ↦
      (∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) -
        ∫ x, ‖fderiv ℝ (bubble t b) x‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact abs_integral_norm_fderiv_cutoff_bubble_sq_sub_le hn hχ hχc hχle hr hball ht
  have hlim := (hdiff.const_mul (conformalCoefficient (finrank ℝ E))).add_const
    ((finrank ℝ E : ℝ) * (finrank ℝ E - 1) * roundSphereVolume (finrank ℝ E))
  simp only [mul_zero, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [← conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_roundSphereVolume hn ht b]
  ring

/-! ### The Sobolev quotient -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Yamabe constant of the round sphere as the quotient of the conformal energy
`n (n - 1) |Sⁿ|` of a bubble by the power `2 / pₙ` of its critical mass `|Sⁿ|`. -/
private lemma sphereYamabeConstant_eq_div {n : ℕ} (hn : n ≠ 0) :
    sphereYamabeConstant n =
      (n : ℝ) * (n - 1) * roundSphereVolume n / roundSphereVolume n ^ (2 / criticalExponent n) := by
  rw [eq_div_iff (Real.rpow_pos_of_pos (roundSphereVolume_pos n) _).ne', two_div_criticalExponent]
  exact sphereYamabeConstant_mul_roundSphereVolume_rpow hn

/-- The actual Euclidean Sobolev quotient of a fixed compact cutoff of the concentrating bubble
converges to the Yamabe constant of the round sphere. The cutoff only needs to be `C¹`. -/
theorem tendsto_cutoff_bubble_sobolev_quotient (hn : 2 < finrank ℝ E)
    {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχle : ∀ x, |χ x| ≤ 1)
    (b : E) (hχone : χ =ᶠ[𝓝 b] fun _ ↦ 1) :
    Tendsto (fun t : ℝ ↦
      (conformalCoefficient (finrank ℝ E) *
        ∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) /
      (∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) ^
        (2 / criticalExponent (finrank ℝ E)))
      (𝓝[>] 0) (𝓝 (sphereYamabeConstant (finrank ℝ E))) := by
  have hmass := tendsto_integral_cutoff_bubble_rpow_criticalExponent hn
    hχ.continuous.measurable hχle b hχone
  have hden := hmass.rpow_const (p := 2 / criticalExponent (finrank ℝ E))
    (Or.inl (roundSphereVolume_pos (finrank ℝ E)).ne')
  have henergy := tendsto_conformalCoefficient_mul_integral_norm_fderiv_cutoff_bubble_sq
    hn hχ hχc hχle b hχone
  have hlim := henergy.div hden (Real.rpow_pos_of_pos (roundSphereVolume_pos _) _).ne'
  simpa only [Pi.div_def, ← sphereYamabeConstant_eq_div (show finrank ℝ E ≠ 0 by omega)]
    using hlim

/-- A perturbation estimate for quotients: if `(1 - δ) b ≤ a ≤ b` with `δ ≤ 1 / 2` and
`|x - y| ≤ e`, then `|x / a - y / b| ≤ 2 (e + y δ) / b`. -/
private lemma abs_div_sub_div_le {x y a b e δ : ℝ} (hb : 0 < b) (hy : 0 ≤ y) (hδ : δ ≤ 1 / 2)
    (hab : (1 - δ) * b ≤ a) (hab' : a ≤ b) (hxy : |x - y| ≤ e) :
    |x / a - y / b| ≤ 2 * (e + y * δ) / b := by
  have hδ0 : 0 ≤ δ := by nlinarith
  have ha : b ≤ 2 * a := by nlinarith
  have he : 0 ≤ e + y * δ := add_nonneg ((abs_nonneg _).trans hxy) (mul_nonneg hy hδ0)
  have h1 : |x * b - a * y| ≤ (e + y * δ) * b := by
    calc
      |x * b - a * y| = |(x - y) * b + y * (b - a)| := by ring_nf
      _ ≤ |(x - y) * b| + |y * (b - a)| := abs_add_le _ _
      _ = |x - y| * b + y * (b - a) := by
        rw [abs_mul, abs_of_pos hb, abs_of_nonneg (mul_nonneg hy (by linarith))]
      _ ≤ e * b + y * (δ * b) :=
        add_le_add (mul_le_mul_of_nonneg_right hxy hb.le)
          (mul_le_mul_of_nonneg_left (by linarith) hy)
      _ = (e + y * δ) * b := by ring
  rw [div_sub_div _ _ (by linarith : a ≠ 0) hb.ne', abs_div, abs_of_pos (by nlinarith : 0 < a * b),
    div_le_div_iff₀ (by nlinarith) hb]
  calc
    |x * b - a * y| * b ≤ (e + y * δ) * b * b := mul_le_mul_of_nonneg_right h1 hb.le
    _ ≤ (e + y * δ) * b * (2 * a) := mul_le_mul_of_nonneg_left ha (mul_nonneg he hb.le)
    _ = 2 * (e + y * δ) * (a * b) := by ring

/-- Two-sided bounds for the power `2 / pₙ` of the critical mass of a cutoff bubble:
`(1 - (2 t / r) ^ n) |Sⁿ| ^ (2 / pₙ) ≤ (∫ |χ U_t| ^ pₙ) ^ (2 / pₙ) ≤ |Sⁿ| ^ (2 / pₙ)`. -/
private lemma cutoff_bubble_critical_norm_bounds (hn : 2 < finrank ℝ E) {χ : E → ℝ}
    (hχ : Measurable χ) (hχle : ∀ x, |χ x| ≤ 1) {b : E} {r : ℝ} (hr : 0 < r)
    (hχone : ∀ x ∈ ball b r, χ x = 1) {t : ℝ} (ht : 0 < t) (hs : (2 * t / r) ^ finrank ℝ E ≤ 1) :
    (1 - (2 * t / r) ^ finrank ℝ E) *
        roundSphereVolume (finrank ℝ E) ^ (2 / criticalExponent (finrank ℝ E)) ≤
      (∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) ^
        (2 / criticalExponent (finrank ℝ E)) ∧
    (∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) ^
        (2 / criticalExponent (finrank ℝ E)) ≤
      roundSphereVolume (finrank ℝ E) ^ (2 / criticalExponent (finrank ℝ E)) := by
  have hn' : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
  have hV := roundSphereVolume_pos (finrank ℝ E)
  have hq0 : 0 ≤ 2 / criticalExponent (finrank ℝ E) :=
    div_nonneg zero_le_two (criticalExponent_pos hn).le
  have hq1 : 2 / criticalExponent (finrank ℝ E) ≤ 1 := by
    rw [two_div_criticalExponent, div_le_one (by positivity)]
    linarith
  have hs0 : 0 ≤ 1 - (2 * t / r) ^ finrank ℝ E := sub_nonneg.mpr hs
  have hlow : (1 - (2 * t / r) ^ finrank ℝ E) * roundSphereVolume (finrank ℝ E) ≤
      ∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E) := by
    have := (abs_le.mp (abs_integral_cutoff_bubble_rpow_criticalExponent_sub_roundSphereVolume_le
      hn hχ hχle hr hχone ht)).1
    linarith
  refine ⟨?_, Real.rpow_le_rpow (by positivity)
    (integral_cutoff_bubble_rpow_criticalExponent_le_roundSphereVolume hn hχle ht b) hq0⟩
  calc
    _ ≤ (1 - (2 * t / r) ^ finrank ℝ E) ^ (2 / criticalExponent (finrank ℝ E)) *
        roundSphereVolume (finrank ℝ E) ^ (2 / criticalExponent (finrank ℝ E)) :=
      mul_le_mul_of_nonneg_right (Real.self_le_rpow_of_le_one hs0 (by
        linarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * t / r) (finrank ℝ E)]) hq1)
        (by positivity)
    _ = _ := (Real.mul_rpow hs0 hV.le).symm
    _ ≤ _ := Real.rpow_le_rpow (mul_nonneg hs0 hV.le) hlow hq0

/-- The Euclidean Sobolev quotient `aₙ ∫ |∇(χ U_t)|² / ‖χ U_t‖_{pₙ}²` of a bubble of scale `t`
multiplied by a fixed compactly supported `C¹` cutoff `χ` with values in `[-1, 1]`, equal to one
near the centre, differs from the Yamabe constant `Y(Sⁿ)` of the round sphere by
`O(t ^ (n - 2))` as `t → 0⁺`. -/
theorem isBigO_cutoff_bubble_sobolev_quotient_sub_sphereYamabeConstant (hn : 2 < finrank ℝ E)
    {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (hχle : ∀ x, |χ x| ≤ 1)
    (b : E) (hχone : χ =ᶠ[𝓝 b] fun _ ↦ 1) :
    (fun t : ℝ ↦ (conformalCoefficient (finrank ℝ E) *
        ∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) /
      (∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) ^
        (2 / criticalExponent (finrank ℝ E)) - sphereYamabeConstant (finrank ℝ E))
      =O[𝓝[>] 0] fun t ↦ t ^ (finrank ℝ E - 2) := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hχone
  set n := finrank ℝ E
  set D := roundSphereVolume n ^ (2 / criticalExponent n)
  set N := (n : ℝ) * (n - 1) * roundSphereVolume n
  set a := conformalCoefficient n
  set K := ∫ x, (12 * ‖fderiv ℝ (bubble r b) x‖ ^ 2 + 2 * ‖fderiv ℝ χ x‖ ^ 2 * bubble r b x ^ 2)
  have hD : 0 < D := Real.rpow_pos_of_pos (roundSphereVolume_pos n) _
  have hn' : (2 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 ≤ N := mul_nonneg (mul_nonneg (by positivity) (by linarith))
    (roundSphereVolume_pos n).le
  have ha : 0 ≤ a := (conformalCoefficient_pos hn).le
  refine Asymptotics.IsBigO.of_bound (2 * (a * K + N) / D * (2 / r) ^ (n - 2)) ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (Iio_mem_nhds (show (0 : ℝ) < r / 4 by positivity))] with t ht htr
  have ht : 0 < t := mem_Ioi.mp ht
  set s := 2 * t / r
  have hs0 : 0 ≤ s := by positivity
  have hs : s ≤ 1 / 2 := by
    rw [div_le_iff₀ hr]
    linarith [mem_Iio.mp htr]
  have hsn : s ^ n ≤ s ^ (n - 2) := pow_le_pow_of_le_one hs0 (by linarith) (Nat.sub_le n 2)
  have hsn' : s ^ n ≤ 1 / 2 := (pow_le_of_le_one hs0 (by linarith) (by omega)).trans hs
  -- The energy error of the cutoff, compared with the energy `N` of the uncut bubble.
  have hE : |a * (∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) - N| ≤
      a * (s ^ (n - 2) * K) := by
    have hN' : a * ∫ x, ‖fderiv ℝ (bubble t b) x‖ ^ 2 = N :=
      conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_roundSphereVolume hn ht b
    rw [← hN', ← mul_sub, abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left
      (abs_integral_norm_fderiv_cutoff_bubble_sq_sub_le hn hχ hχc hχle hr hball ht) ha
  -- The mass error enters through the denominator.
  obtain ⟨hlow, hup⟩ := cutoff_bubble_critical_norm_bounds hn hχ.continuous.measurable hχle hr
    hball ht (by linarith)
  rw [sphereYamabeConstant_eq_div (by omega), Real.norm_eq_abs,
    Real.norm_of_nonneg (by positivity)]
  refine (abs_div_sub_div_le hD hN hsn' hlow hup hE).trans ?_
  have hst : s ^ (n - 2) = (2 / r) ^ (n - 2) * t ^ (n - 2) := by
    rw [← mul_pow, div_mul_eq_mul_div]
  calc
    2 * (a * (s ^ (n - 2) * K) + N * s ^ n) / D ≤
        2 * (a * (s ^ (n - 2) * K) + N * s ^ (n - 2)) / D := by
      gcongr
    _ = _ := by
      rw [hst]
      ring

/-- Every nonempty open set in dimension greater than two contains a nonnegative smooth
compactly supported test function with positive critical mass and Sobolev quotient less than
`Y(Sⁿ) + ε`. Thus restricting to compactly supported smooth tests cannot improve the sphere
constant in the Euclidean Sobolev inequality. -/
theorem exists_contDiff_hasCompactSupport_sobolev_quotient_lt (hn : 2 < finrank ℝ E)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩne : Ω.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ω ∧
      (∀ x, 0 ≤ u x) ∧ (0 < ∫ x, |u x| ^ criticalExponent (finrank ℝ E)) ∧
      (conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ u x‖ ^ 2) /
        (∫ x, |u x| ^ criticalExponent (finrank ℝ E)) ^
          (2 / criticalExponent (finrank ℝ E)) < sphereYamabeConstant (finrank ℝ E) + ε := by
  obtain ⟨b, hb⟩ := hΩne
  obtain ⟨χ, hχ, hχrange, hχone, hχc, hχΩ⟩ :=
    (isCompact_singleton (x := b)).exists_contDiff_cutoff hΩ (singleton_subset_iff.mpr hb)
  have hχrange' (x : E) : χ x ∈ Icc (0 : ℝ) 1 := hχrange (mem_range_self x)
  have hχle (x : E) : |χ x| ≤ 1 := abs_le.mpr ⟨by linarith [(hχrange' x).1], (hχrange' x).2⟩
  have hχone' : χ =ᶠ[𝓝 b] fun _ ↦ 1 := by
    filter_upwards [mem_interior_iff_mem_nhds.mp (hχone (mem_singleton b))] with x hx
    exact hx
  have hm := tendsto_integral_cutoff_bubble_rpow_criticalExponent hn hχ.continuous.measurable hχle
    b hχone'
  have hq := tendsto_cutoff_bubble_sobolev_quotient hn (hχ.of_le (by simp)) hχc hχle b hχone'
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧
      (0 < ∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) ∧
      (conformalCoefficient (finrank ℝ E) *
        ∫ x, ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ^ 2) /
        (∫ x, |χ x * bubble t b x| ^ criticalExponent (finrank ℝ E)) ^
          (2 / criticalExponent (finrank ℝ E)) < sphereYamabeConstant (finrank ℝ E) + ε := by
    filter_upwards [self_mem_nhdsWithin,
      hm.eventually_const_lt (roundSphereVolume_pos (finrank ℝ E)),
      hq.eventually_lt_const (lt_add_of_pos_right _ hε)] with t ht hmt hqt
    exact ⟨ht, hmt, hqt⟩
  obtain ⟨t, ht, hmt, hqt⟩ := hev.exists
  refine ⟨fun x ↦ χ x * bubble t b x, hχ.mul (contDiff_bubble ht.ne' b), hχc.mul_right,
    tsupport_mul_subset_left.trans hχΩ, fun x ↦ mul_nonneg (hχrange' x).1 (bubble_pos ht b x).le,
    hmt, hqt⟩

end TauCeti.Yamabe
