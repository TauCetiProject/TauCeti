/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Potential
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.MeasureTheory.Integral.MeanInequalities
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Morrey's inequality for `C¹` functions

Let `E` be a finite-dimensional real normed space of dimension `n`, let `μ` be an additive Haar
measure on `E`, and let `p > n`. This file proves Morrey's inequality: a `C¹` function whose
derivative lies in `Lᵖ` is Hölder continuous of exponent `1 - n / p`, with

`‖u x - u y‖ ≤ C(n, p, μ) * ‖x - y‖ ^ (1 - n / p) * ‖Du‖_{Lᵖ}`.

The constant is explicit. Writing `ω = μ(B(0, 1))` and `K = n ω (p - 1) / (p - n)`, it is
`C = 2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * 2 ^ (1 - n / p)`. For `n ≥ 2` it blows up as
`p ↓ n`, as it must, since the embedding fails in the borderline case `p = n`. For `n = 1` one has
`K = ω` independently of `p`, and no blow-up occurs.

The proof starts from the pointwise potential estimate behind the Poincaré–Wirtinger inequality
(`TauCeti.enorm_sub_setAverage_le_of_starConvex`), which bounds the deviation of `u x` from a mean
of `u` by the Riesz potential `∫ ‖Du y‖ ‖x - y‖ ^ (1 - n) dy`. For `p > n`, Hölder's inequality
bounds that potential by `‖Du‖_{Lᵖ}`, because the conjugate power `‖x - y‖ ^ ((1 - n) p')` of
the kernel is integrable near the pole exactly when `p > n`. Comparing `u x` and `u y` with the
mean of `u` over a ball containing both points gives the Hölder estimate.

## Main declarations

* `TauCeti.setLIntegral_mul_enorm_sub_rpow_one_sub_finrank_le`: for `p > n`, the Riesz potential
  of order one of `g`, over a set of radius `D` about the pole, is at most
  `K ^ (1 - 1 / p) * D ^ (1 - n / p) * ‖g‖_{Lᵖ}`.
* `TauCeti.enorm_sub_setAverage_le_of_starConvex_of_finrank_lt`: the deviation of `u x` from the
  mean of `u` over a subset of a star-convex domain, bounded by `‖Du‖_{Lᵖ}`.
* `TauCeti.enorm_sub_setAverage_le_of_convex_of_finrank_lt`: the same on a bounded convex domain.
* `TauCeti.enorm_sub_le_of_mem_ball_of_finrank_lt`: Morrey's inequality on a ball.
* `TauCeti.enorm_sub_le_of_contDiff_of_finrank_lt`: Morrey's inequality on the whole space.
* `TauCeti.holderWith_of_contDiff_of_finrank_lt`: a `C¹` function with derivative in `Lᵖ`,
  `p > n`, is Hölder continuous of exponent `1 - n / p`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.17.
* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω S : Set E} {x : E} {D : ℝ} {p : ℝ≥0}

/-- **The Riesz potential of order one is bounded on `Lᵖ` for `p > n`.** If `Ω` lies in
`closedBall x D` and `p` exceeds the dimension `n` of the space, then the Riesz potential at `x`
of a function `g` on `Ω` is at most `K ^ (1 - 1 / p) * D ^ (1 - n / p)` times the `Lᵖ(Ω)` norm of
`g`, where `K = n μ(B(0, 1)) (p - 1) / (p - n)`. -/
theorem setLIntegral_mul_enorm_sub_rpow_one_sub_finrank_le (hD : Ω ⊆ closedBall x D)
    {g : E → ℝ≥0∞} (hg : AEMeasurable g (μ.restrict Ω)) (hp : (finrank ℝ E : ℝ≥0) < p) :
    ∫⁻ y in Ω, g y * ‖x - y‖ₑ ^ (1 - (finrank ℝ E : ℝ)) ∂μ ≤
      ENNReal.ofReal ((finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^
          (1 - 1 / (p : ℝ)) * D ^ (1 - finrank ℝ E / (p : ℝ))) *
        (∫⁻ y in Ω, g y ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) := by
  set n := finrank ℝ E with hn_def
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In dimension zero the kernel vanishes.
    have hzero : ∀ y, g y * ‖x - y‖ₑ ^ (1 - (n : ℝ)) = 0 := fun y => by
      simp [n, Subsingleton.elim x y, finrank_zero_of_subsingleton]
    simp [hzero]
  rcases lt_or_ge D 0 with hD0 | hD0
  · have hΩ : Ω = ∅ := eq_empty_of_subset_empty (hD.trans (closedBall_eq_empty.2 hD0).subset)
    simp [hΩ]
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast finrank_pos
  have hpn : (n : ℝ) < p := by exact_mod_cast hp
  have hp1 : 1 < (p : ℝ) := hn.trans_lt hpn
  -- The exponent conjugate to `p`, and the power of the kernel that it produces.
  set q : ℝ := p / (p - 1) with hq_def
  have hpq : (p : ℝ).HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp1).2 rfl
  have he : (n : ℝ) + (1 - n) * q = (p - n) / (p - 1) := by
    rw [hq_def]
    field_simp [(by linarith : (p : ℝ) - 1 ≠ 0)]
    ring_nf
  have hs : -(n : ℝ) < (1 - n) * q := by
    have : 0 < (n : ℝ) + (1 - n) * q := he ▸ div_pos (by linarith) (by linarith)
    linarith
  have hk : AEMeasurable (fun y => ‖x - y‖ₑ ^ (1 - (n : ℝ))) (μ.restrict Ω) := by fun_prop
  -- The integral of the conjugate power of the kernel.
  set K : ℝ := n * μ.real (ball 0 1) * (p - 1) / (p - n)
  have hK : 0 ≤ K := div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  have hkernel : ∫⁻ y in Ω, (‖x - y‖ₑ ^ (1 - (n : ℝ))) ^ q ∂μ ≤
      ENNReal.ofReal (K * D ^ (((p : ℝ) - n) / ((p : ℝ) - 1))) :=
    calc
      _ ≤ ∫⁻ y in closedBall x D, ‖x - y‖ₑ ^ ((1 - n) * q) ∂μ := by
        simp_rw [← ENNReal.rpow_mul]
        exact lintegral_mono_set hD
      _ = _ := by
        rw [setLIntegral_closedBall_enorm_sub_rpow hs hD0, ← hn_def, he]
        congr 1
        simp only [K]
        field_simp
  have hexp : ((p : ℝ) - n) / (p - 1) * (1 / q) = 1 - n / p := by
    rw [hq_def]
    field_simp [(by linarith : (p : ℝ) - 1 ≠ 0)]
  have hq' : 1 / q = 1 - 1 / (p : ℝ) := by
    rw [hq_def]
    field_simp
  calc
    _ ≤ (∫⁻ y in Ω, g y ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) *
        (∫⁻ y in Ω, (‖x - y‖ₑ ^ (1 - (n : ℝ))) ^ q ∂μ) ^ (1 / q) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq hg hk
    _ ≤ (∫⁻ y in Ω, g y ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) *
        ENNReal.ofReal (K * D ^ (((p : ℝ) - n) / ((p : ℝ) - 1))) ^ (1 / q) := by
      gcongr
    _ = _ := by
      rw [mul_comm, ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hK (Real.rpow_nonneg hD0 _))
        (one_div_nonneg.2 hpq.symm.nonneg), Real.mul_rpow hK (by positivity),
        ← Real.rpow_mul hD0, hexp, hq']

/-- **The Morrey potential estimate for the mean.** If `u` is `C¹` on an open set `Ω` which is
star-convex about `x` and contained in `closedBall x D`, and `p` exceeds the dimension `n` of the
space, then for every `S ⊆ Ω` of positive measure the deviation of `u x` from the mean of `u`
over `S` is at most `D ^ n / (n μ(S)) * K ^ (1 - 1 / p) * D ^ (1 - n / p)` times the `Lᵖ(Ω)`
norm of the derivative of `u`, where `K = n μ(B(0, 1)) (p - 1) / (p - n)`. -/
theorem enorm_sub_setAverage_le_of_starConvex_of_finrank_lt [CompleteSpace F] (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 1 u Ω) (hx : StarConvex ℝ x Ω) (hD : Ω ⊆ closedBall x D) (hS : S ⊆ Ω)
    (hS₀ : μ S ≠ 0) (hp : (finrank ℝ E : ℝ≥0) < p) :
    ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤
      ENNReal.ofReal (D ^ finrank ℝ E / finrank ℝ E) / μ S *
        ENNReal.ofReal ((finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^
          (1 - 1 / (p : ℝ)) * D ^ (1 - finrank ℝ E / (p : ℝ))) *
        eLpNorm (fderiv ℝ u) p (μ.restrict Ω) := by
  have hcont := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  rw [eLpNorm_nnreal_eq_lintegral (zero_le.trans_lt hp).ne', mul_assoc]
  refine (enorm_sub_setAverage_le_of_starConvex hΩ hu hx hD hS hS₀).trans ?_
  gcongr
  exact setLIntegral_mul_enorm_sub_rpow_one_sub_finrank_le hD
    (hcont.enorm.aemeasurable hΩ.measurableSet) hp

/-- **The Morrey potential estimate on a convex domain.** If `u` is `C¹` on a bounded convex
open set `Ω`, `x ∈ Ω`, and `p` exceeds the dimension `n` of the space, then for every `S ⊆ Ω`
of positive measure the deviation of `u x` from the mean of `u` over `S` is at most
`d ^ n / (n μ(S)) * K ^ (1 - 1 / p) * d ^ (1 - n / p)` times the `Lᵖ(Ω)` norm of the derivative
of `u`, where `d = diam Ω` and `K = n μ(B(0, 1)) (p - 1) / (p - n)`. -/
theorem enorm_sub_setAverage_le_of_convex_of_finrank_lt [CompleteSpace F] (hΩ : IsOpen Ω)
    (hΩc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 1 u Ω) (hx : x ∈ Ω)
    (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0) (hp : (finrank ℝ E : ℝ≥0) < p) :
    ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤
      ENNReal.ofReal (diam Ω ^ finrank ℝ E / finrank ℝ E) / μ S *
        ENNReal.ofReal ((finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^
          (1 - 1 / (p : ℝ)) * diam Ω ^ (1 - finrank ℝ E / (p : ℝ))) *
        eLpNorm (fderiv ℝ u) p (μ.restrict Ω) :=
  enorm_sub_setAverage_le_of_starConvex_of_finrank_lt hΩ hu (hΩc.starConvex hx)
    (fun _ hy => mem_closedBall.2 (dist_le_diam_of_mem hb hy hx)) hS hS₀ hp

/-- **Morrey's inequality on a ball.** If `u` is `C¹` on `ball z r` and `p` exceeds the dimension
`n` of the space, then for all `x, y` in the ball, `‖u x - u y‖` is at most
`2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * (2 r) ^ (1 - n / p)` times the `Lᵖ` norm of the
derivative of `u` on the ball, where `ω = μ(B(0, 1))` and `K = n ω (p - 1) / (p - n)`. -/
theorem enorm_sub_le_of_mem_ball_of_finrank_lt [CompleteSpace F] {z : E} {r : ℝ}
    (hu : ContDiffOn ℝ 1 u (ball z r)) {x y : E} (hx : x ∈ ball z r) (hy : y ∈ ball z r)
    (hp : (finrank ℝ E : ℝ≥0) < p) :
    ‖u x - u y‖ₑ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / (finrank ℝ E * μ.real (ball 0 1)) *
        (finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^ (1 - 1 / (p : ℝ)) *
          (2 * r) ^ (1 - finrank ℝ E / (p : ℝ))) *
        eLpNorm (fderiv ℝ u) p (μ.restrict (ball z r)) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [Subsingleton.elim x y]
  set n := finrank ℝ E
  set ω := μ.real (ball (0 : E) 1) with hω_def
  set K : ℝ := n * ω * (p - 1) / (p - n)
  set N := eLpNorm (fderiv ℝ u) p (μ.restrict (ball z r))
  have hr : 0 < r := pos_of_mem_ball hx
  have hball₀ : μ (ball z r) ≠ 0 := (measure_ball_pos μ z hr).ne'
  -- Each point of the ball sees the whole ball within distance `2 r`.
  have hmean : ∀ w ∈ ball z r, ‖u w - ⨍ v in ball z r, u v ∂μ‖ₑ ≤
      ENNReal.ofReal ((2 * r) ^ n / n) / μ (ball z r) *
        ENNReal.ofReal (K ^ (1 - 1 / (p : ℝ)) * (2 * r) ^ (1 - n / (p : ℝ))) * N :=
    fun w hw => enorm_sub_setAverage_le_of_starConvex_of_finrank_lt isOpen_ball hu
      ((convex_ball z r).starConvex hw) (fun v hv => mem_closedBall.2 (by
        linarith [dist_triangle v z w, mem_ball.1 hv, mem_ball'.1 hw])) subset_rfl hball₀ hp
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast finrank_pos
  have hpn : (n : ℝ) < p := by exact_mod_cast hp
  have hK : 0 ≤ K := div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  -- The constant: the mean-value factor `(2 r) ^ n / (n μ(ball z r))` is `2 ^ n / (n ω)`.
  have hconst : ENNReal.ofReal ((2 * r) ^ n / n) / μ (ball z r) *
      ENNReal.ofReal (K ^ (1 - 1 / (p : ℝ)) * (2 * r) ^ (1 - n / (p : ℝ))) * N +
      ENNReal.ofReal ((2 * r) ^ n / n) / μ (ball z r) *
      ENNReal.ofReal (K ^ (1 - 1 / (p : ℝ)) * (2 * r) ^ (1 - n / (p : ℝ))) * N =
      ENNReal.ofReal (2 ^ (n + 1) / (n * ω) * K ^ (1 - 1 / (p : ℝ)) *
        (2 * r) ^ (1 - n / (p : ℝ))) * N := by
    have hX : 0 ≤ (2 * r) ^ n / n / (r ^ n * ω) := by
      have := hr.le
      positivity
    have hY : 0 ≤ K ^ (1 - 1 / (p : ℝ)) * (2 * r) ^ (1 - n / (p : ℝ)) :=
      mul_nonneg (Real.rpow_nonneg hK _) (Real.rpow_nonneg (by linarith) _)
    rw [Measure.addHaar_ball_of_pos μ z hr, ← ofReal_measureReal measure_ball_lt_top.ne,
      ← hω_def, ← ENNReal.ofReal_mul (pow_nonneg hr.le _),
      ← ENNReal.ofReal_div_of_pos (mul_pos (pow_pos hr _) hω), ← ENNReal.ofReal_mul hX,
      ← add_mul, ← ENNReal.ofReal_add (mul_nonneg hX hY) (mul_nonneg hX hY)]
    congr 2
    rw [mul_pow, pow_succ]
    field_simp
    ring
  calc
    ‖u x - u y‖ₑ ≤ ‖u x - ⨍ v in ball z r, u v ∂μ‖ₑ + ‖u y - ⨍ v in ball z r, u v ∂μ‖ₑ := by
      simpa only [edist_eq_enorm_sub] using edist_triangle_right (u x) (u y) _
    _ ≤ _ := add_le_add (hmean x hx) (hmean y hy)
    _ = _ := hconst

/-- **Morrey's inequality.** If `u` is `C¹` on the whole space and `p` exceeds the dimension `n`
of the space, then `‖u x - u y‖` is at most
`2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * (2 ‖x - y‖) ^ (1 - n / p)` times the `Lᵖ` norm of the
derivative of `u`, where `ω = μ(B(0, 1))` and `K = n ω (p - 1) / (p - n)`. -/
theorem enorm_sub_le_of_contDiff_of_finrank_lt [CompleteSpace F] (hu : ContDiff ℝ 1 u) (x y : E)
    (hp : (finrank ℝ E : ℝ≥0) < p) :
    ‖u x - u y‖ₑ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / (finrank ℝ E * μ.real (ball 0 1)) *
        (finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^ (1 - 1 / (p : ℝ)) *
          (2 * ‖x - y‖) ^ (1 - finrank ℝ E / (p : ℝ))) *
        eLpNorm (fderiv ℝ u) p μ := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  -- Both points lie in the ball of radius `‖x - y‖` about their midpoint.
  have hpos : 0 < dist x y := dist_pos.2 hxy
  have hx : x ∈ ball (midpoint ℝ x y) ‖x - y‖ := by
    rw [mem_ball, dist_left_midpoint, ← dist_eq_norm]
    norm_num
    linarith
  have hy : y ∈ ball (midpoint ℝ x y) ‖x - y‖ := by
    rw [mem_ball, dist_right_midpoint, ← dist_eq_norm]
    norm_num
    linarith
  refine (enorm_sub_le_of_mem_ball_of_finrank_lt (μ := μ) hu.contDiffOn hx hy hp).trans ?_
  gcongr
  exact Measure.restrict_le_self

/-- **Morrey's inequality, Hölder form.** If `u` is `C¹` on the whole space, `p` exceeds the
dimension `n` of the space, and the derivative of `u` lies in `Lᵖ`, then `u` is Hölder continuous
of exponent `1 - n / p`, with constant
`2 ^ (n + 1) / (n ω) * K ^ (1 - 1 / p) * 2 ^ (1 - n / p) * ‖Du‖_{Lᵖ}`, where `ω = μ(B(0, 1))`
and `K = n ω (p - 1) / (p - n)`. -/
theorem holderWith_of_contDiff_of_finrank_lt [CompleteSpace F] (hu : ContDiff ℝ 1 u)
    (hp : (finrank ℝ E : ℝ≥0) < p) (hDu : eLpNorm (fderiv ℝ u) p μ ≠ ∞) :
    HolderWith (Real.toNNReal (2 ^ (finrank ℝ E + 1) / (finrank ℝ E * μ.real (ball 0 1)) *
        (finrank ℝ E * μ.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^ (1 - 1 / (p : ℝ)) *
          2 ^ (1 - finrank ℝ E / (p : ℝ))) * (eLpNorm (fderiv ℝ u) p μ).toNNReal)
      (1 - finrank ℝ E / p) u := by
  set n := finrank ℝ E
  have hα : (((1 - n / p : ℝ≥0)) : ℝ) = 1 - n / (p : ℝ) := by
    rw [NNReal.coe_sub ((div_le_one (zero_le.trans_lt hp)).2 hp.le), NNReal.coe_one,
      NNReal.coe_div, NNReal.coe_natCast]
  have hα0 : 0 ≤ 1 - n / (p : ℝ) := hα ▸ NNReal.coe_nonneg _
  have hK : 0 ≤ (n * μ.real (ball 0 1) * (p - 1) / (p - n) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    have hpn : (n : ℝ) < p := by exact_mod_cast hp
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  intro x y
  rw [edist_eq_enorm_sub, edist_eq_enorm_sub, hα, ENNReal.coe_mul, ENNReal.coe_toNNReal hDu,
    ENNReal.ofNNReal_toNNReal, ← ofReal_norm (x - y),
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hα0, mul_right_comm,
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hK _))
      (by positivity)), mul_assoc _ (2 ^ _),
    ← Real.mul_rpow zero_le_two (norm_nonneg _)]
  exact enorm_sub_le_of_contDiff_of_finrank_lt hu x y hp

end TauCeti
