/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Uniform Cauchy expansions with parameters

The Cauchy power series of a family of circle-integrable functions converges uniformly in
both the parameter and the evaluation point on every smaller closed disc, provided the family
is uniformly bounded on the integration circle. The coefficients satisfy a geometric bound,
and the partial sums have an explicit geometric error estimate. A continuous family on a
compact parameter set automatically satisfies the boundedness hypothesis.

For a jointly analytic family, the scalar-variable coefficients are analytic functions of the
parameter. On compact parameter sets the resulting series converges uniformly to the original
family on smaller discs. These results use Mathlib's `cauchyPowerSeries` and its pointwise
Cauchy integral expansion; no new power-series representation is introduced.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Complex Filter Metric Real Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A bound on a function on the integration circle bounds its Cauchy coefficients.
No regularity assumption on the function is needed for this estimate. -/
theorem norm_cauchyPowerSeries_le_of_bound {f : ℂ → E} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖cauchyPowerSeries f c R n‖ ≤ M * R⁻¹ ^ n := by
  have hb : (∫ θ : ℝ in 0..2 * π, ‖f (circleMap c R θ)‖) ≤ (2 * π) * M := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun θ : ℝ ↦ ‖f (circleMap c R θ)‖)
      (a := 0) (b := 2 * π) (fun θ _ ↦ by
        simpa only [Real.norm_eq_abs, abs_norm] using hf _ (circleMap_mem_sphere c hR.le θ))
    exact (le_abs_self _).trans (by simpa [abs_of_pos Real.two_pi_pos, mul_comm] using h)
  calc
    ‖cauchyPowerSeries f c R n‖ ≤
        ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖f (circleMap c R θ)‖) * R⁻¹ ^ n := by
      simpa only [abs_of_pos hR] using norm_cauchyPowerSeries_le f c R n
    _ ≤ ((2 * π)⁻¹ * ((2 * π) * M)) * R⁻¹ ^ n := by gcongr
    _ = M * R⁻¹ ^ n := by rw [inv_mul_cancel_left₀ Real.two_pi_pos.ne']

/-- The homogeneous terms of the Cauchy expansion are bounded geometrically on a smaller
closed disc. The constant in the bound is independent of the evaluation point. -/
theorem norm_cauchyPowerSeries_apply_le_of_bound {f : ℂ → E} {c w : ℂ} {R r M : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r)
    (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hw : w ∈ closedBall c r) (n : ℕ) :
    ‖cauchyPowerSeries f c R n (fun _ ↦ w - c)‖ ≤ M * (r / R) ^ n := by
  calc
    ‖cauchyPowerSeries f c R n (fun _ ↦ w - c)‖ ≤
        ‖cauchyPowerSeries f c R n‖ * r ^ n :=
      (cauchyPowerSeries f c R n).le_opNorm_mul_pow_of_le
        ((pi_norm_le_iff_of_nonneg hr).2 fun _ ↦ by
          simpa only [mem_closedBall, dist_eq_norm] using hw)
    _ ≤ (M * R⁻¹ ^ n) * r ^ n :=
      mul_le_mul_of_nonneg_right (norm_cauchyPowerSeries_le_of_bound hR hf n)
        (pow_nonneg hr n)
    _ = M * (r / R) ^ n := by rw [div_eq_mul_inv, mul_pow]; ring

/-- Geometric error bound for the Cauchy expansion on a smaller closed disc. A bound on
the integration circle gives a common error bound for every point of the smaller disc. -/
theorem norm_cauchyPowerSeries_partialSum_sub_integral_le {f : ℂ → E} {c : ℂ} {R r M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hf : CircleIntegrable f c R)
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) {w : ℂ} (hw : w ∈ closedBall c r) (N : ℕ) :
    ‖(∑ n ∈ Finset.range N, cauchyPowerSeries f c R n (fun _ ↦ w - c)) -
      (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z‖ ≤
        M * (r / R) ^ N / (1 - r / R) := by
  have hR : 0 < R := hr.trans_lt hrR
  apply norm_sub_le_of_geometric_bound_of_hasSum ((div_lt_one hR).2 hrR)
    (fun n ↦ norm_cauchyPowerSeries_apply_le_of_bound hR hr hb hw n)
  simpa using hasSum_cauchyPowerSeries_integral (w := w - c) hf
    (by simpa only [dist_eq_norm] using (mem_closedBall.1 hw).trans_lt hrR)

/-- Cauchy expansions converge uniformly in both the parameter and the point on every
smaller closed disc, whenever the functions have a common bound on the integration circle. -/
theorem tendstoUniformlyOn_cauchyPowerSeries {P : Type*} {S : Set P}
    {f : P → ℂ → E} {c : ℂ} {R r M : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hf : ∀ x ∈ S, CircleIntegrable (f x) c R)
    (hb : ∀ x ∈ S, ∀ z ∈ sphere c R, ‖f x z‖ ≤ M) :
    TendstoUniformlyOn
      (fun N b ↦ ∑ n ∈ Finset.range N, cauchyPowerSeries (f b.1) c R n (fun _ ↦ b.2 - c))
      (fun b ↦ (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - b.2)⁻¹ • f b.1 z)
      atTop (S ×ˢ closedBall c r) := by
  have hR : 0 < R := hr.trans_lt hrR
  have ht : Tendsto (fun N : ℕ ↦ M * (r / R) ^ N / (1 - r / R)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr hR.le)
      ((div_lt_one hR).2 hrR)).const_mul M).div_const (1 - r / R)
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
  filter_upwards [(tendsto_order.1 ht).2 ε hε] with N hN b hb'
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_cauchyPowerSeries_partialSum_sub_integral_le hr hrR
    (hf b.1 hb'.1) (hb b.1 hb'.1) hb'.2 N).trans_lt hN

/-- Joint continuity on a compact parameter set times the integration circle supplies uniform
convergence of its Cauchy expansions on every smaller closed disc. -/
theorem _root_.IsCompact.tendstoUniformlyOn_cauchyPowerSeries {P : Type*} [TopologicalSpace P]
    {S : Set P} (hS : IsCompact S) {f : P × ℂ → E} {c : ℂ} {R r : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hf : ContinuousOn f (S ×ˢ sphere c R)) :
    TendstoUniformlyOn
      (fun N b ↦ ∑ n ∈ Finset.range N,
        cauchyPowerSeries (fun z ↦ f (b.1, z)) c R n (fun _ ↦ b.2 - c))
      (fun b ↦ (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - b.2)⁻¹ • f (b.1, z))
      atTop (S ×ˢ closedBall c r) := by
  obtain ⟨M, hM⟩ := (hS.prod (isCompact_sphere c R)).exists_bound_of_continuousOn hf
  refine TauCeti.tendstoUniformlyOn_cauchyPowerSeries
    (f := fun x z ↦ f (x, z)) hr hrR (M := M) ?_ ?_
  · intro x hx
    exact (hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz ↦ ⟨hx, hz⟩)).circleIntegrable (hr.trans_lt hrR).le
  · intro x hx z hz
    exact hM (x, z) ⟨hx, hz⟩

variable [CompleteSpace E] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- The coefficients of the scalar-variable Cauchy expansion of a jointly analytic family
are analytic in the parameter. Evaluating a multilinear coefficient at the tuple of ones
recovers the usual coefficient of the scalar power series. -/
theorem analyticOnNhd_cauchyPowerSeries_apply_one {S : Set V} {f : V × ℂ → E}
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (S ×ˢ sphere c R)) (n : ℕ) :
    AnalyticOnNhd ℂ
      (fun x ↦ cauchyPowerSeries (fun z ↦ f (x, z)) c R n (fun _ ↦ 1)) S := by
  simp only [cauchyPowerSeries_apply, one_div]
  apply AnalyticOnNhd.const_smul
  apply analyticOnNhd_circleIntegral (c := c) (R := R)
    (f := fun b : V × ℂ ↦ (b.2 - c)⁻¹ ^ n • (b.2 - c)⁻¹ • f b)
  intro b hb
  have hz : b.2 - c ≠ 0 := sub_ne_zero.2 (ne_of_mem_sphere (by simpa [abs_of_pos hR] using hb.2)
    hR.ne')
  exact (((analyticAt_snd.sub analyticAt_const).inv hz).pow n).smul
    (((analyticAt_snd.sub analyticAt_const).inv hz).smul
      (hf b ⟨hb.1, by simpa [abs_of_pos hR] using hb.2⟩))

omit [FiniteDimensional ℂ V] in
/-- A jointly analytic family is recovered uniformly by its scalar-variable Cauchy expansions
on compact parameter sets times smaller closed discs. -/
theorem _root_.IsCompact.tendstoUniformlyOn_cauchyPowerSeries_of_analyticOnNhd
    {S : Set V} (hS : IsCompact S) {f : V × ℂ → E} {c : ℂ} {R r : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hf : AnalyticOnNhd ℂ f (S ×ˢ closedBall c R)) :
    TendstoUniformlyOn
      (fun N b ↦ ∑ n ∈ Finset.range N,
        cauchyPowerSeries (fun z ↦ f (b.1, z)) c R n (fun _ ↦ b.2 - c))
      f atTop (S ×ˢ closedBall c r) := by
  refine (hS.tendstoUniformlyOn_cauchyPowerSeries hr hrR
    (hf.continuousOn.mono (prod_mono subset_rfl sphere_subset_closedBall))).congr_right ?_
  intro b hb
  have hd : DifferentiableOn ℂ (fun z ↦ f (b.1, z)) (closedBall c R) := by
    intro z hz
    exact ((hf (b.1, z) ⟨hb.1, hz⟩).comp
      (analyticAt_const.prod analyticAt_id)).differentiableAt.differentiableWithinAt
  have hw : b.2 ∈ ball c R := (mem_closedBall.1 hb.2).trans_lt hrR
  exact (hd.mono closure_ball_subset_closedBall).diffContOnCl
    |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

end TauCeti
