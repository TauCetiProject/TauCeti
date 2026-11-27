/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Integrable nonnegative subharmonic functions

A nonnegative integrable `C²` function on a nontrivial finite-dimensional real inner product
space with nonnegative Laplacian is zero. The sub-mean-value inequality bounds its value by
its total integral divided by the volume of an arbitrarily large ball. This is useful for
vanishing arguments in which a squared norm is subharmonic and the original field is in `L²`.

In particular a `C²` solution in `L²` of the Schrödinger equation `Δf = V f` with nonnegative
potential `V` vanishes (`TauCeti.eq_zero_of_memLp_of_laplacian_eq_smul`): the Laplacian of
`‖f‖²` is `2 ‖Df‖² + 2 V ‖f‖² ≥ 0`.

## Codimension-two growth

Integrability can be replaced by a growth condition of codimension two. In dimension `n`, a
nonnegative subharmonic `C²` function `v` such that both `Δ v` and the truncation `min v 1` have
integrals at most `C Rⁿ⁻²` over every ball of radius `R ≥ 1` is zero
(`TauCeti.eq_zero_of_laplacian_nonneg_of_setIntegral_ball_le`). The integral of `Δ v` over a ball
of radius `3 r` controls the increase of the sphere integrals of `v` from the radius `r` to `2 r`
(`TauCeti.integral_toSphere_sub_integral_toSphere_le`), so they grow at most like `log R`. By
the sub-mean-value inequality on balls about nearby centres, `v` is then at most of order
`log R` on the ball of radius `R`, so its truncation still has integral of order `Rⁿ / log R`
there if `v` is positive somewhere, which exceeds `C Rⁿ⁻²`.

This is the form in which the theorem applies to vortex-type equations: for a nowhere vanishing
section `α` with `|α| ≤ 1` and `Δ log |α|² = κ (|α|² - 1)`, the function `v = -log |α|²` has
`Δ v = κ (1 - |α|²)` and `min v 1 ≤ 2 (1 - |α|²)`, so a quadratic bound on the integrals of the
defect `1 - |α|²` over balls in four dimensions forces `|α| = 1`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Filter Topology

/-- A nonnegative integrable subharmonic `C²` function on a nontrivial Euclidean space is zero.
The measure can be any additive Haar measure. -/
theorem eq_zero_of_integrable_of_nonneg_of_laplacian_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfi : Integrable f μ)
    (hf₀ : ∀ x, 0 ≤ f x) (hΔ : ∀ x, 0 ≤ Δ f x) : f = 0 := by
  funext x
  apply le_antisymm _ (hf₀ x)
  by_contra! hx
  have hv : 0 < μ.real (ball (0 : E) 1) :=
    Metric.measureReal_ball_pos μ 0 one_pos
  have ht : Tendsto (fun r : ℝ ↦ r ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1) * f x)
      atTop atTop :=
    ((tendsto_pow_atTop (ne_of_gt Module.finrank_pos)).atTop_mul_const hv).atTop_mul_const hx
  obtain ⟨r, hr, hbig⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (ht.eventually_gt_atTop (∫ y, f y ∂μ))).exists
  have hmean := mul_le_setIntegral_ball_of_laplacian_nonneg (μ := μ)
    (x₀ := x) (R := r) hf.contDiffOn hf.continuous.continuousOn (fun y _ ↦ hΔ y)
  rw [μ.addHaar_real_ball_of_pos x hr] at hmean
  exact (hmean.trans (setIntegral_le_integral hfi (Filter.Eventually.of_forall hf₀))).not_gt hbig

/-- A `C²` solution in `L²` of the Schrödinger equation `Δf = V f` with nonnegative potential `V`,
on a nontrivial Euclidean space and with values in a real inner product space, is zero. No
regularity of `V` is needed. The measure can be any additive Haar measure. -/
theorem eq_zero_of_memLp_of_laplacian_eq_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] {f : E → G} {V : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hf₂ : MemLp f 2 μ) (hV : ∀ x, 0 ≤ V x)
    (hΔ : ∀ x, Δ f x = V x • f x) : f = 0 := by
  have hnorm : (fun x ↦ ‖f x‖ ^ 2) = 0 := by
    refine eq_zero_of_integrable_of_nonneg_of_laplacian_nonneg (μ := μ) (hf.norm_sq ℝ)
      ((memLp_two_iff_integrable_sq_norm hf₂.aestronglyMeasurable).mp hf₂)
      (fun x ↦ sq_nonneg ‖f x‖) fun x ↦ ?_
    rw [hf.contDiffAt.laplacian_norm_sq (stdOrthonormalBasis ℝ E), hΔ, inner_smul_right,
      real_inner_self_eq_norm_sq]
    have := hV x
    positivity
  funext x
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (by simpa using congrFun hnorm x))

/-! ### Codimension-two growth -/

section CodimensionTwo

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {v : E → ℝ} {C : ℝ}

/-- An exponential `c 4ᵏ` with `c > 0` eventually exceeds every affine function `A + B k`. -/
private lemma exists_add_mul_lt_mul_four_pow {c : ℝ} (hc : 0 < c) (A B : ℝ) :
    ∃ k : ℕ, A + B * k < c * 4 ^ k := by
  have h : Tendsto (fun k : ℕ ↦ (A + B * k) / 4 ^ k) atTop (𝓝 0) := by
    have h0 := (tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 4)).const_mul A
    have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 4)).const_mul B
    have h01 := h0.add h1
    rw [mul_zero, mul_zero, add_zero] at h01
    refine h01.congr fun k ↦ ?_
    simp only [pow_zero, pow_one]
    ring
  obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds hc)).exists
  exact ⟨k, by rwa [div_lt_iff₀ (by positivity)] at hk⟩

/-- `r / r ^ (n - 1) * (3 r) ^ (n - 2) = 3 ^ (n - 2)` for `r ≠ 0` and `n ≥ 1`. -/
private lemma div_pow_mul_three_mul_zpow_eq {r : ℝ} (hr : r ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    r / r ^ (n - 1) * (3 * r) ^ ((n : ℤ) - 2) = 3 ^ ((n : ℤ) - 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [zpow_sub₀ (mul_ne_zero three_ne_zero hr), zpow_sub₀ three_ne_zero, zpow_natCast,
    zpow_natCast, Nat.add_sub_cancel]
  field_simp
  ring

/-- `(2 ^ k) ^ n = (2 ^ k) ^ (n - 2) 4 ^ k`, with the integer exponent `n - 2`. -/
private lemma two_pow_pow_eq_zpow_sub_two_mul_four_pow (k n : ℕ) :
    ((2 : ℝ) ^ k) ^ n = ((2 : ℝ) ^ k) ^ ((n : ℤ) - 2) * 4 ^ k := by
  rw [zpow_sub₀ (by positivity), zpow_natCast]
  field_simp
  rw [sq, ← mul_pow]
  norm_num

/-- The sphere integrals about `x₀` of a subharmonic `v` whose Laplacian has integral at most
`C Rⁿ⁻²` over the balls of radius `R ≥ 1` grow at most linearly in `k` along the radii `2 ^ k`. -/
private lemma integral_toSphere_two_pow_le (hv : ContDiff ℝ 2 v) (hΔ : ∀ x, 0 ≤ Δ v x)
    (hΔC : ∀ y R, 1 ≤ R → ∫ x in ball y R, Δ v x ∂μ ≤ C * R ^ ((Module.finrank ℝ E : ℤ) - 2))
    (x₀ : E) (k : ℕ) :
    ∫ θ : sphere (0 : E) 1, v (x₀ + (2 : ℝ) ^ k • (θ : E)) ∂μ.toSphere ≤
      ∫ θ : sphere (0 : E) 1, v (x₀ + (θ : E)) ∂μ.toSphere +
        k * (3 ^ ((Module.finrank ℝ E : ℤ) - 2) * C) := by
  -- One doubling step: from the radius `r ≥ 1` to `2 r`, through the ball of radius `3 r`.
  have hstep : ∀ r : ℝ, 1 ≤ r → ∫ θ : sphere (0 : E) 1, v (x₀ + (2 * r) • (θ : E)) ∂μ.toSphere -
      ∫ θ : sphere (0 : E) 1, v (x₀ + r • (θ : E)) ∂μ.toSphere ≤
        3 ^ ((Module.finrank ℝ E : ℤ) - 2) * C := by
    intro r hr
    have hr0 : 0 < r := by linarith
    have h := integral_toSphere_sub_integral_toSphere_le (μ := μ) (x₀ := x₀) (R := 3 * r)
      hv.contDiffOn hv.continuous.continuousOn (fun x _ ↦ hΔ x)
      ((hv.continuous_laplacian.continuousOn.integrableOn_compact
        (isCompact_closedBall x₀ _)).mono_set ball_subset_closedBall)
      hr0 (by linarith : r ≤ 2 * r) (by linarith)
    refine h.trans ((mul_le_mul_of_nonneg_left (hΔC x₀ (3 * r) (by linarith))
      (div_nonneg (by linarith) (by positivity))).trans_eq ?_)
    rw [show 2 * r - r = r by ring, mul_left_comm,
      div_pow_mul_three_mul_zpow_eq hr0.ne' (Module.finrank_pos (R := ℝ) (M := E)).ne', mul_comm]
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hstep (2 ^ k) (one_le_pow₀ (by norm_num))
    rw [← pow_succ'] at h
    push_cast
    linarith

omit [Nontrivial E] in
/-- A nonnegative subharmonic `v` is bounded on `ball x₀ R` by `2ⁿ` times its average over the
sphere of radius `2 R` about `x₀`. -/
private lemma mul_le_two_pow_mul_integral_toSphere (hv : ContDiff ℝ 2 v) (hv₀ : ∀ x, 0 ≤ v x)
    (hΔ : ∀ x, 0 ≤ Δ v x) {x₀ y : E} {R : ℝ} (hR : 0 < R) (hy : y ∈ ball x₀ R) :
    μ.toSphere.real univ * v y ≤
      2 ^ Module.finrank ℝ E * ∫ θ : sphere (0 : E) 1, v (x₀ + (2 * R) • (θ : E)) ∂μ.toSphere := by
  have hVy : 0 < μ.real (ball y R) := measureReal_ball_pos μ y hR
  have hmean := mul_le_setIntegral_ball_of_laplacian_nonneg (μ := μ) (x₀ := y) (R := R)
    hv.contDiffOn hv.continuous.continuousOn fun x _ ↦ hΔ x
  have hmono : ∫ x in ball y R, v x ∂μ ≤ ∫ x in ball x₀ (2 * R), v x ∂μ :=
    setIntegral_mono_set ((hv.continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall x₀ _)).mono_set ball_subset_closedBall) (ae_of_all _ fun x ↦ hv₀ x)
      (ball_subset_ball' (by linarith [mem_ball.1 hy])).eventuallySubset
  have hsphere := mul_setIntegral_ball_le_mul_integral_toSphere_of_laplacian_nonneg (μ := μ)
    (x₀ := x₀) (R := 2 * R) hv.contDiffOn hv.continuous.continuousOn fun x _ ↦ hΔ x
  have hball : μ.real (ball x₀ (2 * R)) = 2 ^ Module.finrank ℝ E * μ.real (ball y R) := by
    rw [μ.addHaar_real_ball_of_pos x₀ (by positivity), μ.addHaar_real_ball_of_pos y hR, mul_pow]
    ring
  refine le_of_mul_le_mul_left ?_ hVy
  calc μ.real (ball y R) * (μ.toSphere.real univ * v y) =
        μ.toSphere.real univ * (μ.real (ball y R) * v y) := by ring
    _ ≤ μ.toSphere.real univ * ∫ x in ball x₀ (2 * R), v x ∂μ :=
        mul_le_mul_of_nonneg_left (hmean.trans hmono) measureReal_nonneg
    _ ≤ μ.real (ball x₀ (2 * R)) *
        ∫ θ : sphere (0 : E) 1, v (x₀ + (2 * R) • (θ : E)) ∂μ.toSphere := hsphere
    _ = μ.real (ball y R) * (2 ^ Module.finrank ℝ E *
        ∫ θ : sphere (0 : E) 1, v (x₀ + (2 * R) • (θ : E)) ∂μ.toSphere) := by rw [hball]; ring

/-- The estimate at the scales `R = 2 ^ k` behind the growth argument: if `v` is a nonnegative
subharmonic function with codimension-two growth, then `4ᵏ V₁ v x₀ ≤ C (1 + T_k)`, where `V₁` is
the measure of the unit ball and `T_k` bounds `v` on the ball of radius `2 ^ k` about `x₀`. Since
`T_k` is affine in `k`, so is the bound. -/
private lemma exists_mul_four_pow_le (hv : ContDiff ℝ 2 v) (hv₀ : ∀ x, 0 ≤ v x)
    (hΔ : ∀ x, 0 ≤ Δ v x)
    (hΔC : ∀ y R, 1 ≤ R → ∫ x in ball y R, Δ v x ∂μ ≤ C * R ^ ((Module.finrank ℝ E : ℤ) - 2))
    (hvC : ∀ y R, 1 ≤ R →
      ∫ x in ball y R, min (v x) 1 ∂μ ≤ C * R ^ ((Module.finrank ℝ E : ℤ) - 2))
    (hS : 0 < μ.toSphere.real univ) (x₀ : E) :
    ∃ A B : ℝ, ∀ k : ℕ, μ.real (ball (0 : E) 1) * v x₀ * 4 ^ k ≤ A + B * k := by
  set I := ∫ θ : sphere (0 : E) 1, v (x₀ + (θ : E)) ∂μ.toSphere
  set K := 3 ^ ((Module.finrank ℝ E : ℤ) - 2) * C
  set S := μ.toSphere.real univ
  refine ⟨C * (1 + 2 ^ Module.finrank ℝ E * (I + K) / S), C * (2 ^ Module.finrank ℝ E * K / S),
    fun k ↦ ?_⟩
  have hR1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hR0 : (0 : ℝ) < 2 ^ k := by positivity
  set T := 2 ^ Module.finrank ℝ E * (I + (k + 1) * K) / S
  -- `v ≤ T` on the ball of radius `2 ^ k`, by the sub-mean-value inequality and the growth of
  -- the sphere integrals.
  have hT : ∀ y ∈ ball x₀ (2 ^ k), v y ≤ T := fun y hy ↦ by
    have h1 := mul_le_two_pow_mul_integral_toSphere (μ := μ) hv hv₀ hΔ hR0 hy
    have h2 := integral_toSphere_two_pow_le (μ := μ) hv hΔ hΔC x₀ (k + 1)
    rw [pow_succ'] at h2
    push_cast at h2
    rw [le_div_iff₀ hS, mul_comm]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hT0 : 0 ≤ T := (hv₀ x₀).trans (hT x₀ (mem_ball_self hR0))
  -- On the ball, `v / (1 + T) ≤ min v 1`.
  have hmin : ∀ y ∈ ball x₀ (2 ^ k), v y / (1 + T) ≤ min (v y) 1 := fun y hy ↦ by
    rw [div_le_iff₀ (by positivity)]
    rcases le_total (v y) 1 with h | h
    · rw [min_eq_left h]
      nlinarith [hv₀ y]
    · rw [min_eq_right h]
      linarith [hT y hy]
  have hmean := mul_le_setIntegral_ball_of_laplacian_nonneg (μ := μ) (x₀ := x₀) (R := 2 ^ k)
    hv.contDiffOn hv.continuous.continuousOn fun x _ ↦ hΔ x
  have hlow : μ.real (ball x₀ (2 ^ k)) * v x₀ / (1 + T) ≤
      ∫ x in ball x₀ (2 ^ k), min (v x) 1 ∂μ := by
    calc μ.real (ball x₀ (2 ^ k)) * v x₀ / (1 + T) ≤
          (∫ x in ball x₀ (2 ^ k), v x ∂μ) / (1 + T) := by gcongr
      _ = ∫ x in ball x₀ (2 ^ k), v x / (1 + T) ∂μ := (integral_div _ _).symm
      _ ≤ ∫ x in ball x₀ (2 ^ k), min (v x) 1 ∂μ :=
          setIntegral_mono_on (((hv.continuous.div_const _).continuousOn.integrableOn_compact
            (isCompact_closedBall x₀ _)).mono_set ball_subset_closedBall)
            (((hv.continuous.min continuous_const).continuousOn.integrableOn_compact
            (isCompact_closedBall x₀ _)).mono_set ball_subset_closedBall) measurableSet_ball hmin
  -- Divide the two bounds on the integral of `min v 1` by `(2 ^ k)ⁿ⁻²`.
  rw [μ.addHaar_real_ball_of_pos x₀ hR0, two_pow_pow_eq_zpow_sub_two_mul_four_pow] at hlow
  have h := hlow.trans (hvC x₀ _ hR1)
  have hz : 0 < ((2 : ℝ) ^ k) ^ ((Module.finrank ℝ E : ℤ) - 2) := zpow_pos hR0 _
  rw [div_le_iff₀ (by positivity)] at h
  calc μ.real (ball (0 : E) 1) * v x₀ * 4 ^ k ≤ C * (1 + T) := by nlinarith
    _ = _ := by
        simp only [T]
        ring

/-- **A Liouville theorem under codimension-two growth.** Let `v` be a nonnegative `C²` function
on a nontrivial finite-dimensional real inner product space of dimension `n`, with nonnegative
Laplacian. If, for some constant `C`, both `Δ v` and the truncation `min v 1` have integrals at
most `C Rⁿ⁻²` over every ball of radius `R ≥ 1`, then `v` is zero. The measure can be any
additive Haar measure. -/
theorem eq_zero_of_laplacian_nonneg_of_setIntegral_ball_le (hv : ContDiff ℝ 2 v)
    (hv₀ : ∀ x, 0 ≤ v x) (hΔ : ∀ x, 0 ≤ Δ v x)
    (hΔC : ∀ y R, 1 ≤ R → ∫ x in ball y R, Δ v x ∂μ ≤ C * R ^ ((Module.finrank ℝ E : ℤ) - 2))
    (hvC : ∀ y R, 1 ≤ R →
      ∫ x in ball y R, min (v x) 1 ∂μ ≤ C * R ^ ((Module.finrank ℝ E : ℤ) - 2)) :
    v = 0 := by
  funext x₀
  refine le_antisymm (not_lt.1 fun hpos ↦ ?_) (hv₀ x₀)
  have : NeZero μ.toSphere := ⟨μ.toSphere_ne_zero⟩
  have hS : 0 < μ.toSphere.real univ := measureReal_univ_pos
  have hc : 0 < μ.real (ball (0 : E) 1) * v x₀ := mul_pos (measureReal_ball_pos μ 0 one_pos) hpos
  -- The bound of `exists_mul_four_pow_le` is affine in `k`; it fails for large `k`.
  obtain ⟨A, B, h⟩ := exists_mul_four_pow_le (μ := μ) hv hv₀ hΔ hΔC hvC hS x₀
  obtain ⟨k, hk⟩ := exists_add_mul_lt_mul_four_pow hc A B
  exact (h k).not_gt hk

end CodimensionTwo

end TauCeti
