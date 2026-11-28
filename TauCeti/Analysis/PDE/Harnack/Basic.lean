/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.Compactness.LocalComparison

/-!
# Harnack's inequality in every dimension

Let `E` be a finite-dimensional real inner product space of dimension `n`. This file proves
**Harnack's inequality** for nonnegative harmonic functions `u : E → ℝ`: on a compact subset `K`
of a preconnected open set `U`, the values of `u` are comparable,

`u x ≤ C * u y` for all `x, y ∈ K`,

with a constant `C` that depends only on `K` and `U`, not on `u`. Equivalently,
`sup_K u ≤ C * inf_K u`.

The argument is the classical one through the mean-value property on balls
(`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_eq`). If `closedBall x r ⊆ closedBall y s`,
then for `u ≥ 0` the integral of `u` over `ball x r` is at most its integral over `ball y s`,
and the mean-value property turns this into `r ^ n * u x ≤ s ^ n * u y`. Choosing the balls as
in Gilbarg–Trudinger gives the local estimate `u x ≤ 3 ^ n * u y` for `x, y ∈ ball c r` when `u`
is harmonic and nonnegative on `ball c (4 * r)`. The global inequality follows by chaining the
local one: along the preconnected set `U` for comparability of any two points, and over a finite
cover of `K` for uniformity of the constant.

The planar inequality with the sharp Poisson-kernel constant is
`TauCeti.Analysis.PDE.Harnack.Planar`.

## Main declarations

* `InnerProductSpace.HarmonicOnNhd.le_div_pow_mul_of_nonneg`: nested balls compare values,
  `u x ≤ (s / r) ^ n * u y` when `r + dist x y ≤ s`.
* `InnerProductSpace.HarmonicOnNhd.le_three_pow_mul_of_nonneg`: the local Harnack inequality
  `u x ≤ 3 ^ n * u y` on `ball c r`, for `u` harmonic and nonnegative on `ball c (4 * r)`.
* `IsCompact.harnack_inequality`: **Harnack's inequality** on a compact subset of a
  preconnected open set.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.2, Theorem 11.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 2.5.
-/

public section

namespace TauCeti

open Filter InnerProductSpace MeasureTheory Metric Module Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {u : E → ℝ} {x y c : E} {r s : ℝ}

/-- **Nested balls compare the values of a nonnegative harmonic function.** If `u` is harmonic
on a neighbourhood of `closedBall y s` and nonnegative on `ball y s`, and `closedBall x r` lies
inside `closedBall y s` in the sense that `r + dist x y ≤ s`, then
`u x ≤ (s / r) ^ n * u y`, where `n` is the dimension of `E`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.le_div_pow_mul_of_nonneg
    (hu : HarmonicOnNhd u (closedBall y s)) (hnonneg : ∀ z ∈ ball y s, 0 ≤ u z) (hr : 0 < r)
    (hxy : r + dist x y ≤ s) :
    u x ≤ (s / r) ^ finrank ℝ E * u y := by
  borelize E
  set μ : Measure E := Measure.addHaar
  have hs : 0 < s := hr.trans_le ((le_add_of_nonneg_right dist_nonneg).trans hxy)
  have hint : IntegrableOn u (ball y s) μ :=
    (hu.contDiffOn.continuousOn.integrableOn_compact (isCompact_closedBall y s)).mono_set
      ball_subset_closedBall
  have hle : ∫ z in ball x r, u z ∂μ ≤ ∫ z in ball y s, u z ∂μ :=
    setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ hnonneg))
      (ball_subset_ball' hxy).eventuallySubset
  rw [(hu.mono (closedBall_subset_closedBall' hxy)).setIntegral_ball_eq,
    hu.setIntegral_ball_eq] at hle
  simp only [smul_eq_mul, μ.addHaar_real_ball_of_pos x hr, μ.addHaar_real_ball_of_pos y hs,
    measureReal_def] at hle
  have hB : 0 < (μ (ball 0 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  refine le_of_mul_le_mul_left ?_ hB
  nlinarith [hle]

/-- **The local Harnack inequality.** If `u` is harmonic and nonnegative on `ball c (4 * r)`, then
any two of its values on `ball c r` are within the factor `3 ^ n` of each other, where `n` is the
dimension of `E`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.le_three_pow_mul_of_nonneg
    (hu : HarmonicOnNhd u (ball c (4 * r))) (hnonneg : ∀ z ∈ ball c (4 * r), 0 ≤ u z)
    (hx : x ∈ ball c r) (hy : y ∈ ball c r) :
    u x ≤ 3 ^ finrank ℝ E * u y := by
  have hr : 0 < r := pos_of_mem_ball hx
  rw [mem_ball] at hx hy
  have hsub : closedBall y (3 * r) ⊆ ball c (4 * r) :=
    closedBall_subset_ball' (by linarith)
  have hxy : r + dist x y ≤ 3 * r := by linarith [dist_triangle_right x y c]
  have := (hu.mono hsub).le_div_pow_mul_of_nonneg
    (fun z hz ↦ hnonneg z (hsub (ball_subset_closedBall hz))) hr hxy
  rwa [mul_div_cancel_right₀ 3 hr.ne'] at this

/-- **Harnack's inequality.** Let `K` be a compact subset of a preconnected open set `U`. There
is a constant `C`, depending only on `K` and `U`, such that every function `u` harmonic and
nonnegative on `U` satisfies `u x ≤ C * u y` for all `x, y ∈ K`; that is,
`sup_K u ≤ C * inf_K u`. -/
theorem _root_.IsCompact.harnack_inequality {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hKU : K ⊆ U) :
    ∃ C, 0 ≤ C ∧ ∀ u : E → ℝ, HarmonicOnNhd u U → (∀ z ∈ U, 0 ≤ u z) →
      ∀ x ∈ K, ∀ y ∈ K, u x ≤ C * u y := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, le_rfl, by simp⟩
  let F := {u : E → ℝ // HarmonicOnNhd u U ∧ ∀ z ∈ U, 0 ≤ u z}
  have hlocal (a : E) (ha : a ∈ U) : ∃ V ∈ 𝓝[U] a, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ u : F in ⊤, ∀ z ∈ V, u.val z ≤ C * u.val a ∧ u.val a ≤ C * u.val z := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU a ha
    have hball : ball a (4 * (ε / 4)) ⊆ U := by rwa [mul_div_cancel₀ _ four_ne_zero]
    have hr : 0 < ε / 4 := by positivity
    refine ⟨ball a (ε / 4), nhdsWithin_le_nhds (ball_mem_nhds a hr),
      3 ^ finrank ℝ E, by positivity, eventually_top.2 fun u z hz ↦ ?_⟩
    have hu := u.property.1.mono hball
    have h0 := fun w hw ↦ u.property.2 w (hball hw)
    exact ⟨hu.le_three_pow_mul_of_nonneg h0 hz (mem_ball_self hr),
      hu.le_three_pow_mul_of_nonneg h0 (mem_ball_self hr) hz⟩
  obtain ⟨C, hC, h⟩ := hUc.exists_eventually_forall_le_mul_of_locally
    (u := fun u : F ↦ u.val) (l := ⊤) hK hKU (hKU hx₀)
    (eventually_top.2 fun u ↦ u.property.2 x₀ (hKU hx₀)) hlocal
  have hC₀ := zero_le_one.trans hC
  refine ⟨C * C, mul_nonneg hC₀ hC₀, ?_⟩
  intro u hu h0 x hx y hy
  have hu' := eventually_top.1 h (⟨u, hu, h0⟩ : F)
  rw [mul_assoc]
  exact (hu' x hx).1.trans (mul_le_mul_of_nonneg_left (hu' y hy).2 hC₀)

end TauCeti
