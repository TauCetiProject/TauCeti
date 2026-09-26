/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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

open InnerProductSpace MeasureTheory Metric Module Set Topology

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
      (ball_subset_ball' hxy).eventuallyLE
  rw [(hu.mono (closedBall_subset_closedBall' hxy)).setIntegral_ball_eq,
    hu.setIntegral_ball_eq] at hle
  simp only [smul_eq_mul, measureReal_def, μ.addHaar_ball_of_pos x hr,
    μ.addHaar_ball_of_pos y hs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _), ENNReal.toReal_ofReal (pow_nonneg hs.le _)] at hle
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

/-- `IsHarnackPair U a b C`: every function harmonic and nonnegative on `U` has
`u a ≤ C * u b`. -/
private def IsHarnackPair (U : Set E) (a b : E) (C : ℝ) : Prop :=
  ∀ u : E → ℝ, HarmonicOnNhd u U → (∀ z ∈ U, 0 ≤ u z) → u a ≤ C * u b

private lemma IsHarnackPair.trans {U : Set E} {a b d : E} {C C' : ℝ} (hC : 0 ≤ C)
    (hab : IsHarnackPair U a b C) (hbd : IsHarnackPair U b d C') :
    IsHarnackPair U a d (C * C') := fun u hu h0 ↦ by
  rw [mul_assoc]
  exact (hab u hu h0).trans (mul_le_mul_of_nonneg_left (hbd u hu h0) hC)

private lemma IsHarnackPair.mono {U : Set E} {a b : E} {C C' : ℝ} (hb : b ∈ U) (hC : C ≤ C')
    (hab : IsHarnackPair U a b C) : IsHarnackPair U a b C' :=
  fun u hu h0 ↦ (hab u hu h0).trans (mul_le_mul_of_nonneg_right hC (h0 b hb))

/-- Near each point `a` of an open set `U`, the values of every nonnegative harmonic function on
`U` are within the factor `3 ^ n` of its value at `a`. -/
private lemma eventually_isHarnackPair {U : Set E} (hU : IsOpen U) {a : E} (ha : a ∈ U) :
    ∀ᶠ z in 𝓝 a,
      IsHarnackPair U z a (3 ^ finrank ℝ E) ∧ IsHarnackPair U a z (3 ^ finrank ℝ E) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU a ha
  have hball : ball a (4 * (ε / 4)) ⊆ U := by rwa [mul_div_cancel₀ _ four_ne_zero]
  have ha' : a ∈ ball a (ε / 4) := mem_ball_self (by positivity)
  filter_upwards [ball_mem_nhds a (by positivity : 0 < ε / 4)] with z hz
  exact ⟨fun u hu h0 ↦ (hu.mono hball).le_three_pow_mul_of_nonneg (fun w hw ↦ h0 w (hball hw))
      hz ha',
    fun u hu h0 ↦ (hu.mono hball).le_three_pow_mul_of_nonneg (fun w hw ↦ h0 w (hball hw)) ha' hz⟩

/-- On a preconnected open set, the values of nonnegative harmonic functions at any two points are
comparable, by chaining the local estimate along the set. -/
private lemma exists_isHarnackPair {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U) {a b : E}
    (ha : a ∈ U) (hb : b ∈ U) : ∃ C, 0 ≤ C ∧ IsHarnackPair U a b C := by
  refine hUc.induction₂' (fun a b ↦ ∃ C, 0 ≤ C ∧ IsHarnackPair U a b C) (fun a ha ↦ ?_)
    (fun a b d _ _ _ ⟨C, hC, hab⟩ ⟨C', hC', hbd⟩ ↦
      ⟨C * C', mul_nonneg hC hC', hab.trans hC hbd⟩) ha hb
  filter_upwards [nhdsWithin_le_nhds (eventually_isHarnackPair hU ha)] with z hz
  exact ⟨⟨_, by positivity, hz.2⟩, ⟨_, by positivity, hz.1⟩⟩

/-- On a compact subset `K` of a preconnected open set `U`, every point is comparable with a fixed
point `x₀ ∈ K`, with one constant for all of `K`. -/
private lemma exists_forall_isHarnackPair {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hKU : K ⊆ U) {x₀ : E} (hx₀ : x₀ ∈ K) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ K, IsHarnackPair U z x₀ C ∧ IsHarnackPair U x₀ z C := by
  -- Compactness, for the property of `t ∩ U` rather than of `t`: the union step enlarges the
  -- constants, which needs `u ≥ 0` at the points compared.
  suffices ∃ C, 0 ≤ C ∧ ∀ z ∈ K ∩ U, IsHarnackPair U z x₀ C ∧ IsHarnackPair U x₀ z C by
    obtain ⟨C, hC, h⟩ := this
    exact ⟨C, hC, fun z hz ↦ h z ⟨hz, hKU hz⟩⟩
  have hx₀U := hKU hx₀
  refine hK.induction_on
    (p := fun t ↦ ∃ C, 0 ≤ C ∧ ∀ z ∈ t ∩ U, IsHarnackPair U z x₀ C ∧ IsHarnackPair U x₀ z C)
    ⟨0, le_rfl, by simp⟩ (fun t t' htt' ⟨C, hC, h⟩ ↦ ⟨C, hC, fun z hz ↦ h z ⟨htt' hz.1, hz.2⟩⟩)
    (fun t t' ⟨C, hC, h⟩ ⟨C', hC', h'⟩ ↦ ⟨max C C', le_max_of_le_left hC, ?_⟩) (fun z hz ↦ ?_)
  · rintro w ⟨hw | hw, hwU⟩
    · exact ⟨(h w ⟨hw, hwU⟩).1.mono hx₀U (le_max_left _ _),
        (h w ⟨hw, hwU⟩).2.mono hwU (le_max_left _ _)⟩
    · exact ⟨(h' w ⟨hw, hwU⟩).1.mono hx₀U (le_max_right _ _),
        (h' w ⟨hw, hwU⟩).2.mono hwU (le_max_right _ _)⟩
  -- Near `z ∈ K`, compare with `z` by the local estimate and then `z` with `x₀`.
  have hzU := hKU hz
  obtain ⟨C₁, hC₁, h₁⟩ := exists_isHarnackPair hU hUc hzU hx₀U
  obtain ⟨C₂, hC₂, h₂⟩ := exists_isHarnackPair hU hUc hx₀U hzU
  refine ⟨_, nhdsWithin_le_nhds (eventually_isHarnackPair hU hzU),
    3 ^ finrank ℝ E * max C₁ C₂, by positivity, fun w ⟨hw, _⟩ ↦
      ⟨(hw.1.trans (by positivity) h₁).mono hx₀U ?_, ?_⟩⟩
  · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  · rw [mul_comm]
    exact (h₂.mono hzU (le_max_right _ _)).trans (le_max_of_le_left hC₁) hw.2

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
  obtain ⟨C, hC, h⟩ := exists_forall_isHarnackPair hK hU hUc hKU hx₀
  exact ⟨C * C, mul_nonneg hC hC, fun u hu h0 x hx y hy ↦
    ((h x hx).1.trans hC (h y hy).2) u hu h0⟩

end TauCeti
