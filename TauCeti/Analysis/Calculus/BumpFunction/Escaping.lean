/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Escaping profiles

For every sequence `S` of reals there are smooth compactly supported functions `φₙ` on `ℝ` with
`∫ φₙ² = 1` and `∫ φₙ'² → 0`, with pairwise disjoint supports, and with `φₙ` supported in
`[Sₙ, ∞)` (or in `(-∞, Sₙ]`). In `W^{1,2}(ℝ)` they form a bounded sequence escaping to `+∞` (or
`-∞`) whose terms stay `√2` apart in `L²` while their derivatives tend to `0`. Multiplied by a
fixed vector they are the escaping approximate kernels which show that a trajectory operator
`u ↦ u' + A u` with a degenerate limit is not Fredholm.

The profiles are `φₙ(s) = ((n + 1) ∫ ψ²)^(-1/2) ψ((s - cₙ) / (n + 1))` for a smooth bump `ψ`
supported in `(-1, 1)`, with centres `cₙ` far enough out that the windows `|s - cₙ| < n + 1` are
pairwise disjoint and lie beyond `Sₙ`. Dilating by `n + 1` keeps `∫ φₙ² = 1` and divides
`∫ φₙ'²` by `(n + 1)²`.

## Main results

* `TauCeti.exists_seq_contDiff_hasCompactSupport_escaping_atTop` and
  `TauCeti.exists_seq_contDiff_hasCompactSupport_escaping_atBot`: the escaping profiles at `+∞`
  and at `-∞`.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace TauCeti

/-- The smooth bump `ψ` on `ℝ`, equal to `1` on `[-1/2, 1/2]` and supported in `(-1, 1)`. -/
private def bump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

private theorem bump_ne_zero {t : ℝ} (ht : bump t ≠ 0) : |t| < 1 := by
  have h : t ∈ Function.support bump := ht
  rw [bump.support_eq] at h
  simpa [bump] using h

private theorem integral_bump_sq_pos : 0 < ∫ t, bump t ^ 2 := by
  have hint :=
    bump.continuous.integrable_sq_of_hasCompactSupport (μ := volume) bump.hasCompactSupport
  rw [integral_pos_iff_support_of_nonneg (fun t ↦ sq_nonneg _) hint]
  have hsupp : Function.support (fun t ↦ bump t ^ 2) = Metric.ball 0 1 := by
    ext t
    simpa [bump] using Set.ext_iff.1 bump.support_eq t
  rw [hsupp, Real.volume_ball]
  norm_num

/-- Translating by `c` and dilating by `r > 0` multiplies the integral by `r`. -/
private theorem integral_comp_sub_div (g : ℝ → ℝ) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ s, g ((s - c) / r) = r * ∫ t, g t := by
  rw [integral_sub_right_eq_self (μ := volume) (fun s ↦ g (s / r)) c, Measure.integral_comp_div,
    abs_of_pos hr, smul_eq_mul]

/-- The profile `s ↦ (r a)^(-1/2) ψ((s - c) / r)`, where `a = ∫ ψ²`, normalized to have unit `L²`
norm and supported in `(c - r, c + r)`. -/
private def profile (c r s : ℝ) : ℝ :=
  (√(r * ∫ t, bump t ^ 2))⁻¹ * bump ((s - c) / r)

private theorem contDiff_profile (c r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (profile c r) :=
  contDiff_const.mul (bump.contDiff.comp ((contDiff_id.sub contDiff_const).div_const r))

private theorem abs_sub_lt_of_profile_ne_zero {c r s : ℝ} (h : profile c r s ≠ 0) :
    |s - c| < |r| := by
  have hr : r ≠ 0 := by
    rintro rfl
    simp [profile] at h
  have h1 := bump_ne_zero (right_ne_zero_of_mul h)
  rwa [abs_div, div_lt_one (abs_pos.2 hr)] at h1

private theorem hasCompactSupport_profile (c r : ℝ) : HasCompactSupport (profile c r) :=
  HasCompactSupport.intro (isCompact_closedBall c |r|) fun s hs ↦ by
    by_contra h
    exact hs (Metric.mem_closedBall.2 (by
      rw [Real.dist_eq]
      exact (abs_sub_lt_of_profile_ne_zero h).le))

private theorem integral_profile_sq {c r : ℝ} (hr : 0 < r) : ∫ s, profile c r s ^ 2 = 1 := by
  have ha := integral_bump_sq_pos
  simp only [profile, mul_pow, inv_pow]
  rw [integral_const_mul, integral_comp_sub_div (fun t ↦ bump t ^ 2) c hr,
    Real.sq_sqrt (by positivity)]
  field_simp

private theorem deriv_profile (c r s : ℝ) :
    deriv (profile c r) s =
      (√(r * ∫ t, bump t ^ 2))⁻¹ * (deriv bump ((s - c) / r) * r⁻¹) := by
  have hψ : HasDerivAt bump (deriv bump ((s - c) / r)) ((s - c) / r) :=
    (bump.contDiff (n := 1).differentiable one_ne_zero _).hasDerivAt
  have hlin : HasDerivAt (fun s ↦ (s - c) / r) r⁻¹ s := by
    simpa [div_eq_mul_inv] using ((hasDerivAt_id s).sub_const c).div_const r
  exact ((hψ.comp s hlin).const_mul _).deriv

private theorem integral_deriv_profile_sq {c r : ℝ} (hr : 0 < r) :
    ∫ s, deriv (profile c r) s ^ 2 =
      (∫ t, deriv bump t ^ 2) / ((∫ t, bump t ^ 2) * r ^ 2) := by
  have ha := integral_bump_sq_pos
  simp only [deriv_profile, mul_pow, inv_pow]
  rw [integral_const_mul, integral_mul_const,
    integral_comp_sub_div (fun t ↦ deriv bump t ^ 2) c hr, Real.sq_sqrt (by positivity)]
  field_simp

/-- The windows `|t - (aₙ + n + 1)| < n + 1`, that is `aₙ < t < aₙ + 2 (n + 1)`, are pairwise
disjoint when each `aₙ` lies beyond the window of every `aₘ` with `m < n`. -/
private theorem le_abs_sub_of_abs_sub_lt {a : ℕ → ℝ}
    (ha : ∀ m n, m < n → a m + 2 * ((m : ℝ) + 1) ≤ a n) {m n : ℕ} (hmn : m ≠ n) {t : ℝ}
    (ht : |t - (a m + (m + 1))| < m + 1) : (n : ℝ) + 1 ≤ |t - (a n + (n + 1))| := by
  rw [abs_lt] at ht
  rw [le_abs]
  rcases hmn.lt_or_gt with h | h
  · have := ha m n h
    right
    linarith
  · have := ha n m h
    left
    linarith

/-- Any sequence `S` is dominated in absolute value by a sequence `a` whose windows
`(aₙ, aₙ + 2 (n + 1))` are pairwise disjoint. -/
private theorem exists_abs_le_and_add_two_mul_le (S : ℕ → ℝ) :
    ∃ a : ℕ → ℝ, (∀ n, |S n| ≤ a n) ∧ ∀ m n, m < n → a m + 2 * ((m : ℝ) + 1) ≤ a n := by
  refine ⟨fun n ↦ ∑ k ∈ Finset.range n, (2 * ((k : ℝ) + 1) + |S k|) + |S n|,
    fun n ↦ le_add_of_nonneg_left (Finset.sum_nonneg fun k _ ↦ by positivity), fun m n hmn ↦ ?_⟩
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hmn)
    (fun k _ _ ↦ by positivity) (f := fun k : ℕ ↦ 2 * ((k : ℝ) + 1) + |S k|)
  rw [Finset.sum_range_succ] at h
  have := abs_nonneg (S n)
  dsimp only
  linarith

/-- Profiles on the windows `|s - cₙ| < n + 1` have pairwise disjoint supports when the windows
are pairwise disjoint. -/
private theorem profile_mul_profile_eq_zero {c : ℕ → ℝ}
    (hdisj : ∀ m n, m ≠ n → ∀ s, |s - c m| < m + 1 → (n : ℝ) + 1 ≤ |s - c n|) {m n : ℕ}
    (hmn : m ≠ n) (s : ℝ) : profile (c m) (m + 1) s * profile (c n) (n + 1) s = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have h3 := hdisj m n hmn s (by
    simpa [abs_of_pos (by positivity : (0 : ℝ) < m + 1)] using abs_sub_lt_of_profile_ne_zero h1)
  have h4 := abs_sub_lt_of_profile_ne_zero h2
  rw [abs_of_pos (by positivity : (0 : ℝ) < n + 1)] at h4
  linarith

/-- The profiles on the windows `|s - cₙ| < n + 1` have `∫ φₙ'² → 0`. -/
private theorem tendsto_integral_deriv_profile_sq (c : ℕ → ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ s, deriv (profile (c n) (n + 1)) s ^ 2) atTop (𝓝 0) := by
  have h (n : ℕ) : ∫ s, deriv (profile (c n) (n + 1)) s ^ 2 =
      (∫ t, deriv bump t ^ 2) / (∫ t, bump t ^ 2) * (1 / ((n : ℝ) + 1)) ^ 2 := by
    rw [integral_deriv_profile_sq (by positivity), one_div, inv_pow, ← div_eq_mul_inv, div_div]
  simpa [h] using (tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).const_mul
    ((∫ t, deriv bump t ^ 2) / ∫ t, bump t ^ 2)

/-- **Escaping profiles at `+∞`.** For every sequence `S`, there are smooth compactly supported
functions `φₙ` on `ℝ` with `∫ φₙ² = 1` and `∫ φₙ'² → 0`, each supported in `[Sₙ, ∞)`, with pairwise
disjoint supports. In `W^{1,2}(ℝ)` they form a bounded sequence escaping to `+∞` whose terms stay
`√2` apart in `L²` while their derivatives tend to `0`. -/
theorem exists_seq_contDiff_hasCompactSupport_escaping_atTop (S : ℕ → ℝ) :
    ∃ φ : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧ (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, ∫ s, φ n s ^ 2 = 1) ∧ Tendsto (fun n ↦ ∫ s, deriv (φ n) s ^ 2) atTop (𝓝 0) ∧
      (∀ n s, φ n s ≠ 0 → S n ≤ s) ∧ ∀ m n, m ≠ n → ∀ s, φ m s * φ n s = 0 := by
  obtain ⟨a, haS, ha⟩ := exists_abs_le_and_add_two_mul_le S
  refine ⟨fun n ↦ profile (a n + (n + 1)) (n + 1), fun n ↦ contDiff_profile _ _,
    fun n ↦ hasCompactSupport_profile _ _, fun n ↦ integral_profile_sq (by positivity),
    tendsto_integral_deriv_profile_sq _, fun n s hs ↦ ?_,
    fun m n hmn ↦ profile_mul_profile_eq_zero (c := fun n ↦ a n + (n + 1))
      (fun m n hmn s hs ↦ le_abs_sub_of_abs_sub_lt ha hmn hs) hmn⟩
  have h := abs_sub_lt_of_profile_ne_zero hs
  rw [abs_of_pos (by positivity : (0 : ℝ) < n + 1), abs_lt] at h
  linarith [le_abs_self (S n), haS n]

/-- **Escaping profiles at `-∞`.** For every sequence `S`, there are smooth compactly supported
functions `φₙ` on `ℝ` with `∫ φₙ² = 1` and `∫ φₙ'² → 0`, each supported in `(-∞, Sₙ]`, with
pairwise disjoint supports. -/
theorem exists_seq_contDiff_hasCompactSupport_escaping_atBot (S : ℕ → ℝ) :
    ∃ φ : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧ (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, ∫ s, φ n s ^ 2 = 1) ∧ Tendsto (fun n ↦ ∫ s, deriv (φ n) s ^ 2) atTop (𝓝 0) ∧
      (∀ n s, φ n s ≠ 0 → s ≤ S n) ∧ ∀ m n, m ≠ n → ∀ s, φ m s * φ n s = 0 := by
  obtain ⟨a, haS, ha⟩ := exists_abs_le_and_add_two_mul_le S
  -- The windows are the reflections of those used at `+∞`.
  have hrefl (n : ℕ) (s : ℝ) : |s - -(a n + (n + 1))| = |-s - (a n + (n + 1))| := by
    rw [← abs_neg]
    ring_nf
  refine ⟨fun n ↦ profile (-(a n + (n + 1))) (n + 1), fun n ↦ contDiff_profile _ _,
    fun n ↦ hasCompactSupport_profile _ _, fun n ↦ integral_profile_sq (by positivity),
    tendsto_integral_deriv_profile_sq _, fun n s hs ↦ ?_,
    fun m n hmn ↦ profile_mul_profile_eq_zero (c := fun n ↦ -(a n + (n + 1)))
      (fun m n hmn s hs ↦ ?_) hmn⟩
  · have h := abs_sub_lt_of_profile_ne_zero hs
    rw [abs_of_pos (by positivity : (0 : ℝ) < n + 1), abs_lt] at h
    linarith [neg_abs_le (S n), haS n]
  · rw [hrefl] at hs ⊢
    exact le_abs_sub_of_abs_sub_lt ha hmn hs

end TauCeti
