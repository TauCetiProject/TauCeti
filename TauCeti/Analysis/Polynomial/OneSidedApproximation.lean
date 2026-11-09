/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# One-sided polynomial approximation

Shifting a uniform Weierstrass approximation by a constant gives one-sided approximations: a
function continuous on `[a, b]` lies below a polynomial within `ε` of it, and above another one.

Applied to a continuous ramp, this squeezes the indicator of `[a, 1]` on `[0, 1]` between two
polynomials whose integrals are both within `η` of the length `1 - a`. This is the approximation
step of Karamata's proof of the Hardy–Littlewood Tauberian theorem.

## Main results

* `TauCeti.exists_polynomial_ge_of_continuousOn`: a polynomial above `f` and within `ε` of it.
* `TauCeti.exists_polynomial_le_of_continuousOn`: a polynomial below `f` and within `ε` of it.
* `TauCeti.exists_polynomial_ge_indicator`: a polynomial above the indicator of `[a, 1]` on
  `[0, 1]`, with integral at most `1 - a + η`.
* `TauCeti.exists_polynomial_le_indicator`: a polynomial below the indicator of `[a, 1]` on
  `[0, 1]`, with integral at least `1 - a - η`.

## References

* J. Karamata, *Über die Hardy–Littlewoodschen Umkehrungen des Abelschen Stetigkeitssatzes*,
  Math. Z. **32** (1930), 319–320.
-/

public section

open Polynomial

namespace TauCeti

/-- **One-sided Weierstrass approximation from above.** A function continuous on `[a, b]` is
bounded above on `[a, b]` by a polynomial exceeding it by at most `ε`. -/
theorem exists_polynomial_ge_of_continuousOn {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, f x ≤ p.eval x ∧ p.eval x ≤ f x + ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf (ε / 2) (half_pos hε)
  refine ⟨p + C (ε / 2), fun x hx ↦ ?_⟩
  have := abs_lt.1 (hp x hx)
  simp only [eval_add, eval_C]
  constructor <;> linarith [this.1, this.2]

/-- **One-sided Weierstrass approximation from below.** A function continuous on `[a, b]` is
bounded below on `[a, b]` by a polynomial falling short of it by at most `ε`. -/
theorem exists_polynomial_le_of_continuousOn {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, f x - ε ≤ p.eval x ∧ p.eval x ≤ f x := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf (ε / 2) (half_pos hε)
  refine ⟨p - C (ε / 2), fun x hx ↦ ?_⟩
  have := abs_lt.1 (hp x hx)
  simp only [eval_sub, eval_C]
  constructor <;> linarith [this.1, this.2]

/-- A continuous piecewise linear ramp, `0` left of `b` and `1` right of `b + w`. -/
private noncomputable def ramp (b w u : ℝ) : ℝ := max 0 (min 1 ((u - b) / w))

private lemma continuous_ramp (b w : ℝ) : Continuous (ramp b w) :=
  continuous_const.max (continuous_const.min ((continuous_id.sub continuous_const).div_const w))

private lemma ramp_nonneg (b w u : ℝ) : 0 ≤ ramp b w u := le_max_left _ _

private lemma ramp_le_one (b w u : ℝ) : ramp b w u ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

private lemma ramp_eq_zero {b w u : ℝ} (hw : 0 < w) (hu : u ≤ b) : ramp b w u = 0 :=
  max_eq_left (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le))

private lemma ramp_eq_one {b w u : ℝ} (hw : 0 < w) (hu : b + w ≤ u) : ramp b w u = 1 := by
  rw [ramp, min_eq_left ((le_div_iff₀ hw).2 (by linarith)), max_eq_right zero_le_one]

private lemma integral_ramp_le {b w : ℝ} (hw : 0 < w) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∫ u in (0 : ℝ)..1, ramp b w u ≤ 1 - b := by
  have hc := continuous_ramp b w
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 b)
    (hc.intervalIntegrable b 1)]
  have h1 : ∫ u in (0 : ℝ)..b, ramp b w u ≤ ∫ u in (0 : ℝ)..b, (0 : ℝ) :=
    intervalIntegral.integral_mono_on hb0 (hc.intervalIntegrable _ _) intervalIntegrable_const
      fun u hu ↦ (ramp_eq_zero hw hu.2).le
  have h2 : ∫ u in b..1, ramp b w u ≤ ∫ u in b..1, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hb1 (hc.intervalIntegrable _ _) intervalIntegrable_const
      fun u _ ↦ ramp_le_one b w u
  simp only [intervalIntegral.integral_zero, intervalIntegral.integral_const, smul_eq_mul,
    mul_one] at h1 h2
  linarith

private lemma le_integral_ramp {b w : ℝ} (hw : 0 < w) (hb0 : 0 ≤ b) (hbw : b + w ≤ 1) :
    1 - (b + w) ≤ ∫ u in (0 : ℝ)..1, ramp b w u := by
  have hc := continuous_ramp b w
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (b + w))
    (hc.intervalIntegrable (b + w) 1)]
  have h1 : 0 ≤ ∫ u in (0 : ℝ)..(b + w), ramp b w u :=
    intervalIntegral.integral_nonneg (by linarith) fun u _ ↦ ramp_nonneg b w u
  have h2 : ∫ u in (b + w)..1, (1 : ℝ) ≤ ∫ u in (b + w)..1, ramp b w u :=
    intervalIntegral.integral_mono_on hbw intervalIntegrable_const (hc.intervalIntegrable _ _)
      fun u hu ↦ (ramp_eq_one hw hu.1).ge
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
  linarith

/-- A polynomial above the indicator of `[a, 1]` on `[0, 1]`, with integral at most
`1 - a + η`. -/
theorem exists_polynomial_ge_indicator {a η : ℝ} (ha1 : a ≤ 1) (hη : 0 < η) :
    ∃ Q : ℝ[X], (∀ u ∈ Set.Icc (0 : ℝ) 1, (if a ≤ u then (1 : ℝ) else 0) ≤ Q.eval u) ∧
      ∫ u in (0 : ℝ)..1, Q.eval u ≤ 1 - a + η := by
  rcases le_or_gt a 0 with ha0 | ha0
  · refine ⟨C 1, fun u _ ↦ ?_, ?_⟩
    · rw [eval_C]
      split_ifs <;> norm_num
    · simp only [eval_C, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
      linarith
  set w := min (η / 3) a
  have hw : 0 < w := lt_min (by positivity) ha0
  have hwa : w ≤ a := min_le_right _ _
  have hwη : w ≤ η / 3 := min_le_left _ _
  obtain ⟨Q, hQ⟩ := exists_polynomial_ge_of_continuousOn (continuous_ramp (a - w) w).continuousOn
    (a := 0) (b := 1) hw
  refine ⟨Q, fun u hu ↦ le_trans ?_ (hQ u hu).1, ?_⟩
  · split_ifs with h
    · rw [ramp_eq_one hw (by linarith)]
    · exact ramp_nonneg _ _ _
  · have hint : ∫ u in (0 : ℝ)..1, Q.eval u ≤ ∫ u in (0 : ℝ)..1, (ramp (a - w) w u + w) :=
      intervalIntegral.integral_mono_on zero_le_one (Q.continuous.intervalIntegrable _ _)
        (((continuous_ramp _ _).add continuous_const).intervalIntegrable _ _)
        fun u hu ↦ (hQ u hu).2
    rw [intervalIntegral.integral_add ((continuous_ramp _ _).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const] at hint
    have := integral_ramp_le hw (by linarith) (by linarith : a - w ≤ 1)
    simp only [sub_zero, smul_eq_mul, one_mul] at hint
    linarith

/-- A polynomial below the indicator of `[a, 1]` on `[0, 1]`, with integral at least
`1 - a - η`. -/
theorem exists_polynomial_le_indicator {a η : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hη : 0 < η) :
    ∃ Q : ℝ[X], (∀ u ∈ Set.Icc (0 : ℝ) 1, Q.eval u ≤ if a ≤ u then (1 : ℝ) else 0) ∧
      1 - a - η ≤ ∫ u in (0 : ℝ)..1, Q.eval u := by
  set w := min (η / 3) (1 - a)
  have hw : 0 < w := lt_min (by positivity) (by linarith)
  have hwa : w ≤ 1 - a := min_le_right _ _
  have hwη : w ≤ η / 3 := min_le_left _ _
  obtain ⟨Q, hQ⟩ := exists_polynomial_le_of_continuousOn (continuous_ramp a w).continuousOn
    (a := 0) (b := 1) hw
  refine ⟨Q, fun u hu ↦ (hQ u hu).2.trans ?_, ?_⟩
  · split_ifs with h
    · exact ramp_le_one _ _ _
    · exact (ramp_eq_zero hw (not_le.1 h).le).le
  · have hint : ∫ u in (0 : ℝ)..1, (ramp a w u - w) ≤ ∫ u in (0 : ℝ)..1, Q.eval u :=
      intervalIntegral.integral_mono_on zero_le_one
        (((continuous_ramp _ _).sub continuous_const).intervalIntegrable _ _)
        (Q.continuous.intervalIntegrable _ _) fun u hu ↦ (hQ u hu).1
    rw [intervalIntegral.integral_sub ((continuous_ramp _ _).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const] at hint
    have := le_integral_ramp hw ha0 (by linarith : a + w ≤ 1)
    simp only [sub_zero, smul_eq_mul, one_mul] at hint
    linarith

end TauCeti
