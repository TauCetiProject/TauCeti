/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import TauCeti.Analysis.Convex.FunctionTopology

/-!
# Scalar consequences of McCann's condition

A function `U : ℝ → ℝ` satisfies *McCann's condition* in dimension `n` when
`φ(s) = sⁿ U(s⁻ⁿ)` is convex and nonincreasing on `(0, ∞)`. This is the hypothesis of McCann's
displacement convexity of the internal energy `∫ U(dμ/dρ) dρ`. This file records the scalar facts
about `U` and `φ` that it is used through, independently of any transport.

## Main results

* `TauCeti.pow_mul_apply_div_pow_eq`: for `r, a > 0`, `aⁿ U(r / aⁿ) = r φ(r^{-1/n} a)`.
* `TauCeti.pow_mul_apply_div_pow_le`: McCann's pointwise inequality, comparing `aⁿ U(r / aⁿ)` with
  the convex combination of its values at `1` and `a₁` when `(1 - t) + t a₁ ≤ a`.
* `TauCeti.measurable_apply_max_of_convexOn`: if `φ` is convex on `(0, ∞)`, then `U` is measurable
  on `[0, ∞)`.

## References

* R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153–179.
-/

public section

open Set Filter

namespace TauCeti

variable {U : ℝ → ℝ} {n : ℕ}

/-- For `r > 0` and `a > 0`, the function `a ↦ aⁿ U(r / aⁿ)` is `r φ(c a)` with
`φ(s) = sⁿ U(s⁻ⁿ)` and `c = r^{-1/n}`. -/
theorem pow_mul_apply_div_pow_eq (hn : n ≠ 0) {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 0 < a) :
    a ^ n * U (r / a ^ n) =
      r * ((r⁻¹ ^ (n⁻¹ : ℝ) * a) ^ n * U ((r⁻¹ ^ (n⁻¹ : ℝ) * a) ^ n)⁻¹) := by
  rw [mul_pow, Real.rpow_inv_natCast_pow (inv_nonneg.2 hr.le) hn,
    show (r⁻¹ * a ^ n)⁻¹ = r / a ^ n by field_simp]
  field_simp

/-- **McCann's pointwise inequality.** Let `U 0 = 0` and let `φ(s) = sⁿ U(s⁻ⁿ)` be convex and
nonincreasing on `(0, ∞)`, with `n ≠ 0`. If `a > 0` and `a₁ ≥ 0` satisfy the concavity bound
`(1 - t) + t a₁ ≤ a` for some `t ∈ [0, 1]`, then for every `r ≥ 0`,
`aⁿ U(r / aⁿ) ≤ (1 - t) U(r) + t a₁ⁿ U(r / a₁ⁿ)` when `a₁ > 0`, and
`aⁿ U(r / aⁿ) ≤ (1 - t) U(r) + t r L` when `a₁ = 0`, where `L` bounds `φ` above. -/
theorem pow_mul_apply_div_pow_le (hn : n ≠ 0) (hU0 : U 0 = 0)
    (hc : ConvexOn ℝ (Ioi 0) fun s : ℝ => s ^ n * U (s ^ n)⁻¹)
    (ha : AntitoneOn (fun s : ℝ => s ^ n * U (s ^ n)⁻¹) (Ioi 0)) {r t a a₁ L : ℝ} (hr : 0 ≤ r)
    (ht : t ∈ Icc (0 : ℝ) 1) (hapos : 0 < a) (ha₁ : 0 ≤ a₁) (hle : 1 - t + t * a₁ ≤ a)
    (hL : a₁ = 0 → 0 < r → ∀ s ∈ Ioi (0 : ℝ), s ^ n * U (s ^ n)⁻¹ ≤ L) :
    a ^ n * U (r / a ^ n) ≤
      (1 - t) * U r + t * (if a₁ = 0 then r * L else a₁ ^ n * U (r / a₁ ^ n)) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [hU0]
  set φ : ℝ → ℝ := fun s => s ^ n * U (s ^ n)⁻¹
  set c := r⁻¹ ^ (n⁻¹ : ℝ)
  have hc0 : 0 < c := Real.rpow_pos_of_pos (inv_pos.2 hr) _
  have hU1 : U r = r * φ (c * 1) := by
    simpa using pow_mul_apply_div_pow_eq (U := U) hn hr one_pos
  rw [pow_mul_apply_div_pow_eq hn hr hapos, hU1, mul_one]
  split_ifs with ha₁0
  · -- The degenerate case: compare with `φ (c (1 - t))` and use the bound `L` at `0`.
    subst ha₁0
    have hφL := hL rfl hr
    rcases ht.2.eq_or_lt with rfl | ht₁
    · simpa using mul_le_mul_of_nonneg_left (hφL _ (mul_pos hc0 hapos)) hr.le
    have hb : 0 < 1 - t := sub_pos.2 ht₁
    have h₁ : φ (c * a) ≤ φ ((1 - t) * c) :=
      ha (mem_Ioi.2 (mul_pos hb hc0)) (mem_Ioi.2 (mul_pos hc0 hapos))
        (by nlinarith)
    have h₂ := hc.apply_mul_le_of_forall_le hφL hc0 hb (by linarith [ht.1])
    have := mul_le_mul_of_nonneg_left (h₁.trans h₂) hr.le
    linarith
  · have ha₁' : 0 < a₁ := lt_of_le_of_ne ha₁ (Ne.symm ha₁0)
    rw [pow_mul_apply_div_pow_eq hn hr ha₁']
    have hpos : 0 < 1 - t + t * a₁ := by
      rcases ht.2.eq_or_lt with rfl | ht₁
      · simpa using ha₁'
      · nlinarith [ht.1]
    have h₁ : φ (c * a) ≤ φ (c * (1 - t + t * a₁)) :=
      ha (mem_Ioi.2 (mul_pos hc0 hpos)) (mem_Ioi.2 (mul_pos hc0 hapos))
        (mul_le_mul_of_nonneg_left hle hc0.le)
    have h₂ : φ (c * (1 - t + t * a₁)) ≤ (1 - t) * φ c + t * φ (c * a₁) := by
      have := hc.2 (mem_Ioi.2 hc0) (mem_Ioi.2 (mul_pos hc0 ha₁')) (sub_nonneg.2 ht.2) ht.1
        (by ring)
      simp only [smul_eq_mul] at this
      convert this using 2
      ring
    have := mul_le_mul_of_nonneg_left (h₁.trans h₂) hr.le
    linarith

/-- If `φ(s) = sⁿ U(s⁻ⁿ)` is convex on `(0, ∞)`, with `n ≠ 0`, then `U` is measurable on
`[0, ∞)`: it is continuous on `(0, ∞)`, where `U(r) = r φ(r^{-1/n})` with `φ` convex. -/
theorem measurable_apply_max_of_convexOn (hn : n ≠ 0)
    (hc : ConvexOn ℝ (Ioi 0) fun s : ℝ => s ^ n * U (s ^ n)⁻¹) :
    Measurable fun r : ℝ => U (max r 0) := by
  refine measurable_of_continuousOn_compl_singleton 0 fun r hr => ?_
  rcases lt_or_gt_of_ne hr with hr | hr
  · -- Left of `0` the function is constant.
    refine (continuousAt_const (y := U 0)).congr ?_ |>.continuousWithinAt
    filter_upwards [Iio_mem_nhds hr] with r' hr'
    rw [max_eq_right hr'.le]
  · -- Right of `0` it is `r ↦ r φ(r^{-1/n})`, with `φ` continuous as a convex function.
    have hφ : ContinuousOn (fun s : ℝ => s ^ n * U (s ^ n)⁻¹) (Ioi 0) := by
      simpa using hc.continuousOn_interior
    have hpos : 0 < r⁻¹ ^ (n⁻¹ : ℝ) := Real.rpow_pos_of_pos (inv_pos.2 hr) _
    have hcont : ContinuousAt (fun r : ℝ => r * ((r⁻¹ ^ (n⁻¹ : ℝ)) ^ n *
        U ((r⁻¹ ^ (n⁻¹ : ℝ)) ^ n)⁻¹)) r := by
      exact continuousAt_id.mul ((hφ.continuousAt (Ioi_mem_nhds hpos)).comp
        (f := fun r : ℝ => r⁻¹ ^ (n⁻¹ : ℝ))
        ((continuousAt_inv₀ hr.ne').rpow_const (.inl (inv_ne_zero hr.ne'))))
    refine (hcont.congr ?_).continuousWithinAt
    filter_upwards [Ioi_mem_nhds hr] with r' hr'
    have := pow_mul_apply_div_pow_eq (U := U) hn hr' one_pos
    simp only [one_pow, div_one, one_mul, mul_one] at this
    rw [max_eq_left (le_of_lt hr'), this]

end TauCeti
