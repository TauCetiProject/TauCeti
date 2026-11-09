/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Trigonometric bounds and nonvanishing criteria

The sine of `π / x` is positive for real `x > 1`. The sine of `π * x` is nonzero for nonzero
`x ∈ (-1, 1)`, a criterion used to detect nonflat Schwarz–Christoffel turns. The sine is
nonpositive on `[π, 2π]`. For real `a < 1` the quantity `1 - a sin² θ` is positive, a bound
`a sin² φ < 1` with `φ ≤ π / 2` gives `a sin² θ < 1` for `θ ∈ [0, φ]`, and
`1 - k² ≤ 1 - k² sin² θ ≤ 1` for every real `k`. Jordan's inequality gives `θ ≤ π / 2 * sin θ` on
`[0, π / 2]`. Cosine is positive strictly between two
angles in `[-π/2, π/2]`, in either orientation (`TauCeti.cos_pos_of_mem_uIoo`). On
`(-π / 2, π / 2)` the square of the sine is less than `1`, so `sin (x / 2) ^ 2 < 1` for `|x| < π`.
If `cos (2πr) < cos (2πx)` with `r ≥ 0`, then `x` lies within `r` of an integer
(`TauCeti.exists_abs_sub_int_lt_of_cos_lt`).

For angles `α, β > 0` and `γ ≥ 0` with
`α + β + γ < π`, the quotient `(cos α cos β + cos γ) / (sin α sin β)` is greater than `1`; by the
second hyperbolic law of cosines it is the hyperbolic cosine of the side opposite `γ` in a
hyperbolic triangle with angles `α`, `β`, `γ`. These supply the positive sine factors and the
hyperbolic scale in the matrix representations of triangle groups.
-/

public section

open Real

namespace TauCeti

/-- Cosine is positive strictly between two angles in `[-π/2, π/2]`, in either orientation. -/
theorem cos_pos_of_mem_uIoo {a b θ : ℝ}
    (ha : |a| ≤ π / 2) (hb : |b| ≤ π / 2) (hθ : θ ∈ Set.uIoo a b) :
    0 < cos θ :=
  cos_pos_of_mem_Ioo (Set.uIoo_subset_Ioo (abs_le.mp ha) (abs_le.mp hb) hθ)

/-- The sine is nonpositive on `[π, 2π]`. -/
theorem sin_nonpos_of_pi_le_of_le_two_pi {x : ℝ} (hpx : π ≤ x) (hxp : x ≤ 2 * π) : sin x ≤ 0 := by
  rw [← sin_sub_two_pi]
  exact sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)

/-- The quantity `1 - a sin² θ` is positive when `a < 1`. -/
theorem one_sub_mul_sin_sq_pos {a : ℝ} (ha : a < 1) (θ : ℝ) : 0 < 1 - a * sin θ ^ 2 := by
  have h₀ := sq_nonneg (sin θ)
  have h₁ := sin_sq_le_one θ
  rcases le_or_gt a 0 with h | h <;> nlinarith

/-- A bound `a sin² φ < 1` propagates from `φ ≤ π / 2` to every `θ ∈ [0, φ]`. -/
theorem mul_sin_sq_lt_one_of_le {a θ φ : ℝ} (ha : a * sin φ ^ 2 < 1) (h0 : 0 ≤ θ) (hθ : θ ≤ φ)
    (hφ : φ ≤ π / 2) : a * sin θ ^ 2 < 1 := by
  rcases le_or_gt 0 a with ha0 | ha0
  · have hsin : sin θ ^ 2 ≤ sin φ ^ 2 :=
      pow_le_pow_left₀ (sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos]))
        (sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hφ hθ) 2
    exact (mul_le_mul_of_nonneg_left hsin ha0).trans_lt ha
  · nlinarith [sq_nonneg (sin θ)]

/-- For every real `k`, `1 - k² ≤ 1 - k² sin² θ`. -/
theorem one_sub_sq_le_one_sub_sq_mul_sin_sq (k θ : ℝ) :
    1 - k ^ 2 ≤ 1 - k ^ 2 * sin θ ^ 2 := by
  nlinarith [sin_sq_le_one θ, sq_nonneg k]

/-- For every real `k`, `1 - k² sin² θ ≤ 1`. -/
theorem one_sub_sq_mul_sin_sq_le_one (k θ : ℝ) : 1 - k ^ 2 * sin θ ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg (sin θ), sq_nonneg k]

/-- The square of the sine is less than `1` on `(-π / 2, π / 2)`. -/
theorem sin_sq_lt_one_of_abs_lt {x : ℝ} (hx : |x| < π / 2) : sin x ^ 2 < 1 := by
  have h := cos_pos_of_mem_Ioo ⟨neg_lt_of_abs_lt hx, lt_of_abs_lt hx⟩
  nlinarith [sin_sq_add_cos_sq x]

/-- The square of `sin (x / 2)` is less than `1` for `|x| < π`. -/
theorem sin_half_sq_lt_one_of_abs_lt {x : ℝ} (hx : |x| < π) : sin (x / 2) ^ 2 < 1 :=
  sin_sq_lt_one_of_abs_lt (by rw [abs_div, abs_two]; linarith)

/-- If `x` is nonzero and strictly between `-1` and `1`, then `sin (π * x)` is nonzero. -/
theorem sin_pi_mul_ne_zero_of_mem_Ioo_of_ne_zero {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    sin (π * x) ≠ 0 := by
  have hlow : -π < π * x := by
    nlinarith [mul_lt_mul_of_pos_left hx.1 pi_pos]
  have hupp : π * x < π := by
    nlinarith [mul_lt_mul_of_pos_left hx.2 pi_pos]
  intro hsin
  exact (mul_ne_zero pi_ne_zero hx0)
    ((sin_eq_zero_iff_of_lt_of_lt hlow hupp).mp hsin)

/-- For a real denominator greater than one, the sine of `π / x` is positive. -/
theorem sin_pi_div_pos {x : ℝ} (hx : 1 < x) : 0 < sin (π / x) :=
  sin_pos_of_pos_of_lt_pi (div_pos pi_pos (by linarith)) (div_lt_self pi_pos hx)

/-- If `α, β > 0`, `γ ≥ 0` and `α + β + γ < π`, then `(cos α cos β + cos γ) / (sin α sin β) > 1`.
Indeed `cos α cos β - sin α sin β = -cos (π - α - β)`, and `cos (π - α - β) < cos γ` because
`0 ≤ γ < π - α - β ≤ π`. -/
theorem one_lt_cos_mul_cos_add_cos_div_sin_mul_sin {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 ≤ γ) (h : α + β + γ < π) : 1 < (cos α * cos β + cos γ) / (sin α * sin β) := by
  have hs : 0 < sin α * sin β :=
    mul_pos (sin_pos_of_pos_of_lt_pi hα (by linarith)) (sin_pos_of_pos_of_lt_pi hβ (by linarith))
  have hcos : cos (π - (α + β)) < cos γ :=
    cos_lt_cos_of_nonneg_of_le_pi hγ (by linarith) (by linarith)
  rw [cos_pi_sub, cos_add] at hcos
  rw [one_lt_div hs]
  linarith

/-- Positive angles with sum less than `π` determine a positive hyperbolic scale `t` for which
`cosh t * sin α * sin β = cos α * cos β + cos γ`. -/
theorem exists_pos_cosh_mul_sin_mul_sin_eq {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 ≤ γ) (h : α + β + γ < π) :
    ∃ t : ℝ, 0 < t ∧ cosh t * (sin α * sin β) = cos α * cos β + cos γ := by
  have hs : 0 < sin α * sin β :=
    mul_pos (sin_pos_of_pos_of_lt_pi hα (by linarith))
      (sin_pos_of_pos_of_lt_pi hβ (by linarith))
  have hκ := one_lt_cos_mul_cos_add_cos_div_sin_mul_sin hα hβ hγ h
  refine ⟨arcosh _, arcosh_pos hκ, ?_⟩
  rw [cosh_arcosh hκ.le, div_mul_cancel₀ _ hs.ne']

/-- If `cos (2πr) < cos (2πx)` for some `0 ≤ r`, then `x` lies within `r` of an integer. -/
theorem exists_abs_sub_int_lt_of_cos_lt {x r : ℝ} (hr₀ : 0 ≤ r)
    (h : cos (2 * π * r) < cos (2 * π * x)) : ∃ k : ℤ, |x - k| < r := by
  refine ⟨round x, not_le.mp fun hle ↦ h.not_ge ?_⟩
  have hy := abs_sub_round x
  have hcos : cos (2 * π * x) = cos (2 * π * |x - round x|) := by
    rw [← abs_of_pos (by positivity : 0 < 2 * π), ← abs_mul, abs_of_pos (by positivity : 0 < 2 * π),
      cos_abs, mul_sub, ← cos_sub_int_mul_two_pi (2 * π * x) (round x)]
    ring_nf
  rw [hcos]
  exact cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos])
    (by nlinarith [pi_pos])

/-- Jordan's inequality in the form `θ ≤ π / 2 * sin θ` for `θ ∈ [0, π / 2]`, with the sine given
as a value `s`. -/
theorem le_pi_div_two_mul_of_sin_eq {θ s : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2)
    (hsin : sin θ = s) : θ ≤ π / 2 * s := by
  have h := mul_le_sin h0 h1
  rw [hsin, div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at h
  nlinarith

/-- **The parameters of the hyperbolic law of cosines.** Positive angles `α, β` and `γ ≥ 0` with
`α + β + γ < π` determine `K` with `K sin α sin β = cos α cos β + cos γ` and `t > 1` with
`t + t⁻¹ = 2 K`, that is `t ^ 2 + 1 = 2 K t`. Here `t` is the exponential of the positive number
of `exists_pos_cosh_mul_sin_mul_sin_eq`. -/
theorem exists_cosine_rule_parameter {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ)
    (h : α + β + γ < π) :
    ∃ K t : ℝ, K * (sin α * sin β) = cos α * cos β + cos γ ∧ 1 < t ∧ t ^ 2 + 1 = 2 * K * t := by
  obtain ⟨d, hd, hK⟩ := exists_pos_cosh_mul_sin_mul_sin_eq hα hβ hγ h
  refine ⟨cosh d, exp d, hK, Real.one_lt_exp_iff.2 hd, ?_⟩
  rw [cosh_eq, exp_neg]
  field_simp

end TauCeti
