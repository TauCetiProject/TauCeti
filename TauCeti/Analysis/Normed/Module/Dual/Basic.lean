/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Real parts of continuous linear functionals on balls

For a continuous linear functional `f` on a seminormed space over `RCLike` scalars and a radius
`0 ≤ r`, every upper bound of `re ∘ f` on `closedBall x r` is at least `re (f x) + r * ‖f‖`.
Hahn–Banach separation arguments use this to turn a separating real-part bound on a ball into a
bound on the norm of the separating functional. Conversely, for `0 ≤ r < ‖f‖` the real part of
`f` exceeds `r * ‖x‖` at some point `x`, and for `r < ‖f‖` it exceeds `r` at some point of the
closed unit ball, so that `‖f‖` is the supremum of `re ∘ f` on the closed unit ball.

## Main results

* `StrongDual.re_apply_add_mul_norm_le`: a bound for the real part of a functional on a closed
  ball of nonnegative radius bounds its value at the centre plus the radius times its norm.
* `StrongDual.exists_mul_norm_lt_re_apply`: for `0 ≤ r < ‖f‖`, the real part of `f` exceeds
  `r * ‖x‖` at some point `x`.
* `StrongDual.exists_lt_re_apply_of_lt_norm`: for `r < ‖f‖`, the real part of `f` exceeds `r` at
  some point of the closed unit ball.
-/

public section

open Metric RCLike

variable {𝕜 E : Type*}

namespace StrongDual

variable [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If the real part of a continuous linear functional `f` is at most `u` on the closed ball of
radius `r ≥ 0` about `x`, then `re (f x) + r * ‖f‖ ≤ u`. -/
theorem re_apply_add_mul_norm_le {f : StrongDual 𝕜 E} {x : E} {r u : ℝ} (hr : 0 ≤ r)
    (h : ∀ y ∈ closedBall x r, re (f y) ≤ u) : re (f x) + r * ‖f‖ ≤ u := by
  have hx : re (f x) ≤ u := h x (mem_closedBall_self hr)
  rcases hr.eq_or_lt with rfl | hr
  · simpa using hx
  suffices ‖f‖ ≤ (u - re (f x)) / r by
    rw [le_div_iff₀ hr] at this
    linarith
  refine f.opNorm_le_bound' (div_nonneg (sub_nonneg.2 hx) hr.le) fun z hz ↦ ?_
  have hz : 0 < ‖z‖ := (norm_nonneg z).lt_of_ne' hz
  -- Rotate `z` so that `f` takes a nonnegative real value on it, and rescale it to norm `r`.
  obtain ⟨a, ha, hfz⟩ := exists_norm_eq_mul_self (f z)
  have hy := h (x + ((r / ‖z‖ : ℝ) : 𝕜) • a • z) <| by
    simp [dist_eq_norm, norm_smul, ha, abs_of_pos hr, hz.ne']
  simp only [map_add, map_smul, smul_eq_mul, ← hfz, ← ofReal_mul, ofReal_re] at hy
  rw [div_mul_eq_mul_div, le_div_iff₀ hr]
  field_simp at hy
  nlinarith

/-- If `0 ≤ r < ‖f‖`, then the real part of `f` exceeds `r * ‖x‖` at some point `x`. -/
theorem exists_mul_norm_lt_re_apply (f : StrongDual 𝕜 E) {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < ‖f‖) :
    ∃ x, r * ‖x‖ < re (f x) := by
  obtain ⟨x, hx⟩ := f.exists_mul_lt_of_lt_opNorm hr₀ hr
  -- Rotate `x` so that `f` takes the nonnegative real value `‖f x‖` on it.
  obtain ⟨a, ha, hax⟩ := exists_norm_eq_mul_self (f x)
  refine ⟨a • x, ?_⟩
  rw [map_smul, smul_eq_mul, ← hax, ofReal_re, norm_smul, ha, one_mul]
  exact hx

/-- If `r < ‖f‖`, then the real part of `f` exceeds `r` at some point of the closed unit ball. -/
theorem exists_lt_re_apply_of_lt_norm (f : StrongDual 𝕜 E) {r : ℝ} (hr : r < ‖f‖) :
    ∃ x, ‖x‖ ≤ 1 ∧ r < re (f x) := by
  rcases lt_or_ge r 0 with hr₀ | hr₀
  · exact ⟨0, by simp, by simpa using hr₀⟩
  obtain ⟨x, hx⟩ := f.exists_mul_norm_lt_re_apply hr₀ hr
  have hx₀ : 0 < ‖x‖ := by
    refine (norm_nonneg x).lt_of_ne' fun h ↦ ?_
    have := (re_le_norm (f x)).trans (f.le_opNorm x)
    rw [h, mul_zero] at this hx
    linarith
  -- Normalize `x` to the unit sphere.
  refine ⟨((‖x‖⁻¹ : ℝ) : 𝕜) • x, ?_, ?_⟩
  · rw [norm_smul, norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hx₀.ne']
  · rwa [map_smul, smul_eq_mul, re_ofReal_mul, ← div_eq_inv_mul, lt_div_iff₀ hx₀]

end StrongDual
