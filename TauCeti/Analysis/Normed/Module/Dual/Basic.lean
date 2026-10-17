/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# Real parts of continuous linear functionals on balls

For a continuous linear functional `f` on a seminormed space over `RCLike` scalars and a radius
`0 ≤ r`, every upper bound of `re ∘ f` on `closedBall x r` is at least `re (f x) + r * ‖f‖`.
Hahn–Banach separation arguments use this to turn a separating real-part bound on a ball into a
bound on the norm of the separating functional.

## Main results

* `StrongDual.re_apply_add_mul_norm_le`: a bound for the real part of a functional on a closed
  ball of nonnegative radius bounds its value at the centre plus the radius times its norm.
-/

public section

open Metric RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace StrongDual

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

end StrongDual
