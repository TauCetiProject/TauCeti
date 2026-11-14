/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Real parts of continuous linear functionals on balls

For a continuous linear functional `f` on a seminormed space over `RCLike` scalars and a radius
`0 ≤ r`, every upper bound of `re ∘ f` on `closedBall x r` is at least `re (f x) + r * ‖f‖`.
Hahn–Banach separation arguments use this to turn a separating real-part bound on a ball into a
bound on the norm of the separating functional. Conversely, for `0 ≤ r < ‖f‖` the real part of
`f` exceeds `r * ‖x‖` at some point `x`. Applying `re_apply_add_mul_norm_le` on unit balls of two
factors gives the `ℓ¹` norm identity `‖Ψ ∘ inl‖ + ‖Ψ ∘ inr‖ = ‖Ψ‖` on `ℓ^∞` products `E × F`.

## Main results

* `StrongDual.re_apply_add_mul_norm_le`: a bound for the real part of a functional on a closed
  ball of nonnegative radius bounds its value at the centre plus the radius times its norm.
* `StrongDual.exists_mul_norm_lt_re_apply`: for `0 ≤ r < ‖f‖`, the real part of `f` exceeds
  `r * ‖x‖` at some point `x`.
* `StrongDual.norm_comp_inl_add_norm_comp_inr`: on `E × F` over `RCLike` scalars, the operator
  norm of `Ψ` equals the sum of the norms of its restrictions `Ψ.comp (.inl 𝕜 E F)` and
  `Ψ.comp (.inr 𝕜 E F)`.
-/

public section

open Metric RCLike

variable {𝕜 E F : Type*}

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

/-- On an `ℓ^∞`-normed product `E × F` over `RCLike` scalars, the operator norm of `Ψ` is at least
the sum of the norms of its restrictions to the two factors. -/
theorem norm_comp_inl_add_norm_comp_inr_le [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (Ψ : StrongDual 𝕜 (E × F)) :
    ‖Ψ.comp (ContinuousLinearMap.inl 𝕜 E F)‖ + ‖Ψ.comp (ContinuousLinearMap.inr 𝕜 E F)‖ ≤ ‖Ψ‖ := by
  set f₀ := Ψ.comp (ContinuousLinearMap.inl 𝕜 E F)
  set f₁ := Ψ.comp (ContinuousLinearMap.inr 𝕜 E F)
  have hball (y₀ : E) (hy₀ : y₀ ∈ closedBall (0 : E) 1) (y₁ : F)
      (hy₁ : y₁ ∈ closedBall (0 : F) 1) : re (f₀ y₀) + re (f₁ y₁) ≤ ‖Ψ‖ := by
    have hnorm : ‖(y₀, y₁)‖ ≤ 1 := by
      simp [Prod.norm_def, mem_closedBall_zero_iff.1 hy₀, mem_closedBall_zero_iff.1 hy₁]
    rw [← map_add, Ψ.comp_inl_add_comp_inr (y₀, y₁)]
    exact (re_le_norm _).trans <| (Ψ.le_opNorm _).trans <|
      (mul_le_mul_of_nonneg_left hnorm (norm_nonneg Ψ)).trans_eq (mul_one _)
  have h₁ : ∀ y₁ ∈ closedBall (0 : F) 1, re (f₁ y₁) ≤ ‖Ψ‖ - ‖f₀‖ := fun y₁ hy₁ ↦ by
    have := re_apply_add_mul_norm_le (f := f₀) (x := 0) (u := ‖Ψ‖ - re (f₁ y₁)) zero_le_one
      fun y₀ hy₀ ↦ by linarith [hball y₀ hy₀ y₁ hy₁]
    linarith [show re (f₀ 0) = 0 by simp]
  linarith [re_apply_add_mul_norm_le (f := f₁) (x := 0) zero_le_one h₁, show re (f₁ 0) = 0 by simp]

/-- On an `ℓ^∞`-normed product `E × F` over `RCLike` scalars, the operator norm of `Ψ` equals the
sum of the norms of its restrictions to the two factors. -/
theorem norm_comp_inl_add_norm_comp_inr [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (Ψ : StrongDual 𝕜 (E × F)) :
    ‖Ψ.comp (ContinuousLinearMap.inl 𝕜 E F)‖ + ‖Ψ.comp (ContinuousLinearMap.inr 𝕜 E F)‖ = ‖Ψ‖ :=
  le_antisymm (norm_comp_inl_add_norm_comp_inr_le Ψ) <|
    Ψ.opNorm_le_bound (by positivity) fun p ↦ by
      rw [← Ψ.comp_inl_add_comp_inr]
      exact (norm_add_le _ _).trans <| (add_le_add ((Ψ.comp _).le_opNorm _)
        ((Ψ.comp _).le_opNorm _)).trans <| by
          rw [add_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le p) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (norm_snd_le p) (norm_nonneg _))

end StrongDual
