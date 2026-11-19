/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Dilation
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Compact chart seminorms of quadratics and exponentials on `ℝ`

This file computes compact chart seminorms of two explicit functions on `ℝ`, in the identity
chart, and uses them to illustrate the scalar-field analogue of the comparison of compact chart
seminorms under a change of coordinates (`ContMDiffMap.exists_chartCkSeminorm_le_coordChange`),
where the change of coordinates is applied to the map rather than to the chart.

* **Quadratics.** For `f x = a * x ^ 2` and the interval `[-r, r]`, `r ≥ 0`, the `m`th
  derivative seminorm is `2.descFactorial m * |a| * r ^ (2 - m)`
  (`ContMDiffMap.chartDerivativeSeminorm_Icc_of_forall_apply_eq_mul_sq`). For `δ x ^ 2` on
  `[-1, 1]` the suprema of orders `0`, `1` and `2` are `δ`, `2 δ` and `2 δ`: a bound on the values
  alone misses the bounds on the derivatives.
* **A contraction.** Under the change of coordinates `x = y / 2`, which carries `K = [-2, 2]` onto
  `[-1, 1]`, the function `x ^ 2` becomes `y ^ 2 / 4`. Its suprema of orders `0`, `1` and `2` are
  `1`, `1` and `1 / 2` on `K`, against `1`, `2` and `2` for `x ^ 2` on `[-1, 1]`: the `m`th
  derivative is scaled by `(1 / 2) ^ m`, so the compact `C^k` seminorm does not increase, with
  constant `1` in every order
  (`ContMDiffMap.chartCkSeminorm_selfChartCompacts_le_of_forall_apply_eq_apply_mul_of_norm_le_one`).
* **An expansion.** The reverse change `y = 2 x` scales the `m`th derivative by `2 ^ m`. The
  exponential attains the resulting constant `2 ^ k`: the compact `C^k` seminorm of `exp (2 x)`
  on `[-1, 1]` is `2 ^ k` times that of `exp` on `[-2, 2]`
  (`ContMDiffMap.chartCkSeminorm_Icc_exp_two_mul_eq`). So no constant independent of the order
  `k` bounds the `C^k` seminorms after this change of coordinates
  (`ContMDiffMap.not_exists_forall_chartCkSeminorm_le_of_forall_apply_eq_apply_two_mul`): the
  constant for the dilation `y ↦ 2 * y` must depend on `k`, matching the analogous chart-change
  comparison, whose constant is chosen after `k`.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for the compact `C^r` seminorms
  and their behaviour under changes of charts.
-/

public section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace ContMDiffMap

variable {n : WithTop ℕ∞}

/-- The ordinary iterated derivatives of `a * x ^ 2`. -/
private theorem iteratedDeriv_of_forall_apply_eq_mul_sq {f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯} {a : ℝ}
    (hf : ∀ y, f y = a * y ^ 2) (m : ℕ) (y : ℝ) :
    iteratedDeriv m f y = (Nat.descFactorial 2 m : ℝ) * a * y ^ (2 - m) := by
  have hf' : (f : ℝ → ℝ) = fun y ↦ a * y ^ 2 := funext hf
  rw [hf', iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  ring

/-- **Derivative seminorms of a quadratic.** For `f x = a * x ^ 2` on `ℝ` and `r ≥ 0`, the `m`th
derivative seminorm on `[-r, r]` is `2.descFactorial m * |a| * r ^ (2 - m)`: it is `|a| * r ^ 2`,
`2 * |a| * r` and `2 * |a|` in the orders `0`, `1` and `2`, and `0` above. -/
theorem chartDerivativeSeminorm_Icc_of_forall_apply_eq_mul_sq {f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯}
    {a r : ℝ} (hf : ∀ y, f y = a * y ^ 2) (hr : 0 ≤ r) (x : ℝ) (m : ℕ) (hm : m ≤ n) :
    chartDerivativeSeminorm x (selfChartCompacts x ⟨Icc (-r) r, isCompact_Icc⟩) m hm f =
      (Nat.descFactorial 2 m : ℝ) * |a| * r ^ (2 - m) := by
  have hnorm (y : ℝ) :
      ‖iteratedDeriv m f y‖ = (Nat.descFactorial 2 m : ℝ) * |a| * |y| ^ (2 - m) := by
    rw [iteratedDeriv_of_forall_apply_eq_mul_sq hf, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      Nat.abs_cast]
  refine le_antisymm ((chartDerivativeSeminorm_selfChartCompacts_le_iff f x _ m hm
    (by positivity)).mpr fun y hy ↦ ?_) ?_
  · rw [hnorm]
    gcongr
    exact abs_le.mpr hy
  · have h := norm_iteratedDeriv_le_chartDerivativeSeminorm f x ⟨Icc (-r) r, isCompact_Icc⟩ m hm
      (z := r) ⟨by linarith, le_rfl⟩
    rwa [hnorm, abs_of_nonneg hr] at h

/-- The interval `[-2, 2]` is carried onto `[-1, 1]` by `y ↦ y / 2`. -/
private theorem map_half_mul_Icc :
    (⟨Icc (-2) 2, isCompact_Icc⟩ : Compacts ℝ).map ((1 / 2 : ℝ) * ·) (continuous_const_mul _) =
      ⟨Icc (-1) 1, isCompact_Icc⟩ := by
  ext y
  rw [Compacts.coe_map, Compacts.coe_mk, Set.image_mul_left_Icc (by norm_num) (by norm_num)]
  norm_num

/-- `δ x ^ 2` on `[-1, 1]`: the suprema of orders `0`, `1` and `2` are `δ`, `2 δ` and `2 δ`. -/
example {f : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯} {δ : ℝ} (hδ : 0 < δ) (hf : ∀ y, f y = δ * y ^ 2)
    (h2 : 2 ≤ n) :
    chartDerivativeSeminorm 0 (selfChartCompacts 0 ⟨Icc (-1) 1, isCompact_Icc⟩) 0 (by simp) f =
        δ ∧
      chartDerivativeSeminorm 0 (selfChartCompacts 0 ⟨Icc (-1) 1, isCompact_Icc⟩) 1
        (le_trans (by norm_num) h2) f = 2 * δ ∧
      chartDerivativeSeminorm 0 (selfChartCompacts 0 ⟨Icc (-1) 1, isCompact_Icc⟩) 2 h2 f =
        2 * δ := by
  simp only [chartDerivativeSeminorm_Icc_of_forall_apply_eq_mul_sq hf zero_le_one,
    abs_of_pos hδ]
  norm_num [Nat.descFactorial]

/-- Under `x = y / 2`, the function `x ^ 2` becomes `y ^ 2 / 4`, whose suprema of orders `0`, `1`
and `2` on `[-2, 2]` are `1`, `1` and `1 / 2`, against `1`, `2` and `2` for `x ^ 2` on `[-1, 1]`;
the `m`th one is scaled by `(1 / 2) ^ m`. -/
example {f g : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯} (hf : ∀ x, f x = x ^ 2) (hg : ∀ y, g y = f (1 / 2 * y))
    (h2 : 2 ≤ n) :
    (chartDerivativeSeminorm 0 (selfChartCompacts 0 ⟨Icc (-2) 2, isCompact_Icc⟩) 0 (by simp) g,
      chartDerivativeSeminorm 0 (selfChartCompacts 0 ⟨Icc (-2) 2, isCompact_Icc⟩) 1
        (le_trans (by norm_num) h2) g,
      chartDerivativeSeminorm 0 (selfChartCompacts 0 ⟨Icc (-2) 2, isCompact_Icc⟩) 2 h2 g) =
        (1, 1, 1 / 2) ∧
    (chartDerivativeSeminorm 0 (selfChartCompacts 0 ⟨Icc (-1) 1, isCompact_Icc⟩) 0 (by simp) f,
      chartDerivativeSeminorm 0 (selfChartCompacts 0 ⟨Icc (-1) 1, isCompact_Icc⟩) 1
        (le_trans (by norm_num) h2) f,
      chartDerivativeSeminorm 0 (selfChartCompacts 0 ⟨Icc (-1) 1, isCompact_Icc⟩) 2 h2 f) =
        (1, 2, 2) := by
  have hf' (x : ℝ) : f x = 1 * x ^ 2 := by rw [hf, one_mul]
  have hg' (y : ℝ) : g y = 1 / 4 * y ^ 2 := by rw [hg, hf]; ring
  simp only [chartDerivativeSeminorm_Icc_of_forall_apply_eq_mul_sq hf' zero_le_one,
    chartDerivativeSeminorm_Icc_of_forall_apply_eq_mul_sq hg' zero_le_two]
  norm_num [Nat.descFactorial]

/-- Under `x = y / 2` the compact `C^k` seminorms do not increase, in every order `k`. -/
example {f g : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯} (hg : ∀ y, g y = f (1 / 2 * y)) (k : ℕ) (hk : k ≤ n) :
    chartCkSeminorm 0 (selfChartCompacts 0 ⟨Icc (-2) 2, isCompact_Icc⟩) k hk g ≤
      chartCkSeminorm 0 (selfChartCompacts 0 ⟨Icc (-1) 1, isCompact_Icc⟩) k hk f := by
  rw [← map_half_mul_Icc]
  exact chartCkSeminorm_selfChartCompacts_le_of_forall_apply_eq_apply_mul_of_norm_le_one hg
    (by norm_num) 0 0 _ k hk

/-- **Compact `C^k` seminorms of an exponential.** For `g x = exp (c * x)` on `ℝ` with `c ≥ 1`
and `r ≥ 0`, the compact `C^k` seminorm on `[-r, r]` is `c ^ k * exp (c * r)`, the supremum of
the top derivative `c ^ k * exp (c * x)`. -/
theorem chartCkSeminorm_Icc_of_forall_apply_eq_exp_mul {g : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯} {c r : ℝ}
    (hg : ∀ y, g y = Real.exp (c * y)) (hc : 1 ≤ c) (hr : 0 ≤ r) (x : ℝ) (k : ℕ)
    (hk : k ≤ n) :
    chartCkSeminorm x (selfChartCompacts x ⟨Icc (-r) r, isCompact_Icc⟩) k hk g =
      c ^ k * Real.exp (c * r) := by
  have hg' : (g : ℝ → ℝ) = fun y ↦ Real.exp (c * y) := funext hg
  have hnorm (m : ℕ) (y : ℝ) : ‖iteratedDeriv m g y‖ = c ^ m * Real.exp (c * y) := by
    rw [hg', iteratedDeriv_exp_const_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  refine le_antisymm ((chartCkSeminorm_selfChartCompacts_le_iff g x _ k hk
    (by positivity)).mpr fun m hm y hy ↦ ?_) ?_
  · rw [hnorm]
    have hc0 : 0 ≤ c := zero_le_one.trans hc
    exact mul_le_mul (pow_le_pow_right₀ hc hm)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy.2 hc0)) (by positivity) (by positivity)
  · have h := norm_iteratedDeriv_le_chartCkSeminorm g x ⟨Icc (-r) r, isCompact_Icc⟩ k hk le_rfl
      (z := r) ⟨by linarith, le_rfl⟩
    rwa [hnorm] at h

/-- **The expansion `x ↦ 2 * x` attains the constant `2 ^ k`.** The compact `C^k` seminorm of
`exp (2 x)` on `[-1, 1]` is `2 ^ k` times that of `exp` on `[-2, 2]`, the image of `[-1, 1]`. -/
theorem chartCkSeminorm_Icc_exp_two_mul_eq {f g : C^n⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯}
    (hf : ∀ y, f y = Real.exp y) (hg : ∀ y, g y = f (2 * y)) (x : ℝ) (k : ℕ) (hk : k ≤ n) :
    chartCkSeminorm x (selfChartCompacts x ⟨Icc (-1) 1, isCompact_Icc⟩) k hk g =
      2 ^ k * chartCkSeminorm x (selfChartCompacts x ⟨Icc (-2) 2, isCompact_Icc⟩) k hk f := by
  rw [chartCkSeminorm_Icc_of_forall_apply_eq_exp_mul (c := 2) (fun y ↦ by rw [hg, hf])
      one_le_two zero_le_one,
    chartCkSeminorm_Icc_of_forall_apply_eq_exp_mul (c := 1) (fun y ↦ by rw [hf, one_mul])
      le_rfl zero_le_two]
  norm_num

/-- **The constants of the change of coordinates `x ↦ 2 * x` depend on the order.** No constant
`C` bounds the compact `C^k` seminorm on `[-1, 1]` of every `g = f (2 ·)` by `C` times the compact
`C^k` seminorm of `f` on `[-2, 2]`, for all orders `k` at once. -/
theorem not_exists_forall_chartCkSeminorm_le_of_forall_apply_eq_apply_two_mul (x : ℝ) :
    ¬ ∃ C : ℝ, ∀ (k : ℕ) (f g : C^∞⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯), (∀ y, g y = f (2 * y)) →
      chartCkSeminorm x (selfChartCompacts x ⟨Icc (-1) 1, isCompact_Icc⟩) k
          (by exact_mod_cast le_top) g ≤
        C * chartCkSeminorm x (selfChartCompacts x ⟨Icc (-2) 2, isCompact_Icc⟩) k
          (by exact_mod_cast le_top) f := by
  rintro ⟨C, hC⟩
  let f : C^∞⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ := ⟨Real.exp, Real.contDiff_exp.contMDiff⟩
  let g : C^∞⟮𝓘(ℝ), ℝ; 𝓘(ℝ), ℝ⟯ :=
    ⟨fun y ↦ Real.exp (2 * y), (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contMDiff⟩
  -- The seminorms of `f` are positive, so `hC` forces `2 ^ k ≤ C` for every `k`.
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C one_lt_two
  have h := hC k f g fun _ ↦ rfl
  rw [chartCkSeminorm_Icc_exp_two_mul_eq (f := f) (g := g) (fun _ ↦ rfl) (fun _ ↦ rfl),
    chartCkSeminorm_Icc_of_forall_apply_eq_exp_mul (c := 1) (fun y ↦ by simp [f]) le_rfl
      zero_le_two] at h
  have hpos : 0 < (1 : ℝ) ^ k * Real.exp (1 * 2) := by positivity
  exact hk.not_ge (le_of_mul_le_mul_right h hpos)

end ContMDiffMap
