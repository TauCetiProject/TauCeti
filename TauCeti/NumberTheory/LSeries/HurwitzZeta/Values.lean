/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.ZMod
import TauCeti.Analysis.SpecialFunctions.Complex.Log.UnitCircle
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Basic

/-!
# Values of Hurwitz zeta functions at `s = 0`, and periodic L-functions at nonpositive integers

Mathlib's `HurwitzZeta.hurwitzZeta_neg_nat` evaluates `ζ(-k, x)` for `k ≥ 1` and `x ∈ [0, 1]` as
`-Bₖ₊₁(x) / (k + 1)`. This file supplies the missing value at `s = 0`:
`ζ(0, x) = 1 / 2 - x` for `x ∈ (0, 1]`. Together they give `ζ(-k, x) = -Bₖ₊₁(x) / (k + 1)` for
every `k ≥ 0`, with representatives `x ∈ (0, 1]`. The endpoint `x = 0` must be excluded when
`k = 0`: Mathlib's `hurwitzZeta` is a function on the circle, so `ζ(0, 0) = ζ(0, 1) = -1 / 2`,
while `-B₁(0) = 1 / 2`.

The even part of `ζ(0, x)` is known in Mathlib (`HurwitzZeta.hurwitzZetaEven_apply_zero`). The
odd part is `sinZeta x 1 / π` by the functional equation, and
`sinZeta x 1 = ∑ sin (2π n x) / n = π (1 / 2 - x)` is the conditionally convergent sawtooth
series `Real.tendsto_sum_Icc_sin_mul_div`. The ordered limit is identified with the continued
value by `TauCeti.LSeries.eq_of_tendsto_sum_Icc_div`.

Summing over residue classes, the L-function of any `ZMod N`-periodic function `Φ` at `-k` is
`-Nᵏ / (k + 1) ∑ⱼ Φ(j) Bₖ₊₁(r(j) / N)` for every `k ≥ 0`, where the representative `r(j)` of `j`
is taken in `{1, …, N}`, so that `r(0) = N`.

## Main results

* `HurwitzZeta.sinZeta_one_of_mem_Ioo`: `sinZeta x 1 = π (1 / 2 - x)` for `x ∈ (0, 1)`.
* `HurwitzZeta.hurwitzZetaOdd_apply_zero_of_mem_Ioo`: `hurwitzZetaOdd x 0 = 1 / 2 - x` for
  `x ∈ (0, 1)`.
* `HurwitzZeta.hurwitzZeta_apply_zero_of_mem_Ioc`: `hurwitzZeta x 0 = 1 / 2 - x` for
  `x ∈ (0, 1]`.
* `HurwitzZeta.hurwitzZeta_neg_nat_of_mem_Ioc`: `ζ(-k, x) = -Bₖ₊₁(x) / (k + 1)` for every
  natural `k` and `x ∈ (0, 1]`.
* `ZMod.LFunction_neg_nat`: `L(Φ, -k) = -Nᵏ / (k + 1) ∑ⱼ Φ(j) Bₖ₊₁(r(j) / N)` for every
  `Φ : ZMod N → ℂ` and natural `k`, with representatives `r(j) ∈ {1, …, N}`.
-/

public section

open Complex Filter Set
open scoped Real Topology

namespace HurwitzZeta

/-- **The sine zeta function at `s = 1`.** For `x ∈ (0, 1)`, the continued value of
`∑ sin (2π n x) / n` is `π (1 / 2 - x)`. -/
theorem sinZeta_one_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    sinZeta x 1 = π * (1 / 2 - x) := by
  have hθ : 2 * π * x ∈ Ioo 0 (2 * π) :=
    ⟨by have := hx.1; positivity, by nlinarith [hx.2, Real.pi_pos]⟩
  have hlim : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Icc 1 N, (Real.sin (2 * π * x * n) : ℂ) / n)
      atTop (𝓝 (((π - 2 * π * x) / 2 : ℝ) : ℂ)) := by
    refine ((continuous_ofReal.tendsto _).comp (Real.tendsto_sum_Icc_sin_mul_div hθ)).congr
      fun N ↦ ?_
    simp only [Function.comp_apply, ofReal_sum, ofReal_div, ofReal_natCast]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [mul_comm (n : ℝ)]
  have hF : Tendsto (fun σ : ℝ ↦ sinZeta x σ) (𝓝[>] 1) (𝓝 (sinZeta x 1)) := by
    have h := ((differentiableAt_sinZeta x).continuous.tendsto 1).comp
      (continuous_ofReal.tendsto 1)
    exact h.mono_left nhdsWithin_le_nhds
  rw [TauCeti.LSeries.eq_of_tendsto_sum_Icc_div hlim hF fun σ hσ ↦
    LSeriesHasSum_sin x (by simpa using hσ)]
  push_cast
  ring

/-- **The odd Hurwitz zeta function at `s = 0`.** For `x ∈ (0, 1)`,
`hurwitzZetaOdd x 0 = 1 / 2 - x`. -/
theorem hurwitzZetaOdd_apply_zero_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    hurwitzZetaOdd x 0 = 1 / 2 - x := by
  have h := hurwitzZetaOdd_one_sub x (s := 1) fun n ↦ by
    rw [Ne, ← ofReal_one, ← ofReal_natCast, ← ofReal_neg, ofReal_inj]
    linarith [n.cast_nonneg (α := ℝ)]
  rw [sub_self, sinZeta_one_of_mem_Ioo hx, cpow_neg_one, Gamma_one, mul_one, mul_one,
    sin_pi_div_two] at h
  rw [h]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- **The Hurwitz zeta function at `s = 0`.** For `x ∈ (0, 1]`, `hurwitzZeta x 0 = 1 / 2 - x`.
At `x = 1` this is `ζ(0) = -1 / 2`. The interval is the right one: Mathlib's `hurwitzZeta` is a
function on the circle, so its value at `x = 0` is also `-1 / 2`. -/
theorem hurwitzZeta_apply_zero_of_mem_Ioc {x : ℝ} (hx : x ∈ Ioc 0 1) :
    hurwitzZeta x 0 = 1 / 2 - x := by
  rcases hx.2.lt_or_eq with hx1 | rfl
  · have hne : (x : UnitAddCircle) ≠ 0 := by
      rw [Ne, AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hx.1.le, hx1⟩]
      exact hx.1.ne'
    simp only [hurwitzZeta, hurwitzZetaEven_apply_zero, hne, ↓reduceIte, zero_add,
      hurwitzZetaOdd_apply_zero_of_mem_Ioo ⟨hx.1, hx1⟩]
  · rw [show ((1 : ℝ) : UnitAddCircle) = 0 from AddCircle.coe_period (1 : ℝ), hurwitzZeta_zero,
      riemannZeta_zero]
    push_cast
    ring

/-- **Hurwitz zeta values at the nonpositive integers.** For every natural `k` and
`x ∈ (0, 1]`, `ζ(-k, x) = -Bₖ₊₁(x) / (k + 1)`. Mathlib's `hurwitzZeta_neg_nat` gives this for
`k ≠ 0` and `x ∈ [0, 1]`; the case `k = 0` is `hurwitzZeta_apply_zero_of_mem_Ioc`, where `x = 0`
must be excluded. -/
theorem hurwitzZeta_neg_nat_of_mem_Ioc (k : ℕ) {x : ℝ} (hx : x ∈ Ioc 0 1) :
    hurwitzZeta x (-k) =
      -1 / (k + 1) * ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Nat.cast_zero, neg_zero, hurwitzZeta_apply_zero_of_mem_Ioc hx, zero_add,
      Polynomial.bernoulli_one]
    simp
  · exact hurwitzZeta_neg_nat hk (Ioc_subset_Icc_self hx)

end HurwitzZeta

namespace ZMod

/-- **Periodic L-functions at the nonpositive integers.** For `Φ : ZMod N → ℂ` and every natural
`k`, `L(Φ, -k) = -Nᵏ / (k + 1) ∑ⱼ Φ(j) Bₖ₊₁(r(j) / N)`, where `r(j) ∈ {1, …, N}` represents `j`.
The representative `N` of the zero class is forced at `k = 0`, by
`HurwitzZeta.hurwitzZeta_apply_zero_of_mem_Ioc`. -/
theorem LFunction_neg_nat {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (k : ℕ) :
    LFunction Φ (-k) = -(N : ℂ) ^ k / (k + 1) * ∑ j : ZMod N, Φ j *
      ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval
        (((if j = 0 then N else j.val : ℕ) : ℂ) / N) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [LFunction, neg_neg, cpow_natCast, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  -- `j` is the class of its representative `r(j) ∈ {1, …, N}`, and `r(j) / N ∈ (0, 1]`
  set r : ℕ := if j = 0 then N else j.val with hr
  have hrj : (r : ZMod N) = j := by
    rcases eq_or_ne j 0 with rfl | hj
    · simp [hr]
    · simp [hr, hj]
  have hmem : (r / N : ℝ) ∈ Ioc 0 1 := by
    refine ⟨div_pos ?_ hN, (div_le_one hN).mpr ?_⟩ <;> rcases eq_or_ne j 0 with rfl | hj
    · simpa [hr] using hN
    · simp only [hr, hj, ↓reduceIte]; exact_mod_cast ZMod.val_pos.mpr hj
    · simp [hr]
    · simp only [hr, hj, ↓reduceIte]; exact_mod_cast (ZMod.val_lt j).le
  rw [← hrj, toAddCircle_natCast, HurwitzZeta.hurwitzZeta_neg_nat_of_mem_Ioc k hmem, hrj]
  push_cast
  ring

end ZMod
