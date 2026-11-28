/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Nat

/-!
# Von Mangoldt sums of ramps beyond a cutoff

A cap of at least `w` makes the ramp `max (a / n - cap n) 0` vanish beyond `X` when
`a ≤ w * X`. If `a` is increased by a relative amount at most `θ`, the new terms are
supported on an interval of length at most `X * θ` and each ramp has height at most
`w * θ`. The resulting bound keeps both the quadratic cost and the integer rounding term.
-/

public section

open ArithmeticFunction Finset
open scoped BigOperators

namespace TauCeti

/-- A von Mangoldt sum of capped ramps beyond `X`, where `a` exceeds `w * X` by at most
a relative amount `θ`. The caps may vary with the summation index. -/
theorem sum_vonMangoldt_mul_ramp_tail_le (s : Finset ℕ) (cap : ℕ → ℝ) {X w a θ : ℝ}
    (hw : 0 ≤ w) (hθ : 0 ≤ θ) (ha : a ≤ w * (X * (1 + θ)))
    (hs : ∀ n ∈ s, X < (n : ℝ)) (hc : ∀ n ∈ s, w ≤ cap n) :
    ∑ n ∈ s, Λ n * max (a / (n : ℝ) - cap n) 0 ≤
      Real.log (max 1 (X * (1 + θ))) * (w * X * θ ^ 2 + w * θ) := by
  by_cases hX : 0 < X
  · let U := X * (1 + θ)
    have hXU : X ≤ U := by dsimp [U]; nlinarith
    have hU : 0 ≤ U := hX.le.trans hXU
    let I := Ioc ⌊X⌋₊ ⌊U⌋₊
    have hheight (n : ℕ) (hn : n ∈ s) : max (a / (n : ℝ) - cap n) 0 ≤ w * θ := by
      refine max_le (sub_le_iff_le_add.mpr ?_) (mul_nonneg hw hθ)
      have hdiv : a / (n : ℝ) ≤ w * (1 + θ) := by
        refine (div_le_iff₀ (hX.trans (hs n hn))).2 (ha.trans ?_)
        calc
          w * (X * (1 + θ)) = (w * (1 + θ)) * X := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hs n hn).le (by positivity)
      linarith [hc n hn]
    have hz (n : ℕ) (hn : n ∈ s) (hnI : n ∉ I) :
        Λ n * max (a / (n : ℝ) - cap n) 0 = 0 := by
      have hlow := (Nat.floor_lt hX.le).mpr (hs n hn)
      have hnU : U ≤ (n : ℝ) := (Nat.floor_lt hU |>.mp (by
        simpa only [I, mem_Ioc, hlow, true_and, not_le] using hnI)).le
      have hdiv := (div_le_iff₀ (hX.trans (hs n hn))).2
        (ha.trans (mul_le_mul_of_nonneg_left hnU hw))
      rw [max_eq_right (sub_nonpos.mpr (hdiv.trans (hc n hn))), mul_zero]
    have hcard : (#I : ℝ) ≤ X * θ + 1 := by
      rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono hXU)]
      linarith [Nat.floor_le hU, Nat.lt_floor_add_one X]
    calc
      _ = ∑ n ∈ s ∩ I, Λ n * max (a / (n : ℝ) - cap n) 0 := by
        symm
        exact sum_subset inter_subset_left fun n hn hout ↦
          hz n hn fun hi ↦ hout (mem_inter.mpr ⟨hn, hi⟩)
      _ ≤ ∑ _n ∈ s ∩ I, Real.log (max 1 U) * (w * θ) := by
        refine sum_le_sum fun n hn ↦ mul_le_mul ?_ (hheight n (mem_inter.mp hn).1)
          (by positivity) (Real.log_nonneg (le_max_left ..))
        have hnI := mem_Ioc.mp (mem_inter.mp hn).2
        exact vonMangoldt_le_log.trans (Real.log_le_log (hX.trans (hs n (mem_inter.mp hn).1))
          ((Nat.le_floor_iff hU |>.mp hnI.2).trans (le_max_right ..)))
      _ ≤ (X * θ + 1) * (Real.log (max 1 U) * (w * θ)) := by
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right
          ((Nat.cast_le.mpr (card_le_card inter_subset_right)).trans hcard)
          (mul_nonneg (Real.log_nonneg (le_max_left ..)) (mul_nonneg hw hθ))
      _ = _ := by dsimp [U]; ring
  · have hU : X * (1 + θ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hX) (by positivity)
    have ha₀ : a ≤ 0 := ha.trans (mul_nonpos_of_nonneg_of_nonpos hw hU)
    rw [max_eq_left (hU.trans zero_le_one), Real.log_one, zero_mul]
    refine (sum_eq_zero fun n hn ↦ ?_).le
    have hdiv : a / (n : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha₀ (Nat.cast_nonneg n)
    rw [max_eq_right (sub_nonpos.mpr (hdiv.trans (hw.trans (hc n hn)))), mul_zero]

end TauCeti
