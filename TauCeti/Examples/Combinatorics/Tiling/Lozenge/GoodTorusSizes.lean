/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.GoodTorusSizes
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Regression examples: good torus sizes

* `θ = π/2`: no even `n` is a good torus size (`j = n/2` gives distance `0`), and every odd `n`
  is one, since the nearest `πj/n` is at distance `π/(2n) > n^{-3/2}`. So the "`n` or `n + 2`" of
  Gorin's Lemma 4.7 (*Lectures on random lozenge tilings*, 2021) fails at `θ = π/2`, while
  "`n` or `n + 1`" holds.
* `θ = 2π/3`: `3` is not a good torus size (`j = 2`), and `4` is one, since
  `min_j |2π/3 - πj/4| = π/12 > 1/8`.
* `θ = 0.1`: neither `188` nor `189` is a good torus size, through `j = 6` in both cases. How large
  `n` must be in `TauCeti.eventually_mem_goodTorusSizes_or_add_one` depends on `θ`.
-/

public section

open Real

namespace TauCeti.Examples.GoodTorusSizes

/-- No even number is a good torus size for `θ = π/2`. -/
theorem two_mul_notMem_goodTorusSizes_pi_div_two (n : ℕ) :
    2 * n ∉ goodTorusSizes (π / 2) := by
  intro hm
  obtain ⟨h1, h⟩ := mem_goodTorusSizes.1 hm
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have := h n
  rw [show π / 2 - π * ((n : ℤ) : ℝ) / ((2 * n : ℕ) : ℝ) = 0 by push_cast; field_simp; ring,
    abs_zero] at this
  exact this.not_ge (by positivity)

/-- Every odd number is a good torus size for `θ = π/2`. -/
theorem mem_goodTorusSizes_pi_div_two_of_odd {n : ℕ} (hn : Odd n) :
    n ∈ goodTorusSizes (π / 2) := by
  have h1 : 1 ≤ n := hn.pos
  refine mem_goodTorusSizes.2 ⟨h1, fun j => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
  have hodd : (1 : ℝ) ≤ |(((n : ℤ) - 2 * j : ℤ) : ℝ)| := by
    have hne : (n : ℤ) - 2 * j ≠ 0 := by
      obtain ⟨m, rfl⟩ := hn
      omega
    exact_mod_cast Int.one_le_abs hne
  have hs : (1 : ℝ) ≤ √n := one_le_sqrt.2 (by exact_mod_cast h1)
  have heq : π / 2 - π * j / n = π * ((n : ℤ) - 2 * j : ℤ) / (2 * n) := by
    push_cast
    field_simp
  rw [heq, abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * n),
    inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hA : 1 ≤ |(((n : ℤ) - 2 * j : ℤ) : ℝ)| * √n := one_le_mul_of_one_le_of_one_le hodd hs
  nlinarith [pi_gt_three, mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ π * n)]

/-- `3` is not a good torus size for `θ = 2π/3`. -/
theorem three_notMem_goodTorusSizes_two_pi_div_three : 3 ∉ goodTorusSizes (2 * π / 3) := by
  intro hm
  obtain ⟨-, h⟩ := mem_goodTorusSizes.1 hm
  have := h 2
  rw [show 2 * π / 3 - π * ((2 : ℤ) : ℝ) / ((3 : ℕ) : ℝ) = 0 by push_cast; ring, abs_zero] at this
  exact this.not_ge (by positivity)

/-- `4` is a good torus size for `θ = 2π/3`. -/
theorem four_mem_goodTorusSizes_two_pi_div_three : 4 ∈ goodTorusSizes (2 * π / 3) := by
  refine mem_goodTorusSizes.2 ⟨by norm_num, fun j => ?_⟩
  have hne : (1 : ℝ) ≤ |((8 - 3 * j : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (by omega)
  have hs : √((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, sqrt_sq zero_le_two]
  have heq : 2 * π / 3 - π * j / ((4 : ℕ) : ℝ) = π * ((8 - 3 * j : ℤ) : ℝ) / 12 := by
    push_cast
    ring
  rw [hs, heq, abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 12),
    lt_div_iff₀ (by norm_num)]
  push_cast at hne ⊢
  nlinarith [pi_gt_three]

/-- `188` is not a good torus size for `θ = 0.1`. -/
theorem notMem_goodTorusSizes_one_eighty_eight : 188 ∉ goodTorusSizes 0.1 := by
  intro hm
  obtain ⟨-, h⟩ := mem_goodTorusSizes.1 hm
  have := h 6
  have hs : √((188 : ℕ) : ℝ) < 14 := by
    rw [sqrt_lt' (by norm_num)]
    norm_num
  have hpos : 0 ≤ π * ((6 : ℤ) : ℝ) / ((188 : ℕ) : ℝ) - 0.1 := by
    push_cast
    linarith [pi_gt_d2]
  rw [abs_sub_comm, abs_of_nonneg hpos, inv_lt_iff_one_lt_mul₀ (by positivity)] at this
  have hs0 : 0 ≤ √((188 : ℕ) : ℝ) := sqrt_nonneg _
  push_cast at this hs hs0
  nlinarith [pi_lt_d4]

/-- `189` is not a good torus size for `θ = 0.1`. -/
theorem notMem_goodTorusSizes_one_eighty_nine : 189 ∉ goodTorusSizes 0.1 := by
  intro hm
  obtain ⟨-, h⟩ := mem_goodTorusSizes.1 hm
  have := h 6
  have hs : √((189 : ℕ) : ℝ) < 14 := by
    rw [sqrt_lt' (by norm_num)]
    norm_num
  have hpos : 0 ≤ 0.1 - π * ((6 : ℤ) : ℝ) / ((189 : ℕ) : ℝ) := by
    push_cast
    linarith [pi_lt_d2]
  rw [abs_of_nonneg hpos, inv_lt_iff_one_lt_mul₀ (by positivity)] at this
  have hs0 : 0 ≤ √((189 : ℕ) : ℝ) := sqrt_nonneg _
  push_cast at this hs hs0
  nlinarith [pi_gt_d4]

end TauCeti.Examples.GoodTorusSizes
