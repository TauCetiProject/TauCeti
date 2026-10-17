/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic grids of a closed real interval

The dyadic grid of level `n` of `[a, b]` consists of the points `a + k * ((b - a) / 2 ^ n)` for
`k ≤ 2 ^ n`. The grids are nested, and their points of all levels are dense in `[a, b]`.

## Main results

* `TauCeti.exists_eq_add_mul_div_two_pow_of_le`: a point of the dyadic grid of level `m` lies on
  the dyadic grids of all levels `n ≥ m`.
* `TauCeti.dense_setOfPred_eq_add_mul_div_two_pow`: the points of the dyadic grids of `[a, b]`,
  of all levels, are dense in `[a, b]`.
-/

public section

open Set

namespace TauCeti

/-- A point of the dyadic grid of level `m` of `[a, b]` lies on the dyadic grids of all levels
`n ≥ m`. -/
lemma exists_eq_add_mul_div_two_pow_of_le {K : Type*} [Field K] [CharZero K] {a b t : K}
    {m n k : ℕ} (hk : k ≤ 2 ^ m) (ht : t = a + k * ((b - a) / 2 ^ m)) (hmn : m ≤ n) :
    ∃ j : ℕ, j ≤ 2 ^ n ∧ t = a + j * ((b - a) / 2 ^ n) := by
  have h2 : 2 ^ n = 2 ^ m * 2 ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  refine ⟨k * 2 ^ (n - m), h2 ▸ Nat.mul_le_mul_right _ hk, ?_⟩
  have h2' : (2 : K) ^ n = 2 ^ m * 2 ^ (n - m) := by exact_mod_cast h2
  rw [ht, h2']
  push_cast
  field_simp

/-- The points of the dyadic grids of `[a, b]`, of all levels, are dense in `[a, b]`. -/
theorem dense_setOfPred_eq_add_mul_div_two_pow {a b : ℝ} (hab : a < b) :
    Dense {t : Icc a b | ∃ n k : ℕ, k ≤ 2 ^ n ∧ (t : ℝ) = a + k * ((b - a) / 2 ^ n)} := by
  refine Metric.dense_iff.2 fun t r hr ↦ ?_
  have hba : 0 < b - a := sub_pos.2 hab
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hr hba) (one_half_lt_one (α := ℝ))
  set h := (b - a) / 2 ^ n with h_def
  have hh : 0 < h := by positivity
  have hhr : h < r := calc
    h = (1 / 2) ^ n * (b - a) := by rw [h_def, one_div_pow]; ring
    _ < r := (lt_div_iff₀ hba).1 hn
  set k := ⌊((t : ℝ) - a) / h⌋₊
  have hta : 0 ≤ ((t : ℝ) - a) / h := div_nonneg (sub_nonneg.2 t.2.1) hh.le
  have hk₁ : (k : ℝ) * h ≤ t - a := (le_div_iff₀ hh).1 (Nat.floor_le hta)
  have hk₂ : (t : ℝ) - a < (k + 1) * h := (div_lt_iff₀ hh).1 (Nat.lt_floor_add_one _)
  have hkn : k ≤ 2 ^ n := by
    refine Nat.floor_le_of_le ?_
    push_cast
    rw [div_le_iff₀ hh, h_def, mul_div_cancel₀ _ (by positivity)]
    linarith [t.2.2]
  refine ⟨⟨a + k * h, by nlinarith [hh.le, (k.cast_nonneg : (0 : ℝ) ≤ k)], by linarith [t.2.2]⟩,
    ?_, n, k, hkn, rfl⟩
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
  constructor <;> simp only <;> nlinarith

end TauCeti
