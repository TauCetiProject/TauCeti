/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Metric bounds and circular packing on `UnitAddCircle`

This file records elementary metric and geometric estimates on the unit additive circle
`UnitAddCircle = ℝ / ℤ`:

* `Real.norm_unitAddCircle_sub_le_abs_sub_round`: circle norm of `a - b` is at most the distance
  between centered rounded representatives `(a - round a) - (b - round b)`.
* `TauCeti.card_filter_floor_norm_unitAddCircle_div_le_two`: circular radial bin-packing bound
  showing that at most two points of a `δ`-separated finite family lie in each shell
  `m δ ≤ ‖(c - x j : UnitAddCircle)‖ < (m + 1) δ`.
* `TauCeti.card_le_one_of_half_lt_of_unitAddCircle_separated`: since every point of `UnitAddCircle`
  has norm at most `1 / 2`, a `δ`-separated finite family with `1 / 2 < δ` has at most one element.

## References

* E. Bombieri, *A note on the large sieve*, Acta Arithmetica **18** (1971), 401–404, p. 404
  (the radial intervals `I_m` and the at-most-two-points-per-interval claim; here taken half-open
  `[m δ, (m + 1) δ)` via `⌊· / δ⌋₊ = m` so that adjacent endpoints do not overlap).
-/

public section

namespace Real

/-- For any `a b : ℝ`, the norm of `((a - b : ℝ) : UnitAddCircle)` is at most the distance
between the centered fractional representatives `(a - round a) - (b - round b)`. -/
theorem norm_unitAddCircle_sub_le_abs_sub_round (a b : ℝ) :
    ‖((a - b : ℝ) : UnitAddCircle)‖ ≤ |(a - round a) - (b - round b)| := by
  have hcoe : ((a - b : ℝ) : UnitAddCircle) =
      (((a - round a) - (b - round b) : ℝ) : UnitAddCircle) := by
    have hsub : (a - round a) - (b - round b) = (a - b) + (round b - round a : ℤ) • (1 : ℝ) := by
      simp only [zsmul_eq_mul, mul_one, Int.cast_sub]; ring
    rw [hsub, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]
  rw [hcoe, UnitAddCircle.norm_eq]
  simpa using round_le ((a - round a) - (b - round b)) 0

end Real

namespace TauCeti

/-- Circular radial bin-packing bound: around any center `c : ℝ`, each radial bin
`⌊‖c - x j‖ / δ⌋₊ = m` of a `δ`-separated finite family in `UnitAddCircle` contains at most two
indices `j ∈ s` (at most one on each side of `c`). -/
theorem card_filter_floor_norm_unitAddCircle_div_le_two {ι : Type*}
    {s : Finset ι} {x : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖)
    (c : ℝ) (m : ℕ) :
    (s.filter fun j ↦ ⌊‖((c - x j : ℝ) : UnitAddCircle)‖ / δ⌋₊ = m).card ≤ 2 := by
  classical
  let B : Finset ι :=
    s.filter fun j ↦ ⌊‖((c - x j : ℝ) : UnitAddCircle)‖ / δ⌋₊ = m
  let u : ι → ℝ := fun j ↦ (c - x j) - round (c - x j)
  have hbin : ∀ j ∈ B, (m : ℝ) * δ ≤ |u j| ∧ |u j| < ((m : ℝ) + 1) * δ := by
    intro j hj
    have hm : ⌊‖((c - x j : ℝ) : UnitAddCircle)‖ / δ⌋₊ = m := (Finset.mem_filter.mp hj).2
    rw [← UnitAddCircle.norm_eq (x := c - x j)]
    exact ⟨(le_div_iff₀ hδ).mp (hm ▸ Nat.floor_le (by positivity)),
      (div_lt_iff₀ hδ).mp (hm ▸ Nat.lt_floor_add_one _)⟩
  -- Split the radial shell `B` (`m * δ ≤ |u j| < (m + 1) * δ`) into its nonnegative (`0 ≤ u j`)
  -- and negative (`u j < 0`) halves. Two distinct indices in the same half satisfy
  -- `|u j₂ - u j₁| = |(|u j₂| - |u j₁|)| < δ`, contradicting `δ`-separation via
  -- `Real.norm_unitAddCircle_sub_le_abs_sub_round`.
  have hside : ∀ (P : ℝ → Prop) [DecidablePred P],
      (∀ r₁ r₂, P r₁ → P r₂ → |r₂ - r₁| = |(|r₂| - |r₁|)|) →
      (B.filter fun j ↦ P (u j)).card ≤ 1 := by
    intro P _ hP
    refine Finset.card_le_one.mpr fun j₁ hj₁ j₂ hj₂ ↦ ?_
    by_contra hne
    rcases Finset.mem_filter.mp hj₁ with ⟨hj₁B, hP₁⟩
    rcases Finset.mem_filter.mp hj₂ with ⟨hj₂B, hP₂⟩
    have hb₁ := hbin j₁ hj₁B
    have hb₂ := hbin j₂ hj₂B
    have hlt : |u j₂ - u j₁| < δ := by
      rw [hP (u j₁) (u j₂) hP₁ hP₂, abs_lt]
      exact ⟨by linarith, by linarith⟩
    have hdiff := Real.norm_unitAddCircle_sub_le_abs_sub_round (c - x j₂) (c - x j₁)
    have hsub : (c - x j₂) - (c - x j₁) = x j₁ - x j₂ := by ring
    rw [hsub] at hdiff
    linarith [hsep j₁ (Finset.mem_filter.mp hj₁B).1 j₂ (Finset.mem_filter.mp hj₂B).1 hne]
  have hpos_card := hside (0 ≤ ·) fun r₁ r₂ h₁ h₂ ↦ by rw [abs_of_nonneg h₁, abs_of_nonneg h₂]
  have hneg_card := hside (¬ 0 ≤ ·) fun r₁ r₂ h₁ h₂ ↦ by
    rw [abs_of_neg (lt_of_not_ge h₁), abs_of_neg (lt_of_not_ge h₂), ← abs_neg (r₂ - r₁)]
    congr 1; ring
  have hpart := Finset.card_filter_add_card_filter_not (s := B) (fun j ↦ 0 ≤ u j)
  dsimp only [B] at hpart hpos_card hneg_card
  omega

/-- Because every point of `UnitAddCircle` has norm at most `1 / 2`, a `δ`-separated finite family
with `1 / 2 < δ` has cardinality at most `1`. -/
theorem card_le_one_of_half_lt_of_unitAddCircle_separated {ι : Type*} {s : Finset ι}
    {x : ι → ℝ} {δ : ℝ} (hδ : 1 / 2 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖) :
    s.card ≤ 1 := by
  refine Finset.card_le_one.mpr fun i hi j hj ↦ ?_
  by_contra hne
  have hle : ‖((x i - x j : ℝ) : UnitAddCircle)‖ ≤ 1 / 2 := by
    simpa using AddCircle.norm_le_half_period (p := (1 : ℝ)) one_ne_zero
      (x := ((x i - x j : ℝ) : UnitAddCircle))
  linarith [hsep i hi j hj hne]

end TauCeti
