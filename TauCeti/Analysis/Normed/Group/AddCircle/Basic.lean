/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Metric bounds and circular packing on `UnitAddCircle`

This file records elementary metric and geometric estimates on the unit additive circle
`UnitAddCircle = ℝ / ℤ`:

* `Real.two_mul_norm_unitAddCircle_le_abs_sin` and
  `Real.four_mul_norm_unitAddCircle_sq_le_sin_sq`: Jordan's sine lower bound
  `2 * ‖(t : UnitAddCircle)‖ ≤ |sin (π * t)|` and its squared form.
* `TauCeti.card_filter_floor_norm_unitAddCircle_div_le_two`: circular radial bin-packing bound
  showing that at most two points of a `δ`-separated finite family lie in each shell
  `m δ ≤ ‖(c - x j : UnitAddCircle)‖ < (m + 1) δ`.
* `TauCeti.card_le_one_of_half_lt_of_unitAddCircle_separated`: since every point of `UnitAddCircle`
  has norm at most `1 / 2`, a `δ`-separated finite family with `1 / 2 < δ` has at most one element.
-/

public section

namespace Real

/-- Jordan's sine lower bound on `UnitAddCircle = ℝ / ℤ`:
`2 * ‖(t : UnitAddCircle)‖ ≤ |sin (π * t)|`. -/
theorem two_mul_norm_unitAddCircle_le_abs_sin (t : ℝ) :
    2 * ‖(t : UnitAddCircle)‖ ≤ |Real.sin (Real.pi * t)| := by
  set u : ℝ := t - round t
  have hu : ‖(t : UnitAddCircle)‖ = |u| := UnitAddCircle.norm_eq
  have hle : |u| ≤ 1 / 2 := abs_sub_round t
  have hsin_le : 2 * |u| ≤ Real.sin (Real.pi / 2 * (2 * |u|)) :=
    Real.le_sin_mul (by positivity) (by linarith)
  have harg : Real.pi / 2 * (2 * |u|) = Real.pi * |u| := by ring
  have habs_u : |Real.sin (Real.pi * |u|)| = |Real.sin (Real.pi * u)| := by
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.sin_neg, abs_neg]
  have habs_t : |Real.sin (Real.pi * u)| = |Real.sin (Real.pi * t)| := by
    have hsub : Real.pi * u = Real.pi * t - (round t : ℤ) * Real.pi := by
      simp only [u]; ring
    rw [hsub, Real.sin_sub_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  calc
    2 * ‖(t : UnitAddCircle)‖ = 2 * |u| := by rw [hu]
    _ ≤ Real.sin (Real.pi * |u|) := harg ▸ hsin_le
    _ ≤ |Real.sin (Real.pi * |u|)| := le_abs_self _
    _ = |Real.sin (Real.pi * t)| := habs_u.trans habs_t

/-- Squared form of Jordan's sine lower bound on `UnitAddCircle`:
`4 * ‖(t : UnitAddCircle)‖ ^ 2 ≤ sin (π * t) ^ 2`. -/
theorem four_mul_norm_unitAddCircle_sq_le_sin_sq (t : ℝ) :
    4 * ‖(t : UnitAddCircle)‖ ^ 2 ≤ Real.sin (Real.pi * t) ^ 2 := by
  nlinarith [t.two_mul_norm_unitAddCircle_le_abs_sin, sq_abs (Real.sin (Real.pi * t)),
    norm_nonneg (t : UnitAddCircle)]

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
  have hdiff_le : ∀ j₁ j₂, ‖((x j₁ - x j₂ : ℝ) : UnitAddCircle)‖ ≤ |u j₂ - u j₁| := by
    intro j₁ j₂
    have hcoe : ((x j₁ - x j₂ : ℝ) : UnitAddCircle) = ((u j₂ - u j₁ : ℝ) : UnitAddCircle) := by
      let k : ℤ := round (c - x j₁) - round (c - x j₂)
      have hsub : u j₂ - u j₁ = (x j₁ - x j₂) + k • (1 : ℝ) := by
        simp only [u, k, zsmul_eq_mul, mul_one, Int.cast_sub]; ring
      rw [hsub, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]
    rw [hcoe, UnitAddCircle.norm_eq]
    simpa using round_le (u j₂ - u j₁) 0
  have hbin : ∀ j ∈ B, (m : ℝ) * δ ≤ |u j| ∧ |u j| < ((m : ℝ) + 1) * δ := by
    intro j hj
    have hm : ⌊‖((c - x j : ℝ) : UnitAddCircle)‖ / δ⌋₊ = m := (Finset.mem_filter.mp hj).2
    rw [← UnitAddCircle.norm_eq (x := c - x j)]
    exact ⟨(le_div_iff₀ hδ).mp (hm ▸ Nat.floor_le (by positivity)),
      (div_lt_iff₀ hδ).mp (hm ▸ Nat.lt_floor_add_one _)⟩
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
    linarith [hsep j₁ (Finset.mem_filter.mp hj₁B).1 j₂ (Finset.mem_filter.mp hj₂B).1 hne,
      hdiff_le j₁ j₂]
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
