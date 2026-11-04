/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Comparing an angle with an arccosine

Mathlib's `Analysis/SpecialFunctions/Trigonometric/Inverse.lean` carries a complete comparison
family for `Real.arcsin` — `Real.arcsin_le_iff_le_sin`, `Real.le_arcsin_iff_sin_le`,
`Real.arcsin_lt_iff_lt_sin`, `Real.lt_arcsin_iff_sin_lt` and their primed variants — turning an
inequality between an angle and an `arcsin` into one between a real number and a `sin`. This file
supplies the counterpart for `Real.arccos`, and reads it off as a description of the sublevel and
superlevel sets of `Real.cos` on one period. Since `arccos` is antitone, the comparisons swap
sides: they have the shape `arccos x ≤ y ↔ cos y ≤ x` where the `arcsin` family has
`arcsin x ≤ y ↔ x ≤ sin y`.

## Main results

* `Real.arccos_le_iff_cos_le` and `Real.lt_arccos_iff_lt_cos` — for `-1 ≤ x` and an angle
  `y ∈ [0, π]`, `arccos x ≤ y ↔ cos y ≤ x` and `y < arccos x ↔ x < cos y`. No upper bound on `x`
  is needed: for `1 ≤ x`, `arccos x = 0` and `cos y ≤ x`, so the two sides of each agree.
* `Real.le_arccos_iff_le_cos` and `Real.arccos_lt_iff_cos_lt` — for `x ≤ 1` and an angle
  `y ∈ [0, π]`, `y ≤ arccos x ↔ x ≤ cos y` and `arccos x < y ↔ cos y < x`. No lower bound on `x`
  is needed: for `x ≤ -1`, `arccos x = π` and `x ≤ cos y`, so the two sides of each agree.
* `Real.arccos_le_iff_cos_le'` and `Real.lt_arccos_iff_lt_cos'` — the same two comparisons with
  nothing assumed of `x`, for an angle `y ∈ [0, π)`.
* `Real.le_arccos_iff_le_cos'` and `Real.arccos_lt_iff_cos_lt'` — the same two comparisons with
  nothing assumed of `x`, for an angle `y ∈ (0, π]`. Exactly as for Mathlib's primed `arcsin`
  lemmas, the primed forms cover the remaining degenerate range of `x` at the price of excluding
  the one endpoint of `[0, π]` at which the comparison would then fail.
* `Real.lt_cos_iff_mem_Ioo` — since `cos` is even, the comparisons extend to the full period
  `[-π, π]`: for `-1 ≤ x` and `t ∈ [-π, π]`, `x < cos t ↔ t ∈ (-arccos x, arccos x)`.
* `Real.le_cos_iff_mem_Icc` — the closed companion: for `x ≤ 1` and `t ∈ [-π, π]`,
  `x ≤ cos t ↔ t ∈ [-arccos x, arccos x]`. On one period centred at `0`, the angles at which `cos`
  reaches a threshold thus form the symmetric interval of half-width `arccos x`.
* `Real.lt_cos_of_mem_Icc` — the unimodality corollary: `cos` has no interior minimum on
  `[-π, π]`. For `-π ≤ a`, `b ≤ π` and `θ ∈ [a, b]`, if `k < cos a` and `k < cos b` then
  `k < cos θ`; nothing is assumed of `k`.
-/

public section

namespace TauCeti

open Set

open scoped Real

/-- **An arccosine is at most an angle exactly when the angle's cosine is at most the value.** For
`-1 ≤ x` and an angle `y ∈ [0, π]`, `arccos x ≤ y ↔ cos y ≤ x`. No upper bound on `x` is needed:
for `1 ≤ x` both sides hold. The `Real.arccos` counterpart of Mathlib's
`Real.le_arcsin_iff_sin_le`, with the sides swapped because `Real.arccos` is antitone. -/
theorem _root_.Real.arccos_le_iff_cos_le {x y : ℝ} (hx : -1 ≤ x) (hy : y ∈ Icc 0 π) :
    Real.arccos x ≤ y ↔ Real.cos y ≤ x := by
  rcases le_total x 1 with hx₁ | hx₁
  · rw [← Real.strictAntiOn_cos.le_iff_ge hy ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩,
      Real.cos_arccos hx hx₁]
  · exact iff_of_true (Real.arccos_of_one_le hx₁ ▸ hy.1) ((Real.cos_le_one y).trans hx₁)

/-- **An arccosine is at most an angle exactly when the angle's cosine is at most the value**, with
nothing assumed of `x`. The `Real.arccos` counterpart of Mathlib's `Real.le_arcsin_iff_sin_le'`.

The angle `y` is excluded from `π`, and in exchange the bound `-1 ≤ x` is dropped: for `x < -1`
both sides then fail. At `y = π` the left side is automatic while the right side, `-1 ≤ x`, is not;
at the other endpoint `y = 0` the statement is `Real.arccos_eq_zero`. -/
theorem _root_.Real.arccos_le_iff_cos_le' {x y : ℝ} (hy : y ∈ Ico 0 π) :
    Real.arccos x ≤ y ↔ Real.cos y ≤ x := by
  rcases lt_or_ge x (-1) with hx | hx
  · exact iff_of_false (Real.arccos_of_le_neg_one hx.le ▸ hy.2.not_ge)
      (hx.trans_le (Real.neg_one_le_cos y)).not_ge
  · exact Real.arccos_le_iff_cos_le hx (mem_Icc_of_Ico hy)

/-- **An angle is at most an arccosine exactly when the value is at most the angle's cosine.** For
`x ≤ 1` and an angle `y ∈ [0, π]`, `y ≤ arccos x ↔ x ≤ cos y`. No lower bound on `x` is needed:
for `x ≤ -1` both sides hold. The `Real.arccos` counterpart of Mathlib's
`Real.arcsin_le_iff_le_sin`. -/
theorem _root_.Real.le_arccos_iff_le_cos {x y : ℝ} (hx : x ≤ 1) (hy : y ∈ Icc 0 π) :
    y ≤ Real.arccos x ↔ x ≤ Real.cos y := by
  rcases le_total (-1) x with hx₁ | hx₁
  · rw [← Real.strictAntiOn_cos.le_iff_ge ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩ hy,
      Real.cos_arccos hx₁ hx]
  · exact iff_of_true (Real.arccos_of_le_neg_one hx₁ ▸ hy.2) (hx₁.trans (Real.neg_one_le_cos y))

/-- **An angle is at most an arccosine exactly when the value is at most the angle's cosine**, with
nothing assumed of `x`. The `Real.arccos` counterpart of Mathlib's `Real.arcsin_le_iff_le_sin'`.

The angle `y` is excluded from `0`, and in exchange the bound `x ≤ 1` is dropped: for `1 < x` both
sides then fail. At `y = 0` the left side is automatic while the right side, `x ≤ 1`, is not; at
the other endpoint `y = π` the statement is `Real.arccos_eq_pi`. -/
theorem _root_.Real.le_arccos_iff_le_cos' {x y : ℝ} (hy : y ∈ Ioc 0 π) :
    y ≤ Real.arccos x ↔ x ≤ Real.cos y := by
  rcases le_or_gt x 1 with hx | hx
  · exact Real.le_arccos_iff_le_cos hx (mem_Icc_of_Ioc hy)
  · exact iff_of_false (Real.arccos_of_one_le hx.le ▸ hy.1.not_ge)
      ((Real.cos_le_one y).trans_lt hx).not_ge

/-- **An arccosine is below an angle exactly when the angle's cosine is below the value.** The
strict form of `Real.arccos_le_iff_cos_le`, for `x ≤ 1` and an angle `y ∈ [0, π]`; it is the
negation of `Real.le_arccos_iff_le_cos`. -/
theorem _root_.Real.arccos_lt_iff_cos_lt {x y : ℝ} (hx : x ≤ 1) (hy : y ∈ Icc 0 π) :
    Real.arccos x < y ↔ Real.cos y < x :=
  not_le.symm.trans <| (not_congr (Real.le_arccos_iff_le_cos hx hy)).trans not_le

/-- **An arccosine is below an angle exactly when the angle's cosine is below the value**, with
nothing assumed of `x`. The strict form of `Real.arccos_le_iff_cos_le'`; as in
`Real.le_arccos_iff_le_cos'`, whose negation it is, the angle `y` runs over `Ioc 0 π`. -/
theorem _root_.Real.arccos_lt_iff_cos_lt' {x y : ℝ} (hy : y ∈ Ioc 0 π) :
    Real.arccos x < y ↔ Real.cos y < x :=
  not_le.symm.trans <| (not_congr (Real.le_arccos_iff_le_cos' hy)).trans not_le

/-- **An angle is below an arccosine exactly when the value is below the angle's cosine.** The
strict form of `Real.le_arccos_iff_le_cos`, for `-1 ≤ x` and an angle `y ∈ [0, π]`; it is the
negation of `Real.arccos_le_iff_cos_le`. -/
theorem _root_.Real.lt_arccos_iff_lt_cos {x y : ℝ} (hx : -1 ≤ x) (hy : y ∈ Icc 0 π) :
    y < Real.arccos x ↔ x < Real.cos y :=
  not_le.symm.trans <| (not_congr (Real.arccos_le_iff_cos_le hx hy)).trans not_le

/-- **An angle is below an arccosine exactly when the value is below the angle's cosine**, with
nothing assumed of `x`. The strict form of `Real.le_arccos_iff_le_cos'`; as in
`Real.arccos_le_iff_cos_le'`, whose negation it is, the angle `y` runs over `Ico 0 π`. -/
theorem _root_.Real.lt_arccos_iff_lt_cos' {x y : ℝ} (hy : y ∈ Ico 0 π) :
    y < Real.arccos x ↔ x < Real.cos y :=
  not_le.symm.trans <| (not_congr (Real.arccos_le_iff_cos_le' hy)).trans not_le

/-- **The cosine exceeds a threshold on a symmetric interval.** For `-1 ≤ x`, the angles of the
period `[-π, π]` at which `Real.cos` exceeds `x` are exactly those of `(-arccos x, arccos x)`. -/
theorem _root_.Real.lt_cos_iff_mem_Ioo {x t : ℝ} (hx : -1 ≤ x) (ht : t ∈ Icc (-π) π) :
    x < Real.cos t ↔ t ∈ Ioo (-Real.arccos x) (Real.arccos x) := by
  rw [← Real.cos_abs, ← Real.lt_arccos_iff_lt_cos hx ⟨abs_nonneg t, abs_le.mpr ⟨ht.1, ht.2⟩⟩,
    abs_lt, mem_Ioo]

/-- **The cosine reaches a threshold on a symmetric closed interval.** For `x ≤ 1`, the angles of
the period `[-π, π]` at which `Real.cos` is at least `x` are exactly those of
`[-arccos x, arccos x]`. The weak companion of `Real.lt_cos_iff_mem_Ioo`. -/
theorem _root_.Real.le_cos_iff_mem_Icc {x t : ℝ} (hx : x ≤ 1) (ht : t ∈ Icc (-π) π) :
    x ≤ Real.cos t ↔ t ∈ Icc (-Real.arccos x) (Real.arccos x) := by
  rw [← Real.cos_abs, ← Real.le_arccos_iff_le_cos hx ⟨abs_nonneg t, abs_le.mpr ⟨ht.1, ht.2⟩⟩,
    abs_le, mem_Icc]

/-- **The cosine has no interior minimum on `[-π, π]`.** If `k < cos a` and `k < cos b`, with
`-π ≤ a` and `b ≤ π`, then `k < cos θ` for every `θ ∈ [a, b]`.

This is `Real.lt_cos_iff_mem_Ioo` read as unimodality: below `-1` the bound is vacuous, and above it
the angles admitted form an interval, which therefore contains `[a, b]` as soon as it contains both
endpoints. -/
theorem _root_.Real.lt_cos_of_mem_Icc {k a b θ : ℝ} (ha : -π ≤ a) (hb : b ≤ π) (hθ : θ ∈ Icc a b)
    (hka : k < Real.cos a) (hkb : k < Real.cos b) : k < Real.cos θ := by
  rcases lt_or_ge k (-1) with hk | hk
  · exact hk.trans_le (Real.neg_one_le_cos θ)
  have hab : a ≤ b := hθ.1.trans hθ.2
  rw [Real.lt_cos_iff_mem_Ioo hk ⟨ha, hab.trans hb⟩] at hka
  rw [Real.lt_cos_iff_mem_Ioo hk ⟨ha.trans hab, hb⟩] at hkb
  rw [Real.lt_cos_iff_mem_Ioo hk ⟨ha.trans hθ.1, hθ.2.trans hb⟩]
  exact ordConnected_Ioo.out hka hkb hθ

end TauCeti
