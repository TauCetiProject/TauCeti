/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Affine envelopes of the ReLU function on an interval

Linear relaxation methods for the certification of neural networks replace the ReLU function
`z ↦ max 0 z` on an interval `[l, u]` of pre-activation values by an affine upper bound and an
affine lower bound. This file proves the scalar facts behind these relaxations. The facts about
the upper chord and the relaxation hold over any linearly ordered field, and the facts about the
lower lines hold over any linearly ordered (semi)ring.

For `l < 0 < u` the *upper chord* `z ↦ u / (u - l) * (z - l)` is the line through `(l, 0)` and
`(u, u)`. It lies above ReLU on `[l, u]`, it meets ReLU exactly at the two endpoints, and it lies
below every other affine upper bound of ReLU on `[l, u]`. The *lower lines* `z ↦ α * z` with
`α ∈ [0, 1]` lie below ReLU everywhere, and they are the only lines through the origin that lie
below ReLU on `[l, u]`.

`TauCeti.crownRelax a l u α` is the slope and the intercept of the affine function that the CROWN
method uses in place of ReLU for one neuron with output coefficient `a` and pre-activation bounds
`l ≤ z ≤ u`: the identity when `0 ≤ l`, zero when `l < 0` and `u ≤ 0`, the lower line of slope
`α` when `l < 0 < u` and `0 ≤ a`, and the upper chord when `l < 0 < u` and `a < 0`. For
`α ∈ [0, 1]`, `a` times this affine function is at most `a` times ReLU on `[l, u]`.

## Main declarations

* `TauCeti.max_zero_le_chord`: the upper chord lies above ReLU on `[l, u]`.
* `TauCeti.chord_eq_max_zero_iff`: for `l < 0 < u`, the upper chord meets ReLU exactly at `l`
  and at `u`.
* `TauCeti.chord_le_of_forall_max_zero_le`: the upper chord lies below every affine upper bound
  of ReLU on `[l, u]`.
* `TauCeti.mul_le_max_zero`: `α * z ≤ max 0 z` for `α ∈ [0, 1]`.
* `TauCeti.forall_mul_le_max_zero_iff`: for `l < 0 < u`, the line `z ↦ α * z` lies below ReLU on
  `[l, u]` if and only if `α ∈ [0, 1]`.
* `TauCeti.crownRelax`: the CROWN relaxation of one neuron, with the four case lemmas
  `TauCeti.crownRelax_of_nonneg`, `TauCeti.crownRelax_of_neg_of_nonpos`,
  `TauCeti.crownRelax_of_neg_of_pos_of_nonneg` and `TauCeti.crownRelax_of_neg_of_pos_of_neg`.
* `TauCeti.mul_crownRelax_le`: the soundness of the relaxation of one neuron.

## References

* E. Wong and J. Z. Kolter, *Provable defenses against adversarial examples via the convex outer
  adversarial polytope*, ICML 2018, arXiv:1711.00851, eq. (3).
* H. Zhang, T.-W. Weng, P.-Y. Chen, C.-J. Hsieh and L. Daniel, *Efficient neural network
  robustness certification with general activation functions*, NeurIPS 2018, arXiv:1811.00866,
  Section 3.2 and Table 3.
-/

public section

open Set

namespace TauCeti

section LowerLine

variable {R : Type*} [LinearOrder R] {l u α : R}

/-! ### The lower lines -/

/-- The line `z ↦ α * z` lies below ReLU for every slope `α ∈ [0, 1]`. -/
theorem mul_le_max_zero [Semiring R] [IsOrderedRing R] (hα : α ∈ Icc 0 1) (z : R) :
    α * z ≤ max 0 z := by
  rcases le_total 0 z with hz | hz
  · exact (mul_le_of_le_one_left hz hα.2).trans (le_max_right 0 z)
  · exact (mul_nonpos_of_nonneg_of_nonpos hα.1 hz).trans (le_max_left 0 z)

/-- For `l < 0 < u`, the line `z ↦ α * z` lies below ReLU on `[l, u]` if and only if
`α ∈ [0, 1]`. -/
theorem forall_mul_le_max_zero_iff [Ring R] [IsStrictOrderedRing R] (hl : l < 0) (hu : 0 < u) :
    (∀ z ∈ Icc l u, α * z ≤ max 0 z) ↔ α ∈ Icc 0 1 := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun hα z _ => mul_le_max_zero hα z⟩
  · have h' := h l ⟨le_rfl, (hl.trans hu).le⟩
    rw [max_eq_left hl.le] at h'
    exact not_lt.1 fun hα => (mul_pos_of_neg_of_neg hα hl).not_ge h'
  · have h' := h u ⟨(hl.trans hu).le, le_rfl⟩
    rw [max_eq_right hu.le] at h'
    exact not_lt.1 fun hα => (lt_mul_of_one_lt_left hu hα).not_ge h'

end LowerLine

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] {a l u α z c d : 𝕜}

section IsStrictOrderedRing

variable [IsStrictOrderedRing 𝕜]

/-! ### The upper chord -/

/-- The upper chord `z ↦ u / (u - l) * (z - l)` lies above ReLU on `[l, u]` when `l ≤ 0 ≤ u`. -/
theorem max_zero_le_chord (hl : l ≤ 0) (hu : 0 ≤ u) (hz : z ∈ Icc l u) :
    max 0 z ≤ u / (u - l) * (z - l) := by
  obtain ⟨hlz, hzu⟩ := hz
  refine max_le (mul_nonneg (div_nonneg hu (sub_nonneg.2 (hlz.trans hzu))) (sub_nonneg.2 hlz)) ?_
  rcases (sub_nonneg.2 (hlz.trans hzu)).eq_or_lt with h | h
  · rw [← h, div_zero, zero_mul]
    linarith [sub_eq_zero.1 h.symm]
  · rw [div_mul_eq_mul_div, le_div_iff₀ h]
    nlinarith [mul_nonneg (neg_nonneg.2 hl) (sub_nonneg.2 hzu)]

omit [IsStrictOrderedRing 𝕜] in
/-- For `l < 0 < u`, the upper chord `z ↦ u / (u - l) * (z - l)` meets ReLU exactly at the
endpoints `l` and `u`. -/
theorem chord_eq_max_zero_iff (hl : l < 0) (hu : 0 < u) :
    u / (u - l) * (z - l) = max 0 z ↔ z = l ∨ z = u := by
  rw [div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.2 (hl.trans hu).ne')]
  constructor
  · intro h
    rcases le_total z 0 with hz | hz
    · rw [max_eq_left hz, zero_mul] at h
      exact .inl (sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hu.ne'))
    · rw [max_eq_right hz] at h
      have h' : (u - z) * l = 0 := by linear_combination -h
      exact .inr (sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right hl.ne)).symm
  · rintro (rfl | rfl)
    · rw [max_eq_left hl.le]
      ring
    · rw [max_eq_right hu.le]

/-- The upper chord `z ↦ u / (u - l) * (z - l)` lies below every affine function `z ↦ c * z + d`
that lies above ReLU on `[l, u]`. -/
theorem chord_le_of_forall_max_zero_le (h : ∀ y ∈ Icc l u, max 0 y ≤ c * y + d)
    (hz : z ∈ Icc l u) : u / (u - l) * (z - l) ≤ c * z + d := by
  obtain ⟨hlz, hzu⟩ := hz
  have hcl := (le_max_left 0 l).trans (h l ⟨le_rfl, hlz.trans hzu⟩)
  have hcu := (le_max_right 0 u).trans (h u ⟨hlz.trans hzu, le_rfl⟩)
  rcases (sub_nonneg.2 (hlz.trans hzu)).eq_or_lt with h0 | h0
  · rw [← h0, div_zero, zero_mul]
    exact (le_max_left 0 z).trans (h z ⟨hlz, hzu⟩)
  · rw [div_mul_eq_mul_div, div_le_iff₀ h0]
    nlinarith [mul_nonneg (sub_nonneg.2 hzu) hcl, mul_nonneg (sub_nonneg.2 hlz) (sub_nonneg.2 hcu)]

end IsStrictOrderedRing

/-! ### The relaxation of one neuron -/

/-- The slope and the intercept of the CROWN relaxation of ReLU for one neuron with output
coefficient `a`, pre-activation bounds `l ≤ z ≤ u` and lower slope `α`. It is the identity
`(1, 0)` when `0 ≤ l`, zero when `l < 0` and `u ≤ 0`, the lower line `(α, 0)` when `l < 0 < u`
and `0 ≤ a`, and the upper chord through `(l, 0)` and `(u, u)` when `l < 0 < u` and `a < 0`. -/
def crownRelax (a l u α : 𝕜) : 𝕜 × 𝕜 :=
  if 0 ≤ l then (1, 0)
  else if u ≤ 0 then (0, 0)
  else if 0 ≤ a then (α, 0)
  else (u / (u - l), -(u / (u - l)) * l)

/-- The CROWN relaxation of a neuron with `0 ≤ l` is the identity. -/
theorem crownRelax_of_nonneg (hl : 0 ≤ l) : crownRelax a l u α = (1, 0) := by
  simp [crownRelax, hl]

/-- The CROWN relaxation of a neuron with `l < 0` and `u ≤ 0` is zero. -/
theorem crownRelax_of_neg_of_nonpos (hl : l < 0) (hu : u ≤ 0) : crownRelax a l u α = (0, 0) := by
  simp [crownRelax, hl.not_ge, hu]

/-- The CROWN relaxation of a neuron with `l < 0 < u` and `0 ≤ a` is the lower line of
slope `α`. -/
theorem crownRelax_of_neg_of_pos_of_nonneg (hl : l < 0) (hu : 0 < u) (ha : 0 ≤ a) :
    crownRelax a l u α = (α, 0) := by
  simp [crownRelax, hl.not_ge, hu.not_ge, ha]

/-- The CROWN relaxation of a neuron with `l < 0 < u` and `a < 0` is the upper chord. -/
theorem crownRelax_of_neg_of_pos_of_neg (hl : l < 0) (hu : 0 < u) (ha : a < 0) :
    crownRelax a l u α = (u / (u - l), -(u / (u - l)) * l) := by
  simp [crownRelax, hl.not_ge, hu.not_ge, ha.not_ge]

/-- The soundness of the CROWN relaxation of one neuron: on `[l, u]`, the output coefficient `a`
times the relaxation `crownRelax a l u α` is at most `a` times ReLU, for every slope
`α ∈ [0, 1]`. -/
theorem mul_crownRelax_le [IsStrictOrderedRing 𝕜] (hα : α ∈ Icc 0 1) (hz : z ∈ Icc l u) :
    a * ((crownRelax a l u α).1 * z + (crownRelax a l u α).2) ≤ a * max 0 z := by
  rcases le_or_gt 0 l with hl | hl
  · rw [crownRelax_of_nonneg hl, max_eq_right (hl.trans hz.1), one_mul, add_zero]
  rcases le_or_gt u 0 with hu | hu
  · rw [crownRelax_of_neg_of_nonpos hl hu, max_eq_left (hz.2.trans hu), zero_mul, add_zero]
  rcases le_or_gt 0 a with ha | ha
  · rw [crownRelax_of_neg_of_pos_of_nonneg hl hu ha, add_zero]
    exact mul_le_mul_of_nonneg_left (mul_le_max_zero hα z) ha
  · rw [crownRelax_of_neg_of_pos_of_neg hl hu ha, neg_mul, ← sub_eq_add_neg, ← mul_sub]
    exact mul_le_mul_of_nonpos_left (max_zero_le_chord hl.le hu.le hz) ha.le

/-! ### Examples -/

/-- For `l = -1` and `u = 1` the upper chord is `(z + 1) / 2`. -/
example (z : ℝ) : 1 / (1 - -1) * (z - -1) = (z + 1) / 2 := by ring

/-- The chord for `l = -1` and `u = 1` meets ReLU at `±1` and takes the value `1 / 2` at `0`. -/
example : (1 : ℝ) / (1 - -1) * (-1 - -1) = max 0 (-1) ∧ (1 : ℝ) / (1 - -1) * (1 - -1) = max 0 1 ∧
    (1 : ℝ) / (1 - -1) * (0 - -1) = 1 / 2 := by
  norm_num

/-- The slope `α = 1` gives the lower line `z ≤ max 0 z`. -/
example (z : ℝ) : 1 * z ≤ max 0 z := mul_le_max_zero ⟨zero_le_one, le_rfl⟩ z

/-- The slope `α = 2` gives no lower line of ReLU: it fails at `z = 1`. -/
example : ¬ (2 : ℝ) * 1 ≤ max 0 1 := by norm_num

/-- The relaxation at `l = u = 0` is the identity. -/
example (a α : ℝ) : crownRelax a 0 0 α = (1, 0) := crownRelax_of_nonneg le_rfl

/-- The relaxation of a neuron with `a = -1`, `l = -2 ε` and `u = 2 ε` is `(1 / 2, ε)`. -/
example {ε α : ℝ} (hε : 0 < ε) : crownRelax (-1) (-2 * ε) (2 * ε) α = (1 / 2, ε) := by
  rw [crownRelax_of_neg_of_pos_of_neg (by linarith) (by linarith) (by norm_num)]
  have h : 2 * ε - -2 * ε = 4 * ε := by ring
  rw [h, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

end TauCeti
