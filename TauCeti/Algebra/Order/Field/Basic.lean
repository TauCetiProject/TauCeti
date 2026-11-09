/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Inequalities in ordered fields

This file records a bound on a sum of two reciprocals in a linearly ordered field. It turns a lower
bound on a reciprocal sum `1 / b + 1 / c` with `b ≤ c` into an upper bound on the smaller
denominator `b`; the classifications of sorted triangle-group signatures use it to bound their
second parameter.

It also records an a priori bound from a difference of two quadratic penalties
`b² / (2τ) - a² / (2τ₀)` with `τ < τ₀`: if `a ≤ R + b`, a bound on this difference bounds `a`.
This is the arithmetic behind the equicoercivity of penalized energies in Moreau–Yosida
regularization.

It records that for `0 < d`, `0 < a` and `e < a`, the time `d * e / a` lies strictly before `d`;
this is where a timed piece of duration `d` running across `[0, a]` reaches `e`.

It also records how to remove a term `ε * C` from a bound valid for every `ε > 0`, and how
to transfer bounds from maximizers of `f + εw` when the barrier `w` is bounded above.

Finally, it records the rescaling identity `q |q x - m| = q² |x - m / q|` for `q > 0`, which
converts between the two usual forms of an approximation `x ≈ m / q`.

It also records a perturbation bound for quotients, `|x / a - y / b| ≤ 2 (e + y δ) / b` when
`(1 - δ) b ≤ a ≤ b`, `δ ≤ 1 / 2` and `|x - y| ≤ e`, the comparison
`2 t / (t² + ρ²) ≤ (2 t / r) (2 r / (r² + ρ²))` for `0 < t`, `0 < r ≤ ρ`, which compares the
profiles `2 t / (t² + ρ²)` of two scales `t` and `r` outside the radius `r`, and the clearing
bound `a * b ≤ 1` from `a ≤ (1 + b)⁻¹` for `0 ≤ b`.

Finally, it records a polynomial barrier bound: if `r ≤ M`, `0 < ε`, `1 ≤ c` and `n` is larger
than `M / ε`, then the barrier `ε * (c * (1 + n ^ 2))` exceeds `r`.

It also records how to bound a sum `U + Y` from `U ≤ 2 Z + 2 M² Y` and `c / 2 * Y ≤ a Z + b W`:
solve the second estimate for `Y` and substitute it into the first.

## Main results

* `BddAbove.le_of_forall_pos_exists_add_mul_le`: transfer a bound at maximizers of
  `f + εw` to `f` when `w` is bounded above.
* `TauCeti.one_div_add_one_div_le_two_div`: for `0 < b ≤ c`, the sum `1 / b + 1 / c` is at most
  `2 / b`.
* `TauCeti.le_of_sq_div_sub_sq_div_le`: an upper bound on `a` from `a ≤ R + b` and an upper bound
  on `b² / (2τ) - a² / (2τ₀)`, for `0 < τ < τ₀`.
* `TauCeti.mul_div_lt_self`: `d * e / a < d` for `0 < d`, `0 < a` and `e < a`.
* `TauCeti.mul_abs_mul_sub_eq_sq_mul_abs_sub_div`: `q |q x - m| = q² |x - m / q|` for `q > 0`.
* `TauCeti.abs_div_sub_div_le`: `|x / a - y / b| ≤ 2 (e + y δ) / b` for a relative perturbation
  `(1 - δ) b ≤ a ≤ b` of the denominator with `δ ≤ 1 / 2` and `|x - y| ≤ e`.
* `TauCeti.two_mul_div_add_sq_le_mul`: `2 t / (t² + ρ²) ≤ (2 t / r) (2 r / (r² + ρ²))` for
  `0 < t` and `0 < r ≤ ρ`.
* `TauCeti.mul_le_one_of_le_inv_one_add`: `a * b ≤ 1` for `0 ≤ b` and `a ≤ (1 + b)⁻¹`.
* `TauCeti.sub_mul_mul_one_add_sq_neg_of_lt`: the strict inequality
  `r - ε * (c * (1 + n ^ 2)) < 0` for `r ≤ M`, `0 < ε`, `1 ≤ c` and `M / ε < n`.
* `TauCeti.add_le_mul_add_mul_of_le_of_le`: `U + Y ≤ (2 + (2 M² + 1) (2 / c) (a + b)) (Z + W)` from
  `U ≤ 2 Z + 2 M² Y` and `c / 2 * Y ≤ a Z + b W`.
-/

public section

namespace TauCeti

/-- If `a ≤ m + ε * C` for every positive `ε`, then `a ≤ m`. No sign assumption on `C` is
needed. -/
theorem le_of_forall_pos_mul_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {a m C : α} (h : ∀ ε : α, 0 < ε → a ≤ m + ε * C) : a ≤ m := by
  by_cases hC : 0 < C
  · by_contra! ham
    have hε := h ((a - m) / (2 * C)) (by positivity)
    have heq : (a - m) / (2 * C) * C = (a - m) / 2 := by field_simp
    rw [heq] at hε
    linarith
  · have hε := h 1 one_pos
    simp only [one_mul] at hε
    linarith

/-- For `0 < b ≤ c`, the sum `1 / b + 1 / c` is at most `2 / b`. -/
theorem one_div_add_one_div_le_two_div {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] {b c : α} (hb : 0 < b) (hbc : b ≤ c) :
    1 / b + 1 / c ≤ 2 / b := by
  have hcb : 1 / c ≤ 1 / b := one_div_le_one_div_of_le hb hbc
  rw [div_eq_mul_one_div (2 : α)]
  linarith

/-- If `a ≤ R + b` and `b² / (2τ) - a² / (2τ₀) ≤ D` with `0 < τ < τ₀` and `R ≥ 0`, then `a` is
bounded by a constant depending only on `R`, `D`, `τ` and `τ₀`. -/
theorem le_of_sq_div_sub_sq_div_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {τ τ₀ a b R D : α} (hτ : 0 < τ) (hττ₀ : τ < τ₀) (hR : 0 ≤ R) (hab : a ≤ R + b)
    (h : b ^ 2 / (2 * τ) - a ^ 2 / (2 * τ₀) ≤ D) :
    a ≤ R + 1 + (2 * τ₀ * R + 2 * τ * τ₀ * |D|) / (τ₀ - τ) := by
  have hτ₀ : 0 < τ₀ := hτ.trans hττ₀
  have hs : 0 < τ₀ - τ := sub_pos.2 hττ₀
  have hq : 0 ≤ (2 * τ₀ * R + 2 * τ * τ₀ * |D|) / (τ₀ - τ) := by positivity
  by_contra! ha
  have ha₁ : 1 ≤ a := by linarith
  have hb : (a - R) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  -- Clearing denominators, `τ₀ b² - τ a² ≤ 2ττ₀ |D|`.
  have h' : τ₀ * b ^ 2 - τ * a ^ 2 ≤ 2 * τ * τ₀ * |D| := by
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)] at h
    nlinarith [mul_le_mul_of_nonneg_left (le_abs_self D) (by positivity : (0 : α) ≤ τ * τ₀)]
  -- Hence `(τ₀ - τ) a² ≤ (2τ₀ R + 2ττ₀ |D|) a`, and dividing by `a ≥ 1` contradicts `ha`.
  have key : (τ₀ - τ) * a ≤ 2 * τ₀ * R + 2 * τ * τ₀ * |D| := by
    have : (τ₀ - τ) * a * a ≤ (2 * τ₀ * R + 2 * τ * τ₀ * |D|) * a := by
      nlinarith [mul_le_mul_of_nonneg_left hb hτ₀.le, mul_nonneg hτ₀.le (sq_nonneg R),
        mul_le_mul_of_nonneg_left ha₁ (by positivity : (0 : α) ≤ 2 * τ * τ₀ * |D|)]
    exact le_of_mul_le_mul_right this (by linarith)
  rw [← le_div_iff₀' hs] at key
  linarith

/-- For `0 < d`, `0 < a` and `e < a`, scaling `d` by the fraction `e / a < 1` gives
`d * e / a < d`. -/
theorem mul_div_lt_self {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {d e a : α} (hd : 0 < d) (ha : 0 < a) (hea : e < a) : d * e / a < d := by
  rw [mul_div_assoc]
  exact mul_lt_of_lt_one_right hd ((div_lt_one ha).2 hea)

/-- The rescaling identity `q |q x - m| = q ^ 2 |x - m / q|` for `q > 0`. -/
theorem mul_abs_mul_sub_eq_sq_mul_abs_sub_div {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] {q : α} (hq : 0 < q) (x m : α) :
    q * |q * x - m| = q ^ 2 * |x - m / q| := by
  have h : x - m / q = (q * x - m) / q := by field_simp
  rw [h, abs_div, abs_of_pos hq]
  field_simp

/-- A perturbation estimate for quotients: if `(1 - δ) b ≤ a ≤ b` with `δ ≤ 1 / 2` and
`|x - y| ≤ e`, then `|x / a - y / b| ≤ 2 (e + y δ) / b`. -/
theorem abs_div_sub_div_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {x y a b e δ : α} (hb : 0 < b) (hy : 0 ≤ y) (hδ : δ ≤ 1 / 2)
    (hab : (1 - δ) * b ≤ a) (hab' : a ≤ b) (hxy : |x - y| ≤ e) :
    |x / a - y / b| ≤ 2 * (e + y * δ) / b := by
  have hδ0 : 0 ≤ δ := by nlinarith
  have ha : b ≤ 2 * a := by nlinarith
  have he : 0 ≤ e + y * δ := add_nonneg ((abs_nonneg _).trans hxy) (mul_nonneg hy hδ0)
  have h1 : |x * b - a * y| ≤ (e + y * δ) * b := by
    calc
      |x * b - a * y| = |(x - y) * b + y * (b - a)| := by ring_nf
      _ ≤ |(x - y) * b| + |y * (b - a)| := abs_add_le _ _
      _ = |x - y| * b + y * (b - a) := by
        rw [abs_mul, abs_of_pos hb, abs_of_nonneg (mul_nonneg hy (by linarith))]
      _ ≤ e * b + y * (δ * b) :=
        add_le_add (mul_le_mul_of_nonneg_right hxy hb.le)
          (mul_le_mul_of_nonneg_left (by linarith) hy)
      _ = (e + y * δ) * b := by ring
  rw [div_sub_div _ _ (by linarith : a ≠ 0) hb.ne', abs_div, abs_of_pos (by nlinarith : 0 < a * b),
    div_le_div_iff₀ (by nlinarith) hb]
  calc
    |x * b - a * y| * b ≤ (e + y * δ) * b * b := mul_le_mul_of_nonneg_right h1 hb.le
    _ ≤ (e + y * δ) * b * (2 * a) := mul_le_mul_of_nonneg_left ha (mul_nonneg he hb.le)
    _ = 2 * (e + y * δ) * (a * b) := by ring

/-- For `0 < t` and `0 < r ≤ ρ`, the profile `2 t / (t² + ρ²)` of scale `t` is at most `2 t / r`
times the profile `2 r / (r² + ρ²)` of scale `r`. -/
theorem two_mul_div_add_sq_le_mul {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {t r ρ : α} (ht : 0 < t) (hr : 0 < r) (hρ : r ≤ ρ) :
    2 * t / (t ^ 2 + ρ ^ 2) ≤ 2 * t / r * (2 * r / (r ^ 2 + ρ ^ 2)) := by
  rw [div_mul_div_comm, mul_comm r, ← mul_assoc, mul_div_mul_right _ _ hr.ne',
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hρ hρ hr.le (hr.le.trans hρ)]

/-- If `0 ≤ b` and `a ≤ (1 + b)⁻¹`, then `a * b ≤ 1`. -/
theorem mul_le_one_of_le_inv_one_add {α : Type*} [Semifield α] [LinearOrder α]
    [IsStrictOrderedRing α] {a b : α} (hb : 0 ≤ b) (ha : a ≤ (1 + b)⁻¹) :
    a * b ≤ 1 := by
  refine (mul_le_mul_of_nonneg_right ha hb).trans ?_
  rw [inv_mul_eq_div, div_le_one (add_pos_of_pos_of_nonneg zero_lt_one hb)]
  exact le_add_of_nonneg_left zero_le_one

/-- The barrier `ε * (c * (1 + n ^ 2))` dominates an upper bound `r ≤ M` once the radius `n`
exceeds `M / ε`, for `c ≥ 1` and `ε > 0`. -/
theorem sub_mul_mul_one_add_sq_neg_of_lt {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] {c ε M r n : α} (hc : 1 ≤ c) (hε : 0 < ε)
    (hr : r ≤ M) (hn : M / ε < n) :
    r - ε * (c * (1 + n ^ 2)) < 0 := by
  have h2 : M < ε * n := by
    rw [← div_lt_iff₀' hε]
    linarith
  have h3 : n ≤ 1 + n ^ 2 := by
    nlinarith [sq_nonneg (n - 1)]
  have h4 : ε * (1 + n ^ 2) ≤ ε * (c * (1 + n ^ 2)) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hc) hε.le
  nlinarith [mul_le_mul_of_nonneg_left h3 hε.le]

/-- If `U ≤ 2 Z + 2 M² Y` and `c / 2 * Y ≤ a Z + b W`, where `a, b ≥ 0`, `c > 0` and `Z, W ≥ 0`,
then `U + Y ≤ (2 + (2 M² + 1) (2 / c) (a + b)) (Z + W)`. -/
theorem add_le_mul_add_mul_of_le_of_le {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] {U Y Z W M a b c : α} (hc : 0 < c)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hZ : 0 ≤ Z) (hW : 0 ≤ W)
    (hX : U ≤ 2 * Z + 2 * M ^ 2 * Y) (hY : c / 2 * Y ≤ a * Z + b * W) :
    U + Y ≤ (2 + (2 * M ^ 2 + 1) * (2 / c) * (a + b)) * Z +
      (2 + (2 * M ^ 2 + 1) * (2 / c) * (a + b)) * W := by
  have hY' : Y ≤ 2 / c * (a * Z + b * W) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  have hk : 0 ≤ (2 * M ^ 2 + 1) * (2 / c) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hY' (by positivity : (0 : α) ≤ 2 * M ^ 2 + 1),
    mul_nonneg (mul_nonneg hk hb) hZ, mul_nonneg (mul_nonneg hk ha) hW,
    mul_nonneg (mul_nonneg hk ha) hZ, mul_nonneg (mul_nonneg hk hb) hW]

end TauCeti

/-- If `w` is bounded above on `K` and every positive `ε` admits a point `z ∈ K` with
`f z ≤ m` and `f x + ε * w x ≤ f z + ε * w z`, then `f x ≤ m`. No sign condition on the
barrier or its upper bound is needed. -/
theorem BddAbove.le_of_forall_pos_exists_add_mul_le {X α : Type*}
    [Field α] [LinearOrder α] [IsStrictOrderedRing α] {K : Set X} {w : X → α}
    (hw : BddAbove (w '' K)) {f : X → α} {m : α} {x : X}
    (H : ∀ ε : α, 0 < ε → ∃ z ∈ K, f x + ε * w x ≤ f z + ε * w z ∧ f z ≤ m) :
    f x ≤ m := by
  obtain ⟨C, hC⟩ := hw
  refine TauCeti.le_of_forall_pos_mul_le (C := C - w x) fun ε hε => ?_
  obtain ⟨z, hzK, hxz, hfz⟩ := H ε hε
  have hwzC := mul_le_mul_of_nonneg_left (hC (Set.mem_image_of_mem w hzK)) hε.le
  nlinarith
