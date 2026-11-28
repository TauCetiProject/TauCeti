/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Schur's inequality in a linearly ordered commutative ring

For `z ≤ y ≤ x` in a linearly ordered commutative ring and weights `a`, `b`, `c` with `0 ≤ a`,
`0 ≤ c` and `b ≤ a` or `b ≤ c`, the Schur sum

`a (x - y) (x - z) + b (y - z) (y - x) + c (z - x) (z - y)`

is nonnegative. This is the Vornicu–Schur form of Schur's inequality (V. Vornicu, *Olimpiada de
Matematică... de la provocare la experiență*, GIL, Zalău, 2003); Schur's inequality itself, with
weights `x ^ t`, `y ^ t`, `z ^ t` and its equality case, is in Mitrinović, *Analytic Inequalities*,
§2.17, Thm 1, p. 119. When `b ≤ a` the sum equals
`a (x - y)² + (a - b) (x - y) (y - z) + c (x - z) (y - z)`, and when `b ≤ c` it equals
`c (y - z)² + (c - b) (x - y) (y - z) + a (x - z) (x - y)`; every term is a product of
nonnegative factors. With `0 < a` and `0 < c` the sum vanishes exactly when `x = z`, that is, when
the three points coincide.

The Schur sum is symmetric in the three points. So for weights `f x`, `f y`, `f z` given by a
function `f`, nonnegative at the points of a set `s`, the inequality holds for points of `s` in any
order as soon as, for `u ≤ v ≤ w` in `s`, the middle value `f v` is at most `f u` or `f w`. Weights
monotone on `s` qualify, and the weights `t ↦ t ^ n` on `[0, ∞)` give the polynomial forms; for
`n = 1` this is the cubic `x (x - y) (x - z) + ⋯ ≥ 0`. For `n ≠ 0` the polynomial form vanishes
exactly when `x = y = z` or two of the points are equal and the third is `0`. Schur's inequality
with weights `x ^ t` for a real exponent `t` is `TauCeti.schur_inequality`, and the form with
quasiconvex weights is `QuasiconvexOn.schur_inequality`.

## Main results

* `TauCeti.schur_inequality_of_le`: the Schur sum of `z ≤ y ≤ x` is nonnegative.
* `TauCeti.schur_inequality_eq_zero_iff_of_le`: for positive outer weights it vanishes exactly
  when `x = z`.
* `TauCeti.schur_inequality_of_mid_le`: Schur's inequality with weights `f x`, `f y`, `f z` whose
  middle value is at most one of the outer values.
* `TauCeti.schur_inequality_eq_zero_iff_of_mid_le`: for positive such weights, equality holds
  exactly when `x = y = z`.
* `TauCeti.schur_inequality_pow`: `0 ≤ x ^ n (x - y) (x - z) + ⋯` for `x, y, z ≥ 0`.
* `TauCeti.schur_inequality_pow_eq_zero_iff`: its equality case for `n ≠ 0`.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a b c x y z : R}

/-- Schur's inequality for ordered points: if `z ≤ y ≤ x`, the outer weights `a`, `c` are
nonnegative and the middle weight satisfies `b ≤ a` or `b ≤ c`, then
`0 ≤ a (x - y) (x - z) + b (y - z) (y - x) + c (z - x) (z - y)`. -/
theorem schur_inequality_of_le (hzy : z ≤ y) (hyx : y ≤ x) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hb : b ≤ a ∨ b ≤ c) :
    0 ≤ a * (x - y) * (x - z) + b * (y - z) * (y - x) + c * (z - x) * (z - y) := by
  have hxy : 0 ≤ x - y := sub_nonneg.2 hyx
  have hyz : 0 ≤ y - z := sub_nonneg.2 hzy
  have hxz : 0 ≤ x - z := add_nonneg hxy hyz |>.trans_eq (sub_add_sub_cancel x y z)
  rcases hb with hb | hb
  · -- The sum is `a (x - y)² + (a - b) (x - y) (y - z) + c (x - z) (y - z)`.
    refine (add_nonneg (add_nonneg (mul_nonneg ha (mul_self_nonneg (x - y)))
      (mul_nonneg (mul_nonneg (sub_nonneg.2 hb) hxy) hyz))
      (mul_nonneg (mul_nonneg hc hxz) hyz)).trans_eq ?_
    ring
  · -- The sum is `c (y - z)² + (c - b) (x - y) (y - z) + a (x - z) (x - y)`.
    refine (add_nonneg (add_nonneg (mul_nonneg hc (mul_self_nonneg (y - z)))
      (mul_nonneg (mul_nonneg (sub_nonneg.2 hb) hxy) hyz))
      (mul_nonneg (mul_nonneg ha hxz) hxy)).trans_eq ?_
    ring

/-- The equality case of Schur's inequality for ordered points: if `z ≤ y ≤ x`, the outer
weights `a`, `c` are positive and `b ≤ a` or `b ≤ c`, then the Schur sum
`a (x - y) (x - z) + b (y - z) (y - x) + c (z - x) (z - y)` vanishes exactly when `x = z`. -/
theorem schur_inequality_eq_zero_iff_of_le (hzy : z ≤ y) (hyx : y ≤ x) (ha : 0 < a)
    (hc : 0 < c) (hb : b ≤ a ∨ b ≤ c) :
    a * (x - y) * (x - z) + b * (y - z) * (y - x) + c * (z - x) * (z - y) = 0 ↔ x = z := by
  refine ⟨fun h ↦ le_antisymm ?_ (hzy.trans hyx), fun h ↦ ?_⟩
  · -- If `z < x`, then `y < x` or `z < y`, and either gap makes the sum positive.
    by_contra! hzx
    have hxy : 0 ≤ x - y := sub_nonneg.2 hyx
    have hyz : 0 ≤ y - z := sub_nonneg.2 hzy
    have hxz : 0 < x - z := sub_pos.2 hzx
    rcases hb with hb | hb
    · have h₁ : 0 ≤ a * (x - y) * (x - y) := mul_nonneg (mul_nonneg ha.le hxy) hxy
      have h₂ : 0 ≤ (a - b) * (x - y) * (y - z) :=
        mul_nonneg (mul_nonneg (sub_nonneg.2 hb) hxy) hyz
      have h₃ : 0 ≤ c * (x - z) * (y - z) := mul_nonneg (mul_nonneg hc.le hxz.le) hyz
      rcases hxy.eq_or_lt with hxy | hxy
      · have : 0 < c * (x - z) * (y - z) := mul_pos (mul_pos hc hxz) (by linarith)
        linarith
      · have : 0 < a * (x - y) * (x - y) := mul_pos (mul_pos ha hxy) hxy
        linarith
    · have h₁ : 0 ≤ c * (y - z) * (y - z) := mul_nonneg (mul_nonneg hc.le hyz) hyz
      have h₂ : 0 ≤ (c - b) * (x - y) * (y - z) :=
        mul_nonneg (mul_nonneg (sub_nonneg.2 hb) hxy) hyz
      have h₃ : 0 ≤ a * (x - z) * (x - y) := mul_nonneg (mul_nonneg ha.le hxz.le) hxy
      rcases hyz.eq_or_lt with hyz | hyz
      · have : 0 < a * (x - z) * (x - y) := mul_pos (mul_pos ha hxz) (by linarith)
        linarith
      · have : 0 < c * (y - z) * (y - z) := mul_pos (mul_pos hc hyz) hyz
        linarith
  · subst h
    obtain rfl : y = x := le_antisymm hyx hzy
    ring

section Weights

variable {s : Set R} {f : R → R}

/-- Schur's inequality with weights from `f` for sorted points `z ≤ y ≤ x` of `s`, with its
equality case for positive outer weights. -/
private theorem schur_of_mid_le_of_le
    (hf : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s → u ≤ v → v ≤ w → f v ≤ f u ∨ f v ≤ f w)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hzy : z ≤ y) (hyx : y ≤ x) (hfx : 0 ≤ f x)
    (hfz : 0 ≤ f z) :
    0 ≤ f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) ∧
      (0 < f x → 0 < f z →
        f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) = 0 →
          x = z) := by
  have hb := (hf hz hy hx hzy hyx).symm
  exact ⟨schur_inequality_of_le hzy hyx hfx hfz hb, fun hfx hfz ↦
    (schur_inequality_eq_zero_iff_of_le hzy hyx hfx hfz hb).1⟩

/-- Schur's inequality with weights from `f` and its equality case, for points of `s` in any
order: the Schur sum is symmetric in the three points, so this is the sorted case after sorting
them. -/
private theorem schur_aux_of_mid_le
    (hf : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s → u ≤ v → v ≤ w → f v ≤ f u ∨ f v ≤ f w)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hfx : 0 ≤ f x) (hfy : 0 ≤ f y) (hfz : 0 ≤ f z) :
    0 ≤ f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) ∧
      (0 < f x → 0 < f y → 0 < f z →
        f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) = 0 →
          x = y ∧ y = z) := by
  rcases le_total z y with hzy | hyz <;> rcases le_total y x with hyx | hxy <;>
    rcases le_total z x with hzx | hxz
  -- In each order, apply the sorted form to the sorted points; the sums agree up to `ring`.
  all_goals first
    | have h := schur_of_mid_le_of_le hf hx hy hz hzy hyx hfx hfz
    | have h := schur_of_mid_le_of_le hf hy hx hz hzx hxy hfy hfz
    | have h := schur_of_mid_le_of_le hf hx hz hy hyz hzx hfx hfy
    | have h := schur_of_mid_le_of_le hf hz hx hy hyx hxz hfz hfy
    | have h := schur_of_mid_le_of_le hf hy hz hx hxz hzy hfy hfx
    | have h := schur_of_mid_le_of_le hf hz hy hx hxy hyz hfz hfx
  all_goals exact ⟨by linarith [h.1], fun _ _ _ h₀ ↦
    have := h.2 (by assumption) (by assumption) (by linarith); ⟨by linarith, by linarith⟩⟩

/-- **Schur's inequality** with weights from a function `f`: if `f` is nonnegative at
`x`, `y`, `z ∈ s`, and for all `u ≤ v ≤ w` in `s` the middle value `f v` is at most `f u` or
`f w`, then `0 ≤ f x (x - y) (x - z) + f y (y - z) (y - x) + f z (z - x) (z - y)`. -/
theorem schur_inequality_of_mid_le
    (hf : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s → u ≤ v → v ≤ w → f v ≤ f u ∨ f v ≤ f w)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hfx : 0 ≤ f x) (hfy : 0 ≤ f y) (hfz : 0 ≤ f z) :
    0 ≤ f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) :=
  (schur_aux_of_mid_le hf hx hy hz hfx hfy hfz).1

/-- The equality case of Schur's inequality with weights from a function `f`: if `f` is positive
at `x`, `y`, `z ∈ s`, and for all `u ≤ v ≤ w` in `s` the middle value `f v` is at most `f u` or
`f w`, then `f x (x - y) (x - z) + f y (y - z) (y - x) + f z (z - x) (z - y) = 0` exactly when
`x = y = z`. -/
theorem schur_inequality_eq_zero_iff_of_mid_le
    (hf : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → ∀ ⦃w⦄, w ∈ s → u ≤ v → v ≤ w → f v ≤ f u ∨ f v ≤ f w)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hfx : 0 < f x) (hfy : 0 < f y) (hfz : 0 < f z) :
    f x * (x - y) * (x - z) + f y * (y - z) * (y - x) + f z * (z - x) * (z - y) = 0 ↔
      x = y ∧ y = z := by
  refine ⟨(schur_aux_of_mid_le hf hx hy hz hfx.le hfy.le hfz.le).2 hfx hfy hfz, ?_⟩
  rintro ⟨rfl, rfl⟩
  ring

end Weights

/-- **Schur's inequality** for natural exponents: for `x, y, z ≥ 0`,
`0 ≤ x ^ n (x - y) (x - z) + y ^ n (y - z) (y - x) + z ^ n (z - x) (z - y)`. For `n = 1` this is
the cubic `0 ≤ x (x - y) (x - z) + y (y - z) (y - x) + z (z - x) (z - y)`. -/
theorem schur_inequality_pow (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ x ^ n * (x - y) * (x - z) + y ^ n * (y - z) * (y - x) + z ^ n * (z - x) * (z - y) :=
  -- On `Ici 0 = {x | 0 ≤ x}` the middle power is at most the largest.
  schur_inequality_of_mid_le (s := Set.Ici 0) (f := (· ^ n))
    (fun _ _ _ hv _ _ _ hvw ↦ .inr (pow_le_pow_left₀ hv hvw n)) hx hy hz (pow_nonneg hx n)
    (pow_nonneg hy n) (pow_nonneg hz n)

/-- The equality case of Schur's inequality for a natural exponent `n ≠ 0` and `x, y, z ≥ 0`:
`x ^ n (x - y) (x - z) + y ^ n (y - z) (y - x) + z ^ n (z - x) (z - y) = 0` exactly when
`x = y = z`, or two of the points are equal and the third is `0`. -/
theorem schur_inequality_pow_eq_zero_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) {n : ℕ}
    (hn : n ≠ 0) :
    x ^ n * (x - y) * (x - z) + y ^ n * (y - z) * (y - x) + z ^ n * (z - x) * (z - y) = 0 ↔
      x = y ∧ y = z ∨ x = y ∧ z = 0 ∨ y = z ∧ x = 0 ∨ z = x ∧ y = 0 := by
  -- With one point at `0`, the sum is `(a - b) (a ^ (n + 1) - b ^ (n + 1))` for the other two.
  have key {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : (a - b) * (a ^ (n + 1) - b ^ (n + 1)) = 0) :
      a = b := by
    rcases mul_eq_zero.1 h with h | h
    · exact sub_eq_zero.1 h
    · exact (pow_left_inj₀ ha hb n.succ_ne_zero).1 (sub_eq_zero.1 h)
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases hx.eq_or_lt with rfl | hx'
    · refine .inr (.inr (.inl ⟨key hy hz ?_, rfl⟩))
      rw [← h, zero_pow hn]
      ring
    rcases hy.eq_or_lt with rfl | hy'
    · refine .inr (.inr (.inr ⟨key hz hx ?_, rfl⟩))
      rw [← h, zero_pow hn]
      ring
    rcases hz.eq_or_lt with rfl | hz'
    · refine .inr (.inl ⟨key hx hy ?_, rfl⟩)
      rw [← h, zero_pow hn]
      ring
    -- On `Ici 0 = {x | 0 ≤ x}` the middle power is at most the largest.
    exact .inl ((schur_inequality_eq_zero_iff_of_mid_le (s := Set.Ici 0) (f := (· ^ n))
      (fun _ _ _ hv _ _ _ hvw ↦ .inr (pow_le_pow_left₀ hv hvw n)) hx hy hz (pow_pos hx' n)
      (pow_pos hy' n) (pow_pos hz' n)).1 h)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [zero_pow hn]

end TauCeti
