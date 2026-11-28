/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.Tactic.FieldSimp
import TauCeti.RingTheory.Valuation.Basic

/-!
# The valuation of a difference of powers

For a valuation `v` on a ring and elements `x`, `y` with `v x ≤ c` and `v y ≤ c`, the identity
`x ^ (n + 1) - y ^ (n + 1) = x ^ n * (x - y) + (x ^ n - y ^ n) * y`, which needs no
commutativity, and the ultrametric inequality give

`v (x ^ n - y ^ n) ≤ v (x - y) * c ^ (n - 1)`.

This estimate controls the nonlinear terms of a power series on sufficiently deep inputs; for
instance, it shows that the logarithm is an isometry on the deep units of a local field.

The exact formulas here say that powers whose exponent has valuation one preserve the distance
of a principal unit from one (natural powers over any ring, integer powers over any division
ring), and compute differences of integer powers in a field after translation by an element of
smaller valuation. These give the displacement orders of explicit
uniformizers in wildly ramified Artin--Schreier extensions. The principal-unit bound also
controls the errors of congruences modulo `(1 + X) ^ (p ^ n) - 1` under a Gauss valuation.
-/

public section

namespace Valuation

section Ring

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]

/-- If `v x ≤ c` and `v y ≤ c`, then `v (x ^ n - y ^ n) ≤ v (x - y) * c ^ (n - 1)`. -/
theorem map_pow_sub_pow_le (v : Valuation R Γ₀) {x y : R} {c : Γ₀} (hx : v x ≤ c)
    (hy : v y ≤ c) (n : ℕ) :
    v (x ^ n - y ^ n) ≤ v (x - y) * c ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases n with _ | n
    · simp
    simp only [Nat.add_sub_cancel] at ih ⊢
    -- `x ^ (n + 2) - y ^ (n + 2) = x ^ (n + 1) * (x - y) + (x ^ (n + 1) - y ^ (n + 1)) * y`
    -- holds without `x` and `y` commuting.
    have heq : x ^ (n + 1 + 1) - y ^ (n + 1 + 1) =
        x ^ (n + 1) * (x - y) + (x ^ (n + 1) - y ^ (n + 1)) * y := by
      rw [pow_succ x (n + 1), pow_succ y (n + 1), mul_sub, sub_mul]
      abel
    rw [heq]
    refine (v.map_add _ _).trans (max_le ?_ ?_)
    · rw [map_mul, map_pow, mul_comm]
      gcongr
      exact zero_le
    · rw [map_mul, pow_succ c, ← mul_assoc]
      gcongr

/-- The geometric sum at `1 + x` differs from its value at `1` by an element of
valuation at most `v x`, when `v x ≤ 1`. -/
theorem map_geom_sum_one_add_sub_natCast_le (v : Valuation R Γ₀) {x : R} (hx : v x ≤ 1)
    (n : ℕ) : v ((∑ i ∈ Finset.range n, (1 + x) ^ i) - (n : R)) ≤ v x := by
  have hcast : (n : R) = ∑ _i ∈ Finset.range n, (1 : R) := by simp
  have hval : v (1 + x) ≤ 1 := (v.map_add 1 x).trans (by simp [hx])
  rw [hcast, ← Finset.sum_sub_distrib]
  refine v.map_sum_le fun i _ ↦ ?_
  simpa using v.map_pow_sub_pow_le hval (y := 1) (c := 1) (by simp) i

/-- In the closed unit ball, taking an `n`-th power contracts the distance of `1 + x`
from `1` by a factor bounded by `max (v n) (v x)`. -/
theorem map_one_add_pow_sub_one_le (v : Valuation R Γ₀) {x : R} (hx : v x ≤ 1)
    (n : ℕ) : v ((1 + x) ^ n - 1) ≤ v x * max (v (n : R)) (v x) := by
  let s : R := ∑ i ∈ Finset.range n, (1 + x) ^ i
  have hs := (v.map_add (s - n) (n : R)).trans
    (max_le_max (v.map_geom_sum_one_add_sub_natCast_le hx n) le_rfl)
  rw [sub_add_cancel, max_comm] at hs
  rw [← geom_sum_mul, add_sub_cancel_left, map_mul, mul_comm]
  exact mul_le_mul_right hs _

/-- Iterating the contraction bound gives a factor `(max (v p) (v x))^n` for the
`p^n`-th power of an element `1 + x` of the closed unit ball. -/
theorem map_one_add_pow_pow_sub_one_le (v : Valuation R Γ₀) {x : R} (hx : v x ≤ 1)
    (p n : ℕ) : v ((1 + x) ^ p ^ n - 1) ≤ v x * max (v (p : R)) (v x) ^ n := by
  let c := max (v (p : R)) (v x)
  have hc : c ≤ 1 := max_le (v.map_natCast_le_one p) hx
  induction n with
  | zero => simp
  | succ n ih =>
    let y := (1 + x) ^ p ^ n - 1
    have hy : v y ≤ v x := ih.trans (mul_le_of_le_one_right' (pow_le_one' hc _))
    have he : 1 + y = (1 + x) ^ p ^ n := by simp [y]
    rw [pow_succ p n, pow_mul, ← he, pow_succ c, ← mul_assoc]
    exact (v.map_one_add_pow_sub_one_le (hy.trans hx) p).trans
      (mul_le_mul' ih (max_le_max le_rfl hy))

/-- Raising a principal unit to a natural power of valuation one preserves its distance
from one. -/
@[simp] theorem map_one_add_pow_sub_one (v : Valuation R Γ₀) {x : R} (hx : v x < 1)
    (n : ℕ) (hn : v (n : R) = 1) : v ((1 + x) ^ n - 1) = v x := by
  let s : R := ∑ i ∈ Finset.range n, (1 + x) ^ i
  have hsum : v (s - n) < v (n : R) :=
    (v.map_geom_sum_one_add_sub_natCast_le hx.le n).trans_lt (hn ▸ hx)
  have hs : v s = 1 := by
    simpa only [sub_add_cancel, hn] using v.map_add_eq_of_lt_right hsum
  rw [← geom_sum_mul, add_sub_cancel_left, map_mul, hs, one_mul]

end Ring

section DivisionRing

variable {K Γ₀ : Type*} [DivisionRing K] [LinearOrderedCommMonoidWithZero Γ₀]

/-- Raising a principal unit to an integer power of valuation one preserves its distance
from one, including negative powers. -/
@[simp] theorem map_one_add_zpow_sub_one (v : Valuation K Γ₀) {x : K} (hx : v x < 1)
    (n : ℤ) (hn : v (n : K) = 1) : v ((1 + x) ^ n - 1) = v x := by
  have : Nontrivial Γ₀ := ⟨⟨v x, 1, hx.ne⟩⟩
  cases n with
  | ofNat n => simpa using v.map_one_add_pow_sub_one hx n (by simpa using hn)
  | negSucc n =>
    rw [Int.cast_negSucc, v.map_neg] at hn
    have ha : v ((1 + x) ^ (n + 1)) = 1 := by rw [map_pow, v.map_one_add_of_lt hx, one_pow]
    have ha0 : (1 + x) ^ (n + 1) ≠ 0 := fun h => by simp [h] at ha
    -- `a⁻¹ - 1 = (1 - a) * a⁻¹`, and `a⁻¹` has valuation one along with `a`.
    have hinv : v ((1 + x) ^ (n + 1))⁻¹ = 1 := by
      simpa [ha] using congr(v $(mul_inv_cancel₀ ha0))
    have heq : ((1 + x) ^ (n + 1))⁻¹ - 1 =
        (1 - (1 + x) ^ (n + 1)) * ((1 + x) ^ (n + 1))⁻¹ := by
      rw [sub_mul, one_mul, mul_inv_cancel₀ ha0]
    rw [zpow_negSucc, heq, map_mul, hinv, mul_one, map_sub_swap,
      v.map_one_add_pow_sub_one hx (n + 1) hn]

end DivisionRing

section Field

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]

/-- Translating by an element of smaller valuation gives the exact valuation of the
difference of integer powers, when the exponent has valuation one. -/
@[simp] theorem map_add_zpow_sub_zpow (v : Valuation F Γ₀) {y c : F}
    (hc : v c < v y) (n : ℤ) (hn : v (n : F) = 1) :
    v ((y + c) ^ n - y ^ n) = v y ^ (n - 1) * v c := by
  have hyv : v y ≠ 0 := (zero_le.trans_lt hc).ne'
  have hy0 : y ≠ 0 := v.ne_zero_iff.mp hyv
  have hx : v (c / y) < 1 := by
    rw [v.map_div]
    exact (div_lt_one₀ (pos_iff_ne_zero.mpr hyv)).mpr hc
  have he : y + c = y * (1 + c / y) := by field_simp
  have heq : (y + c) ^ n - y ^ n = y ^ n * ((1 + c / y) ^ n - 1) := by
    rw [he, mul_zpow]
    ring
  rw [heq, v.map_mul, map_zpow₀, v.map_one_add_zpow_sub_one hx n hn, v.map_div,
    zpow_sub₀ hyv, zpow_one]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

end Field

end Valuation
