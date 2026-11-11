/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Leading digits of points of `[0, 1)`

For `x ≥ 0` in a linearly ordered semifield, `⌊bᵐ x⌋₊` records the first `m` base-`b` digits of
`x`, and dropping the last `d` of the first `m + d` digits is division by `bᵈ`. In base `2`,
`⌊2ᵐ x⌋₊ = j` says that `x` lies in the `j`-th dyadic interval `[j 2^{-m}, (j + 1) 2^{-m})`.
Two points `x < y` of `[0, 1)` in an Archimedean field lie in the two halves of a common dyadic
interval, `⌊2^{n + 1} x⌋₊ = 2k` and `⌊2^{n + 1} y⌋₊ = 2k + 1`, at exactly one level `n + 1`: the
first level at which their binary digits differ. This is the indexing of the dyadic Whitney
decomposition of `{(x, y) | x < y}` in `[0, 1)²`.

## Main results

* `TauCeti.floor_pow_mul_eq_div`: `⌊bᵐ x⌋₊ = ⌊b^{m + d} x⌋₊ / bᵈ`.
* `TauCeti.exists_floor_two_pow_mul_eq`: points `0 ≤ x < y < 1` lie in sibling dyadic intervals at
  some level.
* `TauCeti.eq_of_floor_two_pow_mul_eq`: that level and the common parent are unique.
-/

public section

namespace TauCeti

section Semifield

variable {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

/-- Truncating a base-`b` expansion: the first `m` digits of `x` are the first `m + d` digits with
the last `d` dropped. -/
theorem floor_pow_mul_eq_div (x : K) {b : ℕ} (hb : b ≠ 0) (m d : ℕ) :
    ⌊(b : K) ^ m * x⌋₊ = ⌊(b : K) ^ (m + d) * x⌋₊ / b ^ d := by
  rw [← Nat.floor_div_natCast]
  congr 1
  have hb' : (b : K) ≠ 0 := Nat.cast_ne_zero.2 hb
  push_cast
  rw [pow_add]
  field_simp

/-- Two points lie in sibling dyadic intervals at no more than one level, and the common parent
interval at that level is unique. -/
theorem eq_of_floor_two_pow_mul_eq {x y : K} {n k n' k' : ℕ}
    (h₁ : ⌊2 ^ (n + 1) * x⌋₊ = 2 * k) (h₂ : ⌊2 ^ (n + 1) * y⌋₊ = 2 * k + 1)
    (h₁' : ⌊2 ^ (n' + 1) * x⌋₊ = 2 * k') (h₂' : ⌊2 ^ (n' + 1) * y⌋₊ = 2 * k' + 1) :
    n = n' ∧ k = k' := by
  have h (m d : ℕ) := floor_pow_mul_eq_div (b := 2) x two_ne_zero m d
  have h' (m d : ℕ) := floor_pow_mul_eq_div (b := 2) y two_ne_zero m d
  push_cast at h h'
  -- At a level where the digits differ, they differ at every finer level.
  have key : ∀ {n k n' k' : ℕ}, ⌊2 ^ (n + 1) * x⌋₊ = 2 * k → ⌊2 ^ (n + 1) * y⌋₊ = 2 * k + 1 →
      ⌊2 ^ (n' + 1) * x⌋₊ = 2 * k' → ⌊2 ^ (n' + 1) * y⌋₊ = 2 * k' + 1 → ¬ n < n' := by
    intro n k n' k' h₁ h₂ h₁' h₂' hlt
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_iff_add_one_le.1 hlt)
    have ex := h (n + 1) d
    have ey := h' (n + 1) d
    have ex' := h (n + 1 + d) 1
    have ey' := h' (n + 1 + d) 1
    have : ⌊2 ^ (n + 1 + d) * x⌋₊ = ⌊2 ^ (n + 1 + d) * y⌋₊ := by omega
    rw [this] at ex
    omega
  have hn : n = n' := le_antisymm (not_lt.1 (key h₁' h₂' h₁ h₂)) (not_lt.1 (key h₁ h₂ h₁' h₂'))
  subst hn
  exact ⟨rfl, by omega⟩

end Semifield

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
  [Archimedean K]

/-- Two points `x < y` of `[0, 1)` lie in sibling dyadic intervals at some level: the first level
`n + 1` at which their binary digits differ. -/
theorem exists_floor_two_pow_mul_eq {x y : K} (hx : 0 ≤ x) (hxy : x < y) (hy : y < 1) :
    ∃ n k : ℕ, ⌊2 ^ (n + 1) * x⌋₊ = 2 * k ∧ ⌊2 ^ (n + 1) * y⌋₊ = 2 * k + 1 := by
  have hex : ∃ m : ℕ, ⌊2 ^ m * x⌋₊ ≠ ⌊2 ^ m * y⌋₊ := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (y - x)⁻¹ (by norm_num : (1 : K) < 2)
    have h : ⌊2 ^ m * x⌋₊ + 1 ≤ ⌊2 ^ m * y⌋₊ := by
      rw [← Nat.floor_add_one (by positivity)]
      refine Nat.floor_mono ?_
      have h := (inv_lt_iff_one_lt_mul₀ (sub_pos.2 hxy)).1 hm
      nlinarith
    exact ⟨m, by omega⟩
  classical
  have hzero : ⌊2 ^ 0 * x⌋₊ = ⌊2 ^ 0 * y⌋₊ := by
    rw [pow_zero, one_mul, one_mul, Nat.floor_eq_zero.2 (hxy.trans hy), Nat.floor_eq_zero.2 hy]
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact this hzero
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := Nat.exists_eq_add_one.2 (Nat.pos_of_ne_zero hpos)
  have hdiff := Nat.find_spec hex
  have hsame : ⌊2 ^ n * x⌋₊ = ⌊2 ^ n * y⌋₊ := by
    by_contra h
    exact Nat.find_min hex (by omega) h
  rw [hn] at hdiff
  have hle : ⌊2 ^ (n + 1) * x⌋₊ ≤ ⌊2 ^ (n + 1) * y⌋₊ := Nat.floor_mono (by gcongr)
  have h₁ := floor_pow_mul_eq_div (b := 2) x two_ne_zero n 1
  have h₂ := floor_pow_mul_eq_div (b := 2) y two_ne_zero n 1
  push_cast at h₁ h₂
  refine ⟨n, ⌊2 ^ n * x⌋₊, ?_, ?_⟩ <;> omega

end TauCeti
