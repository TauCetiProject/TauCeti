/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Factorization.PowMul
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.BinaryForm

/-!
# The superelliptic equation `y ^ 3 = 2 x (x - 3)` via Thue equations

A superelliptic equation `y ^ n = (p x + q) (r x + s)` with `n ≥ 3`, integers `p, r ≠ 0` and
`p s - q r ≠ 0` (two nonproportional linear factors) reduces to finitely many Thue equations: a
prime dividing both factors divides `r (p x + q) - p (r x + s) = q r - p s`, so each factor is an
`n`-th power up to one of finitely many coefficients, and eliminating `x` between
`p x + q = a u ^ n` and `r x + s = b v ^ n` gives the Thue equation
`r a U ^ n - p b V ^ n = q r - p s` of degree `n`.

This file carries out the reduction for `y ^ 3 = 2 x (x - 3)`. A prime dividing both `2 x` and
`x - 3` divides `2 x - 2 (x - 3) = 6`, so by
`Int.exists_dvd_and_eq_mul_pow_of_mul_eq_pow` there are divisors `a` and `b` of
`36 = (2 · 3) ^ 2` and integers `u` and `v` with `2 x = a u ^ 3` and `x - 3 = b v ^ 3`. Then
`(u, v)` solves the Thue equation `a U ^ 3 - 2 b V ^ 3 = 6`, and `x = b v ^ 3 + 3`. The divisors
of `36` are the eighteen integers `± 2 ^ k 3 ^ l` with `k, l ≤ 2`, so the solutions of
`y ^ 3 = 2 x (x - 3)` are recovered from those of `18 ^ 2 = 324` Thue equations. Each of these
has finitely many solutions (`TauCeti.finite_setOf_mul_pow_add_mul_pow_eq`), and `x` determines
`y`, so the superelliptic equation has finitely many integer solutions. Thue's theorem is
proved here through Roth's theorem, so this finiteness is ineffective; the reduction itself is
explicit.

## Main results

* `TauCeti.exists_dvd_and_eq_mul_pow_three_of_pow_three_eq_two_mul_mul_sub_three`: every integer
  solution of `y ^ 3 = 2 x (x - 3)` has `2 x = a u ^ 3` and `x - 3 = b v ^ 3` with `a, b ∣ 36`.
* `TauCeti.finite_setOf_pow_three_eq_two_mul_mul_sub_three`: the equation `y ^ 3 = 2 x (x - 3)`
  has only finitely many integer solutions.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, the example following Theorem 5.13, pp. 98–99.
-/

public section

namespace TauCeti

/-- **Reduction of `y ^ 3 = 2 x (x - 3)` to Thue equations.** Every integer solution has
`2 x = a u ^ 3` and `x - 3 = b v ^ 3` for some divisors `a` and `b` of `36` and integers `u` and
`v`. Hence `(u, v)` solves the Thue equation `a U ^ 3 - 2 b V ^ 3 = 6`. -/
theorem exists_dvd_and_eq_mul_pow_three_of_pow_three_eq_two_mul_mul_sub_three {x y : ℤ}
    (h : y ^ 3 = 2 * x * (x - 3)) :
    ∃ a b u v : ℤ, a ∣ 36 ∧ b ∣ 36 ∧ 2 * x = a * u ^ 3 ∧ x - 3 = b * v ^ 3 := by
  -- A prime dividing both `2 x` and `x - 3` divides `2 x - 2 (x - 3) = 6`.
  have hS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * x → (p : ℤ) ∣ x - 3 →
      p ∈ ({2, 3} : Finset ℕ) := by
    intro p hp h₁ h₂
    have h6 : p ∣ 2 * 3 := by
      have := dvd_sub h₁ (dvd_mul_of_dvd_right h₂ 2)
      rw [show 2 * x - 2 * (x - 3) = 6 by ring] at this
      exact_mod_cast this
    rcases hp.dvd_mul.mp h6 with h | h
    · simp [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h]
    · simp [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h]
  have h36 : (∏ p ∈ ({2, 3} : Finset ℕ), (p : ℤ)) ^ (3 - 1) = 36 := by norm_num
  obtain ⟨a, u, ha, hu⟩ :=
    Int.exists_dvd_and_eq_mul_pow_of_mul_eq_pow three_ne_zero h.symm hS
  obtain ⟨b, v, hb, hv⟩ :=
    Int.exists_dvd_and_eq_mul_pow_of_mul_eq_pow three_ne_zero (by rw [h]; ring)
      fun p hp h₁ h₂ ↦ hS p hp h₂ h₁
  exact ⟨a, b, u, v, h36 ▸ ha, h36 ▸ hb, hu, hv⟩

/-- **Finiteness for `y ^ 3 = 2 x (x - 3)`.** The superelliptic equation `y ^ 3 = 2 x (x - 3)`
has only finitely many integer solutions. -/
theorem finite_setOf_pow_three_eq_two_mul_mul_sub_three :
    {p : ℤ × ℤ | p.2 ^ 3 = 2 * p.1 * (p.1 - 3)}.Finite := by
  have hD : {a : ℤ | a ∣ 36}.Finite :=
    (Set.finite_Icc (-36) 36).subset fun a ha ↦
      abs_le.mp (Int.le_of_dvd (by norm_num) ((abs_dvd a 36).mpr ha))
  have hD0 : ∀ a ∈ {a : ℤ | a ∣ 36}, a ≠ 0 := fun a ha ↦ ne_zero_of_dvd_ne_zero (by norm_num) ha
  -- The first coordinates of the solutions are the values `b v ^ 3 + 3` at the solutions
  -- `(u, v)` of the Thue equations `a U ^ 3 - 2 b V ^ 3 = 6` with `a, b ∣ 36`.
  have hX : (⋃ a ∈ {a : ℤ | a ∣ 36}, ⋃ b ∈ {b : ℤ | b ∣ 36},
      (fun q : ℤ × ℤ ↦ b * q.2 ^ 3 + 3) ''
        {q : ℤ × ℤ | a * q.1 ^ 3 + -2 * b * q.2 ^ 3 = 6}).Finite :=
    hD.biUnion fun a ha ↦ hD.biUnion fun b hb ↦
      (finite_setOf_mul_pow_add_mul_pow_eq le_rfl (hD0 a ha)
        (mul_ne_zero (by norm_num) (hD0 b hb)) (by norm_num)).image _
  refine Set.Finite.of_finite_image (f := Prod.fst) (hX.subset ?_) ?_
  · rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
    obtain ⟨a, b, u, v, ha, hb, hu, hv⟩ :=
      exists_dvd_and_eq_mul_pow_three_of_pow_three_eq_two_mul_mul_sub_three hxy
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
    exact ⟨a, ha, b, hb, (u, v), by linear_combination -hu + 2 * hv, by linear_combination -hv⟩
  · -- The first coordinate determines the second, since cubing is injective on `ℤ`.
    rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' (rfl : x = x')
    simp only [Set.mem_ofPred_eq] at hxy hxy'
    rw [(Odd.pow_injective (by decide : Odd 3)) (hxy.trans hxy'.symm)]

end TauCeti
