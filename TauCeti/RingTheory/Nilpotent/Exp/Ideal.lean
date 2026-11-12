/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import TauCeti.RingTheory.Nilpotent.Exp.Basic

/-!
# Finite exponentials and ideals

Finite exponentials of elements of an ideal are congruent to one modulo the
ideal, as are products of such exponentials. These arguments apply to left
ideals in associative rational algebras, without commutativity or topology.
If the ideal has vanishing `n`-th power, the difference from one of a product of
two such exponentials also has vanishing `n`-th power.

The ideal membership follows from `IsNilpotent.exists_commute_mul_eq_exp_sub_one`.

Adapted from `yuma-mizuno-lean/Mei`, commit
`2f6cbcc81315ba2d32fd3e4bfc4c592476cf5471`,
`Mei/RingTheory/Nilpotent/Exp.lean` (Apache 2.0).
-/

public section

namespace Ideal

variable {A : Type*} [Ring A] [Algebra ℚ A] (I : Ideal A)

/-- A finite exponential of an element of an ideal differs from one by an element of that ideal. -/
theorem exp_sub_one_mem {a : A} (ha : a ∈ I) (hna : IsNilpotent a) :
    IsNilpotent.exp a - 1 ∈ I := by
  obtain ⟨u, hc, he⟩ := hna.exists_commute_mul_eq_exp_sub_one
  rw [← he, hc.eq]
  exact I.mul_mem_left _ ha

/-- Products of finite exponentials of members of an ideal remain congruent to
one modulo that ideal. -/
theorem exp_mul_exp_sub_one_mem {a b : A} (ha : a ∈ I) (hb : b ∈ I)
    (hna : IsNilpotent a) (hnb : IsNilpotent b) :
    IsNilpotent.exp a * IsNilpotent.exp b - 1 ∈ I := by
  have he : IsNilpotent.exp a * IsNilpotent.exp b - 1 =
      IsNilpotent.exp a * (IsNilpotent.exp b - 1) + (IsNilpotent.exp a - 1) := by
    simp only [mul_sub, mul_one]
    abel
  rw [he]
  exact I.add_mem (I.mul_mem_left _ (I.exp_sub_one_mem hb hnb)) (I.exp_sub_one_mem ha hna)

/-- The difference from one of a product of finite exponentials of elements of a left ideal
has vanishing `n`-th power whenever the ideal does. -/
theorem exp_mul_exp_sub_one_pow_eq_zero {n : ℕ} (hI : I ^ n = ⊥)
    {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    (IsNilpotent.exp x * IsNilpotent.exp y - 1) ^ n = 0 := by
  have hI0 : I ^ n = 0 := by simpa only [Ideal.zero_eq_bot] using hI
  exact Ideal.pow_eq_zero_of_mem hI0 le_rfl
    (I.exp_mul_exp_sub_one_mem hx hy
      ⟨n, Ideal.pow_eq_zero_of_mem hI0 le_rfl hx⟩
      ⟨n, Ideal.pow_eq_zero_of_mem hI0 le_rfl hy⟩)

end Ideal
