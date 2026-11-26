/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic

import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-!
# Orders of roots of unity in rational cyclotomic extensions

Over `ℚ`, a cyclotomic field of even order `n` has no roots of unity of order not dividing `n`.
If the order is `np` for a prime `p`, a proper subfield containing a primitive `n`-th root
has no roots of unity of order not dividing `n`.

See Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section

open Module Polynomial

namespace IsPrimitiveRoot

/-- In an even `n`-th cyclotomic extension of `ℚ`, the positive order of a root of unity
divides `n`. -/
theorem dvd_of_isCyclotomicExtension_even {F : Type*} [Field F] [CharZero F]
    {n m : ℕ} [IsCyclotomicExtension {n} ℚ F] {z : F}
    (hz : IsPrimitiveRoot z m) (hm : m ≠ 0) (hn : Even n) : m ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact dvd_zero m
  have : NeZero n := ⟨hn0⟩
  have : NeZero m := ⟨hm⟩
  have : NumberField F := IsCyclotomicExtension.numberField {n} ℚ F
  have h := NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot hz
  rwa [IsCyclotomicExtension.Rat.torsionOrder_eq (n := n), ite_eq_left hn] at h

/-- Let `p` be prime with `np` even. If a field embeds in the `np`-th rational cyclotomic
extension but has degree less than `φ(np)`, then every root of unity in it has order dividing `n`,
provided it contains a primitive `n`-th root. -/
theorem dvd_of_finrank_lt_totient_mul_prime {E F : Type*} [Field E] [CharZero E] [Field F]
    [CharZero F] {n p m : ℕ} [IsCyclotomicExtension {n * p} ℚ F]
    {z ζ : E} (hz : IsPrimitiveRoot z m) (hm : m ≠ 0) (hζ : IsPrimitiveRoot ζ n)
    (f : E →ₐ[ℚ] F) (heven : Even (n * p)) (hp : p.Prime)
    (hdeg : finrank ℚ E < (n * p).totient) : m ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact dvd_zero m
  have : NumberField F := IsCyclotomicExtension.numberField {n * p} ℚ F
  have : FiniteDimensional ℚ E := FiniteDimensional.of_injective f.toLinearMap f.injective
  have hdiv : m ∣ n * p :=
    (hz.map_of_injective f.injective).dvd_of_isCyclotomicExtension_even hm heven
  -- The only divisors of `np` that are multiples of `n` are `n` and `np`.
  obtain ⟨k, hk⟩ := dvd_lcm_left n m
  have hkdiv : k ∣ p := by
    apply Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hn0)
    rw [← hk]
    exact Nat.lcm_dvd (dvd_mul_right n p) hdiv
  rcases (Nat.dvd_prime hp).mp hkdiv with rfl | rfl
  · exact (dvd_lcm_right n m).trans (by simp [hk])
  · have hle := hζ.lcm_totient_le_finrank hz
      (cyclotomic.irreducible_rat (Nat.lcm_pos (Nat.pos_of_ne_zero hn0) (Nat.pos_of_ne_zero hm)))
    exact False.elim (hdeg.not_ge (hk ▸ hle))

end IsPrimitiveRoot
