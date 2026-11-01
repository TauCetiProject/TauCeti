/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfection

/-!
# Coordinates of the perfection of a monoid

For a commutative monoid `M`, Mathlib's `Perfection M p` is the monoid of compatible systems
`(xₙ)ₙ` with `xₙ₊₁ ^ p = xₙ`. If every element of `M` has a `p`-th root, every element of `M`
starts such a system, and more generally every coordinate map `Perfection M p → M` is surjective.
Mathlib proves this for rings of characteristic `p` with surjective Frobenius
(`Perfection.coeff_surjective`); the statement here needs no ring structure, and applies for
instance to the multiplicative monoid of an algebraically closed field of any characteristic.

## Main results

* `Perfection.coeffMonoidHom_surjective`: if `x ↦ x ^ p` is surjective on `M`, so is every
  coordinate map `Perfection.coeffMonoidHom M p n`.
* `TauCeti.dvd_of_compatible_roots`: in a compatible root sequence, later roots divide earlier ones.
-/

public section

namespace Perfection

variable {M : Type*} [CommMonoid M] {p : ℕ}

/-- **If every element of `M` has a `p`-th root, every coordinate of `Perfection M p` is
surjective.** -/
theorem coeffMonoidHom_surjective (h : Function.Surjective fun x : M ↦ x ^ p) (n : ℕ) :
    Function.Surjective (coeffMonoidHom M p n) := by
  intro x
  -- iterating a choice of `p`-th roots starting at `x` gives a compatible system `f` with zeroth
  -- term `x`, and raising `f` to the `p ^ n`-th power moves `x` to the `n`-th term
  choose r hr using h
  let f : Perfection M p := ⟨fun k ↦ r^[k] x, fun k ↦ by
    simp only [Function.iterate_succ_apply', hr]⟩
  refine ⟨f ^ p ^ n, ?_⟩
  have hf := coeffMonoidHom_pow_p_pow f 0 n
  rw [zero_add] at hf
  exact hf.trans (coeffMonoidHom_mk _ _ 0)

end Perfection

namespace TauCeti

section CommMonoid

variable {R : Type*} [CommMonoid R] {p : ℕ} {r : ℕ → R}

/-- In a compatible root sequence, every later root divides every earlier root. -/
theorem dvd_of_compatible_roots (hr : ∀ n, r (n + 1) ^ p = r n)
    {m n : ℕ} (hmn : m ≤ n) : r n ∣ r m := by
  by_cases hp : p = 0
  · have hone (n : ℕ) : r n = 1 := by
      simpa only [hp, pow_zero] using (hr n).symm
    simp only [hone, dvd_refl]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hpow : r (m + k) ^ p ^ k = r m := by
    simpa only [Perfection.coeffMonoidHom_mk] using
      Perfection.coeffMonoidHom_pow_p_pow' (⟨r, hr⟩ : Perfection R p) m k
  rw [← hpow]
  exact dvd_pow_self _ (pow_ne_zero k hp)

end CommMonoid

end TauCeti
