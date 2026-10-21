/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.Order.Lattice.Nat

/-!
# Bounds on root exponents in a free group

The cyclically reduced part of a nonidentity word has positive length. Consequently,
the exponent of any positive power representing a nonidentity element is bounded by
the length of that element's reduced word. This gives a root with greatest exponent,
the first step in constructing the intrinsic maximal root of a free-group element.

The length calculation is in `TauCeti.GroupTheory.FreeGroup.CyclicallyReduced`.
-/

public section

namespace FreeGroup

variable {α : Type*}

section

variable [DecidableEq α]

/-- The exponent of a power representing a nonidentity element cannot exceed its
reduced-word length. -/
@[to_additive]
theorem le_norm_of_pow_eq {x y : FreeGroup α} {n : ℕ}
    (hx : x ≠ 1) (hpow : y ^ n = x) : n ≤ norm x := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hpow
    exact hx hpow.symm
  have hy : y ≠ 1 := by
    intro h
    rw [h, one_pow] at hpow
    exact hx hpow.symm
  have hl : 0 < (reduceCyclically y.toWord).length :=
    List.length_pos_iff_ne_nil.mpr (by simpa using hy)
  rw [← hpow, norm_pow_eq y hn]
  calc
    n = n * 1 := by omega
    _ ≤ n * (reduceCyclically y.toWord).length := Nat.mul_le_mul_left n hl
    _ ≤ 2 * (reduceCyclically.conjugator y.toWord).length +
      n * (reduceCyclically y.toWord).length := Nat.le_add_left _ _

end

/-- A nonidentity free-group element has a root whose exponent is greatest among
all of its positive root exponents. This root is not a positive proper power. -/
@[to_additive]
theorem exists_root_maximal_exponent {x : FreeGroup α} (hx : x ≠ 1) :
    ∃ r k, 0 < k ∧ r ^ k = x ∧
      (∀ (y : FreeGroup α) (n : ℕ), y ^ n = x → n ≤ k) ∧
      ∀ (y : FreeGroup α) (m : ℕ), 1 < m → y ^ m ≠ r := by
  classical
  let s : Set ℕ := {n | ∃ y : FreeGroup α, y ^ n = x}
  have hbdd : BddAbove s := ⟨norm x, by
    intro n hn
    obtain ⟨y, hy⟩ := hn
    exact le_norm_of_pow_eq hx hy⟩
  have hne : s.Nonempty := ⟨1, by simp [s]⟩
  let k := sSup s
  have hk : k ∈ s := Nat.sSup_mem hne hbdd
  obtain ⟨r, hr⟩ := hk
  have hk0 : 0 < k := by
    by_contra h
    have hkz : k = 0 := by omega
    rw [hkz, pow_zero] at hr
    exact hx hr.symm
  have hmax : ∀ (y : FreeGroup α) (n : ℕ), y ^ n = x → n ≤ k := by
    intro y n hy
    exact le_csSup hbdd ⟨y, hy⟩
  refine ⟨r, k, hk0, hr, hmax, ?_⟩
  intro y m hm hpower
  have hroot : y ^ (m * k) = x := by
    rw [pow_mul, hpower, hr]
  have hlt : k < m * k := by
    simpa using Nat.mul_lt_mul_of_pos_right hm hk0
  exact (hmax y (m * k) hroot).not_gt hlt

end FreeGroup
