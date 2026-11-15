/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.RingTheory.IntegralDomain

/-!
# Nonzero elements of a field with a nontrivial power

A field with more than `k + 1` elements has a nonzero element whose `k`-th power is not one, for
every positive `k`: the field is finite, its unit group is cyclic of order `Nat.card F - 1 > k`,
and a generator has order larger than `k`. For `k = 2` and fields with at least four elements this
is the input to the perfectness of the special linear groups in rank two.

Over a field of order `q ^ 2`, any ring endomorphism acting as `a ↦ a ^ q` is an involution, every
`m < q` admits a nonzero element with `a ^ m ≠ a ^ q`, and subtracting a non-fixed element from its
image produces a nonzero skew-trace element `d + σ d = 0`.

## Main results

* `TauCeti.FiniteField.exists_ne_zero_pow_ne_one`: a field with more than `k + 1` elements has a
  nonzero element `a` with `a ^ k ≠ 1`.
* `TauCeti.FiniteField.exists_ne_zero_pow_ne_pow`: for `m < n`, a field with more than
  `n - m + 1` elements has a nonzero element `a` with `a ^ m ≠ a ^ n`.
* `TauCeti.FiniteField.involutive_of_natCard_eq_sq`: in a field of order `q ^ 2`, any ring
  endomorphism acting as `a ↦ a ^ q` is an involution.
* `TauCeti.FiniteField.exists_ne_zero_pow_ne_pow_of_natCard_eq_sq`: in a field of order `q ^ 2`,
  for every `m < q`, some nonzero element `a` satisfies `a ^ m ≠ a ^ q`.
* `TauCeti.FiniteField.exists_ne_zero_add_map_eq_zero_of_natCard_eq_sq`: in a field of order
  `q ^ 2`, any ring endomorphism acting as `a ↦ a ^ q` admits a nonzero `d` with `d + σ d = 0`.
-/

public section

namespace TauCeti.FiniteField

variable {F : Type*} [Field F]

/-- A field with more than `k + 1` elements has a nonzero element whose `k`-th power is not one,
for every positive `k`. Such a field is finite with a cyclic unit group of order larger than `k`,
so this is `exists_pow_ne_one_of_isCyclic`. -/
theorem exists_ne_zero_pow_ne_one {k : ℕ} (hk : k ≠ 0) (hF : k + 1 < Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ k ≠ 1 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨a, ha⟩ := exists_pow_ne_one_of_isCyclic (G := Fˣ) hk
    (by rw [Nat.card_eq_card_units_add_one F] at hF; omega)
  exact ⟨a, a.ne_zero, fun h ↦ ha (Units.ext <| by simpa using h)⟩

/-- In a field with more than `n - m + 1` elements, for `m < n`, some nonzero element has distinct
`m`-th and `n`-th powers. -/
theorem exists_ne_zero_pow_ne_pow {m n : ℕ} (hmn : m < n) (hF : n - m + 1 < Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ m ≠ a ^ n := by
  obtain ⟨a, ha0, ha⟩ := exists_ne_zero_pow_ne_one (Nat.sub_ne_zero_of_lt hmn) hF
  refine ⟨a, ha0, fun heq ↦ ha ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero m ha0)
  rw [← pow_add, Nat.add_sub_cancel' hmn.le, mul_one, heq]

/-- In a field of order `q ^ 2`, any ring endomorphism acting as `a ↦ a ^ q` is an involution. -/
theorem involutive_of_natCard_eq_sq {σ : F →+* F} {q : ℕ}
    (hF : Nat.card F = q ^ 2) (hσ : ∀ a, σ a = a ^ q) :
    Function.Involutive σ := by
  have hq : q ≠ 0 := fun h ↦ by simpa [h] using hσ 0
  have : Finite F := Nat.finite_of_card_ne_zero (hF ▸ pow_ne_zero 2 hq)
  let _ := Fintype.ofFinite F
  intro a
  rw [hσ, hσ, ← pow_mul, ← sq, ← hF, Nat.card_eq_fintype_card]
  exact _root_.FiniteField.pow_card a

/-- In a field of order `q ^ 2`, for every `m < q`, some nonzero element has distinct `m`-th and
`q`-th powers. -/
theorem exists_ne_zero_pow_ne_pow_of_natCard_eq_sq {m q : ℕ} (hmq : m < q)
    (hF : Nat.card F = q ^ 2) :
    ∃ a : F, a ≠ 0 ∧ a ^ m ≠ a ^ q := by
  have : Finite F := Nat.finite_of_card_ne_zero (hF ▸ pow_ne_zero 2 (by omega))
  have h1q : 1 < q := (Nat.one_lt_pow_iff two_ne_zero).mp (hF ▸ Finite.one_lt_card)
  have hqq : 2 * q ≤ q ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right q h1q
  exact exists_ne_zero_pow_ne_pow hmq (by omega)

/-- In a field of order `q ^ 2`, any ring endomorphism acting as `a ↦ a ^ q` admits a nonzero
element `d` with `d + σ d = 0`. -/
theorem exists_ne_zero_add_map_eq_zero_of_natCard_eq_sq {σ : F →+* F} {q : ℕ}
    (hF : Nat.card F = q ^ 2) (hσ : ∀ a, σ a = a ^ q) :
    ∃ d : F, d ≠ 0 ∧ d + σ d = 0 := by
  have hq : q ≠ 0 := fun h ↦ by simpa [h] using hσ 0
  have : Finite F := Nat.finite_of_card_ne_zero (hF ▸ pow_ne_zero 2 hq)
  have h1q : 1 < q := (Nat.one_lt_pow_iff two_ne_zero).mp (hF ▸ Finite.one_lt_card)
  obtain ⟨b, -, hb⟩ := exists_ne_zero_pow_ne_pow_of_natCard_eq_sq (F := F) h1q hF
  have hne : b ≠ σ b := by rwa [pow_one, ← hσ b] at hb
  refine ⟨b - σ b, sub_ne_zero.mpr hne, ?_⟩
  rw [map_sub, involutive_of_natCard_eq_sq hF hσ b, sub_add_sub_cancel, sub_self]

end TauCeti.FiniteField
