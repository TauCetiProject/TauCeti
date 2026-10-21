/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Order.Group.Unbundled.Int

/-!
# Proper powers

An element `x` of a monoid is a *proper power* when `x = y ^ n` for some `y` and some natural
number `n ≥ 2`. In a free group the elements that are not proper powers are the maximal roots:
every nontrivial element is a positive power of exactly one of them, and they generate the
centralizers of nontrivial elements. Periods of periodic words are likewise cyclically reduced
words that are not proper powers.

The identity is always a proper power, since `1 = 1 ^ 2`. Hence an element that is not a proper
power is nontrivial, and statements about non-proper-powers treat the identity separately.

## Main definitions

* `Group.IsProperPower x`: `x = y ^ n` for some `y` and some `n ≥ 2`.

## Main results

* `Group.IsProperPower.map`: homomorphisms send proper powers to proper powers.
* `Group.isProperPower_map_iff`: multiplicative isomorphisms preserve and reflect proper powers;
  in particular so does conjugation (`Group.isProperPower_conj_iff`).
* `Group.isProperPower_zpow`: `y ^ n` is a proper power whenever `2 ≤ |n|`.
* `Group.natAbs_eq_one_of_not_isProperPower_zpow`: if `y ^ n` is not a proper power, then
  `n = ±1`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.4 (periods are cyclically reduced words that are not proper powers).
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually
  free groups: algorithmic problems*, Contemp. Math. 360 (2004), §5, proof of Lemma 21.
-/

public section

namespace Group

variable {M N F : Type*}

section Monoid

variable [Monoid M] [Monoid N]

/-- An element `x` of a monoid is a *proper power* if `x = y ^ n` for some `y` and some natural
number `n ≥ 2`. The identity is a proper power, as `1 = 1 ^ 2`. -/
def IsProperPower (x : M) : Prop :=
  ∃ y : M, ∃ n : ℕ, 2 ≤ n ∧ x = y ^ n

theorem isProperPower_iff {x : M} : IsProperPower x ↔ ∃ y : M, ∃ n : ℕ, 2 ≤ n ∧ x = y ^ n :=
  Iff.rfl

/-- `y ^ n` is a proper power for every natural number `n ≥ 2`. -/
theorem isProperPower_pow (y : M) {n : ℕ} (hn : 2 ≤ n) : IsProperPower (y ^ n) :=
  ⟨y, n, hn, rfl⟩

/-- The identity is a proper power: `1 = 1 ^ 2`. -/
@[simp]
theorem IsProperPower.one : IsProperPower (1 : M) :=
  ⟨1, 2, le_rfl, (one_pow 2).symm⟩

/-- An element that is not a proper power is not the identity. -/
theorem ne_one_of_not_isProperPower {x : M} (hx : ¬IsProperPower x) : x ≠ 1 := by
  rintro rfl
  exact hx .one

/-- A monoid homomorphism sends proper powers to proper powers. -/
theorem IsProperPower.map [FunLike F M N] [MonoidHomClass F M N] (f : F) {x : M}
    (hx : IsProperPower x) : IsProperPower (f x) := by
  obtain ⟨y, n, hn, rfl⟩ := hx
  exact ⟨f y, n, hn, map_pow f y n⟩

/-- A multiplicative isomorphism preserves and reflects proper powers. -/
@[simp]
theorem isProperPower_map_iff [EquivLike F M N] [MulEquivClass F M N] (f : F) {x : M} :
    IsProperPower (f x) ↔ IsProperPower x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map f⟩
  simpa using h.map (MulEquivClass.toMulEquiv f).symm

end Monoid

section DivisionMonoid

variable [DivisionMonoid M]

/-- The inverse of a proper power is a proper power. -/
theorem IsProperPower.inv {x : M} (hx : IsProperPower x) : IsProperPower x⁻¹ := by
  obtain ⟨y, n, hn, rfl⟩ := hx
  exact ⟨y⁻¹, n, hn, (inv_pow y n).symm⟩

@[simp]
theorem isProperPower_inv_iff {x : M} : IsProperPower x⁻¹ ↔ IsProperPower x :=
  ⟨fun h ↦ by simpa using h.inv, IsProperPower.inv⟩

/-- `y ^ n` is a proper power for every integer `n` with `2 ≤ |n|`. -/
theorem isProperPower_zpow (y : M) {n : ℤ} (hn : 2 ≤ |n|) : IsProperPower (y ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  all_goals rw [Int.abs_eq_natAbs] at hn
  · exact ⟨y, m, by omega, by simp⟩
  · exact ⟨y⁻¹, m, by omega, by simp [inv_pow]⟩

/-- If `y ^ n` is not a proper power, then `n = 1` or `n = -1`. The exponent `0` is excluded
because `y ^ 0 = 1` is a proper power. -/
theorem natAbs_eq_one_of_not_isProperPower_zpow {y : M} {n : ℤ} (h : ¬IsProperPower (y ^ n)) :
    n.natAbs = 1 := by
  have h0 : n ≠ 0 := by
    rintro rfl
    exact h (by simp)
  by_contra h1
  exact h (isProperPower_zpow y (by rw [Int.abs_eq_natAbs]; omega))

end DivisionMonoid

/-- Conjugation preserves and reflects proper powers. -/
@[simp]
theorem isProperPower_conj_iff [Group M] (g x : M) :
    IsProperPower (g * x * g⁻¹) ↔ IsProperPower x :=
  isProperPower_map_iff (MulAut.conj g)

end Group
