/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Order.SuccPred.Nat

/-!
# Proper powers in monoids

A proper power is a power with a natural exponent at least two. In particular the identity is
a proper power; the predicate makes no exception for it, so an element that is not a proper
power is nontrivial. Homomorphisms preserve proper powers, and conjugation by a unit preserves
and reflects them (`IsConj.isProperPower_iff`).

An element whose root exponents are bounded has a maximal-root decomposition: a nonzero
exponent and a root that is not a proper power, of greatest exponent
(`Monoid.exists_maximalRoot_of_bddAbove`).

The results on cyclic subgroups and centralizers are in `TauCeti.GroupTheory.ProperPower`.
-/

public section

namespace Monoid

section Monoid

variable {M : Type*} [Monoid M]

/-- An element of a monoid is a proper power if it has a root with exponent at least two. -/
def IsProperPower (x : M) : Prop :=
  ∃ (y : M) (n : ℕ), 2 ≤ n ∧ x = y ^ n

/-- The root-and-exponent characterization of a proper power. -/
theorem isProperPower_iff {x : M} :
    IsProperPower x ↔ ∃ (y : M) (n : ℕ), 2 ≤ n ∧ x = y ^ n :=
  Iff.rfl

namespace IsProperPower

/-- Homomorphisms preserve proper powers. -/
theorem map {N F : Type*} [Monoid N] [FunLike F M N] [MonoidHomClass F M N] (f : F) {x : M}
    (hx : IsProperPower x) : IsProperPower (f x) := by
  obtain ⟨y, n, hn, rfl⟩ := hx
  exact ⟨f y, n, hn, by simp⟩

/-- The identity is a proper power in every monoid. -/
@[simp] theorem one : IsProperPower (1 : M) :=
  ⟨1, 2, Nat.le_refl 2, by simp⟩

end IsProperPower

/-- Every natural power with exponent at least two is a proper power. -/
theorem isProperPower_pow (y : M) {n : ℕ} (hn : 2 ≤ n) : IsProperPower (y ^ n) :=
  ⟨y, n, hn, rfl⟩

/-- An element that is not a proper power is not the identity. -/
theorem ne_one_of_not_isProperPower {x : M} (hx : ¬IsProperPower x) : x ≠ 1 :=
  fun h => hx (h ▸ .one)

/-- An element `x` whose root exponents `{n | ∃ y, y ^ n = x}` are bounded above has a
maximal-root decomposition `r ^ k = x` in which `k` is the greatest root exponent of `x`. The root
`r` is not a proper power, since a root of `r` with exponent `m ≥ 2` would be a root of `x` with
exponent `m * k > k`. The hypothesis forces `x ≠ 1`, as every natural number is a root exponent
of the identity. -/
theorem exists_maximalRoot_of_bddAbove {x : M}
    (hbdd : BddAbove {n : ℕ | ∃ y : M, y ^ n = x}) :
    ∃ (r : M) (k : ℕ), k ≠ 0 ∧ r ^ k = x ∧ ¬IsProperPower r ∧
      ∀ (y : M) (n : ℕ), y ^ n = x → n ≤ k := by
  obtain ⟨k, ⟨r, hr⟩, hmax⟩ := hbdd.exists_isGreatest_of_nonempty ⟨1, x, pow_one x⟩
  have hk : k ≠ 0 := Nat.one_le_iff_ne_zero.1 (hmax ⟨x, pow_one x⟩)
  refine ⟨r, k, hk, hr, ?_, fun y n hy => hmax ⟨y, hy⟩⟩
  -- A root `y` of `r` with exponent `m ≥ 2` would be a root of `x` with exponent `m * k > k`.
  rintro ⟨y, m, hm, rfl⟩
  exact (hmax ⟨y, (pow_mul y m k).trans hr⟩).not_gt
    ((Nat.lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hk)).2 (by omega))

end Monoid

section DivisionMonoid

variable {G : Type*} [DivisionMonoid G]

/-- An element is a proper power exactly when its inverse is. -/
@[simp] theorem isProperPower_inv {x : G} : IsProperPower x⁻¹ ↔ IsProperPower x := by
  -- Inverting a root of `x` gives a root of `x⁻¹` with the same exponent.
  have key (x : G) : IsProperPower x → IsProperPower x⁻¹ := by
    rintro ⟨y, n, hn, rfl⟩
    exact ⟨y⁻¹, n, hn, (inv_pow y n).symm⟩
  exact ⟨fun h => inv_inv x ▸ key _ h, key x⟩

/-- An integer power with absolute exponent at least two is a proper power. -/
theorem isProperPower_zpow (y : G) {n : ℤ} (hn : 2 ≤ n.natAbs) : IsProperPower (y ^ n) := by
  -- `y ^ n` is `y ^ n.natAbs` or its inverse, and `isProperPower_inv` handles the inverse.
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n <;>
    simpa using isProperPower_pow y (n := m) (by simpa using hn)

/-- If `y ^ n` is not a proper power, then `n = 1` or `n = -1`. The exponent `0` is excluded
because `y ^ 0 = 1` is a proper power. -/
theorem natAbs_eq_one_of_not_isProperPower_zpow {y : G} {n : ℤ}
    (h : ¬IsProperPower (y ^ n)) : n.natAbs = 1 := by
  have h0 : n ≠ 0 := fun hn => h (by simp [hn])
  by_contra h1
  exact h (isProperPower_zpow y (by omega))

end DivisionMonoid

end Monoid

namespace MulEquiv

/-- A multiplicative equivalence preserves and reflects proper powers. -/
@[simp] theorem isProperPower_map_iff {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N) {x : M} :
    Monoid.IsProperPower (e x) ↔ Monoid.IsProperPower x :=
  ⟨fun h => by simpa using h.map e.symm, .map e⟩

end MulEquiv

open Monoid in
/-- Conjugation by a unit preserves and reflects proper powers. -/
theorem IsConj.isProperPower_iff {M : Type*} [Monoid M] {x y : M} (h : IsConj x y) :
    IsProperPower x ↔ IsProperPower y := by
  -- Conjugating a root `r` of `x` by the unit `c` gives a root of `y` with the same exponent.
  have key {x y : M} (h : IsConj x y) : IsProperPower x → IsProperPower y := by
    rintro ⟨r, n, hn, rfl⟩
    obtain ⟨c, hc⟩ := h
    have hr : SemiconjBy (c : M) r (c * r * ↑c⁻¹) := by
      simp [SemiconjBy, mul_assoc]
    exact ⟨_, n, hn, (Units.mul_left_inj c).1 (hc.eq.symm.trans (hr.pow_right n).eq)⟩
  exact ⟨key h, key h.symm⟩

namespace Monoid

/-- Conjugation preserves and reflects proper powers. -/
@[simp] theorem isProperPower_conj_iff {G : Type*} [Group G] (g x : G) :
    IsProperPower (g * x * g⁻¹) ↔ IsProperPower x :=
  (isConj_iff.2 ⟨g, rfl⟩).isProperPower_iff.symm

end Monoid
