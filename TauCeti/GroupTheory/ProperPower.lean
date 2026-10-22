/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Proper powers in groups

A proper power is a power with a natural exponent at least two. In particular the identity is
a proper power; the predicate makes no exception for it, so an element that is not a proper
power is nontrivial. Homomorphisms preserve proper powers; in particular conjugation preserves
and reflects them.

Conjugation, inversion, and positive powers transport maximal-root decompositions,
specified by a nonzero exponent and a root that is not a proper power.
-/

public section

namespace Group

/-- An element of a group is a proper power if it has a root with exponent at least two. -/
def IsProperPower {G : Type*} [Group G] (x : G) : Prop :=
  ∃ (y : G) (n : ℕ), 2 ≤ n ∧ x = y ^ n

/-- The root-and-exponent characterization of a proper power. -/
theorem isProperPower_iff {G : Type*} [Group G] {x : G} :
    IsProperPower x ↔ ∃ (y : G) (n : ℕ), 2 ≤ n ∧ x = y ^ n :=
  Iff.rfl

namespace IsProperPower

/-- Homomorphisms preserve proper powers. -/
theorem map {G H F : Type*} [Group G] [Group H] [FunLike F G H] [MonoidHomClass F G H]
    (f : F) {x : G}
    (hx : IsProperPower x) : IsProperPower (f x) := by
  obtain ⟨y, n, hn, rfl⟩ := hx
  exact ⟨f y, n, hn, by simp⟩

/-- The identity is a proper power in every group. -/
@[simp] theorem one {G : Type*} [Group G] : IsProperPower (1 : G) :=
  ⟨1, 2, Nat.le_refl 2, by simp⟩

end IsProperPower

/-- Every natural power with exponent at least two is a proper power. -/
theorem isProperPower_pow {G : Type*} [Group G] (y : G) {n : ℕ} (hn : 2 ≤ n) :
    IsProperPower (y ^ n) :=
  ⟨y, n, hn, rfl⟩

/-- An integer power with absolute exponent at least two is a proper power. -/
theorem isProperPower_zpow {G : Type*} [Group G] (y : G) {n : ℤ}
    (hn : 2 ≤ n.natAbs) : IsProperPower (y ^ n) := by
  rcases Int.natAbs_eq n with h | h
  · rw [h, zpow_natCast]
    exact isProperPower_pow y hn
  · rw [h, zpow_neg, zpow_natCast]
    simpa only [inv_pow] using isProperPower_pow y⁻¹ hn

/-- An element that is not a proper power is not the identity. -/
theorem ne_one_of_not_isProperPower {G : Type*} [Group G] {x : G} (hx : ¬IsProperPower x) :
    x ≠ 1 := by
  rintro rfl
  exact hx .one

/-- If `y ^ n` is not a proper power, then `n = 1` or `n = -1`. The exponent `0` is excluded
because `y ^ 0 = 1` is a proper power. -/
theorem natAbs_eq_one_of_not_isProperPower_zpow {G : Type*} [Group G] {y : G} {n : ℤ}
    (h : ¬IsProperPower (y ^ n)) : n.natAbs = 1 := by
  have h0 : n ≠ 0 := by
    rintro rfl
    exact h (by simp)
  by_contra h1
  exact h (isProperPower_zpow y (by omega))

/-- An element is a proper power exactly when its inverse is. -/
@[simp] theorem isProperPower_inv {G : Type*} [Group G] {x : G} :
    IsProperPower x⁻¹ ↔ IsProperPower x := by
  constructor
  · rintro ⟨y, n, hn, heq⟩
    refine ⟨y⁻¹, n, hn, ?_⟩
    simpa only [inv_inv, inv_pow] using congrArg (fun z : G => z⁻¹) heq
  · rintro ⟨y, n, hn, heq⟩
    refine ⟨y⁻¹, n, hn, ?_⟩
    simpa only [inv_pow] using congrArg (fun z : G => z⁻¹) heq

/-- The generator of the additive integers, viewed multiplicatively, is not a proper power. -/
theorem not_isProperPower_ofAdd_one :
    ¬ IsProperPower (Multiplicative.ofAdd (1 : ℤ)) := by
  intro h
  obtain ⟨y, n, hn, heq⟩ := isProperPower_iff.mp h
  have hdiv : (n : ℤ) ∣ 1 := by
    refine ⟨y.toAdd, ?_⟩
    simpa using congrArg Multiplicative.toAdd heq
  have hdiv' : n ∣ 1 := Int.natCast_dvd_natCast.mp hdiv
  have hle : n ≤ 1 := Nat.le_of_dvd (by omega) hdiv'
  omega

end Group

namespace MulEquiv

/-- A multiplicative equivalence preserves and reflects proper powers. -/
@[simp] theorem isProperPower_map_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {x : G} : Group.IsProperPower (e x) ↔ Group.IsProperPower x := by
  constructor
  · intro h
    simpa using Group.IsProperPower.map e.symm h
  · exact Group.IsProperPower.map e

end MulEquiv

namespace Group

/-- Conjugation preserves and reflects proper powers. -/
@[simp] theorem isProperPower_conj_iff {G : Type*} [Group G] (g x : G) :
    IsProperPower (g * x * g⁻¹) ↔ IsProperPower x :=
  MulEquiv.isProperPower_map_iff (MulAut.conj g)

/-- Conjugation transports a maximal-root decomposition without changing its exponent. -/
theorem maximalRoot_conj {G : Type*} [Group G] {x r : G} {k : ℕ} (g : G)
    (hk : k ≠ 0) (hx : r ^ k = x) (hr : ¬IsProperPower r) :
    k ≠ 0 ∧ (g * r * g⁻¹) ^ k = g * x * g⁻¹ ∧ ¬IsProperPower (g * r * g⁻¹) := by
  refine ⟨hk, ?_, (isProperPower_conj_iff g r).not.2 hr⟩
  rw [conj_pow, hx]

/-- Inversion transports a maximal-root decomposition without changing its exponent. -/
theorem maximalRoot_inv {G : Type*} [Group G] {x r : G} {k : ℕ}
    (hk : k ≠ 0) (hx : r ^ k = x) (hr : ¬IsProperPower r) :
    k ≠ 0 ∧ (r⁻¹) ^ k = x⁻¹ ∧ ¬IsProperPower r⁻¹ := by
  refine ⟨hk, ?_, isProperPower_inv.not.2 hr⟩
  rw [inv_pow, hx]

/-- A positive power transports a maximal-root decomposition by multiplying the exponent. -/
theorem maximalRoot_pow {G : Type*} [Group G] {x r : G} {k m : ℕ}
    (hk : k ≠ 0) (hx : r ^ k = x) (hr : ¬IsProperPower r) (hm : m ≠ 0) :
    m * k ≠ 0 ∧ r ^ (m * k) = x ^ m ∧ ¬IsProperPower r := by
  refine ⟨Nat.mul_ne_zero hm hk, ?_, hr⟩
  rw [Nat.mul_comm m k, pow_mul, hx]

/-- A generator of the centralizer of a nontrivial element in a torsion-free group is not a
proper power. -/
theorem not_isProperPower_of_zpowers_eq_centralizer {G : Type*} [Group G]
    [IsMulTorsionFree G] {x r : G} (hx : x ≠ 1)
    (hr : Subgroup.zpowers r = Subgroup.centralizer {x}) : ¬IsProperPower r := by
  rw [isProperPower_iff]
  rintro ⟨s, n, hn, rfl⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1
    (hr ▸ Subgroup.mem_centralizer_singleton_iff.2 rfl : x ∈ _)
  have hs : s ∈ Subgroup.zpowers (s ^ n) :=
    hr ▸ Subgroup.mem_centralizer_singleton_iff.2 ((Commute.self_pow s n).zpow_right m).eq
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hx
  have hn1 : n = 1 := by
    simpa only [orderOf_eq_zero (not_isOfFinOrder_of_isMulTorsionFree hs1),
      Nat.gcd_zero_right] using mem_zpowers_pow_iff.mp hs
  omega

end Group
