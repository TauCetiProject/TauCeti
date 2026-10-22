/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Proper powers in groups

A proper power is a power with a natural exponent at least two. In particular the identity is
a proper power; the predicate makes no exception for it. Homomorphisms preserve proper powers.
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
