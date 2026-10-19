/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Int.GCD

/-!
# Basic facts about local rings

This file records basic facts about possibly noncommutative local rings. Their only idempotents
are `0` and `1`; this fact applies to endomorphism rings in the Krull-Schmidt theorem. In
characteristic two the idempotent criterion identifies the zeros of the Artin–Schreier map
`t ↦ t² + t`, without a finiteness assumption.

## Main results

* `IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing`: an idempotent of a local ring is `0`
  or `1`.
* `TauCeti.IsLocalRing.isDedekindFiniteMonoid`: a local ring is Dedekind-finite.
* `TauCeti.isUnit_add_of_isUnit_of_not_isUnit`: adding a nonunit to a unit in a local ring
  yields a unit.
* `TauCeti.isUnit_sub_of_not_isUnit_of_isUnit`: subtracting a unit from a nonunit in a local ring
  yields a unit.
* `TauCeti.IsLocalRing.sq_add_self_eq_zero_iff`: in characteristic two, `t² + t = 0` exactly
  when `t = 0` or `t = 1`.
* `Nat.Coprime.isUnit_natCast`: if a natural number is not a unit, every coprime natural
  number is a unit.
* `IsCoprime.isUnit_or_isUnit`: of two coprime elements of a commutative local semiring, one is a
  unit.
* `IsLocalRing.sub_one_mem_maximalIdeal_of_card_residueField_eq_two`: when the residue field has
  two elements, every unit is congruent to `1` modulo the maximal ideal, and
  `IsLocalRing.two_mem_maximalIdeal_of_card_residueField_eq_two`: `2` lies in the maximal ideal.
-/

public section

/-- An idempotent of a possibly noncommutative local ring is `0` or `1`. -/
theorem IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing {R : Type*} [Ring R] [IsLocalRing R]
    {a : R} (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  -- One of `a` and `1 - a` is a unit, and an idempotent unit is `1`.
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha)
  · exact Or.inl (sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha.one_sub))

namespace TauCeti

/-- A local ring is Dedekind-finite: a left inverse is also a right inverse. -/
instance IsLocalRing.isDedekindFiniteMonoid {R : Type*} [Ring R] [IsLocalRing R] :
    IsDedekindFiniteMonoid R where
  mul_eq_one_symm := by
    intro p q hpq
    have he : IsIdempotentElem (q * p) := by
      rw [IsIdempotentElem]
      calc
        (q * p) * (q * p) = q * (p * q) * p := by simp only [mul_assoc]
        _ = q * p := by rw [hpq, mul_one]
    rcases IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing he with h0 | h1
    · exfalso
      exact one_ne_zero (by
        simpa only [mul_assoc, hpq, mul_one, mul_zero, zero_mul] using
          congrArg (fun a ↦ p * a * q) h0)
    · exact h1

/-- In a local ring, adding a nonunit to a unit yields a unit. -/
theorem isUnit_add_of_isUnit_of_not_isUnit {R : Type*} [Ring R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : ¬ IsUnit b) : IsUnit (a + b) := by
  by_contra hab
  have hsum := IsLocalRing.nonunits_add (mem_nonunits_iff.mpr hab)
    (mem_nonunits_iff.mpr ((IsUnit.neg_iff b).not.mpr hb))
  have ha' : a ∈ nonunits R := by
    simpa only [add_assoc, add_neg_cancel, add_zero] using hsum
  exact (mem_nonunits_iff.mp ha') ha

/-- In a local ring, subtracting a unit from a nonunit yields a unit. -/
theorem isUnit_sub_of_not_isUnit_of_isUnit {R : Type*} [Ring R] [IsLocalRing R] {a b : R}
    (ha : ¬ IsUnit a) (hb : IsUnit b) : IsUnit (a - b) := by
  have h := isUnit_add_of_isUnit_of_not_isUnit hb
    ((IsUnit.neg_iff a).not.mpr ha)
  simpa only [sub_eq_add_neg, neg_add_rev, neg_neg] using h.neg

/-- Over a local ring of characteristic two, the zeros of `t ↦ t² + t` are `0` and `1`. -/
@[simp]
theorem IsLocalRing.sq_add_self_eq_zero_iff {R : Type*} [Ring R] [IsLocalRing R] [CharP R 2]
    (t : R) : t ^ 2 + t = 0 ↔ t = 0 ∨ t = 1 := by
  rw [CharTwo.add_eq_zero, pow_two]
  constructor
  · exact IsIdempotentElem.eq_zero_or_eq_one_of_isLocalRing
  · rintro (rfl | rfl) <;> simp

end TauCeti

/-- Of two coprime elements of a commutative local semiring, one is a unit: a relation
`u * a + v * b = 1` makes one of the two summands a unit. -/
theorem IsCoprime.isUnit_or_isUnit {R : Type*} [CommSemiring R] [IsLocalRing R] {a b : R}
    (h : IsCoprime a b) : IsUnit a ∨ IsUnit b := by
  obtain ⟨u, v, huv⟩ := h
  exact (IsLocalRing.isUnit_or_isUnit_of_add_one huv).imp isUnit_of_mul_isUnit_right
    isUnit_of_mul_isUnit_right

/-- In a possibly noncommutative local ring, a natural number coprime to a nonunit natural
number is a unit. -/
theorem Nat.Coprime.isUnit_natCast {R : Type*} [Ring R] [IsLocalRing R] {m n : ℕ}
    (h : m.Coprime n) (hn : ¬IsUnit (n : R)) : IsUnit (m : R) := by
  have hab := Nat.gcd_eq_gcd_ab m n
  rw [h.gcd_eq_one, Nat.cast_one] at hab
  have hab' : (m : R) * (m.gcdA n : R) + n * (m.gcdB n : R) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → R) hab.symm
  exact ((IsLocalRing.isUnit_or_isUnit_of_add_one hab').imp isUnit_of_mul_isUnit_left
    isUnit_of_mul_isUnit_left).resolve_right hn

/-- When the residue field of a commutative local ring has two elements, every unit is congruent
to `1` modulo the maximal ideal: its residue is a nonzero element of `𝔽₂`. -/
theorem IsLocalRing.sub_one_mem_maximalIdeal_of_card_residueField_eq_two {R : Type*} [CommRing R]
    [IsLocalRing R] (hR : Nat.card (IsLocalRing.ResidueField R) = 2) {u : R} (hu : IsUnit u) :
    u - 1 ∈ IsLocalRing.maximalIdeal R := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : IsLocalRing.ResidueField R)).mp hR
  rw [hy _ ((IsLocalRing.residue_ne_zero_iff_isUnit u).mpr hu), hy 1 one_ne_zero]

/-- When the residue field of a commutative local ring has two elements, `2` lies in the maximal
ideal: the residue field has characteristic two. -/
theorem IsLocalRing.two_mem_maximalIdeal_of_card_residueField_eq_two {R : Type*} [CommRing R]
    [IsLocalRing R] (hR : Nat.card (IsLocalRing.ResidueField R) = 2) :
    (2 : R) ∈ IsLocalRing.maximalIdeal R := by
  have h := (IsLocalRing.maximalIdeal R).neg_mem
    (IsLocalRing.sub_one_mem_maximalIdeal_of_card_residueField_eq_two hR isUnit_one.neg)
  rwa [show -(-1 - 1 : R) = 2 by ring] at h
