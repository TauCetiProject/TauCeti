/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Ring.Associated
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Squarefree elements, squares, and squarefree parts

This file records a few general facts about squarefree elements, squares, and rational squares
that Mathlib does not provide directly, used across the multiquadratic development.

* `Squarefree.not_isSquare`: a squarefree non-unit of a monoid is not a square (the converse of
  Mathlib's `IsUnit.squarefree`). It is phrased with `Squarefree` dot-notation, so a caller
  holding `ha : Squarefree a` and `hu : ¬ IsUnit a` can write `ha.not_isSquare hu`.
* `Squarefree.neg`: negation preserves squarefreeness in any ring with distributive negation.
* `not_isSquare_intCast_of_squarefree_of_ne_one`: a squarefree integer other than `1` is not a
  rational square.
* `isSquare_mul_sq_iff`: in a commutative group with zero, multiplying by a nonzero square does
  not change squareness — the statement that squareness depends only on the square class.
* `Int.exists_squarefree_mul_sq` and `Rat.exists_squarefree_int_mul_sq`: the **squarefree part**.
  Every nonzero integer, and every nonzero rational, is a squarefree *integer* times a nonzero
  square. Mathlib's `exists_sq_mul_squarefree` proves the underlying factorization in a unique
  factorization monoid; the integer statement here records a nonzero square factor and puts the
  factors in the orientation used by the rational square-class argument.
* `TauCeti.Int.not_four_dvd_of_squarefree` and
  `TauCeti.Int.emod_four_eq_two_or_three_of_squarefree`: the modulo-four restrictions on
  squarefree integers.
* `TauCeti.Int.emod_eight_eq_of_eq_mul_sq_of_not_four_dvd`: removing a square factor
  preserves residues modulo eight when the original integer is not divisible by four.
* `TauCeti.Int.emod_eight_eq_five_iff_exists_eq_mod_eight_eq_five_mul_sq` and
  `TauCeti.Int.exists_eq_mod_eight_eq_five_mul_sq_iff_exists_squarefree_mod_eight_eq_five_mul_sq`:
  membership in the rational square class of an integer congruent to five modulo eight can be
  tested on an integer squarefree part.
* `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_squarefree`: squarefreeness of *every* prime
  divisor of an `n > 2`, read in any ring, yields the single branch that Mathlib's
  `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt` splits into. This is the bridge from a
  uniform hypothesis, which a caller can usually establish without knowing `n`, to the sharp
  branch-dependent one that a proof consumes.
-/

public section

namespace TauCeti.Int

/-- A squarefree integer is not divisible by four. -/
theorem not_four_dvd_of_squarefree {n : ℤ} (hn : Squarefree n) : ¬ (4 : ℤ) ∣ n :=
  fun h => (Int.isUnit_iff.not.mpr (by decide)) (hn 2 (by simpa using h))

/-- A squarefree integer not congruent to one modulo four is congruent to two or three. -/
theorem emod_four_eq_two_or_three_of_squarefree {n : ℤ} (hn : Squarefree n)
    (h : n % 4 ≠ 1) : n % 4 = 2 ∨ n % 4 = 3 := by
  have := not_four_dvd_of_squarefree hn
  omega

end TauCeti.Int

/-- A squarefree non-unit of a monoid is not a square. -/
theorem Squarefree.not_isSquare {R : Type*} [Monoid R] {a : R}
    (ha : Squarefree a) (hu : ¬ IsUnit a) : ¬ IsSquare a := by
  rintro ⟨r, rfl⟩
  exact hu ((ha r dvd_rfl).mul (ha r dvd_rfl))

/-- Negation preserves squarefreeness in any monoid with distributive negation. -/
theorem Squarefree.neg {R : Type*} [Monoid R] [HasDistribNeg R] {n : R}
    (hn : Squarefree n) : Squarefree (-n) :=
  ((Associated.refl n).neg_left).squarefree_iff.mpr hn

/-- A squarefree integer other than `1` is not a rational square. -/
theorem not_isSquare_intCast_of_squarefree_of_ne_one {n : ℤ}
    (hsf : Squarefree n) (hne : n ≠ 1) : ¬ IsSquare ((n : ℤ) : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨a, ha⟩
  have hu : IsUnit a := hsf a (ha ▸ dvd_rfl)
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp_all

/-- **Squareness depends only on the square class.** Multiplying by the square of a nonzero
element does not change whether an element is a square. -/
theorem isSquare_mul_sq_iff {G₀ : Type*} [CommGroupWithZero G₀] {x y : G₀} (hy : y ≠ 0) :
    IsSquare (x * y ^ 2) ↔ IsSquare x := by
  refine ⟨fun h => ?_, fun h => h.mul (IsSquare.sq y)⟩
  have h' := h.mul (IsSquare.sq y⁻¹)
  rwa [mul_assoc, ← mul_pow, mul_inv_cancel₀ hy, one_pow, mul_one] at h'

/-- **The squarefree part of an integer.** Every nonzero integer is a squarefree integer times the
square of a nonzero integer. This specializes Mathlib's unique-factorization-monoid theorem
`exists_sq_mul_squarefree` to `ℤ`, makes the square factor's nonzeroness explicit, and reverses
the factor order to the form used below. -/
theorem Int.exists_squarefree_mul_sq {n : ℤ} (hn : n ≠ 0) :
    ∃ a b : ℤ, Squarefree a ∧ b ≠ 0 ∧ n = a * b ^ 2 := by
  obtain ⟨b, a, hab, ha⟩ := exists_sq_mul_squarefree n
  refine ⟨a, b, ha, ?_, ?_⟩
  · intro hb
    apply hn
    simpa [hb] using hab.symm
  · calc
      n = b ^ 2 * a := hab.symm
      _ = a * b ^ 2 := mul_comm _ _

/-- **The squarefree part of a rational number.** Every nonzero rational is a squarefree *integer*
times the square of a nonzero rational: its square class is represented by a squarefree integer.
This is what lets a square-class argument over `ℚ` work with squarefree integer radicands. -/
theorem Rat.exists_squarefree_int_mul_sq {q : ℚ} (hq : q ≠ 0) :
    ∃ (a : ℤ) (c : ℚ), Squarefree a ∧ c ≠ 0 ∧ q = a * c ^ 2 := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Int.exists_squarefree_mul_sq (n := q.num * (q.den : ℤ))
      (mul_ne_zero (Rat.num_ne_zero.mpr hq) (by exact_mod_cast q.den_ne_zero))
  refine ⟨a, (b : ℚ) / (q.den : ℚ), ha, div_ne_zero (by exact_mod_cast hb) hden, ?_⟩
  have habQ : (q.num : ℚ) * (q.den : ℚ) = (a : ℚ) * (b : ℚ) ^ 2 := by exact_mod_cast hab
  have hnum : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hden).mp (Rat.num_div_den q)
  rw [hnum] at habQ
  field_simp
  linear_combination habQ

namespace TauCeti.Int

/-- Removing an integer square factor preserves the residue modulo eight when the original
integer is not divisible by four. -/
theorem emod_eight_eq_of_eq_mul_sq_of_not_four_dvd {n s b : ℤ} (h : n = s * b ^ 2)
    (hn : ¬ (4 : ℤ) ∣ n) : n % 8 = s % 8 := by
  have hb : ¬ (2 : ℤ) ∣ b := by
    rintro ⟨k, rfl⟩
    apply hn
    refine ⟨s * k ^ 2, ?_⟩
    rw [h]
    ring
  have hsq : b ^ 2 % 8 = 1 := by
    have hodd : Odd b := Int.not_even_iff_odd.mp (fun h => hb h.two_dvd)
    have := Int.dvd_iff_emod_eq_zero.mp (Int.eight_dvd_sq_sub_one_of_odd hodd)
    omega
  rw [h, Int.mul_emod, hsq, mul_one, Int.emod_emod]

/-- For a squarefree integer, being in the rational square class of an integer congruent to
five modulo eight is equivalent to being congruent to five modulo eight itself. -/
theorem emod_eight_eq_five_iff_exists_eq_mod_eight_eq_five_mul_sq {n : ℤ} (hn : Squarefree n) :
    n % 8 = 5 ↔ ∃ (c : ℤ) (q : ℚ), c % 8 = 5 ∧ q ≠ 0 ∧ (n : ℚ) = c * q ^ 2 := by
  refine ⟨fun h => ⟨n, 1, h, one_ne_zero, by simp⟩, ?_⟩
  rintro ⟨c, q, hc, -, h⟩
  have hsq : IsSquare (n * c) := Rat.isSquare_intCast_iff.mp (by
    refine ⟨(c : ℚ) * q, ?_⟩
    push_cast
    rw [h]
    ring)
  obtain ⟨z, hz⟩ := hsq
  obtain ⟨e, he⟩ : n ∣ z := (hn.dvd_pow_iff_dvd two_ne_zero).mp ⟨c, by
    simpa [sq] using hz.symm⟩
  have hce : c = n * e ^ 2 := by
    rw [he] at hz
    apply mul_left_cancel₀ hn.ne_zero
    linear_combination hz
  have hmod : c % 8 = (n % 8 * ((e % 8) ^ 2 % 8)) % 8 := by
    simp only [sq]
    rw [hce, sq, Int.mul_emod, Int.mul_emod e e]
  have hemod := Int.emod_nonneg e (by decide : (8 : ℤ) ≠ 0)
  have helt := Int.emod_lt_of_pos e (by decide : (0 : ℤ) < 8)
  interval_cases e % 8 <;> norm_num at hmod <;> omega

/-- An integer lies in the rational square class of an integer congruent to five modulo eight
exactly when its squarefree part is congruent to five modulo eight. The nonzero integer square
factor excludes zero, which has no squarefree part. -/
theorem exists_eq_mod_eight_eq_five_mul_sq_iff_exists_squarefree_mod_eight_eq_five_mul_sq
    {n : ℤ} :
    (∃ (c : ℤ) (q : ℚ), c % 8 = 5 ∧ q ≠ 0 ∧ (n : ℚ) = c * q ^ 2) ↔
      ∃ s b : ℤ, Squarefree s ∧ b ≠ 0 ∧ n = s * b ^ 2 ∧ s % 8 = 5 := by
  constructor
  · rintro ⟨c, q, hc, hq, h⟩
    have hn : n ≠ 0 := by
      intro hn
      have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
      exact mul_ne_zero hc0 (pow_ne_zero 2 hq) (h.symm.trans (by simp [hn]))
    obtain ⟨s, b, hs, hb, hn⟩ := Int.exists_squarefree_mul_sq hn
    have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    refine ⟨s, b, hs, hb, hn, (emod_eight_eq_five_iff_exists_eq_mod_eight_eq_five_mul_sq hs).mpr
      ⟨c, q / b, hc, div_ne_zero hq hbQ, ?_⟩⟩
    have hnQ : (n : ℚ) = s * (b : ℚ) ^ 2 := by exact_mod_cast hn
    field_simp
    linear_combination h - hnQ
  · rintro ⟨s, b, -, hb, hn, hs⟩
    exact ⟨s, b, hs, by exact_mod_cast hb, by exact_mod_cast hn⟩

end TauCeti.Int

namespace Nat

/-- **From uniform squarefreeness to the sharp branch.** If every prime dividing `n > 2` is
squarefree in `R`, then either `4 ∣ n` and `2` is squarefree there, or some *odd* prime divides
`n` and is squarefree there.

Mathlib's `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt` supplies the dichotomy on `n`; what
this adds is carrying the squarefreeness through it. The point of stating it is that the two
hypotheses differ in usability: the uniform one can be established with no knowledge of `n` — over
`ℤ` it is free, since every rational prime is squarefree — while the branch-dependent one is what a
proof consumes. Anything proved from the sharp form is therefore available from the uniform form
through this lemma.

The ambient ring may be noncommutative. `Squarefree` is a `Monoid` notion and the integer casts
need `AddGroupWithOne`; `Ring` is the bundled class supplying both with a single `1`, which is
the unit `IsUnit` refers to inside `Squarefree`. -/
theorem four_dvd_or_exists_odd_prime_and_dvd_of_squarefree {R : Type*} [Ring R] {n : ℕ}
    (hn : 2 < n) (hsf : ∀ p : ℕ, p.Prime → p ∣ n → Squarefree ((p : ℤ) : R)) :
    (4 ∣ n ∧ Squarefree (2 : R)) ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ n ∧ Squarefree ((p : ℤ) : R) := by
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn with h4 | ⟨p, hp, hpn, hodd⟩
  · exact Or.inl ⟨h4, by simpa using hsf 2 Nat.prime_two (dvd_trans ⟨2, rfl⟩ h4)⟩
  · have hp_ne_two : p ≠ 2 := by rintro rfl; rw [Nat.odd_iff] at hodd; omega
    exact Or.inr ⟨p, hp, hp_ne_two, hpn, hsf p hp hpn⟩

end Nat
