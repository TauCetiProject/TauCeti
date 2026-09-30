/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Data.Fintype.Fiber
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Sign.Defs

/-! # Polynomial sign counts and Tarski queries

`Finset.signCount` counts the points of a finite set realizing a given polynomial
sign condition. `Finset.signSum` sums a polynomial's signs on that set.
`Polynomial.tarskiQuery p q` specializes the sum to the distinct roots of `p`.
For nonzero `p` its cardinality characterization counts the actual zeros of `p`;
for `p = 0` the value is zero and does not describe the infinite zero set.

The definitions and their basic API are independent of matrix inversion.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 10, for sign conditions and Tarski queries.
-/

public section

open Polynomial SignType
open Function (occCount occCount_eq_card_filter)

namespace Finset

section Basic

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- The number of points realizing a specified polynomial sign condition. -/
noncomputable def signCount {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) : ℕ :=
  occCount (fun x : Z => fun j => sign ((Q j).eval x.val)) σ

/-- Polynomial sign counts are multiplicities in the finite family of pointwise signs. -/
theorem signCount_eq_occCount {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    signCount Z Q σ = occCount (fun x : Z => fun j => sign ((Q j).eval x.val)) σ := (rfl)

open scoped Classical in
/-- Sign counts are cardinalities of the realizing subset of the original finite set. -/
theorem signCount_eq_card_filter {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    signCount Z Q σ = (Z.filter fun x => ∀ j, sign ((Q j).eval x) = σ j).card := by
  classical
  simp only [signCount_eq_occCount, occCount_eq_card_filter, Finset.card_filter,
    funext_iff]
  exact Finset.sum_coe_sort Z
    (fun x : R => if ∀ j, sign ((Q j).eval x) = σ j then (1 : ℕ) else 0)

@[simp, grind =]
theorem signCount_empty {J : Type*}
    (Q : J → R[X]) (σ : J → SignType) : signCount ∅ Q σ = 0 := by
  simp [signCount_eq_card_filter]

/-- The sign conditions partition the original finite set of points. -/
theorem sum_signCount {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) : ∑ σ, signCount Z Q σ = Z.card := by
  classical
  simpa only [signCount_eq_occCount, Nat.card_eq_fintype_card, Fintype.card_coe] using
    Function.sum_occCount_eq_card (fun x : Z => fun j => sign ((Q j).eval x.val))
      (fun _ => Finset.mem_univ _)

/-- A positive sign count is equivalent to realization at a point of the finite set. -/
@[simp, grind =]
theorem signCount_pos {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    0 < signCount Z Q σ ↔ ∃ x ∈ Z, ∀ j, sign ((Q j).eval x) = σ j := by
  classical
  simp [signCount_eq_card_filter, Finset.card_pos, Finset.Nonempty]

/-- The integer sum of signs at a specified finite set of points. -/
noncomputable def signSum (Z : Finset R) (p : R[X]) : ℤ := ∑ x : Z, (sign (p.eval x.val) : ℤ)

/-- Sign sums are integer sums of pointwise polynomial signs. -/
theorem signSum_eq_sum_subtype (Z : Finset R) (p : R[X]) :
    signSum Z p = ∑ x : Z, (sign (p.eval x.val) : ℤ) := (rfl)

/-- Sign sums expressed directly over the original finite set. -/
theorem signSum_eq_sum (Z : Finset R) (p : R[X]) :
    signSum Z p = ∑ x ∈ Z, (sign (p.eval x) : ℤ) := by
  rw [signSum_eq_sum_subtype, Finset.sum_coe_sort Z (fun x : R => (sign (p.eval x) : ℤ))]

@[simp, grind =]
theorem signSum_empty (p : R[X]) : signSum ∅ p = 0 := by
  simp [signSum_eq_sum]

@[simp, grind =]
theorem signSum_zero (Z : Finset R) : signSum Z 0 = 0 := by
  simp [signSum_eq_sum]

@[simp, grind =]
theorem signSum_one [ZeroLEOneClass R] [NeZero (1 : R)] (Z : Finset R) : signSum Z 1 = Z.card := by
  simp [signSum_eq_sum]

/-- A finite sign sum is the number of positive evaluations minus the number of negative ones. -/
theorem signSum_eq_card_sub_card (Z : Finset R) (p : R[X]) :
    signSum Z p = ((Z.filter (fun x => 0 < p.eval x)).card : ℤ) -
      (Z.filter (fun x => p.eval x < 0)).card := by
  classical
  rw [signSum_eq_sum]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hpos : 0 < p.eval x
  · have hneg : ¬ p.eval x < 0 := not_lt_of_ge hpos.le
    simp [hpos, hneg]
  · by_cases hneg : p.eval x < 0 <;> simp [sign_apply, hpos, hneg]

end Basic

end Finset

namespace Polynomial

open Finset

section Basic

variable {R : Type*} [CommRing R] [IsDomain R] [LinearOrder R]

/-- Sum of the signs of `q` at the distinct roots of `p`, with value zero when `p = 0`. -/
noncomputable def tarskiQuery (p q : R[X]) : ℤ := signSum p.roots.toFinset q

theorem tarskiQuery_eq_signSum (p q : R[X]) :
    tarskiQuery p q = signSum p.roots.toFinset q := (rfl)

/-- The Tarski query expressed as a sum over distinct polynomial roots. -/
theorem tarskiQuery_eq_sum (p q : R[X]) :
    tarskiQuery p q = ∑ x ∈ p.roots.toFinset, (sign (q.eval x) : ℤ) := by
  rw [tarskiQuery_eq_signSum, signSum_eq_sum]

/-- The number of distinct roots of `p` where `q` is positive minus the number
where `q` is negative. -/
theorem tarskiQuery_eq_card_sub_card (p q : R[X]) :
    tarskiQuery p q = ((p.roots.toFinset.filter (fun x => 0 < q.eval x)).card : ℤ) -
      (p.roots.toFinset.filter (fun x => q.eval x < 0)).card := by
  rw [tarskiQuery_eq_signSum, signSum_eq_card_sub_card]

@[simp, grind =]
theorem tarskiQuery_zero_left (q : R[X]) : tarskiQuery 0 q = 0 := by
  simp [tarskiQuery_eq_signSum]

@[simp, grind =]
theorem tarskiQuery_zero_right (p : R[X]) : tarskiQuery p 0 = 0 := by
  simp [tarskiQuery_eq_signSum]

@[simp, grind =]
theorem tarskiQuery_one_right [ZeroLEOneClass R] (p : R[X]) :
    tarskiQuery p 1 = p.roots.toFinset.card := by
  simp [tarskiQuery_eq_signSum]

/-- Counts at the roots of a nonzero polynomial count exactly its realizing zeros. -/
theorem signCount_roots_eq_natCard {J : Type*} {p : R[X]} (hp : p ≠ 0)
    (Q : J → R[X]) (σ : J → SignType) :
    signCount p.roots.toFinset Q σ =
      Nat.card {x : R // p.eval x = 0 ∧ ∀ j, sign ((Q j).eval x) = σ j} := by
  classical
  rw [signCount_eq_card_filter, ← Nat.card_eq_finsetCard]
  simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hp, IsRoot.def]

/-- A Tarski query counts the zeros of `p` where `q` is positive, minus those
where `q` is negative. -/
theorem tarskiQuery_eq_sub {p : R[X]} (hp : p ≠ 0) (q : R[X]) :
    tarskiQuery p q = (Nat.card {x : R // p.eval x = 0 ∧ 0 < q.eval x} : ℤ) -
      Nat.card {x : R // p.eval x = 0 ∧ q.eval x < 0} := by
  classical
  rw [tarskiQuery_eq_card_sub_card]
  simp only [← Nat.card_eq_finsetCard, Finset.mem_filter, Multiset.mem_toFinset,
    mem_roots hp, IsRoot.def]

/-- A positive count at the roots of a nonzero polynomial is an actual realizable condition. -/
theorem signCount_roots_pos {J : Type*}
    {p : R[X]} (hp : p ≠ 0) (Q : J → R[X]) (σ : J → SignType) :
    0 < signCount p.roots.toFinset Q σ ↔
      ∃ x : R, p.eval x = 0 ∧ ∀ j, sign ((Q j).eval x) = σ j := by
  classical
  simp only [signCount_pos, Multiset.mem_toFinset, mem_roots hp, IsRoot.def]

end Basic

end Polynomial
