/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.LinearCombination

/-!
# The four elements of a field of order four

A root `ω` of `X² + X + 1` labels the four elements as `0, 1, ω, ω²`.
The explicit enumeration supports finite calculations over this alphabet without choosing
another model of the field. Squaring exchanges the two roots in characteristic two.
-/

public section

namespace TauCeti

/-- The Galois field of order four has four elements, independently of its enumeration. -/
theorem card_galoisField_two_two [Fintype (GaloisField 2 2)] :
    Fintype.card (GaloisField 2 2) = 4 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
  decide

variable {F : Type*} [Field F] [Finite F]

/-- Every element other than zero and one in a field of order four is a root of
`X² + X + 1`. -/
theorem sq_add_self_add_one_eq_zero (hF : Nat.card F = 4) {ω : F}
    (h0 : ω ≠ 0) (h1 : ω ≠ 1) : ω ^ 2 + ω + 1 = 0 := by
  let := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  have hpow : ω ^ 3 = 1 := by simpa [hcard] using FiniteField.pow_card_sub_one_eq_one ω h0
  have hmul : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    linear_combination hpow
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h1)

/-- Squaring preserves roots of `X² + X + 1` in characteristic two. -/
theorem sq_sq_add_sq_add_one_eq_zero {R : Type*} [CommSemiring R] [CharP R 2]
    {ω : R} (hω : ω ^ 2 + ω + 1 = 0) : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by
  simpa only [map_add, map_pow, map_one, map_zero, frobenius_def] using
    congrArg (frobenius R 2) hω

/-- Every field of order four contains a root of `X² + X + 1`. -/
theorem exists_sq_add_self_add_one_eq_zero_of_card_eq_four (hF : Nat.card F = 4) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  classical
  let := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ) (by simp [hcard])
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  exact ⟨ω, sq_add_self_add_one_eq_zero hF hω.1 hω.2⟩

omit [Finite F] in
/-- The four elements of a field of order four, labelled by a root of `X² + X + 1`. -/
theorem univ_eq_zero_one_root_sq [Fintype F] [DecidableEq F] (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : Finset.univ = {0, 1, ω, ω ^ 2} := by
  classical
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  let := charP_of_card_eq_prime_pow (p := 2) (f := 2) hcard
  have h0 : ω ≠ 0 := by rintro rfl; simp at hω
  have h1 : ω ≠ 1 := by rintro rfl; simp [CharTwo.add_self_eq_zero] at hω
  have hs0 : ω ^ 2 ≠ 0 := pow_ne_zero _ h0
  have hs1 : ω ^ 2 ≠ 1 := by
    intro h
    have : ω = 0 := by linear_combination hω - h - (CharTwo.two_eq_zero (R := F))
    exact h0 this
  have hself : ω ^ 2 ≠ ω := by
    intro h
    simp [h, CharTwo.add_self_eq_zero] at hω
  apply (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
  simp [hcard, Ne.symm hself, Ne.symm h0, Ne.symm h1,
    Ne.symm hs0, Ne.symm hs1]

/-- Label a field of four elements by `0, 1, ω, ω²`, in that order. -/
noncomputable def finFourEquiv (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : Fin 4 ≃ F := by
  classical
  letI := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  refine Equiv.ofBijective ![0, 1, ω, ω ^ 2] ?_
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, by simp [hcard]⟩
  intro x
  have hx : x ∈ ({0, 1, ω, ω ^ 2} : Finset F) := by
    rw [← univ_eq_zero_one_root_sq hF hω]
    exact Finset.mem_univ x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The four-element labelling evaluates to the displayed tuple. -/
@[simp]
theorem finFourEquiv_apply (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (i : Fin 4) :
    finFourEquiv hF hω i = ![0, 1, ω, ω ^ 2] i := (rfl)

end TauCeti
