/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.LinearCombination

/-!
# The four elements of a field of order four

A root `ω` of `X² + X + 1` labels the four elements as `0, 1, ω, ω²`.
The explicit enumeration supports finite calculations over this alphabet without choosing
another model of the field. Frobenius is an involution on this alphabet.
-/

public section

namespace TauCeti

variable {F : Type*} [Field F] [Fintype F]

/-- Every field of order four contains a root of `X² + X + 1`. -/
theorem exists_sq_add_self_add_one_eq_zero_of_card_eq_four (hF : Fintype.card F = 4) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  classical
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ) (by simp [hF])
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  have hpow : ω ^ 3 = 1 := by simpa [hF] using FiniteField.pow_card_sub_one_eq_one ω hω.1
  have hmul : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    linear_combination hpow
  exact ⟨ω, (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hω.2)⟩

/-- The four elements of a field of order four, labelled by a root of `X² + X + 1`. -/
theorem univ_eq_zero_one_root_sq [DecidableEq F] (hF : Fintype.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : Finset.univ = {0, 1, ω, ω ^ 2} := by
  classical
  let : CharP F 2 := ringChar.of_eq ((FiniteField.even_card_iff_char_two (F := F)).mpr (by omega))
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
  simp [hF, Ne.symm hself, Ne.symm h0, Ne.symm h1,
    Ne.symm hs0, Ne.symm hs1]

/-- Frobenius is an involution on a field of order four. -/
theorem involutive_frobeniusEquiv_of_card_eq_four [CharP F 2]
    (hF : Fintype.card F = 4) : Function.Involutive (frobeniusEquiv F 2) := by
  intro x
  simpa only [frobeniusEquiv_def, ← pow_mul, hF] using FiniteField.pow_card x

/-- Label a field of four elements by `0, 1, ω, ω²`, in that order. -/
noncomputable def finFourEquiv (hF : Fintype.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : Fin 4 ≃ F := by
  classical
  refine Equiv.ofBijective ![0, 1, ω, ω ^ 2] ?_
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, by simp [hF]⟩
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
theorem finFourEquiv_apply (hF : Fintype.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (i : Fin 4) :
    finFourEquiv hF hω i = ![0, 1, ω, ω ^ 2] i := (rfl)

end TauCeti
