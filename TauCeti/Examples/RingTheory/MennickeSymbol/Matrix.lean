/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MennickeSymbol.Matrix

/-!
# First rows of congruence matrices: examples

These examples fix the normalizations of the first-row maps `GL₂(A, I) → W(A, I)` and
`SL₂(A, I) → W(A, I)` and of the values `g ↦ [b/a]` of a Mennicke symbol on matrices.

* At level `2` over `ℤ`, the matrix `[[5, 2], [12, 5]]` of `SL₂(ℤ, 2ℤ)` has first-row pair `(5, 2)`,
  and its transpose `[[5, 12], [2, 5]]` has the inverse value `[12/5] = [2/5]⁻¹`.
* The pair `(3, 2)` is admissible at level `2`, but it is not the first row of a matrix congruent
  to `1` modulo `4`, since `3 ≢ 1` modulo `4`.
* Every Mennicke symbol is trivial on the first rows of `diag(-1, 1)` and `[[-1, 2], [-2, 3]]` at
  level `2`, although neither matrix is the identity: the first row `(-1, 0)` has second entry
  `0`, and `(-1, 2)` has the unit `-1` as first entry.
* Every Mennicke symbol is trivial on the first row `(1, t)` of an upper transvection
  `[[1, t], [0, 1]]` with `t ∈ I`, at every level, including `t = 0` and `I = A`.
-/

public section

open Matrix (GeneralLinearGroup SpecialLinearGroup)
open Ideal Ideal.MennickePair

namespace TauCeti.MennickeFirstRowExamples

/-- The matrix `[[5, 2], [12, 5]]` of `SL₂(ℤ)`, congruent to `1` modulo `2`. -/
def five : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (span {(2 : ℤ)}))).ker :=
  ⟨⟨!![5, 2; 12, 5], by simp [Matrix.det_fin_two_of]⟩,
    SpecialLinearGroup.mem_ker_map_quotientMk_iff.2 fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp [mem_span_singleton]⟩

/-- The transpose `[[5, 12], [2, 5]]` of `five`. -/
def fiveTranspose :
    (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (span {(2 : ℤ)}))).ker :=
  ⟨⟨!![5, 12; 2, 5], by simp [Matrix.det_fin_two_of]⟩,
    SpecialLinearGroup.mem_ker_map_quotientMk_iff.2 fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp [mem_span_singleton]⟩

/-- The first-row pair of `[[5, 2], [12, 5]]` is `(5, 2)`. -/
theorem ofSL_five : (ofSL five).fst = 5 ∧ (ofSL five).snd = 2 := by
  simp [five]

/-- Transposition inverts a Mennicke symbol: `[12/5] = [2/5]⁻¹` at level `2`. -/
theorem map_ofSL_fiveTranspose {C : Type*} [Group C] {s : MennickePair (span {(2 : ℤ)}) → C}
    (hs : IsMennickeSymbol s) : s (ofSL fiveTranspose) = (s (ofSL five))⁻¹ := by
  rw [← ofGL_kerMapToGL, ← ofGL_kerMapToGL]
  refine hs.map_ofGL_of_transpose ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [five, fiveTranspose, SpecialLinearGroup.toGL]

/-- The pair `(3, 2)` is admissible at level `2`. -/
theorem exists_mennickePair_three_two :
    ∃ p : MennickePair (span {(2 : ℤ)}), p.fst = 3 ∧ p.snd = 2 :=
  ⟨⟨3, 2, mem_span_singleton.2 ⟨1, by norm_num⟩, mem_span_singleton.2 dvd_rfl,
    ⟨1, -1, by norm_num⟩⟩, rfl, rfl⟩

/-- The pair `(3, 2)` is not the first row of a matrix of `SL₂(ℤ)` congruent to `1` modulo `4`. -/
theorem not_exists_ofSL_three_two :
    ¬ ∃ g : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (span {(4 : ℤ)}))).ker,
      (ofSL g).fst = 3 ∧ (ofSL g).snd = 2 := by
  rintro ⟨g, hg, -⟩
  have h := (ofSL g).fst_sub_one_mem
  rw [hg, mem_span_singleton] at h
  norm_num at h

/-- The diagonal matrix `diag(-1, 1)`, congruent to `1` modulo `2`. -/
noncomputable def diagNegOne :
    (GeneralLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (span {(2 : ℤ)}))).ker :=
  ⟨GeneralLinearGroup.mk'' !![-1, 0; 0, 1] (by simp [Matrix.det_fin_two_of]),
    (GeneralLinearGroup.mem_ker_map_quotientMk_iff _).2 fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp⟩

/-- Every Mennicke symbol at level `2` is trivial on the first row of `diag(-1, 1)`. -/
theorem map_ofGL_diagNegOne {C : Type*} [Group C] {s : MennickePair (span {(2 : ℤ)}) → C}
    (hs : IsMennickeSymbol s) : s (ofGL diagNegOne) = 1 :=
  hs.map_eq_one_of_snd_eq_zero (by simp [diagNegOne])

/-- The matrix `[[-1, 2], [-2, 3]]` of `SL₂(ℤ)`, congruent to `1` modulo `2`. -/
def negOneTwo : (SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (span {(2 : ℤ)}))).ker :=
  ⟨⟨!![-1, 2; -2, 3], by simp [Matrix.det_fin_two_of]⟩,
    SpecialLinearGroup.mem_ker_map_quotientMk_iff.2 fun i j ↦ by
      fin_cases i <;> fin_cases j <;> simp⟩

/-- Every Mennicke symbol at level `2` is trivial on the first row of `[[-1, 2], [-2, 3]]`. -/
theorem map_ofSL_negOneTwo {C : Type*} [Group C] {s : MennickePair (span {(2 : ℤ)}) → C}
    (hs : IsMennickeSymbol s) : s (ofSL negOneTwo) = 1 :=
  hs.map_eq_one_of_isUnit_fst (by simp [negOneTwo])

/-- At every level `I` and for every `t ∈ I`, every Mennicke symbol is trivial on the first row
`(1, t)` of the upper transvection `[[1, t], [0, 1]]`. -/
theorem map_ofSL_transvection {A : Type*} [CommRing A] {I : Ideal A} {C : Type*} [Group C]
    {s : MennickePair I → C} (hs : IsMennickeSymbol s) {t : A} (ht : t ∈ I) :
    s (ofSL ⟨SpecialLinearGroup.transvection zero_ne_one t,
      SpecialLinearGroup.mem_ker_map_quotientMk_iff.2 fun i j ↦ by
        fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, ht]⟩) = 1 :=
  hs.map_eq_one_of_isUnit_fst (by simp [SpecialLinearGroup.transvection_coe])

end TauCeti.MennickeFirstRowExamples
