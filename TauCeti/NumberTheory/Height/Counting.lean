/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.House

import TauCeti.Algebra.Polynomial.Card.RootSetUnion

/-!
# Counting algebraic numbers of bounded naive height or house

An algebraic number of degree at most `d` and naive height at most `B` is a root of an integer
polynomial of degree at most `d` whose coefficients have absolute value at most `B`. There are at
most `(2⌊B⌋ + 1)^(d + 1)` such polynomials, each with at most `d` roots, which gives an explicit
form of Northcott's theorem for the naive height.

For an algebraic integer the naive height is bounded by a power of the house
(`TauCeti.naiveHeight_le_two_mul_pow_of_house_le`), and the same counting argument, now with
monic polynomials, bounds the number of algebraic integers of bounded degree and bounded house.

All statements hold in an arbitrary field of characteristic zero, for instance `ℂ` or an algebraic
closure of `ℚ`; no complex embedding of the ambient field is needed.

## Main results

* `TauCeti.finite_setOf_naiveHeight_le`: the elements of degree at most `d` and naive height at
  most `B` form a finite set with at most `d (2⌊B⌋ + 1)^(d + 1)` elements.
* `TauCeti.finite_setOf_isIntegral_house_le`: the algebraic integers of degree at most `d` and
  house at most `C` form a finite set with at most `∑ₖ₌₀ᵈ k (2⌊(2 max(C, 1))ᵏ⌋ + 1)ᵏ`
  elements.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 1, Theorem 1.7, and
  ch. 3, Exercise 3.6.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F] [CharZero F]

/-- **Northcott's theorem for the naive height, with Evertse's count.** In a field of
characteristic zero, the algebraic elements of degree at most `d` and naive height at most `B`
form a finite set with at most `d (2⌊B⌋ + 1)^(d + 1)` elements. -/
theorem finite_setOf_naiveHeight_le (d : ℕ) (B : ℝ) :
    {z : F | IsAlgebraic ℚ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ naiveHeight z ≤ B}.Finite ∧
      {z : F | IsAlgebraic ℚ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ naiveHeight z ≤ B}.ncard ≤
        d * (2 * ⌊B⌋₊ + 1) ^ (d + 1) := by
  classical
  -- Every such element is a root of its primitive minimal polynomial `F_z`, an integer
  -- polynomial of degree at most `d` with coefficients bounded by `⌊B⌋₊`.
  have hsub : {z : F | IsAlgebraic ℚ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ naiveHeight z ≤ B} ⊆
      ⋃ (f : ℤ[X]) (_ : f.natDegree ≤ d ∧ ∀ i, |f.coeff i| ≤ (⌊B⌋₊ : ℤ)),
        ((f.map (Int.castRingHom F)).roots.toFinset : Set F) := by
    rintro z ⟨hz, hzd, hzB⟩
    have hroot := mem_rootSet.2 ⟨primitiveMinpoly_ne_zero z, aeval_primitiveMinpoly hz⟩
    rw [rootSet_def, aroots_def, algebraMap_int_eq] at hroot
    refine Set.mem_iUnion₂.2 ⟨primitiveMinpoly z,
      ⟨by rwa [natDegree_primitiveMinpoly], fun i ↦ ?_⟩, hroot⟩
    have h : |((primitiveMinpoly z).coeff i : ℝ)| ≤ B := by
      simpa only [Int.norm_eq_abs] using (norm_coeff_primitiveMinpoly_le_naiveHeight z i).trans hzB
    rw [Int.natCast_floor_eq_floor ((abs_nonneg _).trans h)]
    exact Int.le_floor.2 (by rwa [Int.cast_abs])
  have hfin :=
    Polynomial.finite_biUnion_roots_natDegree_le_abs_intCoeff_le (Int.castRingHom F) d ⌊B⌋₊
  refine ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans ?_⟩
  rw [mul_comm]
  exact Polynomial.ncard_biUnion_roots_natDegree_le_abs_intCoeff_le _ d _

/-- **Finiteness of algebraic integers of bounded house, with a count.** In a field of
characteristic zero, the algebraic integers of degree at most `d` and house at most `C` form a
finite set with at most `∑ₖ₌₀ᵈ k (2⌊(2 max(C, 1))ᵏ⌋ + 1)ᵏ` elements. -/
theorem finite_setOf_isIntegral_house_le (d : ℕ) (C : ℝ) :
    {z : F | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ house z ≤ C}.Finite ∧
      {z : F | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ house z ≤ C}.ncard ≤
        ∑ k ∈ Finset.range (d + 1), k * (2 * ⌊(2 * max C 1) ^ k⌋₊ + 1) ^ k := by
  classical
  -- Algebraic integers of degree exactly `k` are roots of monic integer polynomials of degree
  -- `k` whose lower coefficients are bounded by `(2 max(C, 1))ᵏ`.
  have hk (k : ℕ) :
      {z : F | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree = k ∧ house z ≤ C}.Finite ∧
        {z : F | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree = k ∧ house z ≤ C}.ncard ≤
          k * (2 * ⌊(2 * max C 1) ^ k⌋₊ + 1) ^ k := by
    set N := ⌊(2 * max C 1) ^ k⌋₊
    let s : Fin (k + 1) → Finset ℤ := Fin.lastCases {1} fun _ ↦ Finset.Icc (-(N : ℤ)) N
    have hsub : {z : F | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree = k ∧ house z ≤ C} ⊆
        ⋃ (f : ℤ[X]) (_ : f.natDegree ≤ k ∧ ∀ i : Fin (k + 1), f.coeff i ∈ s i),
          ((f.map (Int.castRingHom F)).roots.toFinset : Set F) := by
      rintro z ⟨hz, hzk, hzC⟩
      have hdeg : (primitiveMinpoly z).natDegree = k := by rwa [natDegree_primitiveMinpoly]
      have hmon : (primitiveMinpoly z).Monic := by
        rw [primitiveMinpoly_eq_minpoly_int hz]
        exact minpoly.monic hz
      have hroot := mem_rootSet.2 ⟨primitiveMinpoly_ne_zero z,
        aeval_primitiveMinpoly (hz.tower_top (A := ℚ)).isAlgebraic⟩
      rw [rootSet_def, aroots_def, algebraMap_int_eq] at hroot
      refine Set.mem_iUnion₂.2 ⟨primitiveMinpoly z, ⟨hdeg.le, Fin.lastCases ?_ fun i ↦ ?_⟩, hroot⟩
      · dsimp only [s]
        rw [Fin.lastCases_last, Fin.val_last, ← hdeg, coeff_natDegree, hmon.leadingCoeff]
        exact Finset.mem_singleton_self 1
      · have h : |((primitiveMinpoly z).coeff i : ℝ)| ≤ (2 * max C 1) ^ k := by
          simpa only [Int.norm_eq_abs, hzk] using
            (norm_coeff_primitiveMinpoly_le_naiveHeight z i).trans <|
              naiveHeight_le_two_mul_pow_of_house_le hz (le_max_right C 1)
                (hzC.trans (le_max_left C 1))
        dsimp only [s]
        rw [Fin.lastCases_castSucc, Fin.val_castSucc, Finset.mem_Icc, ← abs_le,
          Int.natCast_floor_eq_floor ((abs_nonneg _).trans h)]
        exact Int.le_floor.2 (by rwa [Int.cast_abs])
    have hfin := Polynomial.finite_biUnion_roots_natDegree_le_coeff_mem_pi (Int.castRingHom F) k s
    refine ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans <|
      (Polynomial.ncard_biUnion_roots_natDegree_le_coeff_mem_pi_le _ k s).trans_eq ?_⟩
    have hN : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
      rw [Int.card_Icc]
      omega
    simp only [s, Fin.prod_univ_castSucc, Fin.lastCases_last, Fin.lastCases_castSucc, hN,
      Finset.card_singleton, Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul,
      mul_comm]
  have hsub : {z : F | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ house z ≤ C} ⊆
      ⋃ k ∈ Finset.range (d + 1),
        {z : F | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree = k ∧ house z ≤ C} := by
    rintro z ⟨hz, hzd, hzC⟩
    simp only [Set.mem_iUnion, Finset.mem_range]
    exact ⟨_, Nat.lt_succ_of_le hzd, hz, rfl, hzC⟩
  have hfin := (Finset.range (d + 1)).finite_toSet.biUnion fun k _ ↦ (hk k).1
  refine ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans ?_⟩
  exact (Finset.set_ncard_biUnion_le _ _).trans (Finset.sum_le_sum fun k _ ↦ (hk k).2)

end TauCeti
