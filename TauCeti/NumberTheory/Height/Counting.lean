/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.House
public import TauCeti.NumberTheory.Height.Naive

import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Counting algebraic numbers of bounded naive height or house

An algebraic number of degree at most `d` and naive height at most `B` is a root of an integer
polynomial of degree at most `d` whose coefficients have absolute value at most `B`. There are at
most `(2⌊B⌋ + 1)^(d + 1)` such polynomials, each with at most `d` roots, which gives an explicit
form of Northcott's theorem for the naive height.

For an algebraic integer the coefficients of its monic minimal polynomial are elementary symmetric
functions of its conjugates, so they are bounded in terms of the house. This bounds the naive
height of an algebraic integer by a power of its house, and the same counting argument, now with
monic polynomials, bounds the number of algebraic integers of bounded degree and bounded house.

All statements hold in an arbitrary field of characteristic zero, for instance `ℂ` or an algebraic
closure of `ℚ`; no complex embedding of the ambient field is needed.

## Main results

* `TauCeti.finite_setOf_naiveHeight_le`: the elements of degree at most `d` and naive height at
  most `B` form a finite set with at most `d (2⌊B⌋ + 1)^(d + 1)` elements.
* `TauCeti.naiveHeight_le_two_mul_pow_of_house_le`, `TauCeti.naiveHeight_le_two_mul_house_pow`:
  an algebraic integer of degree `d` has naive height at most `(2B)ᵈ` whenever its house is at
  most `B` with `1 ≤ B`; in particular a nonzero algebraic integer satisfies
  `H(x) ≤ (2 ⌈x⌉)ᵈ`.
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

/-- If every element of `Z` is a root of a nonzero integer polynomial of degree at most `n`
whose `i`-th coefficient lies in `s i`, then `Z` is finite with at most `n ∏ᵢ #(s i)` elements:
there are at most `∏ᵢ #(s i)` such polynomials, each with at most `n` roots. -/
private lemma finite_and_ncard_le_of_coeff_mem {Z : Set F} {n : ℕ} (s : Fin (n + 1) → Finset ℤ)
    (hZ : ∀ z ∈ Z, ∃ p : ℤ[X], p ≠ 0 ∧ aeval z p = 0 ∧ p.natDegree ≤ n ∧
      ∀ i : Fin (n + 1), p.coeff i ∈ s i) :
    Z.Finite ∧ Z.ncard ≤ n * ∏ i, (s i).card := by
  classical
  set S := (Fintype.piFinset s).image (ofFn (n + 1))
  have hsub : Z ⊆ ↑(S.biUnion fun p ↦ (p.aroots F).toFinset) := by
    intro z hz
    obtain ⟨p, hp0, hpz, hpn, hps⟩ := hZ z hz
    have hpS : p ∈ S := Finset.mem_image.2 ⟨toFn (n + 1) p, Fintype.mem_piFinset.2 hps,
      ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hpn)⟩
    simp only [Finset.coe_biUnion, Finset.mem_coe, Multiset.mem_toFinset, Set.mem_iUnion]
    exact ⟨p, hpS, mem_aroots.2 ⟨hp0, hpz⟩⟩
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  calc Z.ncard ≤ (S.biUnion fun p ↦ (p.aroots F).toFinset).card := by
        simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ ∑ p ∈ S, (p.aroots F).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ S, n := Finset.sum_le_sum fun p hp ↦ by
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
        exact (Multiset.toFinset_card_le _).trans <| (card_roots' _).trans <|
          natDegree_map_le.trans (Nat.le_of_lt_succ (ofFn_natDegree_lt (Nat.le_add_left 1 n) v))
    _ = n * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ n * ∏ i, (s i).card := by
        gcongr
        exact Finset.card_image_le.trans (Fintype.card_piFinset s).le

/-- An integer whose absolute value is at most `B` lies in `[-⌊B⌋₊, ⌊B⌋₊]`. -/
private lemma mem_Icc_floor_of_abs_le {c : ℤ} {B : ℝ} (h : |(c : ℝ)| ≤ B) :
    c ∈ Finset.Icc (-(⌊B⌋₊ : ℤ)) ⌊B⌋₊ := by
  have h' : ((c.natAbs : ℕ) : ℝ) ≤ B := by rwa [Nat.cast_natAbs, Int.cast_abs]
  have := Nat.le_floor h'
  rw [Finset.mem_Icc]
  omega

/-- The integer interval `[-N, N]` has `2N + 1` elements. -/
private lemma card_Icc_neg_natCast (N : ℕ) : (Finset.Icc (-(N : ℤ)) N).card = 2 * N + 1 := by
  rw [Int.card_Icc]
  omega

/-- **Northcott's theorem for the naive height, with Evertse's count.** In a field of
characteristic zero, the algebraic elements of degree at most `d` and naive height at most `B`
form a finite set with at most `d (2⌊B⌋ + 1)^(d + 1)` elements. -/
theorem finite_setOf_naiveHeight_le (d : ℕ) (B : ℝ) :
    {z : F | IsAlgebraic ℚ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ naiveHeight z ≤ B}.Finite ∧
      {z : F | IsAlgebraic ℚ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ naiveHeight z ≤ B}.ncard ≤
        d * (2 * ⌊B⌋₊ + 1) ^ (d + 1) := by
  have h := finite_and_ncard_le_of_coeff_mem (Z := {z : F | IsAlgebraic ℚ z ∧
      (minpoly ℚ z).natDegree ≤ d ∧ naiveHeight z ≤ B}) (fun _ ↦ Finset.Icc (-(⌊B⌋₊ : ℤ)) ⌊B⌋₊)
    fun z ⟨hz, hzd, hzB⟩ ↦ ⟨primitiveMinpoly z, primitiveMinpoly_ne_zero z,
      aeval_primitiveMinpoly hz, by rwa [natDegree_primitiveMinpoly], fun i ↦
        mem_Icc_floor_of_abs_le <| by
          simpa only [Int.norm_eq_abs, Int.cast_abs] using
            (norm_coeff_primitiveMinpoly_le_naiveHeight z i).trans hzB⟩
  simpa only [card_Icc_neg_natCast, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

/-- An algebraic integer of degree `d` whose house is at most `B`, with `1 ≤ B`, has naive height
at most `(2B)ᵈ`. -/
theorem naiveHeight_le_two_mul_pow_of_house_le {x : F} (hx : IsIntegral ℤ x) {B : ℝ}
    (hB : 1 ≤ B) (hxB : house x ≤ B) :
    naiveHeight x ≤ (2 * B) ^ (minpoly ℚ x).natDegree := by
  have halg : IsAlgebraic ℚ x := (hx.tower_top (A := ℚ)).isAlgebraic
  have hmon : (primitiveMinpoly x).Monic := by
    rw [primitiveMinpoly_eq_minpoly_int hx]
    exact minpoly.monic hx
  -- The roots of `F_x` in `ℂ` are the conjugates of `x`, so the coefficients of the monic `F_x`,
  -- elementary symmetric functions of them, satisfy `|aᵢ| ≤ binom(d, i) Bᵈ⁻ⁱ ≤ 2ᵈ Bᵈ`.
  have hroots : ∀ z ∈ ((primitiveMinpoly x).map (Int.castRingHom ℂ)).roots, ‖z‖ ≤ B := by
    intro z hz
    refine (norm_le_house_of_mem_rootSet ?_).trans hxB
    have hz' : z ∈ (primitiveMinpoly x).aroots ℂ := by rwa [aroots_def, algebraMap_int_eq]
    have h := (mem_aroots.1 hz').2
    rw [← aeval_map_algebraMap ℚ, algebraMap_int_eq, map_primitiveMinpoly halg, aeval_mul,
      aeval_C, mul_eq_zero, map_eq_zero, Int.cast_eq_zero] at h
    exact mem_rootSet.2 ⟨minpoly.ne_zero halg.isIntegral,
      h.resolve_left (leadingCoeff_primitiveMinpoly_pos x).ne'⟩
  obtain ⟨i, hi⟩ := (primitiveMinpoly x).exists_eq_supNorm
  rw [naiveHeight_def, hi, ← natDegree_primitiveMinpoly]
  have hcoeff := coeff_le_of_roots_le i hmon (IsAlgClosed.splits _) hroots
  rw [coeff_map, eq_intCast, Complex.norm_intCast, ← Int.norm_eq_abs] at hcoeff
  set n := (primitiveMinpoly x).natDegree
  calc ‖(primitiveMinpoly x).coeff i‖ ≤ B ^ (n - i) * n.choose i := hcoeff
    _ ≤ B ^ n * 2 ^ n := by
        gcongr
        · exact Nat.sub_le n i
        · exact_mod_cast Nat.choose_le_two_pow n i
    _ = (2 * B) ^ n := by rw [mul_pow, mul_comm]

/-- A nonzero algebraic integer `x` of degree `d` has naive height at most `(2 ⌈x⌉)ᵈ`. -/
theorem naiveHeight_le_two_mul_house_pow {x : F} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    naiveHeight x ≤ (2 * house x) ^ (minpoly ℚ x).natDegree :=
  naiveHeight_le_two_mul_pow_of_house_le hx (one_le_house hx h0) le_rfl

/-- **Finiteness of algebraic integers of bounded house, with a count.** In a field of
characteristic zero, the algebraic integers of degree at most `d` and house at most `C` form a
finite set with at most `∑ₖ₌₀ᵈ k (2⌊(2 max(C, 1))ᵏ⌋ + 1)ᵏ` elements. -/
theorem finite_setOf_isIntegral_house_le (d : ℕ) (C : ℝ) :
    {z : F | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ house z ≤ C}.Finite ∧
      {z : F | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree ≤ d ∧ house z ≤ C}.ncard ≤
        ∑ k ∈ Finset.range (d + 1), k * (2 * ⌊(2 * max C 1) ^ k⌋₊ + 1) ^ k := by
  -- Algebraic integers of degree exactly `k` are roots of monic integer polynomials of degree
  -- `k` whose lower coefficients are bounded by `(2 max(C, 1))ᵏ`.
  have hk (k : ℕ) :
      {z : F | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree = k ∧ house z ≤ C}.Finite ∧
        {z : F | IsIntegral ℤ z ∧ (minpoly ℚ z).natDegree = k ∧ house z ≤ C}.ncard ≤
          k * (2 * ⌊(2 * max C 1) ^ k⌋₊ + 1) ^ k := by
    set N := ⌊(2 * max C 1) ^ k⌋₊
    have h := finite_and_ncard_le_of_coeff_mem (Z := {z : F | IsIntegral ℤ z ∧
        (minpoly ℚ z).natDegree = k ∧ house z ≤ C})
      (Fin.lastCases {1} fun _ ↦ Finset.Icc (-(N : ℤ)) N) fun z ⟨hz, hzk, hzC⟩ ↦ by
        have hdeg : (primitiveMinpoly z).natDegree = k := by rwa [natDegree_primitiveMinpoly]
        have hmon : (primitiveMinpoly z).Monic := by
          rw [primitiveMinpoly_eq_minpoly_int hz]
          exact minpoly.monic hz
        refine ⟨primitiveMinpoly z, primitiveMinpoly_ne_zero z,
          aeval_primitiveMinpoly (hz.tower_top (A := ℚ)).isAlgebraic, hdeg.le,
          Fin.lastCases ?_ fun i ↦ ?_⟩
        · rw [Fin.lastCases_last, Fin.val_last, ← hdeg, coeff_natDegree, hmon.leadingCoeff]
          exact Finset.mem_singleton_self 1
        · rw [Fin.lastCases_castSucc]
          refine mem_Icc_floor_of_abs_le ?_
          simpa only [Int.norm_eq_abs, Int.cast_abs, hzk, Fin.val_castSucc] using
            (norm_coeff_primitiveMinpoly_le_naiveHeight z i).trans <|
              naiveHeight_le_two_mul_pow_of_house_le hz (le_max_right C 1)
                (hzC.trans (le_max_left C 1))
    simpa only [Fin.prod_univ_castSucc, Fin.lastCases_last, Fin.lastCases_castSucc,
      card_Icc_neg_natCast, Finset.card_singleton, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_one] using h
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
