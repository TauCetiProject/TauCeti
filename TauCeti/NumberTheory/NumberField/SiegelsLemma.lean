/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.House

/-!
# Siegel's lemma over a number field with rational integer unknowns

Let `K` be a number field of degree `d` and let `a` be an `M × N` matrix over `𝓞 K` whose entries
have house at most `A ≥ 1`. If `d * M < N`, the system `a x = 0` has a nonzero solution
`x ∈ ℤ^N` with `|xⱼ| ≤ (3 N A) ^ (d M / (N - d M))` for every `j`. The unknowns are rational
integers, and the constant depends only on `N` and `A`, not on a choice of integral basis of `K`.
This is the form of Siegel's lemma used to construct auxiliary polynomials with integer
coefficients, for instance in the proof of Roth's theorem.

Mathlib's `NumberField.house.exists_ne_zero_int_vec_house_le` solves the same system with
unknowns in `𝓞 K` and a constant depending on an integral basis; Mathlib's
`Int.Matrix.exists_ne_zero_int_vec_norm_le` is the case of integer coefficients.

The proof is a pigeonhole argument in the coordinates of Mathlib's `mixedEmbedding.stdBasis`: an
algebraic integer has `d` such real coordinates, and it vanishes as soon as all of them are at
most `2 / 3` in absolute value, because then every conjugate has modulus at most
`2 √2 / 3 < 1`.

## Main results

* `NumberField.mixedEmbedding.abs_stdBasis_repr_le_house`: every `stdBasis` coordinate of the
  mixed embedding of `x` is bounded by the house of `x`.
* `NumberField.RingOfIntegers.eq_zero_of_abs_stdBasis_repr_le`: an algebraic integer whose
  `stdBasis` coordinates are all at most `2 / 3` in absolute value is zero.
* `NumberField.RingOfIntegers.eq_zero_of_abs_re_le_of_abs_im_le`: an algebraic integer whose
  conjugates all have real and imaginary parts at most `2 / 3` in absolute value is zero.
* `NumberField.exists_ne_zero_int_vec_abs_le_of_house_le`: Siegel's lemma over `K` with unknowns
  in `ℤ`.

## References

* J.-H. Evertse, *Diophantine approximation and transcendence theory*, lecture notes (2019),
  Chapter 3, Lemma 3.19 and Theorem 3.20.
* The counting estimate follows the proof of `Int.Matrix.exists_ne_zero_int_vec_norm_le` in
  Mathlib (F. Barroero, L. Capuano, A. Turchet).
-/

public section

open Finset Module NumberField.InfinitePlace

open scoped Matrix

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace mixedEmbedding

/-- Every coordinate of the mixed embedding of `x` in `stdBasis` is bounded in absolute value by
the house of `x`. -/
theorem abs_stdBasis_repr_le_house (x : K) (r : index K) :
    |(stdBasis K).repr (mixedEmbedding K x) r| ≤ house x := by
  have hw (w : InfinitePlace K) : w x ≤ house x := by
    rw [← norm_embedding_eq]
    exact norm_embedding_le_house x _
  rcases r with ⟨w, hw'⟩ | ⟨⟨w, hw'⟩, j⟩
  · rw [stdBasis_apply_isReal, ← Real.norm_eq_abs, ← normAtPlace_apply_of_isReal hw',
      normAtPlace_apply]
    exact hw w
  · have h := hw w
    rw [← normAtPlace_apply, normAtPlace_apply_of_isComplex hw'] at h
    fin_cases j
    · exact (Complex.abs_re_le_norm _).trans h
    · exact (Complex.abs_im_le_norm _).trans h

end mixedEmbedding

open mixedEmbedding

namespace RingOfIntegers

/-- An algebraic integer whose real coordinates `(stdBasis K).repr (mixedEmbedding K x)` are all
at most `2 / 3` in absolute value is zero: each of its conjugates then has modulus at most
`2 √2 / 3 < 1`. -/
theorem eq_zero_of_abs_stdBasis_repr_le {x : 𝓞 K}
    (h : ∀ r, |(stdBasis K).repr (mixedEmbedding K (x : K)) r| ≤ 2 / 3) : x = 0 := by
  by_contra hx
  obtain ⟨σ, hσ⟩ := exists_conjugate_one_le_norm hx
  have hsqrt : √2 * (2 / 3) < 1 := by
    nlinarith [Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  rw [← InfinitePlace.apply, ← normAtPlace_apply] at hσ
  refine hσ.not_gt ?_
  by_cases hw : IsReal (InfinitePlace.mk σ)
  · rw [normAtPlace_apply_of_isReal hw, Real.norm_eq_abs, ← stdBasis_apply_isReal]
    exact (h _).trans_lt (by norm_num)
  · have hw := not_isReal_iff_isComplex.mp hw
    rw [normAtPlace_apply_of_isComplex hw]
    refine (Complex.norm_le_sqrt_two_mul_max _).trans_lt (lt_of_le_of_lt ?_ hsqrt)
    gcongr
    rw [max_le_iff, ← stdBasis_apply_isComplex_fst, ← stdBasis_apply_isComplex_snd]
    exact ⟨h _, h _⟩

/-- **Evertse, Lemma 3.19.** An algebraic integer `x` such that every complex embedding `σ`
satisfies `|Re σ(x)| ≤ 2 / 3` and `|Im σ(x)| ≤ 2 / 3` is zero. -/
theorem eq_zero_of_abs_re_le_of_abs_im_le {x : 𝓞 K}
    (hre : ∀ σ : K →+* ℂ, |(σ x).re| ≤ 2 / 3) (him : ∀ σ : K →+* ℂ, |(σ x).im| ≤ 2 / 3) :
    x = 0 := by
  refine eq_zero_of_abs_stdBasis_repr_le fun r ↦ ?_
  rcases r with ⟨w, hw⟩ | ⟨⟨w, hw⟩, j⟩
  · rw [stdBasis_apply_isReal, mixedEmbedding_apply_isReal, ← Complex.ofReal_re
      (embedding_of_isReal _ _), embedding_of_isReal_apply]
    exact hre _
  · match j with
    | 0 =>
      rw [stdBasis_apply_isComplex_fst, mixedEmbedding_apply_isComplex]
      exact hre _
    | 1 =>
      rw [stdBasis_apply_isComplex_snd, mixedEmbedding_apply_isComplex]
      exact him _

end RingOfIntegers

variable {α β : Type*} [Fintype α] [Fintype β]

omit [Fintype α] in
/-- The `stdBasis` coordinates of the mixed embedding of `a *ᵥ x` are the corresponding `ℤ`-linear
combinations of the coordinates of the entries of `a`. -/
private theorem stdBasis_repr_mulVec_intCast (a : Matrix α β (𝓞 K)) (x : β → ℤ) (i : α)
    (r : index K) :
    (stdBasis K).repr (mixedEmbedding K ((a *ᵥ fun j ↦ (x j : 𝓞 K)) i : K)) r =
      ∑ j, (x j : ℝ) * (stdBasis K).repr (mixedEmbedding K (a i j : K)) r := by
  have : ((a *ᵥ fun j ↦ (x j : 𝓞 K)) i : K) = ∑ j, x j • (a i j : K) := by
    simp [Matrix.mulVec, dotProduct, zsmul_eq_mul, mul_comm]
  rw [this, map_sum, map_sum, Finsupp.finsetSum_apply]
  congr 1 with j
  rw [map_zsmul, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]

/-- The counting estimate of Siegel's lemma: if `C ≥ 1`, `D < n` and `C ^ (D / (n - D)) < B + 1`,
then the `(B + 1) ^ n` integer points of the box `[0, B]^n` outnumber the `(⌊C B⌋₊ + 1) ^ D`
cells of a partition of `[0, C B]^D` into cubes of side less than one. -/
private theorem floor_mul_add_one_pow_lt {C : ℝ} (hC : 1 ≤ C) {D n B : ℕ} (hDn : D < n)
    (hB : C ^ ((D : ℝ) / (n - D)) < B + 1) :
    (⌊C * B⌋₊ + 1) ^ D < (B + 1) ^ n := by
  have hnD : (D : ℝ) < n := by exact_mod_cast hDn
  rw [← Nat.cast_lt (α := ℝ)]
  push_cast
  calc ((⌊C * B⌋₊ : ℝ) + 1) ^ D ≤ (C * (B + 1)) ^ D := by
        gcongr
        linarith [Nat.floor_le (by positivity : 0 ≤ C * B)]
    _ = (C ^ ((D : ℝ) / (n - D))) ^ ((n : ℝ) - D) * (B + 1) ^ D := by
        rw [mul_pow, ← Real.rpow_mul (by positivity), div_mul_cancel₀ _ (by linarith),
          Real.rpow_natCast]
    _ < (B + 1) ^ ((n : ℝ) - D) * (B + 1) ^ D := by gcongr
    _ = (B + 1) ^ n := by
        rw [← Real.rpow_natCast _ D, ← Real.rpow_add (by positivity), sub_add_cancel,
          Real.rpow_natCast]

/-- **Siegel's lemma over a number field, with rational integer unknowns** (Evertse,
Theorem 3.20). Let `K` be a number field of degree `d` and `a` a matrix over `𝓞 K` with `M` rows
and `N` columns, whose entries have house at most `A ≥ 1`. If `d * M < N`, there is a nonzero
`x ∈ ℤ^N` with `a x = 0` and `|xⱼ| ≤ (3 N A) ^ (d M / (N - d M))` for every `j`. -/
theorem exists_ne_zero_int_vec_abs_le_of_house_le (a : Matrix α β (𝓞 K)) {A : ℝ} (hA : 1 ≤ A)
    (hcard : finrank ℚ K * Fintype.card α < Fintype.card β)
    (ha : ∀ i j, house (a i j : K) ≤ A) :
    ∃ x : β → ℤ, x ≠ 0 ∧ a *ᵥ (fun j ↦ (x j : 𝓞 K)) = 0 ∧
      ∀ j, |(x j : ℝ)| ≤ (3 * Fintype.card β * A) ^
        ((finrank ℚ K * Fintype.card α : ℝ) /
          (Fintype.card β - finrank ℚ K * Fintype.card α)) := by
  classical
  -- `D = d M` is the number of real linear forms, `B` the box size for the unknowns.
  set n := Fintype.card β
  set D := finrank ℚ K * Fintype.card α with hD_def
  have hD : (D : ℝ) = finrank ℚ K * Fintype.card α := by rw [hD_def, Nat.cast_mul]
  rw [← hD]
  set B : ℕ := ⌊(3 * n * A) ^ ((D : ℝ) / (n - D))⌋₊
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le D).trans_lt hcard
  have hnA : 1 ≤ 3 * n * A := by nlinarith
  -- The real coefficients of the `D` linear forms and their values at `x`.
  let c : α × index K → β → ℝ := fun p j ↦ (stdBasis K).repr (mixedEmbedding K (a p.1 j)) p.2
  have hc (p) (j) : |c p j| ≤ A := (abs_stdBasis_repr_le_house _ _).trans (ha _ _)
  let L : (β → ℤ) → α × index K → ℝ := fun x p ↦ ∑ j, (x j : ℝ) * c p j
  -- Pigeonhole: points of the box `[0, B]^N` and cells of side `2 / 3` in `ℝ^D`.
  let T : Finset (β → ℤ) := Icc 0 fun _ ↦ (B : ℤ)
  let f : (β → ℤ) → α × index K → ℕ := fun x p ↦ ⌊(L x p + n * A * B) * (3 / 2)⌋₊
  let S : Finset (α × index K → ℕ) := Fintype.piFinset fun _ ↦ range (⌊3 * n * A * B⌋₊ + 1)
  have hT {x : β → ℤ} (hx : x ∈ T) (j : β) : 0 ≤ x j ∧ x j ≤ B := by
    rw [mem_Icc] at hx
    exact ⟨hx.1 j, hx.2 j⟩
  have hL {x : β → ℤ} (hx : x ∈ T) (p : α × index K) : |L x p| ≤ n * A * B := by
    calc |L x p| ≤ ∑ j, |(x j : ℝ) * c p j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : β, A * B := by
        gcongr with j
        have := hT hx j
        rw [abs_mul, mul_comm A]
        gcongr
        · rw [abs_of_nonneg (by exact_mod_cast this.1)]
          exact_mod_cast this.2
        · exact hc p j
      _ = n * A * B := by simp [n, mul_assoc]
  have hmaps (x : β → ℤ) (hx : x ∈ T) : f x ∈ S := by
    simp only [S, Fintype.mem_piFinset, mem_range, Nat.lt_succ_iff]
    intro p
    refine Nat.floor_le_floor ?_
    linarith [(abs_le.mp (hL hx p)).2]
  have hlt : #S < #T := by
    have : Fintype.card (index K) = finrank ℚ K := by
      rw [← mixedEmbedding.finrank K, finrank_eq_card_basis (stdBasis K)]
    have hS : #S = (⌊3 * n * A * B⌋₊ + 1) ^ D := by
      simp [S, Fintype.card_piFinset, Fintype.card_prod, this, hD_def, mul_comm]
    have hT : #T = (B + 1) ^ n := by simp [T, Pi.card_Icc, n]
    rw [hS, hT]
    exact floor_mul_add_one_pow_lt hnA hcard (Nat.lt_floor_add_one _)
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_, fun j ↦ ?_⟩
  · -- Two points in the same cell differ by an integer vector on which every form is `< 2 / 3`.
    funext i
    refine RingOfIntegers.eq_zero_of_abs_stdBasis_repr_le fun r ↦ ?_
    have hfloor := congr_arg (fun k : ℕ ↦ (k : ℤ)) (congr_fun hxy (i, r))
    simp only [f] at hfloor
    rw [Int.natCast_floor_eq_floor (by linarith [(abs_le.mp (hL hx (i, r))).1]),
      Int.natCast_floor_eq_floor (by linarith [(abs_le.mp (hL hy (i, r))).1])] at hfloor
    have hcell := Int.abs_sub_lt_one_of_floor_eq_floor hfloor
    have hsub : ∑ j, ((x - y) j : ℝ) * (stdBasis K).repr (mixedEmbedding K (a i j : K)) r =
        L x (i, r) - L y (i, r) := by
      simp [L, c, sub_mul, sum_sub_distrib]
    rw [stdBasis_repr_mulVec_intCast, hsub]
    rw [← sub_mul, add_sub_add_right_eq_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
      at hcell
    linarith
  · obtain ⟨hx₁, hx₂⟩ := hT hx j
    obtain ⟨hy₁, hy₂⟩ := hT hy j
    calc |((x - y) j : ℝ)| ≤ B := by
          have : |x j - y j| ≤ (B : ℤ) := abs_le.mpr ⟨by linarith, by linarith⟩
          rw [Pi.sub_apply]
          exact_mod_cast this
      _ ≤ _ := Nat.floor_le (by positivity)

end NumberField
