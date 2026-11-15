/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.House
import TauCeti.Algebra.Order.BigOperators.Sum.UnitWeights
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Siegel's lemma over a number field

Let `K` be a number field of degree `d` and let `a` be an `M × N` matrix over `𝓞 K` whose entries
have house at most `A ≥ 1`. If `d * M < N`, the system `a x = 0` has a nonzero solution
`x ∈ ℤ^N` with `|xⱼ| ≤ (3 N A) ^ (d M / (N - d M))` for every `j`. The unknowns are rational
integers, and the constant depends only on `N` and `A`, not on a choice of integral basis of `K`.
This is the form of Siegel's lemma used to construct auxiliary polynomials with integer
coefficients, for instance in the proof of Roth's theorem.

Mathlib's `NumberField.house.exists_ne_zero_int_vec_house_le` solves the same system with
unknowns in `𝓞 K` and a constant depending on an integral basis; Mathlib's
`Int.Matrix.exists_ne_zero_int_vec_norm_le` is the case of integer coefficients. When there are at
least twice as many unknowns as equations, the exponent in Mathlib's bound is at most `1`, which
gives a solution in `𝓞 K` of house at most `C N A` for a constant `C` depending only on `K`.

The proof is a pigeonhole argument in the coordinates of Mathlib's `mixedEmbedding.stdBasis`: an
algebraic integer has `d` such real coordinates, and it vanishes as soon as all of them are at
most `2 / 3` in absolute value, because then every conjugate has modulus at most
`2 √2 / 3 < 1`.

## Main results

* `NumberField.mixedEmbedding.abs_stdBasis_repr_le_house`: every `stdBasis` coordinate of the
  mixed embedding of `x` is bounded by the house of `x`.
* `NumberField.mixedEmbedding.stdBasis_repr_mulVec_intCast`: the `stdBasis` coordinates of the
  mixed embedding of `a *ᵥ x`, for an integer vector `x`, are `ℤ`-linear combinations of those of
  the entries of `a`.
* `NumberField.RingOfIntegers.eq_zero_of_abs_stdBasis_repr_le`: an algebraic integer whose
  `stdBasis` coordinates are all at most `2 / 3` in absolute value is zero.
* `NumberField.RingOfIntegers.eq_zero_of_abs_re_le_of_abs_im_le`: an algebraic integer whose
  conjugates all have real and imaginary parts at most `2 / 3` in absolute value is zero.
* `NumberField.exists_ne_zero_int_vec_abs_le_of_house_le`: Siegel's lemma over `K` with unknowns
  in `ℤ`.
* `NumberField.sum_mul_intCast_eq_zero_of_mulVec_eq_zero`: such a solution satisfies each row
  equation `∑ⱼ aᵢⱼ xⱼ = 0` in `K`.
* `NumberField.house.exists_const_ne_zero_int_vec_house_le`: Siegel's lemma over `K` with unknowns
  in `𝓞 K`, for systems with at least twice as many unknowns as equations, with a solution of house
  at most `C N A` for a constant `C` depending only on `K`. This is the form used to build
  auxiliary functions whose coefficients are algebraic integers of `K`.

## References

* J.-H. Evertse, *Diophantine approximation and transcendence theory*, lecture notes (2019),
  Chapter 3, Lemma 3.19 and Theorem 3.20.
* The counting estimate follows the proof of `Int.Matrix.exists_ne_zero_int_vec_norm_le` in
  Mathlib (F. Barroero, L. Capuano, A. Turchet).
-/

public section

open Finset Module NumberField.InfinitePlace

open scoped Matrix

universe u v

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

variable {α β : Type*} [Fintype α] [Fintype β]

omit [Fintype α] in
/-- The `stdBasis` coordinates of the mixed embedding of `a *ᵥ x` are the corresponding `ℤ`-linear
combinations of the coordinates of the entries of `a`. -/
theorem stdBasis_repr_mulVec_intCast (a : Matrix α β (𝓞 K)) (x : β → ℤ) (i : α)
    (r : index K) :
    (stdBasis K).repr (mixedEmbedding K ((a *ᵥ fun j ↦ (x j : 𝓞 K)) i : K)) r =
      ∑ j, (x j : ℝ) * (stdBasis K).repr (mixedEmbedding K (a i j : K)) r := by
  have : ((a *ᵥ fun j ↦ (x j : 𝓞 K)) i : K) = ∑ j, x j • (a i j : K) := by
    simp [Matrix.mulVec, dotProduct, zsmul_eq_mul, mul_comm]
  rw [this, map_sum, map_sum, Finsupp.finsetSum_apply]
  congr 1 with j
  rw [map_zsmul, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]

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
    refine (Finset.abs_sum_le_card_nsmul (s := Finset.univ) (B := (B : ℝ) * A)
      fun j _ ↦ ?_).trans_eq (by simp [n]; ring)
    obtain ⟨h₀, h₁⟩ := hT hx j
    rw [abs_mul]
    refine mul_le_mul ?_ (hc p j) (abs_nonneg _) (by positivity)
    rw [abs_of_nonneg (by exact_mod_cast h₀)]
    exact_mod_cast h₁
  have hmaps (x : β → ℤ) (hx : x ∈ T) : f x ∈ S := by
    simp only [S, Fintype.mem_piFinset, mem_range, Nat.lt_succ_iff]
    intro p
    refine Nat.floor_le_floor ?_
    linarith [(abs_le.mp (hL hx p)).2]
  have hlt : #S < #T := by
    have : Fintype.card (index K) = finrank ℚ K := by
      rw [← mixedEmbedding.finrank K, finrank_eq_card_basis (stdBasis K)]
    have hγ : Fintype.card (α × index K) = D := by
      simp [Fintype.card_prod, this, hD_def, mul_comm]
    simpa [S, T, Fintype.card_piFinset, Pi.card_Icc, hγ] using
      Real.floor_mul_add_one_pow_lt hnA hcard (Nat.lt_floor_add_one _)
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_, fun j ↦ ?_⟩
  · -- Two points in the same cell differ by an integer vector on which every form is `< 2 / 3`.
    funext i
    refine RingOfIntegers.eq_zero_of_abs_stdBasis_repr_le fun r ↦ ?_
    have hcell := TauCeti.abs_sub_lt_one_div_of_natFloor_mul_eq (t := 3 / 2) (by norm_num)
      (by linarith [(abs_le.mp (hL hx (i, r))).1]) (by linarith [(abs_le.mp (hL hy (i, r))).1])
      (congr_fun hxy (i, r))
    rw [add_sub_add_right_eq_sub] at hcell
    have hsub : ∑ j, ((x - y) j : ℝ) * (stdBasis K).repr (mixedEmbedding K (a i j : K)) r =
        L x (i, r) - L y (i, r) := by
      simp [L, c, sub_mul, sum_sub_distrib]
    rw [stdBasis_repr_mulVec_intCast, hsub]
    linarith
  · obtain ⟨hx₁, hx₂⟩ := hT hx j
    obtain ⟨hy₁, hy₂⟩ := hT hy j
    calc |((x - y) j : ℝ)| ≤ B := by
          rw [Pi.sub_apply]
          exact_mod_cast (abs_le.mpr ⟨by linarith, by linarith⟩ : |x j - y j| ≤ (B : ℤ))
      _ ≤ _ := Nat.floor_le (by positivity)

omit [NumberField K] [Fintype α] in
/-- An integer solution `x` of `a x = 0` over `𝓞 K` solves every row equation in `K`:
`∑ⱼ aᵢⱼ xⱼ = 0`. -/
theorem sum_mul_intCast_eq_zero_of_mulVec_eq_zero {a : Matrix α β (𝓞 K)} {x : β → ℤ}
    (hax : a *ᵥ (fun j ↦ (x j : 𝓞 K)) = 0) (i : α) : ∑ j, (a i j : K) * x j = 0 := by
  simpa [Matrix.mulVec, dotProduct] using congrArg (algebraMap (𝓞 K) K) (congrFun hax i)

/-- For `1 ≤ x` and `0 ≤ e ≤ 1`, `c (c x) ^ e ≤ M M x` with `M = max 1 |c|`, whatever the sign
of `c`. -/
private theorem mul_rpow_le_max_one_abs_mul_max_one_abs {c x e : ℝ} (hx : 1 ≤ x) (he0 : 0 ≤ e)
    (he1 : e ≤ 1) : c * (c * x) ^ e ≤ max 1 |c| * max 1 |c| * x := by
  have hM : 1 ≤ max 1 |c| := le_max_left _ _
  have hcx : |c * x| ≤ max 1 |c| * x := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  calc c * (c * x) ^ e
      ≤ |c| * |c * x| ^ e := by
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (Real.abs_rpow_le_abs_rpow _ _) (abs_nonneg _)
    _ ≤ max 1 |c| * (max 1 |c| * x) ^ e :=
        mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow (abs_nonneg _) hcx he0)
          (by positivity) (by positivity)
    _ ≤ max 1 |c| * (max 1 |c| * x) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_self_of_one_le (one_le_mul_of_one_le_of_one_le hM hx) he1)
          (by positivity)
    _ = max 1 |c| * max 1 |c| * x := by ring

/-- **Siegel's lemma over `K` with a constant depending only on `K`.** There is `C ≥ 1` such that
every system `a ξ = 0` of linear equations over `𝓞 K` with `N ≥ 1` unknowns, at least twice as
many unknowns as equations, and coefficients of house at most `A ≥ 1` has a nonzero solution
`ξ` in `𝓞 K` whose entries have house at most `C N A`.

This is Mathlib's `NumberField.house.exists_ne_zero_int_vec_house_le`, whose bound
`c (c N A) ^ (M / (N - M))` for `M` equations has exponent at most `1` when `2 M ≤ N`; for the
zero system any vector with entries `1` is a solution. -/
theorem house.exists_const_ne_zero_int_vec_house_le (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (α : Type u) (β : Type v) [Fintype α] [Fintype β] [Nonempty β]
      (a : Matrix α β (𝓞 K)) (A : ℝ), 1 ≤ A → 2 * Fintype.card α ≤ Fintype.card β →
      (∀ i j, house (a i j : K) ≤ A) →
      ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧ ∀ l, house (ξ l : K) ≤ C * (Fintype.card β * A) := by
  classical
  -- The constant of Mathlib's Siegel lemma, which is not public, as a number `c`.
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ (α : Type u) (β : Type v) [Fintype α] [Fintype β]
      (a : Matrix α β (𝓞 K)), a ≠ 0 → 0 < Fintype.card α →
      Fintype.card α < Fintype.card β → ∀ A : ℝ, (∀ i j, house (a i j : K) ≤ A) →
      ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧ ∀ l, house (ξ l : K) ≤
        c * (c * Fintype.card β * A) ^
          ((Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α)) :=
    ⟨_, fun _ _ _ _ a ha hp hpq _ hA ↦ exists_ne_zero_int_vec_house_le K a ha hp hpq rfl hA rfl⟩
  have hM : 1 ≤ max 1 |c| := le_max_left _ _
  refine ⟨max 1 |c| * max 1 |c|, one_le_mul_of_one_le_of_one_le hM hM,
    fun α β _ _ _ a A hA hcard ha ↦ ?_⟩
  have hNA : 1 ≤ (Fintype.card β : ℝ) * A :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast Fintype.card_pos) hA
  by_cases ha0 : a = 0
  · refine ⟨fun _ ↦ 1, Function.ne_iff.mpr ⟨Classical.arbitrary β, one_ne_zero⟩,
      by simp [ha0], fun _ ↦ ?_⟩
    have h1 : house ((1 : 𝓞 K) : K) = 1 := by simpa using house_intCast (K := K) 1
    rw [h1]
    nlinarith [one_le_mul_of_one_le_of_one_le hM hM]
  have hp : 0 < Fintype.card α := by
    by_contra! h
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp h)
    exact ha0 (Subsingleton.elim _ _)
  obtain ⟨ξ, hξ0, hξ, hle⟩ := hc α β a ha0 hp (by omega) A ha
  refine ⟨ξ, hξ0, hξ, fun l ↦ (hle l).trans ?_⟩
  -- The exponent `M / (N - M)` lies in `[0, 1]` because `2 M ≤ N`.
  have hcard' : 2 * (Fintype.card α : ℝ) ≤ Fintype.card β := by exact_mod_cast hcard
  have hpos : 0 < (Fintype.card β : ℝ) - Fintype.card α := by
    have : (0 : ℝ) < Fintype.card α := by exact_mod_cast hp
    linarith
  rw [mul_assoc c]
  exact mul_rpow_le_max_one_abs_mul_max_one_abs hNA (div_nonneg (Nat.cast_nonneg _) hpos.le)
    ((div_le_one hpos).mpr (by linarith))

end NumberField
