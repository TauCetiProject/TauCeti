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
* `NumberField.exists_ne_zero_mulVec_eq_zero_house_le_rpow`: Siegel's lemma over `K` with unknowns
  in `𝓞 K`, wrapping Mathlib's `NumberField.house.exists_ne_zero_int_vec_house_le` for arbitrary
  finite index types and covering the zero matrix.
* `NumberField.exists_ne_zero_mulVec_eq_zero_house_le`: specialization of the above when
  `2 * card α ≤ card β`, bounding the house of every coordinate by `C * card β * A`.

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

variable {K : Type*} [Field K]

section

variable [NumberField K]

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

/-- The `stdBasis` coordinates of the mixed embedding of `a *ᵥ x` are the corresponding `ℤ`-linear
combinations of the coordinates of the entries of `a`. -/
theorem stdBasis_repr_mulVec_intCast {α β : Type*} [Fintype β] (a : Matrix α β (𝓞 K))
    (x : β → ℤ) (i : α) (r : index K) :
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

/-- **Siegel's lemma over a number field, with rational integer unknowns** (Evertse,
Theorem 3.20). Let `K` be a number field of degree `d` and `a` a matrix over `𝓞 K` with `M` rows
and `N` columns, whose entries have house at most `A ≥ 1`. If `d * M < N`, there is a nonzero
`x ∈ ℤ^N` with `a x = 0` and `|xⱼ| ≤ (3 N A) ^ (d M / (N - d M))` for every `j`. -/
theorem exists_ne_zero_int_vec_abs_le_of_house_le {α β : Type*} [Fintype α] [Fintype β]
    (a : Matrix α β (𝓞 K)) {A : ℝ} (hA : 1 ≤ A)
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

variable (K) in
/-- **Siegel's lemma over a number field, with algebraic integer unknowns**, wrapping Mathlib's
`NumberField.house.exists_ne_zero_int_vec_house_le` to quantify out its field-dependent constant
and cover the zero matrix. There is a constant `C ≥ 1` depending only on `K` such that for any
finite index types `α, β` with `card α < card β` and any matrix `a : Matrix α β (𝓞 K)` whose
entries have house at most `A ≥ 1`, there is a nonzero `ξ : β → 𝓞 K` with `a *ᵥ ξ = 0` and
`house (ξ j) ≤ C * (C * card β * A) ^ (card α / (card β - card α))` for every `j`. -/
theorem exists_ne_zero_mulVec_eq_zero_house_le_rpow :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {α β : Type*} [Fintype α] [Fintype β] (a : Matrix α β (𝓞 K)) {A : ℝ},
      Fintype.card α < Fintype.card β → 1 ≤ A →
      (∀ i j, house (a i j : K) ≤ A) →
      ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧
        ∀ j, house (ξ j : K) ≤
          C * (C * Fintype.card β * A) ^
            ((Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α)) := by
  classical
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ (p q : ℕ) (a : Matrix (Fin p) (Fin q) (𝓞 K)) (A : ℝ),
      a ≠ 0 → 0 < p → p < q → (∀ i j, house (algebraMap (𝓞 K) K (a i j)) ≤ A) →
      ∃ ξ : Fin q → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧
        ∀ j, house (ξ j : K) ≤ C₀ * (C₀ * q * A) ^ ((p : ℝ) / (q - p)) :=
    ⟨_, fun p q a A ha hp hpq hA ↦ house.exists_ne_zero_int_vec_house_le K a ha hp hpq
      (Fintype.card_fin q) hA (Fintype.card_fin p)⟩
  have hC₀_pos : 0 < C₀ := by
    obtain ⟨ξ₁, hξ₁0, -, hξ₁le⟩ := hC₀ 1 3 !![1, 0, 0] 1
      (fun h ↦ one_ne_zero (congrFun (congrFun h 0) 0)) zero_lt_one (by omega)
      (fun i j ↦ by
        fin_cases i; fin_cases j
        · simpa using (house_intCast (K := K) 1).le
        all_goals simpa using (house_intCast (K := K) 0).trans_le (by norm_num))
    obtain ⟨j₁, hj₁⟩ := Function.ne_iff.mp hξ₁0
    have hle := (one_le_house_of_isIntegral (ξ₁ j₁).property
      (RingOfIntegers.coe_ne_zero_iff.mpr hj₁)).trans (hξ₁le j₁)
    rw [show ((1 : ℕ) : ℝ) / ((3 : ℕ) - (1 : ℕ)) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at hle
    nlinarith [Real.sqrt_nonneg (C₀ * (3 : ℕ) * 1)]
  refine ⟨max 1 C₀, le_max_left 1 C₀, fun {α β} _ _ a {A} hαβ hA1 haA ↦ ?_⟩
  have hβ : 0 < Fintype.card β := (Nat.zero_le _).trans_lt hαβ
  have hsub : (0 : ℝ) < Fintype.card β - Fintype.card α :=
    sub_pos.mpr (by exact_mod_cast hαβ)
  have hexp_nn : 0 ≤ (Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α) :=
    div_nonneg (Nat.cast_nonneg _) hsub.le
  by_cases ha : a = 0
  · obtain ⟨j₀⟩ := Fintype.card_pos_iff.mp hβ
    refine ⟨fun _ ↦ 1, fun h ↦ one_ne_zero (congrFun h j₀), by simp [ha], fun _ ↦ ?_⟩
    have hbase : 1 ≤ max 1 C₀ * Fintype.card β * A :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (le_max_left 1 C₀) (by exact_mod_cast hβ)) hA1
    exact (by simpa using house_intCast (K := K) 1 : house ((1 : 𝓞 K) : K) = 1).trans_le
      (one_le_mul_of_one_le_of_one_le (le_max_left 1 C₀) (Real.one_le_rpow hbase hexp_nn))
  · let eα := Fintype.equivFin α
    let eβ := Fintype.equivFin β
    let a' := a.submatrix eα.symm eβ.symm
    have ha' : a' ≠ 0 := fun h ↦ ha (Matrix.ext fun i j ↦ by
      simpa [a'] using congrFun (congrFun h (eα i)) (eβ j))
    have hp0 : 0 < Fintype.card α := Nat.pos_of_ne_zero fun hp0 ↦
      ha' (Matrix.ext fun i ↦ Fin.elim0 (hp0 ▸ i))
    obtain ⟨ξ', hξ'0, hξ'eq, hξ'le⟩ := hC₀ _ _ a' A ha' hp0 hαβ fun _ _ ↦ haA _ _
    refine ⟨ξ' ∘ eβ, fun h ↦ hξ'0 (funext fun j ↦ by simpa using congrFun h (eβ.symm j)),
      funext fun i ↦ by
        simpa [Matrix.mulVec, dotProduct, a', Function.comp_def, ← eβ.symm.sum_comp] using
          congrFun hξ'eq (eα i),
      fun j ↦ (hξ'le (eβ j)).trans ?_⟩
    exact mul_le_mul (le_max_right 1 C₀)
      (Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right 1 C₀) (Nat.cast_nonneg _))
          (zero_le_one.trans hA1))
        hexp_nn)
      (Real.rpow_nonneg (by positivity) _) (zero_le_one.trans (le_max_left 1 C₀))

variable (K) in
/-- **Siegel's lemma over a number field with at most half as many equations as unknowns.**
There is a constant `C ≥ 1` depending only on `K` such that whenever `0 < card β` and
`2 * card α ≤ card β`, every matrix `a : Matrix α β (𝓞 K)` with entries of house at most `A ≥ 1`
has a nonzero kernel vector `ξ : β → 𝓞 K` with `house (ξ j) ≤ C * card β * A` for every `j`. -/
theorem exists_ne_zero_mulVec_eq_zero_house_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {α β : Type*} [Fintype α] [Fintype β] (a : Matrix α β (𝓞 K)) {A : ℝ},
      0 < Fintype.card β → 2 * Fintype.card α ≤ Fintype.card β → 1 ≤ A →
      (∀ i j, house (a i j : K) ≤ A) →
      ∃ ξ : β → 𝓞 K, ξ ≠ 0 ∧ a *ᵥ ξ = 0 ∧
        ∀ j, house (ξ j : K) ≤ C * Fintype.card β * A := by
  obtain ⟨C₀, hC₀, h⟩ := exists_ne_zero_mulVec_eq_zero_house_le_rpow K
  refine ⟨C₀ ^ 2, one_le_pow₀ hC₀, fun {α β} _ _ a {A} hβ hαβ hA ha ↦ ?_⟩
  obtain ⟨ξ, hξ0, hξeq, hξle⟩ := h a (by omega) hA ha
  refine ⟨ξ, hξ0, hξeq, fun j ↦ (hξle j).trans ?_⟩
  have hsub : (0 : ℝ) < Fintype.card β - Fintype.card α :=
    sub_pos.mpr (by exact_mod_cast (by omega : Fintype.card α < Fintype.card β))
  have hαβ' : (2 : ℝ) * Fintype.card α ≤ Fintype.card β := by exact_mod_cast hαβ
  have hexp : (Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α) ≤ 1 :=
    (div_le_one hsub).mpr (by linarith)
  have hbase : 1 ≤ C₀ * Fintype.card β * A :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC₀ (by exact_mod_cast hβ)) hA
  calc C₀ * (C₀ * Fintype.card β * A) ^
          ((Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α))
      ≤ C₀ * (C₀ * Fintype.card β * A) ^ (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase hexp)
          (zero_le_one.trans hC₀)
    _ = C₀ ^ 2 * Fintype.card β * A := by rw [Real.rpow_one]; ring

end

/-- An integer solution `x` of `a x = 0` over `𝓞 K` solves every row equation in `K`:
`∑ⱼ aᵢⱼ xⱼ = 0`. -/
theorem sum_mul_intCast_eq_zero_of_mulVec_eq_zero {α β : Type*} [Fintype β] {a : Matrix α β (𝓞 K)}
    {x : β → ℤ} (hax : a *ᵥ (fun j ↦ (x j : 𝓞 K)) = 0) (i : α) : ∑ j, (a i j : K) * x j = 0 := by
  simpa [Matrix.mulVec, dotProduct] using congrArg (algebraMap (𝓞 K) K) (congrFun hax i)

end NumberField
