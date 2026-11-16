/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.Complex.Exponential

import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import TauCeti.Algebra.Order.Floor.Semifield

/-!
# Thue–Siegel's lemma for small values of linear forms

Whereas Siegel's lemma (`Int.Matrix.exists_ne_zero_int_vec_norm_le`) produces a nonzero integer
solution of an underdetermined homogeneous linear system `A ξ = 0` over `ℤ`, transcendence proofs
over `ℂ` also need nonzero integer vectors `ξ` of bounded height at which a system of real or
complex linear forms takes *small* values without necessarily vanishing. This is the content of
Thue–Siegel's lemma as formulated by Waldschmidt (Lemmas 4.11 and 4.12):

* Over a linearly ordered field `K` with a natural floor, if `∑ᵢ |uᵢⱼ| ≤ Uⱼ` and `0 < ℓⱼ` for
  each form `j : κ`, and `∏ⱼ ℓⱼ < (X + 1) ^ |ι|`, then some nonzero `ξ : ι → ℤ` with `|ξᵢ| ≤ X`
  satisfies `|∑ᵢ uᵢⱼ ξᵢ| ≤ Uⱼ X / ℓⱼ` for every `j`.
* Over `ℂ`, for nonempty `ι`, `0 < X`, `∑ᵢ ‖uᵢⱼ‖ ≤ Aⱼ`, and `0 < εⱼ`, if
  `∏ⱼ (√2 · X · (Aⱼ / εⱼ) + 1) ^ 2 ≤ (X + 1) ^ |ι|`, then some nonzero `ξ : ι → ℤ` with
  `|ξᵢ| ≤ X` satisfies `‖∑ᵢ uᵢⱼ ξᵢ‖ ≤ εⱼ` for every `j`.

In particular, when `Aⱼ = exp U` and `εⱼ = exp (-V)` are uniform across the forms, the condition
becomes `(√2 · X · exp (U + V) + 1) ^ (2 |κ|) ≤ (X + 1) ^ |ι|`, and choosing `X = ⌊exp N⌋₊` yields
nonzero integer coefficients `|ξᵢ| ≤ exp N` for auxiliary analytic functions on polydiscs.

For `x ∈ [0, X]^ι`, shifting each linear form `∑ᵢ uᵢⱼ xᵢ` by `(∑ᵢ uᵢⱼ⁻) X` places its values in
`[0, Uⱼ X]` (of width `Uⱼ X`, rather than `[-Uⱼ X, Uⱼ X]` of width `2 Uⱼ X`), which accounts for
the sharp factor `√2` in the complex count.

## Main results

* `TauCeti.ThueSiegel.exists_ne_zero_int_vec_abs_le_of_prod_lt`: per-form Thue–Siegel lemma over a
  linearly ordered field with a natural floor.
* `TauCeti.ThueSiegel.exists_ne_zero_int_vec_abs_le_of_pow_lt`: uniform-bound version (Waldschmidt,
  Lemma 4.11).
* `TauCeti.ThueSiegel.exists_ne_zero_int_vec_norm_le_of_prod_le`: per-form complex Thue–Siegel
  lemma.
* `TauCeti.ThueSiegel.exists_ne_zero_int_vec_norm_le_of_pow_le`: uniform exponential-bound complex
  Thue–Siegel lemma (Waldschmidt, Lemma 4.12).
* `TauCeti.ThueSiegel.exists_ne_zero_int_vec_norm_le_of_one_le` and
  `TauCeti.ThueSiegel.exists_ne_zero_int_vec_norm_le_of_exp_le`: real-height corollaries producing
  `|(ξ i : ℝ)| ≤ B` (for `1 ≤ B`) and `|(ξ i : ℝ)| ≤ exp N` (for `0 ≤ N`).

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, Lemmas 4.11 and 4.12 (pp. 132–134) and
  Proposition 4.10 (pp. 131–132).
* Thue–Siegel's lemma for real and complex linear forms is also part of Michail Karatarakis's
  formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`, commit `1d51891b5b`,
  `Mathlib/NumberTheory/Transcendental/Baker/ThueSiegel.lean`, Apache 2.0).
-/

public section

namespace TauCeti.ThueSiegel

section OrderedField

variable {ι κ K : Type*} [Fintype ι] [Fintype κ]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

/-- **Thue–Siegel's lemma for linear forms over an ordered field, with per-form bounds.** Let
`u : ι → κ → K` be a family of linear forms over a linearly ordered field `K` with a natural floor,
with `∑ i, |u i j| ≤ U j` and `0 < ℓ j` for every `j`. If `∏ j, ℓ j < (X + 1) ^ Fintype.card ι`,
then there exists a nonzero integer vector `ξ : ι → ℤ` with `|ξ i| ≤ X` for every `i` and
`|∑ i, u i j * ξ i| ≤ U j * X / ℓ j` for every `j`. -/
theorem exists_ne_zero_int_vec_abs_le_of_prod_lt (u : ι → κ → K) {U : κ → K}
    (hU : ∀ j, ∑ i, |u i j| ≤ U j) {X : ℕ} {ℓ : κ → ℕ} (hℓ : ∀ j, 0 < ℓ j)
    (hcard : ∏ j, ℓ j < (X + 1) ^ Fintype.card ι) :
    ∃ ξ : ι → ℤ, ξ ≠ 0 ∧ (∀ i, |ξ i| ≤ (X : ℤ)) ∧
      ∀ j, |∑ i, u i j * ξ i| ≤ U j * X / ℓ j := by
  classical
  have hU0 (j : κ) : 0 ≤ U j := (Finset.sum_nonneg fun i _ ↦ abs_nonneg _).trans (hU j)
  -- Shifting `∑ i, u i j * x i` by `∑ i, (u i j)⁻ * X` maps `[0, X]^ι` into `∏ j, [0, U j * X]`.
  let s : (ι → ℤ) → κ → K := fun x j ↦ ∑ i, (u i j * (x i : K) + (u i j)⁻ * (X : K))
  let T : Finset (ι → ℤ) := Finset.Icc 0 fun _ ↦ (X : ℤ)
  have hs {x : ι → ℤ} (hx : x ∈ T) (j : κ) : s x j ∈ Set.Icc 0 (U j * X) := by
    obtain ⟨hx₀, hx₁⟩ := Finset.mem_Icc.1 hx
    have hid (i : ι) : u i j * (x i : K) + (u i j)⁻ * (X : K) =
        (u i j)⁺ * (x i : K) + (u i j)⁻ * ((X : K) - x i) := by
      nth_rw 1 [← posPart_sub_negPart (u i j)]
      ring
    refine ⟨Finset.sum_nonneg fun i _ ↦ ?_, ?_⟩
    · rw [hid i]
      exact add_nonneg (mul_nonneg (posPart_nonneg _) (Int.cast_nonneg (hx₀ i)))
        (mul_nonneg (negPart_nonneg _) (sub_nonneg.2 (by exact_mod_cast hx₁ i)))
    · calc s x j
          = ∑ i, ((u i j)⁺ * (x i : K) + (u i j)⁻ * ((X : K) - x i)) :=
            Finset.sum_congr rfl fun i _ ↦ hid i
        _ ≤ ∑ i, ((u i j)⁺ * (X : K) + (u i j)⁻ * (X : K)) :=
            Finset.sum_le_sum fun i _ ↦ add_le_add
              (mul_le_mul_of_nonneg_left (by exact_mod_cast hx₁ i) (posPart_nonneg _))
              (mul_le_mul_of_nonneg_left (sub_le_self _ (Int.cast_nonneg (hx₀ i)))
                (negPart_nonneg _))
        _ = (∑ i, |u i j|) * X := by
            simp_rw [← add_mul, posPart_add_negPart, ← Finset.sum_mul]
        _ ≤ U j * X := mul_le_mul_of_nonneg_right (hU j) (Nat.cast_nonneg X)
  let f : (ι → ℤ) → κ → ℕ := fun x j ↦ min (ℓ j - 1) ⌊s x j / (U j * X / ℓ j)⌋₊
  let S : Finset (κ → ℕ) := Fintype.piFinset fun j ↦ Finset.range (ℓ j)
  have hmaps : Set.MapsTo f T S := fun x _ ↦ by
    simp only [Finset.mem_coe, S, Fintype.mem_piFinset, Finset.mem_range]
    exact fun j ↦ (min_le_left _ _).trans_lt (Nat.sub_lt (hℓ j) zero_lt_one)
  have hlt : S.card < T.card := by
    simpa [S, T, Fintype.card_piFinset, Pi.card_Icc] using hcard
  obtain ⟨x, hx, y, hy, hne, hxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨x - y, sub_ne_zero.2 hne, fun i ↦ ?_, fun j ↦ ?_⟩
  · simp only [T, Finset.mem_Icc, Pi.le_def, Pi.zero_apply] at hx hy
    have := hx.1 i; have := hx.2 i; have := hy.1 i; have := hy.2 i
    rw [Pi.sub_apply]
    exact abs_le.2 ⟨by omega, by omega⟩
  · have hW : 0 ≤ U j * X := mul_nonneg (hU0 j) (Nat.cast_nonneg X)
    have hcell_x := mem_Icc_min_sub_one_natFloor_div hW (hℓ j) (hs hx j)
    have hcell_y := mem_Icc_min_sub_one_natFloor_div hW (hℓ j) (hs hy j)
    have hfj : min (ℓ j - 1) ⌊s x j / (U j * X / ℓ j)⌋₊ =
        min (ℓ j - 1) ⌊s y j / (U j * X / ℓ j)⌋₊ := congrFun hxy j
    rw [hfj] at hcell_x
    have hdiff : ∑ i, u i j * (((x - y) i : ℤ) : K) = s x j - s y j := by
      simp [s, Pi.sub_apply, mul_sub, ← Finset.sum_sub_distrib, add_sub_add_right_eq_sub]
    rw [hdiff]
    exact abs_sub_le_iff.2 ⟨by linarith [hcell_x.2, hcell_y.1], by linarith [hcell_y.2, hcell_x.1]⟩

/-- **Thue–Siegel's lemma for real linear forms** (Waldschmidt, Lemma 4.11), stated over any
linearly ordered field `K` with a natural floor. If `∑ i, |u i j| ≤ U` for every `j`, `0 < ℓ`, and
`ℓ ^ Fintype.card κ < (X + 1) ^ Fintype.card ι`, then some nonzero `ξ : ι → ℤ` has `|ξ i| ≤ X` for
every `i` and `|∑ i, u i j * ξ i| ≤ U * X / ℓ` for every `j`. -/
theorem exists_ne_zero_int_vec_abs_le_of_pow_lt (u : ι → κ → K) {U : K}
    (hU : ∀ j, ∑ i, |u i j| ≤ U) {X ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcard : ℓ ^ Fintype.card κ < (X + 1) ^ Fintype.card ι) :
    ∃ ξ : ι → ℤ, ξ ≠ 0 ∧ (∀ i, |ξ i| ≤ (X : ℤ)) ∧ ∀ j, |∑ i, u i j * ξ i| ≤ U * X / ℓ :=
  exists_ne_zero_int_vec_abs_le_of_prod_lt u hU (fun _ ↦ hℓ) (by simpa using hcard)

end OrderedField

section Complex

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

/-- **Thue–Siegel's lemma for complex linear forms, with per-form bounds.** For nonempty `ι` and
`0 < X`, if `∑ i, ‖u i j‖ ≤ A j` and `0 < ε j` for every `j`, and
`∏ j, (√2 * X * (A j / ε j) + 1) ^ 2 ≤ (X + 1) ^ Fintype.card ι`, then there exists a nonzero
`ξ : ι → ℤ` with `|ξ i| ≤ X` for every `i` and `‖∑ i, u i j * ξ i‖ ≤ ε j` for every `j`. -/
theorem exists_ne_zero_int_vec_norm_le_of_prod_le (u : ι → κ → ℂ) {A ε : κ → ℝ}
    (hA : ∀ j, ∑ i, ‖u i j‖ ≤ A j) (hε : ∀ j, 0 < ε j) {X : ℕ} (hX : 0 < X)
    (hcard : ∏ j, (Real.sqrt 2 * X * (A j / ε j) + 1) ^ 2 ≤ ((X : ℝ) + 1) ^ Fintype.card ι) :
    ∃ ξ : ι → ℤ, ξ ≠ 0 ∧ (∀ i, |ξ i| ≤ (X : ℤ)) ∧
      ∀ j, ‖∑ i, u i j * (ξ i : ℂ)‖ ≤ ε j := by
  classical
  have hA0 (j : κ) : 0 ≤ A j := (Finset.sum_nonneg fun i _ ↦ norm_nonneg _).trans (hA j)
  by_cases hA_zero : ∀ j, A j = 0
  · obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hX1 : (1 : ℤ) ≤ X := by exact_mod_cast hX
    refine ⟨fun _ ↦ 1, fun h ↦ one_ne_zero (congrFun h i₀), fun _ ↦ by simpa using hX1, fun j ↦ ?_⟩
    simpa using (norm_sum_le Finset.univ fun i ↦ u i j).trans
      ((hA j).trans (by rw [hA_zero j]; exact (hε j).le))
  · push Not at hA_zero
    obtain ⟨j₀, hj₀_ne⟩ := hA_zero
    let t : κ → ℝ := fun j ↦ Real.sqrt 2 * X * (A j / ε j)
    have ht0 (j : κ) : 0 ≤ t j :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Nat.cast_nonneg X))
        (div_nonneg (hA0 j) (hε j).le)
    have ht_pos : 0 < t j₀ := mul_pos (mul_pos (Real.sqrt_pos.2 two_pos) (Nat.cast_pos.2 hX))
      (div_pos ((hA0 j₀).lt_of_ne' hj₀_ne) (hε j₀))
    let ℓ : κ → ℕ := fun j ↦ max 1 ⌈t j⌉₊
    have hℓ (j : κ) : 0 < ℓ j := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
    have hprod_lt : (∏ p : κ × Bool, ℓ p.1) < (X + 1) ^ Fintype.card ι := by
      have hreal : ((∏ j, ℓ j ^ 2 : ℕ) : ℝ) < (((X + 1) ^ Fintype.card ι : ℕ) : ℝ) := by
        push_cast
        exact (Finset.prod_lt_prod₀ (fun j _ ↦ pow_pos (Nat.cast_pos.2 (hℓ j)) 2)
          (fun j _ ↦ pow_le_pow_left₀ (Nat.cast_nonneg _)
            (natCast_max_one_ceil_le_add_one (ht0 j)) 2)
          ⟨j₀, Finset.mem_univ j₀, pow_lt_pow_left₀ (natCast_max_one_ceil_lt_add_one ht_pos)
            (Nat.cast_nonneg _) two_ne_zero⟩).trans_le hcard
      simpa [Fintype.prod_prod_type] using Nat.cast_lt.1 hreal
    let v : ι → κ × Bool → ℝ := fun i p ↦ if p.2 then (u i p.1).re else (u i p.1).im
    have hv (p : κ × Bool) : ∑ i, |v i p| ≤ A p.1 := by
      refine (Finset.sum_le_sum fun i _ ↦ ?_).trans (hA p.1)
      rcases p with ⟨j, _ | _⟩
      · simpa [v] using Complex.abs_im_le_norm (u i j)
      · simpa [v] using Complex.abs_re_le_norm (u i j)
    obtain ⟨ξ, hξ0, hξX, hξv⟩ :=
      exists_ne_zero_int_vec_abs_le_of_prod_lt v hv (fun p ↦ hℓ p.1) hprod_lt
    refine ⟨ξ, hξ0, hξX, fun j ↦ ?_⟩
    have hre : |(∑ i, u i j * (ξ i : ℂ)).re| ≤ A j * X / ℓ j := by
      simpa [v, Complex.re_sum] using hξv (j, true)
    have him : |(∑ i, u i j * (ξ i : ℂ)).im| ≤ A j * X / ℓ j := by
      simpa [v, Complex.im_sum] using hξv (j, false)
    have hstep : Real.sqrt 2 * (A j * X / ℓ j) ≤ ε j := by
      have ht_le : Real.sqrt 2 * X * A j / ε j ≤ ℓ j := by
        simpa only [t, mul_div_assoc] using
          (Nat.le_ceil (t j)).trans (Nat.cast_le.2 (le_max_right 1 _))
      rw [← mul_div_assoc, div_le_iff₀ (Nat.cast_pos.2 (hℓ j))]
      linarith [(div_le_iff₀ (hε j)).1 ht_le]
    exact (Complex.norm_le_sqrt_two_mul_max _).trans
      ((mul_le_mul_of_nonneg_left (max_le hre him) (Real.sqrt_nonneg 2)).trans hstep)

/-- **Thue–Siegel's lemma for complex linear forms** (Waldschmidt, Lemma 4.12). For nonempty `ι`
and `0 < X`, if `∑ i, ‖u i j‖ ≤ exp U` for every `j` and
`(√2 * X * exp (U + V) + 1) ^ (2 * Fintype.card κ) ≤ (X + 1) ^ Fintype.card ι`, then some nonzero
`ξ : ι → ℤ` satisfies `|ξ i| ≤ X` for every `i` and `‖∑ i, u i j * ξ i‖ ≤ exp (-V)` for every
`j`. -/
theorem exists_ne_zero_int_vec_norm_le_of_pow_le (u : ι → κ → ℂ) {U V : ℝ}
    (hU : ∀ j, ∑ i, ‖u i j‖ ≤ Real.exp U) {X : ℕ} (hX : 0 < X)
    (hcard : (Real.sqrt 2 * X * Real.exp (U + V) + 1) ^ (2 * Fintype.card κ) ≤
      ((X : ℝ) + 1) ^ Fintype.card ι) :
    ∃ ξ : ι → ℤ, ξ ≠ 0 ∧ (∀ i, |ξ i| ≤ (X : ℤ)) ∧
      ∀ j, ‖∑ i, u i j * (ξ i : ℂ)‖ ≤ Real.exp (-V) := by
  refine exists_ne_zero_int_vec_norm_le_of_prod_le u hU (fun _ ↦ Real.exp_pos (-V)) hX ?_
  simpa [← Real.exp_sub, sub_neg_eq_add, pow_mul] using hcard

/-- **Thue–Siegel's lemma for complex linear forms with a real height bound `B ≥ 1`.** For nonempty
`ι` and `1 ≤ B`, if `∑ i, ‖u i j‖ ≤ A j` and `0 < ε j` for every `j`, and
`∏ j, (√2 * B * (A j / ε j) + 1) ^ 2 ≤ B ^ Fintype.card ι`, then some nonzero `ξ : ι → ℤ`
satisfies `|(ξ i : ℝ)| ≤ B` for every `i` and `‖∑ i, u i j * ξ i‖ ≤ ε j` for every `j`. -/
theorem exists_ne_zero_int_vec_norm_le_of_one_le (u : ι → κ → ℂ) {A ε : κ → ℝ}
    (hA : ∀ j, ∑ i, ‖u i j‖ ≤ A j) (hε : ∀ j, 0 < ε j) {B : ℝ} (hB : 1 ≤ B)
    (hcard : ∏ j, (Real.sqrt 2 * B * (A j / ε j) + 1) ^ 2 ≤ B ^ Fintype.card ι) :
    ∃ ξ : ι → ℤ, ξ ≠ 0 ∧ (∀ i, |(ξ i : ℝ)| ≤ B) ∧
      ∀ j, ‖∑ i, u i j * (ξ i : ℂ)‖ ≤ ε j := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hX : 0 < ⌊B⌋₊ := Nat.floor_pos.2 hB
  have hXB : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB0
  have hA0 (j : κ) : 0 ≤ A j := (Finset.sum_nonneg fun i _ ↦ norm_nonneg _).trans (hA j)
  have hcard' : ∏ j, (Real.sqrt 2 * ⌊B⌋₊ * (A j / ε j) + 1) ^ 2 ≤
      ((⌊B⌋₊ : ℝ) + 1) ^ Fintype.card ι := by
    calc ∏ j, (Real.sqrt 2 * ⌊B⌋₊ * (A j / ε j) + 1) ^ 2
        ≤ ∏ j, (Real.sqrt 2 * B * (A j / ε j) + 1) ^ 2 := by
          refine Finset.prod_le_prod₀ (fun _ _ ↦ sq_nonneg _) fun j _ ↦ ?_
          have hdiv : 0 ≤ A j / ε j := div_nonneg (hA0 j) (hε j).le
          gcongr
      _ ≤ B ^ Fintype.card ι := hcard
      _ ≤ ((⌊B⌋₊ : ℝ) + 1) ^ Fintype.card ι :=
          pow_le_pow_left₀ hB0 (Nat.lt_floor_add_one B).le _
  obtain ⟨ξ, hξ0, hξX, hξu⟩ := exists_ne_zero_int_vec_norm_le_of_prod_le u hA hε hX hcard'
  refine ⟨ξ, hξ0, fun i ↦ ?_, hξu⟩
  exact (by exact_mod_cast hξX i : |(ξ i : ℝ)| ≤ (⌊B⌋₊ : ℝ)).trans hXB

/-- **Exponential-height Thue–Siegel lemma for complex linear forms.** For nonempty `ι` and
`0 ≤ N`, if `∑ i, ‖u i j‖ ≤ exp U` for every `j` and
`(√2 * exp (N + U + V) + 1) ^ (2 * Fintype.card κ) ≤ exp (N * Fintype.card ι)`, then some nonzero
`ξ : ι → ℤ` satisfies `|(ξ i : ℝ)| ≤ exp N` for every `i` and
`‖∑ i, u i j * ξ i‖ ≤ exp (-V)` for every `j`. -/
theorem exists_ne_zero_int_vec_norm_le_of_exp_le (u : ι → κ → ℂ) {N U V : ℝ} (hN : 0 ≤ N)
    (hU : ∀ j, ∑ i, ‖u i j‖ ≤ Real.exp U)
    (hcard : (Real.sqrt 2 * Real.exp (N + U + V) + 1) ^ (2 * Fintype.card κ) ≤
      Real.exp (N * Fintype.card ι)) :
    ∃ ξ : ι → ℤ, ξ ≠ 0 ∧ (∀ i, |(ξ i : ℝ)| ≤ Real.exp N) ∧
      ∀ j, ‖∑ i, u i j * (ξ i : ℂ)‖ ≤ Real.exp (-V) := by
  refine exists_ne_zero_int_vec_norm_le_of_one_le u hU (fun _ ↦ Real.exp_pos (-V))
    (Real.one_le_exp hN) ?_
  have hexp : Real.exp N * (Real.exp U / Real.exp (-V)) = Real.exp (N + U + V) := by
    rw [← Real.exp_sub, ← Real.exp_add]
    congr 1
    ring
  simpa [mul_assoc, hexp, pow_mul, ← Real.exp_nat_mul, mul_comm (Fintype.card ι : ℝ)] using hcard

end Complex

end TauCeti.ThueSiegel
