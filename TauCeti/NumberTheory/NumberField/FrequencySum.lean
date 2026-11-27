/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import TauCeti.RingTheory.Localization.DenIdeal
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.ExpBound

/-!
# Sums over frequencies

Let `E` be a number field with `f` infinite places. For `ν ∈ E` let
`𝔡(ν) = {a ∈ 𝓞 E | a ν ∈ 𝓞 E}` be its denominator ideal (`Algebra.denIdeal E ν`). This file proves
that for every finite set `X ⊆ E`,
`∑_{ν ∈ X} ∏_v max (1, |ν|_v) ^ (-6) · N(𝔡(ν)) ^ (-3) ≤ (64 · 38 · e ^ 4) ^ f`,
a bound exponential in `f` only.

The numbers `ν` with a given denominator `𝔟` lie in `N(𝔟)` cosets of `𝓞 E`
(`NumberField.exists_label_fin_absNorm_of_ne_bot`). Inside one coset, two distinct numbers differ
by a nonzero algebraic integer, which has absolute value at least `1` at some infinite place. So the
map sending `ν` to the squares of side `1 / 2` containing its images in `ℂ` at the infinite places
is injective on the coset. On each such square, the weight `max (1, |z|) ^ (-6)` is at most `64`
times its value at the lower left corner, and the corner weights over all squares add up to at
most `38`. This bounds the sum over one coset by `(64 · 38) ^ f`
(`NumberField.sum_prod_inv_max_one_pow_six_le_of_sub_mem`). Summing `N(𝔟) · N(𝔟) ^ (-3)` over the
denominators leaves `∑ N(𝔟) ^ (-2) ≤ ζ_E(2) ≤ exp (2 [E : ℚ]) ≤ exp (4 f)`
(`TauCeti.sum_absNorm_rpow_neg_le_exp_two_mul_finrank`).

## Main results

* `NumberField.exists_label_fin_absNorm_of_ne_bot`: the numbers whose denominator ideal contains
  a nonzero ideal `𝔟` fall into at most `N(𝔟)` classes modulo `𝓞 E`.
* `NumberField.sum_prod_inv_max_one_pow_six_le_of_sub_mem`: the sum of
  `∏_v max (1, |ν|_v) ^ (-6)` over a finite set of numbers that pairwise differ by algebraic
  integers is at most `(64 · 38) ^ f`.
* `NumberField.sum_prod_inv_max_one_pow_six_mul_inv_absNorm_denIdeal_pow_three_le`: the bound
  above.

## Implementation notes

The absolute value `|Φ_v ν|` of `ν` under a complex embedding `Φ_v` at the infinite place `v` is
written `v ν`; it does not depend on the choice of `Φ_v`. The bound holds for every number field:
the last step only uses `[E : ℚ] ≤ 2 f`, which the infinite places of any number field satisfy.

The constant `38` is reached here by an elementary comparison rather than by a packing argument:
the corner weight at `(a / 2, b / 2)` is at most `h a · h b`, where `h a = 1` for `|a| ≤ 2` and
`h a = 3 / |a| ^ 3` otherwise, and the sum of `h` over any finite set of integers is at most
`215 / 36` (Mathlib's `sum_Ioo_inv_sq_le` bounds the tail), so the corner weights add up to at
most `(215 / 36) ^ 2 < 38`.

## References

* The statement and the route of the proof are adapted from the shorter formal proof of the Riemann
  hypothesis for Dirichlet `L`-functions (https://github.com/lsernau/grh-lean, Apache 2.0,
  Copyright 2026 Anthropic, PBC), file `src/New/Spanning/MainTerm/Frequencies.lean`: declarations
  `New.sum_height_inv_cube_le`, `New.sum_weight_filter_denominator_eq_le`,
  `New.sum_coset_weight_le`, `New.exists_coset_label`, `New.weight_le_weight_corner`,
  `New.squareIndex` and `New.squareCorner`. The bound
  on the corner weights there uses a packing bound for separated points.
-/

public section

open Finset NumberField NumberField.InfinitePlace
open scoped NumberField

/-! ### Squares of side `1 / 2` in the complex plane -/

namespace NumberField.FrequencySum

/-- The index `(⌊2 Re z⌋, ⌊2 Im z⌋)` of the half-open square of side `1 / 2` containing `z`. -/
noncomputable def squareIndex (z : ℂ) : ℤ × ℤ := (⌊2 * z.re⌋, ⌊2 * z.im⌋)

/-- The lower left corner `a / 2 + (b / 2) i` of the square with index `(a, b)`. -/
noncomputable def squareCorner (m : ℤ × ℤ) : ℂ := ⟨m.1 / 2, m.2 / 2⟩

/-- The first coordinate of `squareIndex z` is `⌊2 Re z⌋`. -/
@[simp]
theorem squareIndex_fst (z : ℂ) : (squareIndex z).1 = ⌊2 * z.re⌋ := by
  simp [squareIndex]

/-- The second coordinate of `squareIndex z` is `⌊2 Im z⌋`. -/
@[simp]
theorem squareIndex_snd (z : ℂ) : (squareIndex z).2 = ⌊2 * z.im⌋ := by
  simp [squareIndex]

/-- The real part of `squareCorner (a, b)` is `a / 2`. -/
@[simp]
theorem squareCorner_re (m : ℤ × ℤ) : (squareCorner m).re = m.1 / 2 := by
  simp [squareCorner]

/-- The imaginary part of `squareCorner (a, b)` is `b / 2`. -/
@[simp]
theorem squareCorner_im (m : ℤ × ℤ) : (squareCorner m).im = m.2 / 2 := by
  simp [squareCorner]

/-- Numbers in the same half-open square of side `1 / 2` are at distance less than `1`. -/
theorem norm_sub_lt_one_of_squareIndex_eq {z w : ℂ} (h : squareIndex z = squareIndex w) :
    ‖z - w‖ < 1 := by
  obtain ⟨h_re, h_im⟩ := Prod.ext_iff.1 h
  rw [squareIndex_fst, squareIndex_fst] at h_re
  rw [squareIndex_snd, squareIndex_snd] at h_im
  have h_half {a b : ℝ} (h_floor : ⌊2 * a⌋ = ⌊2 * b⌋) : |a - b| < 1 / 2 := by
    have := Int.abs_sub_lt_one_of_floor_eq_floor h_floor
    rw [← mul_sub, abs_mul, abs_two] at this
    linarith
  have h1 := h_half h_re
  have h2 := h_half h_im
  have := Complex.norm_le_abs_re_add_abs_im (z - w)
  rw [Complex.sub_re, Complex.sub_im] at this
  linarith

/-- A number is at distance less than `1` from the corner of its square. -/
theorem norm_squareCorner_squareIndex_sub_lt_one (z : ℂ) :
    ‖squareCorner (squareIndex z) - z‖ < 1 := by
  have h_floor (a : ℝ) : |(⌊2 * a⌋ : ℝ) / 2 - a| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [Int.floor_le (2 * a), Int.lt_floor_add_one (2 * a)]
  have h1 := h_floor z.re
  have h2 := h_floor z.im
  have hre : (squareCorner (squareIndex z) - z).re = (⌊2 * z.re⌋ : ℝ) / 2 - z.re := by
    simp
  have him : (squareCorner (squareIndex z) - z).im = (⌊2 * z.im⌋ : ℝ) / 2 - z.im := by
    simp
  have := Complex.norm_le_abs_re_add_abs_im (squareCorner (squareIndex z) - z)
  rw [hre, him] at this
  linarith

/-- On a square of side `1 / 2`, the weight `max (1, |z|) ^ (-6)` is at most `64` times its value
at the corner of the square. -/
theorem inv_max_one_norm_pow_six_le (z : ℂ) :
    (max 1 ‖z‖)⁻¹ ^ 6 ≤ 64 * (max 1 ‖squareCorner (squareIndex z)‖)⁻¹ ^ 6 := by
  have h_near := norm_squareCorner_squareIndex_sub_lt_one z
  have h_le : max 1 ‖squareCorner (squareIndex z)‖ ≤ 2 * max 1 ‖z‖ := by
    have := norm_sub_norm_le (squareCorner (squareIndex z)) z
    have h1 := le_max_left 1 ‖z‖
    have h2 := le_max_right 1 ‖z‖
    exact max_le (by linarith) (by linarith)
  calc (max 1 ‖z‖)⁻¹ ^ 6 = 64 * (2 * max 1 ‖z‖)⁻¹ ^ 6 := by ring
    _ ≤ _ := by gcongr

/-- The one-dimensional majorant of the corner weights: `1` on `|a| ≤ 2` and `3 / |a| ^ 3`
beyond. -/
private noncomputable def cornerMajorant (a : ℤ) : ℝ := if |a| ≤ 2 then 1 else 3 / |(a : ℝ)| ^ 3

/-- The majorant `cornerMajorant` is nonnegative. -/
private theorem cornerMajorant_nonneg (a : ℤ) : 0 ≤ cornerMajorant a := by
  unfold cornerMajorant
  split_ifs <;> positivity

/-- The majorant `cornerMajorant` is even. -/
private theorem cornerMajorant_neg (a : ℤ) : cornerMajorant (-a) = cornerMajorant a := by
  simp [cornerMajorant]

/-- The majorant over `1, …, N - 1` adds up to at most `179 / 72`: `1 + 1 + 1 / 9` on `1, 2, 3`,
and beyond `3`, `3 / n ^ 3 ≤ 3 / 4 · n ^ (-2)`, whose sum is bounded by `sum_Ioo_inv_sq_le`. -/
private theorem sum_Ico_cornerMajorant_le (N : ℕ) :
    ∑ n ∈ Ico 1 N, cornerMajorant n ≤ 179 / 72 := by
  have h_tail (n : ℕ) (hn : n ∈ Ioo 3 (N + 4)) :
      cornerMajorant n ≤ 3 / 4 * ((n : ℝ) ^ 2)⁻¹ := by
    have h3 := (mem_Ioo.1 hn).1
    have h4 : (4 : ℝ) ≤ n := by exact_mod_cast h3
    have : ¬|(n : ℤ)| ≤ 2 := by rw [abs_of_nonneg (by positivity)]; omega
    simp only [cornerMajorant, this, ↓reduceIte, Int.cast_natCast]
    rw [abs_of_nonneg (by positivity)]
    calc 3 / (n : ℝ) ^ 3 = 3 / (n * (n : ℝ) ^ 2) := by ring
      _ ≤ 3 / (4 * (n : ℝ) ^ 2) := by gcongr
      _ = 3 / 4 * ((n : ℝ) ^ 2)⁻¹ := by ring
  calc ∑ n ∈ Ico 1 N, cornerMajorant n ≤ ∑ n ∈ Ico 1 (N + 4), cornerMajorant n :=
        sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (by omega))
          fun _ _ _ ↦ cornerMajorant_nonneg _
    _ = ∑ n ∈ Ico 1 (3 + 1), cornerMajorant (n : ℕ) + ∑ n ∈ Ioo 3 (N + 4), cornerMajorant n := by
        rw [← Ico_add_one_left_eq_Ioo, sum_Ico_consecutive _ (by omega) (by omega)]
    _ ≤ 19 / 9 + ∑ n ∈ Ioo 3 (N + 4), 3 / 4 * ((n : ℝ) ^ 2)⁻¹ := by
        gcongr with n hn
        · norm_num [sum_Ico_succ_top, cornerMajorant]
        · exact h_tail n hn
    _ ≤ 19 / 9 + 3 / 4 * (2 / (3 + 1)) := by
        rw [← mul_sum]
        gcongr
        exact_mod_cast sum_Ioo_inv_sq_le 3 (N + 4)
    _ = 179 / 72 := by norm_num

/-- The majorant over a finite set of positive integers adds up to at most `179 / 72`. -/
private theorem sum_cornerMajorant_le_of_pos {t : Finset ℤ} (ht : ∀ a ∈ t, 0 < a) :
    ∑ a ∈ t, cornerMajorant a ≤ 179 / 72 := by
  have h_inj : Set.InjOn Int.toNat t := fun a ha b hb h ↦ by
    have := ht a ha; have := ht b hb; omega
  calc ∑ a ∈ t, cornerMajorant a = ∑ a ∈ t, cornerMajorant (a.toNat : ℤ) :=
        sum_congr rfl fun a ha ↦ by rw [Int.toNat_of_nonneg (ht a ha).le]
    _ = ∑ n ∈ t.image Int.toNat, cornerMajorant n :=
        (sum_image (f := fun n : ℕ ↦ cornerMajorant n) h_inj).symm
    _ ≤ ∑ n ∈ Ico 1 (t.sup Int.toNat + 1), cornerMajorant n := by
        refine sum_le_sum_of_subset_of_nonneg (fun n hn ↦ ?_) fun _ _ _ ↦ cornerMajorant_nonneg _
        obtain ⟨a, ha, rfl⟩ := mem_image.1 hn
        have := ht a ha
        have := le_sup (f := Int.toNat) ha
        rw [mem_Ico]
        omega
    _ ≤ 179 / 72 := sum_Ico_cornerMajorant_le _

/-- The majorant over a finite set of integers adds up to at most `215 / 36`: `1` at `0`, and at
most `179 / 72` on either side. -/
private theorem sum_cornerMajorant_le (t : Finset ℤ) :
    ∑ a ∈ t, cornerMajorant a ≤ 215 / 36 := by
  classical
  have h_split := sum_filter_add_sum_filter_not t (0 < ·) cornerMajorant
  have h_split' := sum_filter_add_sum_filter_not (t.filter fun a ↦ ¬0 < a) (· = 0) cornerMajorant
  have h_pos := sum_cornerMajorant_le_of_pos (t := t.filter (0 < ·)) (by simp +contextual)
  have h_zero : ∑ a ∈ (t.filter fun a ↦ ¬0 < a).filter (· = 0), cornerMajorant a ≤ 1 := by
    refine (sum_le_sum_of_subset_of_nonneg (t := {0}) ?_
      fun _ _ _ ↦ cornerMajorant_nonneg _).trans (by simp [cornerMajorant])
    intro a; simp +contextual
  have h_neg : ∑ a ∈ (t.filter fun a ↦ ¬0 < a).filter (¬· = 0), cornerMajorant a ≤ 179 / 72 := by
    rw [← sum_congr rfl fun a _ ↦ cornerMajorant_neg a,
      ← sum_image (g := Neg.neg) (f := cornerMajorant) fun a _ b _ h ↦ neg_injective h]
    refine sum_cornerMajorant_le_of_pos fun b hb ↦ ?_
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hb
    simp only [mem_filter] at ha
    omega
  linarith

/-- Away from the origin, the corner weight at `(a / 2, b / 2)` is at most
`64 / (a ^ 2 + b ^ 2) ^ 3`. -/
private theorem inv_max_one_norm_squareCorner_pow_six_le_of_pos {a b : ℤ}
    (hab : 0 < (a : ℝ) ^ 2 + (b : ℝ) ^ 2) :
    (max 1 ‖squareCorner (a, b)‖)⁻¹ ^ 6 ≤ 64 / ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) ^ 3 := by
  have h_sq : ‖squareCorner (a, b)‖ ^ 2 = ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / 4 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rw [squareCorner_re, squareCorner_im]
    ring
  have h_pos : 0 < ‖squareCorner (a, b)‖ :=
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
      (by rw [h_sq, zero_pow two_ne_zero]; exact div_pos hab (by norm_num))
  calc (max 1 ‖squareCorner (a, b)‖)⁻¹ ^ 6 ≤ ‖squareCorner (a, b)‖⁻¹ ^ 6 := by
        gcongr; exact le_max_right _ _
    _ = 64 / ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) ^ 3 := by
        rw [inv_pow, show ‖squareCorner (a, b)‖ ^ 6 = (‖squareCorner (a, b)‖ ^ 2) ^ 3 by ring,
          h_sq]
        field_simp
        ring

/-- If `3 ≤ |c|` and `c ^ 2 ≤ x`, then `64 / x ^ 3 ≤ 3 / |c| ^ 3`. -/
private theorem sixty_four_div_pow_three_le {x c : ℝ} (hc : 3 ≤ |c|) (hx : c ^ 2 ≤ x) :
    64 / x ^ 3 ≤ 3 / |c| ^ 3 := by
  have h_pos : 0 < x := by nlinarith [sq_abs c]
  have h6 : (|c| ^ 2) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by positivity) (by rwa [sq_abs]) 3
  have h27 : (27 : ℝ) ≤ |c| ^ 3 := by nlinarith
  rw [div_le_div_iff₀ (pow_pos h_pos 3) (by positivity)]
  nlinarith

/-- The corner weight at `(a / 2, b / 2)` is at most `cornerMajorant a * cornerMajorant b`. -/
private theorem inv_max_one_norm_squareCorner_pow_six_le (m : ℤ × ℤ) :
    (max 1 ‖squareCorner m‖)⁻¹ ^ 6 ≤ cornerMajorant m.1 * cornerMajorant m.2 := by
  obtain ⟨a, b⟩ := m
  have h_one : (max 1 ‖squareCorner (a, b)‖)⁻¹ ^ 6 ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (le_max_left _ _))
  have h_far := @inv_max_one_norm_squareCorner_pow_six_le_of_pos a b
  simp only [cornerMajorant]
  have hA : (a : ℝ) ^ 2 = |(a : ℝ)| ^ 2 := (sq_abs _).symm
  have hB : (b : ℝ) ^ 2 = |(b : ℝ)| ^ 2 := (sq_abs _).symm
  have h_three {c : ℤ} (hc : ¬|c| ≤ 2) : (3 : ℝ) ≤ |(c : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast (by omega : (3 : ℤ) ≤ |c|)
  split_ifs with ha hb hb
  · simpa using h_one
  · -- `|b| ≥ 3`: the weight is at most `64 / b ^ 6 ≤ 3 / |b| ^ 3`.
    have hb3 := h_three hb
    rw [one_mul]
    exact (h_far (by nlinarith)).trans (sixty_four_div_pow_three_le hb3 (by nlinarith))
  · have ha3 := h_three ha
    rw [mul_one]
    exact (h_far (by nlinarith)).trans (sixty_four_div_pow_three_le ha3 (by nlinarith))
  · have ha3 := h_three ha
    have hb3 := h_three hb
    have h_pos : 0 < (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by nlinarith
    refine (h_far h_pos).trans ?_
    -- `(a ^ 2 + b ^ 2) ^ 3 ≥ (2 |a| |b|) ^ 3 = 8 |a| ^ 3 |b| ^ 3`.
    have h_amgm : 2 * |(a : ℝ)| * |(b : ℝ)| ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (|(a : ℝ)| - |(b : ℝ)|)]
    have h_cube := pow_le_pow_left₀ (by positivity) h_amgm 3
    have hab3 : 0 < |(a : ℝ)| ^ 3 * |(b : ℝ)| ^ 3 := by positivity
    rw [div_mul_div_comm, div_le_div_iff₀ (pow_pos h_pos 3) (by positivity)]
    nlinarith

/-- Over any finite set of squares, the corner weights add up to at most `38`. -/
theorem sum_inv_max_one_norm_squareCorner_pow_six_le (s : Finset (ℤ × ℤ)) :
    ∑ m ∈ s, (max 1 ‖squareCorner m‖)⁻¹ ^ 6 ≤ 38 := by
  calc ∑ m ∈ s, (max 1 ‖squareCorner m‖)⁻¹ ^ 6
      ≤ ∑ m ∈ s.image Prod.fst ×ˢ s.image Prod.snd, cornerMajorant m.1 * cornerMajorant m.2 :=
        (sum_le_sum fun m _ ↦ inv_max_one_norm_squareCorner_pow_six_le m).trans <|
          sum_le_sum_of_subset_of_nonneg
            (fun m hm ↦ mem_product.2 ⟨mem_image_of_mem _ hm, mem_image_of_mem _ hm⟩)
            fun m _ _ ↦ mul_nonneg (cornerMajorant_nonneg _) (cornerMajorant_nonneg _)
    _ = (∑ a ∈ s.image Prod.fst, cornerMajorant a) * ∑ b ∈ s.image Prod.snd, cornerMajorant b :=
        by rw [sum_product, sum_mul_sum]
    _ ≤ 215 / 36 * (215 / 36) := by
        gcongr
        · exact sum_nonneg fun _ _ ↦ cornerMajorant_nonneg _
        · exact sum_cornerMajorant_le _
        · exact sum_cornerMajorant_le _
    _ ≤ 38 := by norm_num

end NumberField.FrequencySum

/-! ### Cosets of the ring of integers -/

namespace NumberField

open FrequencySum

variable {E : Type*} [Field E] [NumberField E]

/-- **The numbers with a given denominator lie in `N(𝔟)` cosets of the integers.** For a nonzero
ideal `𝔟` of `𝓞 E`, the numbers `ν` with `𝔟 ≤ 𝔡(ν)`, where `𝔡(ν) = Algebra.denIdeal E ν` is the
ideal of the integers `a` with `a ν` integral, can be labelled by `Fin (N(𝔟))` so that numbers
with the same label differ by an element of `𝓞 E`. -/
theorem exists_label_fin_absNorm_of_ne_bot {𝔟 : Ideal (𝓞 E)} (h𝔟 : 𝔟 ≠ ⊥) :
    ∃ label : E → Fin (Ideal.absNorm 𝔟), ∀ ν ν' : E, 𝔟 ≤ Algebra.denIdeal E ν →
      𝔟 ≤ Algebra.denIdeal E ν' → label ν = label ν' →
        ∃ t : 𝓞 E, algebraMap (𝓞 E) E t = ν - ν' := by
  -- Write `(a) = 𝔟 𝔠` with `a ∈ 𝔟` nonzero. Multiplication by `a` maps these numbers into `𝔠`
  -- and the integers onto `(a)`, and `𝔠 / (a)` has `N(𝔟)` elements.
  obtain ⟨a, ha, ha_ne⟩ := (Submodule.ne_bot_iff 𝔟).1 h𝔟
  obtain ⟨𝔠, h𝔠⟩ : 𝔟 ∣ Ideal.span {a} := Ideal.dvd_span_singleton.2 ha
  have h_lift (ν : E) (hν : 𝔟 ≤ Algebra.denIdeal E ν) :
      ∃ x : 𝔠, algebraMap (𝓞 E) E (x : 𝓞 E) = algebraMap (𝓞 E) E a * ν := by
    have h_mem (r : 𝓞 E) (hr : r ∈ 𝔟) : ∃ y : 𝓞 E, algebraMap (𝓞 E) E r * ν =
        algebraMap (𝓞 E) E y := Algebra.mem_denIdeal_iff E |>.1 (hν hr)
    obtain ⟨x, hx⟩ := h_mem a ha
    -- `𝔟 · (x) ⊆ (a) = 𝔟 𝔠`, so `(x) ⊆ 𝔠` after cancelling `𝔟`.
    have h_le : 𝔟 * Ideal.span {x} ≤ 𝔟 * 𝔠 := by
      rw [← h𝔠, mul_comm, Ideal.span_singleton_mul_le_iff]
      intro r hr
      obtain ⟨y, hy⟩ := h_mem r hr
      refine Ideal.mem_span_singleton'.2 ⟨y, IsFractionRing.injective (𝓞 E) E ?_⟩
      rw [map_mul, map_mul, ← hx, ← hy]
      ring
    have h_dvd : 𝔠 ∣ Ideal.span {x} := (mul_dvd_mul_iff_left h𝔟).1 (Ideal.dvd_iff_le.2 h_le)
    exact ⟨⟨x, Ideal.dvd_span_singleton.1 h_dvd⟩, hx.symm⟩
  choose! x hx using h_lift
  let A : AddSubgroup 𝔠 := (Ideal.span {a}).toAddSubgroup.addSubgroupOf 𝔠.toAddSubgroup
  have h𝔠_ne : 𝔠 ≠ ⊥ := fun h ↦ ha_ne (by simpa [h] using h𝔠)
  have h_index : A.index = Ideal.absNorm 𝔟 := by
    have h_tower : A.index * Ideal.absNorm 𝔠 = Ideal.absNorm (Ideal.span {a}) := by
      -- `AddSubgroup.relIndex` is defined as the index of `addSubgroupOf`, which is `A.index`.
      have := AddSubgroup.relIndex_mul_index <|
        (Submodule.toAddSubgroup_le _ _).2 (h𝔠.trans_le Ideal.mul_le_right)
      rwa [AddSubgroup.relIndex, ← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index] at this
    simpa [h𝔠, Ideal.absNorm_eq_zero_iff, h𝔠_ne] using h_tower
  have : Finite (𝔠 ⧸ A) := AddSubgroup.index_ne_zero_iff_finite.1 <| by
    rwa [h_index, Ne, Ideal.absNorm_eq_zero_iff]
  let e : 𝔠 ⧸ A ≃ Fin (Ideal.absNorm 𝔟) := Finite.equivFinOfCardEq h_index
  refine ⟨fun ν ↦ e (QuotientAddGroup.mk (x ν)), fun ν ν' hν hν' h_label ↦ ?_⟩
  have h_mem : x ν - x ν' ∈ A := QuotientAddGroup.eq_iff_sub_mem.1 (e.injective h_label)
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 E, t * a = x ν - x ν' :=
    Ideal.mem_span_singleton'.1 (AddSubgroup.mem_addSubgroupOf.1 h_mem)
  refine ⟨t, mul_left_cancel₀ (show algebraMap (𝓞 E) E a ≠ 0 by simpa using ha_ne) ?_⟩
  rw [mul_comm, ← map_mul, ht, map_sub, hx ν hν, hx ν' hν', mul_sub]

/-- **The weights over one coset of the integers.** Let `X` be a finite set of numbers of `E` any
two of which differ by an element of `𝓞 E`. Then `∑_{ν ∈ X} ∏_v max (1, v ν) ^ (-6)` is at most
`(64 · 38) ^ f`, where `f` is the number of infinite places `v` of `E`. -/
theorem sum_prod_inv_max_one_pow_six_le_of_sub_mem {X : Finset E}
    (hX : ∀ ν ∈ X, ∀ ν' ∈ X, ∃ t : 𝓞 E, algebraMap (𝓞 E) E t = ν - ν') :
    ∑ ν ∈ X, ∏ v : InfinitePlace E, (max 1 (v ν))⁻¹ ^ 6 ≤
      (64 * 38) ^ Fintype.card (InfinitePlace E) := by
  classical
  -- A product of squares of side `1 / 2`, one at each infinite place, holds at most one point of
  -- `X`: a nonzero algebraic integer has absolute value at least `1` at some infinite place.
  let cell (ν : E) (v : InfinitePlace E) : ℤ × ℤ := squareIndex (v.embedding ν)
  let w (m : ℤ × ℤ) : ℝ := 64 * (max 1 ‖squareCorner m‖)⁻¹ ^ 6
  have h_inj : Set.InjOn cell X := by
    intro ν hν ν' hν' h_cell
    by_contra h_ne
    obtain ⟨t, ht⟩ := hX ν hν ν' hν'
    have ht0 : t ≠ 0 := by rintro rfl; exact h_ne (sub_eq_zero.1 (by simpa using ht.symm))
    have h_lt (v : InfinitePlace E) : v (t : E) < 1 := by
      rw [← norm_embedding_eq, RingOfIntegers.coe_eq_algebraMap, ht, map_sub]
      exact norm_sub_lt_one_of_squareIndex_eq (congrFun h_cell v)
    obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact (one_le_of_lt_one ht0 fun z _ ↦ h_lt z).not_gt (h_lt v)
  let cells (v : InfinitePlace E) : Finset (ℤ × ℤ) := X.image fun ν ↦ cell ν v
  calc ∑ ν ∈ X, ∏ v : InfinitePlace E, (max 1 (v ν))⁻¹ ^ 6
      ≤ ∑ ν ∈ X, ∏ v : InfinitePlace E, w (cell ν v) := by
        gcongr with ν _ v
        rw [← norm_embedding_eq]
        exact inv_max_one_norm_pow_six_le _
    _ = ∑ c ∈ X.image cell, ∏ v : InfinitePlace E, w (c v) := by
        rw [sum_image h_inj]
    _ ≤ ∑ c ∈ Fintype.piFinset cells, ∏ v : InfinitePlace E, w (c v) := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ prod_nonneg fun _ _ ↦ by positivity
        exact image_subset_iff.2 fun ν hν ↦ Fintype.mem_piFinset.2 fun v ↦ mem_image_of_mem _ hν
    _ = ∏ v : InfinitePlace E, ∑ m ∈ cells v, w m := (prod_univ_sum cells fun _ ↦ w).symm
    _ ≤ ∏ _v : InfinitePlace E, (64 * 38 : ℝ) := by
        gcongr with v
        rw [← mul_sum]
        gcongr
        exact sum_inv_max_one_norm_squareCorner_pow_six_le _
    _ = _ := by simp

/-- The weights of the numbers in a finite set `X` with a given nonzero denominator ideal `𝔟` add
up to at most `N(𝔟) · (64 · 38) ^ f`, as these numbers lie in at most `N(𝔟)` cosets of the
integers. -/
theorem sum_filter_denIdeal_eq_prod_inv_max_one_pow_six_le (X : Finset E) {𝔟 : Ideal (𝓞 E)}
    (h𝔟 : 𝔟 ≠ ⊥) :
    ∑ ν ∈ X with Algebra.denIdeal E ν = 𝔟, ∏ v : InfinitePlace E, (max 1 (v ν))⁻¹ ^ 6 ≤
      Ideal.absNorm 𝔟 * (64 * 38) ^ Fintype.card (InfinitePlace E) := by
  classical
  obtain ⟨label, h_label⟩ := exists_label_fin_absNorm_of_ne_bot h𝔟
  calc _ = ∑ k : Fin (Ideal.absNorm 𝔟), ∑ ν ∈ X with Algebra.denIdeal E ν = 𝔟 ∧ label ν = k,
          ∏ v : InfinitePlace E, (max 1 (v ν))⁻¹ ^ 6 := by
        rw [← sum_fiberwise (X.filter fun ν ↦ Algebra.denIdeal E ν = 𝔟) label]
        simp only [filter_filter]
    _ ≤ ∑ _k : Fin (Ideal.absNorm 𝔟), (64 * 38 : ℝ) ^ Fintype.card (InfinitePlace E) := by
        refine sum_le_sum fun k _ ↦ sum_prod_inv_max_one_pow_six_le_of_sub_mem ?_
        intro ν hν ν' hν'
        simp only [mem_filter] at hν hν'
        exact h_label ν ν' hν.2.1.ge hν'.2.1.ge (hν.2.2.trans hν'.2.2.symm)
    _ = _ := by simp

/-- **Sums over frequencies.** Let `E` be a number field with `f` infinite places. For every
finite set `X ⊆ E`,
`∑_{ν ∈ X} ∏_v max (1, v ν) ^ (-6) · N(𝔡(ν)) ^ (-3) ≤ (64 · 38 · e ^ 4) ^ f`, where
`𝔡(ν) = Algebra.denIdeal E ν` is the ideal of the integers `a` with `a ν` integral. -/
theorem sum_prod_inv_max_one_pow_six_mul_inv_absNorm_denIdeal_pow_three_le (X : Finset E) :
    ∑ ν ∈ X, (∏ v : InfinitePlace E, (max 1 (v ν))⁻¹ ^ 6) *
        (Ideal.absNorm (Algebra.denIdeal (R := 𝓞 E) E ν) : ℝ)⁻¹ ^ 3 ≤
      (64 * 38 * Real.exp 4) ^ Fintype.card (InfinitePlace E) := by
  classical
  have h_ne (ν : E) : Algebra.denIdeal (R := 𝓞 E) E ν ≠ (⊥ : Ideal (𝓞 E)) :=
    Algebra.denIdeal_ne_bot E (nonZeroDivisors (𝓞 E)) ν
  -- Group the numbers by their denominator ideal.
  calc _ = ∑ 𝔟 ∈ X.image (Algebra.denIdeal (R := 𝓞 E) E),
          (∑ ν ∈ X with Algebra.denIdeal (R := 𝓞 E) E ν = 𝔟,
          ∏ v : InfinitePlace E, (max 1 (v ν))⁻¹ ^ 6) * (Ideal.absNorm 𝔟 : ℝ)⁻¹ ^ 3 := by
        rw [← sum_fiberwise_of_maps_to fun ν hν ↦
          mem_image_of_mem (Algebra.denIdeal (R := 𝓞 E) E) hν]
        simp_rw [sum_mul]
        exact sum_congr rfl fun 𝔟 _ ↦ sum_congr rfl fun ν hν ↦ by rw [(mem_filter.1 hν).2]
    _ ≤ ∑ 𝔟 ∈ X.image (Algebra.denIdeal (R := 𝓞 E) E),
          (64 * 38) ^ Fintype.card (InfinitePlace E) * (Ideal.absNorm 𝔟 : ℝ) ^ (-(2 : ℝ)) := by
        refine sum_le_sum (forall_mem_image.2 fun ν _ ↦ ?_)
        have hN : (0 : ℝ) < Ideal.absNorm (Algebra.denIdeal (R := 𝓞 E) E ν) := by
          exact_mod_cast Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h_ne ν)
        grw [sum_filter_denIdeal_eq_prod_inv_max_one_pow_six_le X (h_ne ν)]
        rw [Real.rpow_neg hN.le, Real.rpow_two]
        exact le_of_eq (by field_simp)
    _ ≤ (64 * 38) ^ Fintype.card (InfinitePlace E) * Real.exp (2 * Module.finrank ℚ E) := by
        rw [← mul_sum]
        gcongr
        exact TauCeti.sum_absNorm_rpow_neg_le_exp_two_mul_finrank le_rfl _
    _ ≤ (64 * 38) ^ Fintype.card (InfinitePlace E) *
          Real.exp 4 ^ Fintype.card (InfinitePlace E) := by
        -- `[E : ℚ] = r₁ + 2 r₂ ≤ 2 (r₁ + r₂) = 2 f`.
        have h_rank : (Module.finrank ℚ E : ℝ) ≤ 2 * Fintype.card (InfinitePlace E) := by
          have := card_add_two_mul_card_eq_rank E
          have := card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
          exact_mod_cast (by omega : Module.finrank ℚ E ≤ 2 * Fintype.card (InfinitePlace E))
        rw [← Real.exp_natCast_mul]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
    _ = _ := (mul_pow _ _ _).symm

end NumberField
