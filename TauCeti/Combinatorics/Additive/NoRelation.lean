/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import TauCeti.Data.Int.Digits
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Sets of integers with no relation of length `L`

A set `T ⊆ ℤ` has *no relation of length `L`* (`TauCeti.NoRelation L T`) if there are no pairwise
distinct `s₁, s₂, s₃ ∈ T` and integers `i ≠ j` with `0 < |i|, |j| ≤ L` and
`j (s₂ - s₁) = i (s₃ - s₁)`. For `i = 1`, `j = -1` such a relation says that `s₁` is the midpoint
of `s₂` and `s₃`, so for `L ≥ 1` these sets contain no three-term arithmetic progression.

Behrend's construction gives large such sets. The points of `Behrend.sphere n D R` (the vectors
of `{0, …, D - 1}ⁿ` with `∑ k, x k ^ 2 = R`) are read as base-`B` digits by `Behrend.map B`. If
`2 L (D - 1) < B`, a relation `j (s₂ - s₁) = i (s₃ - s₁)` among the images has all its digits
`j (x₂ k - x₁ k) - i (x₃ k - x₁ k)` of absolute value less than `B`, so it holds coordinatewise
(`Int.eq_zero_of_sum_mul_pow_eq_zero`).
On a sphere, `j (x₂ - x₁) = i (x₃ - x₁)` with `j ≠ 0` and `i ≠ j` forces `x₁ = x₂`: indeed
`j (j - i) ‖x₂ - x₁‖² = i² (‖x₃‖² - ‖x₁‖²) - i j (‖x₂‖² - ‖x₁‖²) = 0`. With `B = 4 L D`,
`n = ⌈(log M / log L) ^ (1/2)⌉` and `D` maximal with `4 L (4 L D) ^ n ≤ M`, a sphere carrying at
least `D ^ n / (n D ^ 2)` points (`Behrend.exists_large_sphere`) gives the bound of
`TauCeti.exists_noRelation`, with the constant `C = 14`; when `4 L (4 L) ^ n > M` the single point
`{0}` suffices.

## Main definitions

* `TauCeti.NoRelation L T`: the set `T ⊆ ℤ` has no relation of length `L`.

## Main results

* `TauCeti.NoRelation.mono`, `TauCeti.NoRelation.of_le`: the predicate passes to subsets and to
  shorter lengths.
* `TauCeti.NoRelation.threeAPFree`: for `L ≠ 0`, a set with no relation of length `L` is
  `ThreeAPFree`.
* `TauCeti.noRelation_vadd_set`: the predicate is invariant under translation.
* `Behrend.map_lt_pow`: digits below `d` give a value of `Behrend.map d` below `d ^ n`.
* `TauCeti.noRelation_image_map_sphere`: for `2 L (D - 1) < B`, the image of
  `Behrend.sphere n D R` under `Behrend.map B` has no relation of length `L`.
* `TauCeti.exists_noRelation_of_two_mul_lt`: for `2 L (D - 1) < B` and `D ≤ B` there is
  `T ⊆ [0, B ^ n)` with no relation of length `L` and `D ^ n / (n D ^ 2) ≤ |T| ≤ D ^ n`.
* `TauCeti.exists_noRelation`: there is a constant `C` such that for all `M ≥ 1` and `L ≥ 2` some
  nonempty `T ⊆ [0, M / (4 L))` has no relation of length `L` and
  `|T| ≥ M exp (-C (log M log L) ^ (1/2)) / L`, and `|T| ≤ M / (4 L)` when `4 L ≤ M`.

## References

* F. A. Behrend, *On sets of integers which contain no three terms in arithmetical progression*,
  Proc. Nat. Acad. Sci. 32 (1946), 331–332.
* I. Z. Ruzsa, *Solving a linear equation in a set of integers I*, Acta Arith. 65 (1993),
  259–282.
* L. Alpöge et al., Lean formalization of the Riemann hypothesis for Dirichlet L-functions,
  https://github.com/leanprover-community/riemann-hypothesis: the predicate is
  `Formalism.FrobeniusOrbits.NoRel` and the existence theorem
  `Formalism.FrobeniusOrbits.HostThickExists` (proved as
  `Formalism.FrobeniusOrbits.hostThickExists`). They are the source of the statements here; that
  development has no licence file and was not read, and the proofs here are independent.
-/

public section

open Finset Real
open scoped Pointwise

namespace Behrend

/-- If every coordinate of `x` is less than `d`, then `Behrend.map d x < d ^ n`. -/
theorem map_lt_pow {n d : ℕ} {x : Fin n → ℕ} (hx : ∀ k, x k < d) : map d x < d ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ih (x := x ∘ Fin.succ) fun k => hx k.succ
    have h0 := hx 0
    rw [map_succ', pow_succ]
    linarith [Nat.mul_le_mul_right d (Nat.succ_le_of_lt h)]

end Behrend

namespace TauCeti

/-- A set `T ⊆ ℤ` has *no relation of length `L`* if there are no pairwise distinct
`s₁, s₂, s₃ ∈ T` and integers `i ≠ j` with `0 < |i|, |j| ≤ L` and `j (s₂ - s₁) = i (s₃ - s₁)`. -/
def NoRelation (L : ℕ) (T : Set ℤ) : Prop :=
  ∀ s₁ ∈ T, ∀ s₂ ∈ T, ∀ s₃ ∈ T, s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ → ∀ i j : ℤ, i ≠ j →
    0 < |i| → |i| ≤ L → 0 < |j| → |j| ≤ L → j * (s₂ - s₁) ≠ i * (s₃ - s₁)

variable {L L' : ℕ} {T T' : Set ℤ}

/-- A subset of a set with no relation of length `L` has no relation of length `L`. -/
theorem NoRelation.mono (hT : T' ⊆ T) (h : NoRelation L T) : NoRelation L T' :=
  fun _ h₁ _ h₂ _ h₃ => h _ (hT h₁) _ (hT h₂) _ (hT h₃)

/-- A set with no relation of length `L` has no relation of any length `L' ≤ L`. -/
theorem NoRelation.of_le (hL : L' ≤ L) (h : NoRelation L T) : NoRelation L' T :=
  fun _ h₁ _ h₂ _ h₃ h₁₂ h₁₃ h₂₃ i j hij hi hiL hj hjL =>
    h _ h₁ _ h₂ _ h₃ h₁₂ h₁₃ h₂₃ i j hij hi (hiL.trans (by exact_mod_cast hL)) hj
      (hjL.trans (by exact_mod_cast hL))

/-- The empty set has no relation of any length. -/
theorem noRelation_empty : NoRelation L ∅ := fun _ h => h.elim

/-- A set with at most one element has no relation of any length. -/
theorem _root_.Set.Subsingleton.noRelation (hT : T.Subsingleton) : NoRelation L T :=
  fun _ h₁ _ h₂ _ _ h₁₂ => (h₁₂ (hT h₁ h₂)).elim

/-- A singleton has no relation of any length. -/
theorem noRelation_singleton (a : ℤ) : NoRelation L {a} :=
  Set.subsingleton_singleton.noRelation

/-- For `L ≠ 0`, a set with no relation of length `L` contains no three-term arithmetic
progression `a, b, c`: the relation `-(a - b) = c - b`, with `i = 1` and `j = -1`, says that `b`
is the midpoint of `a` and `c`. -/
theorem NoRelation.threeAPFree (hL : L ≠ 0) (h : NoRelation L T) : ThreeAPFree T := by
  intro a ha b hb c hc habc
  by_contra hab
  have hbc : b ≠ c := by rintro rfl; exact hab (by linarith)
  have hac : a ≠ c := by rintro rfl; exact hab (by linarith)
  have hL' : |(1 : ℤ)| ≤ L := by rw [abs_one]; exact_mod_cast Nat.one_le_iff_ne_zero.2 hL
  exact h b hb a ha c hc (Ne.symm hab) hbc hac 1 (-1) (by norm_num) (by norm_num) hL'
    (by norm_num) (by rwa [abs_neg]) (by linarith)

/-- Translating a set by `a` preserves having no relation of length `L`. -/
theorem NoRelation.vadd_set (h : NoRelation L T) (a : ℤ) : NoRelation L (a +ᵥ T) := by
  rintro _ ⟨s₁, h₁, rfl⟩ _ ⟨s₂, h₂, rfl⟩ _ ⟨s₃, h₃, rfl⟩ h₁₂ h₁₃ h₂₃ i j hij hi hiL hj hjL hrel
  refine h s₁ h₁ s₂ h₂ s₃ h₃ (by rintro rfl; exact h₁₂ rfl) (by rintro rfl; exact h₁₃ rfl)
    (by rintro rfl; exact h₂₃ rfl) i j hij hi hiL hj hjL ?_
  simpa [vadd_eq_add] using hrel

/-- Having no relation of length `L` is invariant under translation. -/
@[simp]
theorem noRelation_vadd_set {a : ℤ} : NoRelation L (a +ᵥ T) ↔ NoRelation L T :=
  ⟨fun h => by simpa using h.vadd_set (-a), fun h => h.vadd_set a⟩

/-- On a sphere `∑ k, x k ^ 2 = const`, a relation `j (x₂ - x₁) = i (x₃ - x₁)` with `j ≠ 0` and
`i ≠ j` forces `x₁ = x₂`, since `j (j - i) ∑ k, (x₂ k - x₁ k) ^ 2` is a combination of the
differences of the squared norms. -/
private lemma eq_of_mul_sub_eq {n : ℕ} {x₁ x₂ x₃ : Fin n → ℤ} {i j : ℤ} (hj : j ≠ 0)
    (hij : i ≠ j) (h₂ : ∑ k, x₂ k ^ 2 = ∑ k, x₁ k ^ 2) (h₃ : ∑ k, x₃ k ^ 2 = ∑ k, x₁ k ^ 2)
    (h : ∀ k, j * (x₂ k - x₁ k) = i * (x₃ k - x₁ k)) : x₁ = x₂ := by
  have key : j * (j - i) * ∑ k, (x₂ k - x₁ k) ^ 2 =
      i ^ 2 * (∑ k, x₃ k ^ 2 - ∑ k, x₁ k ^ 2) - i * j * (∑ k, x₂ k ^ 2 - ∑ k, x₁ k ^ 2) := by
    simp only [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    linear_combination (j * (x₂ k - x₁ k) + i * (x₃ k - x₁ k) + 2 * i * x₁ k) * h k
  rw [h₂, h₃, sub_self, mul_zero, mul_zero, sub_zero, mul_eq_zero,
    or_iff_right (mul_ne_zero hj (sub_ne_zero.2 hij.symm)),
    sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg _] at key
  ext k
  linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (key k (mem_univ k))]

/-- The digit bound of Behrend's construction: for coordinates in `[0, D - 1]` and
`0 < |i|, |j| ≤ L`, the combination `j (x₂ - x₁) - i (x₃ - x₁)` has absolute value less than
any `B > 2 L (D - 1)`. -/
private lemma abs_digit_lt {L B D : ℕ} (hB : 2 * L * (D - 1) < B) {a₁ a₂ a₃ : ℕ} (h₁ : a₁ < D)
    (h₂ : a₂ < D) (h₃ : a₃ < D) {i j : ℤ} (hiL : |i| ≤ L) (hjL : |j| ≤ L) :
    |j * ((a₂ : ℤ) - a₁) - i * ((a₃ : ℤ) - a₁)| < B := by
  have he (a b : ℕ) (ha : a < D) (hb : b < D) : |(a : ℤ) - b| ≤ ((D - 1 : ℕ) : ℤ) := by
    have ha' : a ≤ D - 1 := Nat.le_sub_one_of_lt ha
    have hb' : b ≤ D - 1 := Nat.le_sub_one_of_lt hb
    rw [abs_sub_le_iff]
    constructor <;> omega
  calc |j * ((a₂ : ℤ) - a₁) - i * ((a₃ : ℤ) - a₁)|
      ≤ |j| * |(a₂ : ℤ) - a₁| + |i| * |(a₃ : ℤ) - a₁| := by
        rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ L * ((D - 1 : ℕ) : ℤ) + L * ((D - 1 : ℕ) : ℤ) := by
        gcongr
        exacts [he _ _ h₂ h₁, he _ _ h₃ h₁]
    _ = ((2 * L * (D - 1) : ℕ) : ℤ) := by push_cast; ring
    _ < B := by exact_mod_cast hB

/-- **Behrend's construction for relations of length `L`.** If `2 L (D - 1) < B`, the image of
`Behrend.sphere n D R` under the base-`B` reading `Behrend.map B` has no relation of length `L`. -/
theorem noRelation_image_map_sphere {L B n D R : ℕ} (hB : 2 * L * (D - 1) < B) :
    NoRelation L
      ((fun x => (Behrend.map B x : ℤ)) '' (Behrend.sphere n D R : Set (Fin n → ℕ))) := by
  rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ _ ⟨x₃, hx₃, rfl⟩ h₁₂ - - i j hij - hiL hj hjL hrel
  simp only [Behrend.sphere, coe_filter, Behrend.mem_box, Set.mem_ofPred_eq] at hx₁ hx₂ hx₃
  have hc := Int.eq_zero_of_sum_mul_pow_eq_zero (b := B)
    (c := fun k => j * ((x₂ k : ℤ) - x₁ k) - i * ((x₃ k : ℤ) - x₁ k))
    (fun k => abs_digit_lt hB (hx₁.1 k) (hx₂.1 k) (hx₃.1 k) hiL hjL) (by
      simp only [Behrend.map_apply, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] at hrel
      simp only [sub_mul, mul_assoc, ← mul_sum, sum_sub_distrib]
      linear_combination hrel)
  have hx := eq_of_mul_sub_eq (x₁ := fun k => (x₁ k : ℤ)) (x₂ := fun k => (x₂ k : ℤ))
    (x₃ := fun k => (x₃ k : ℤ)) (abs_pos.1 hj) hij (by exact_mod_cast hx₂.2.trans hx₁.2.symm)
    (by exact_mod_cast hx₃.2.trans hx₁.2.symm) fun k => by simpa [sub_eq_zero] using congrFun hc k
  exact h₁₂ (congrArg (fun x => (Behrend.map B x : ℤ)) (funext fun k => by
    exact_mod_cast congrFun hx k))

/-- **An explicit Behrend bound for relations of length `L`.** If `2 L (D - 1) < B` and
`D ≤ B`, some `T ⊆ [0, B ^ n)` has no relation of length `L` and
`D ^ n / (n D ^ 2) ≤ |T| ≤ D ^ n`. -/
theorem exists_noRelation_of_two_mul_lt {L B n D : ℕ} (hB : 2 * L * (D - 1) < B) (hD : D ≤ B) :
    ∃ T : Finset ℤ, (∀ s ∈ T, 0 ≤ s ∧ s < B ^ n) ∧ NoRelation L T ∧
      ((D ^ n : ℕ) / (n * D ^ 2 : ℕ) : ℝ) ≤ #T ∧ #T ≤ D ^ n := by
  obtain ⟨R, hR⟩ := Behrend.exists_large_sphere n D
  have hlt (x) (hx : x ∈ Behrend.sphere n D R) : ∀ k, x k < B := fun k =>
    (Behrend.mem_box.1 (Behrend.sphere_subset_box hx) k).trans_le hD
  have hinj : Set.InjOn (fun x => (Behrend.map B x : ℤ)) (Behrend.sphere n D R) :=
    Nat.cast_injective.comp_injOn (Behrend.map_injOn.mono fun x hx => hlt x hx)
  refine ⟨(Behrend.sphere n D R).image fun x => (Behrend.map B x : ℤ), ?_, ?_, ?_, ?_⟩
  · simp only [mem_image, forall_exists_index, and_imp]
    rintro _ x hx rfl
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast Behrend.map_lt_pow (hlt x hx)⟩
  · rw [coe_image]
    exact noRelation_image_map_sphere hB
  · rwa [card_image_of_injOn hinj]
  · rw [card_image_of_injOn hinj, ← Behrend.card_box]
    exact card_le_card Behrend.sphere_subset_box

/-- The real numbers of the parameter choice: with `l = log L`, `m = log M` and
`t = (m / l) ^ (1/2)`, one has `log 2 ≤ l`, `m = t ^ 2 l` and `(m l) ^ (1/2) = t l`. -/
private lemma params {M L : ℕ} (hL : 2 ≤ L) :
    log 2 ≤ log L ∧ log M = √(log M / log L) ^ 2 * log L ∧
      √(log M * log L) = √(log M / log L) * log L := by
  have hl2 : log 2 ≤ log L := log_le_log two_pos (by exact_mod_cast hL)
  have hl : 0 < log L := (log_pos one_lt_two).trans_le hl2
  have ht2 : √(log M / log L) ^ 2 * log L = log M := by
    rw [sq_sqrt (div_nonneg (log_natCast_nonneg M) hl.le), div_mul_cancel₀ _ hl.ne']
  refine ⟨hl2, ht2.symm, ?_⟩
  rw [← sqrt_sq (mul_nonneg (sqrt_nonneg _) hl.le)]
  congr 1
  linear_combination (-log L) * ht2

/-- `log (4 L) = 2 log 2 + log L` for `L ≠ 0`. -/
private lemma log_four_mul {L : ℕ} (hL : L ≠ 0) : log ((4 * L : ℕ) : ℝ) = 2 * log 2 + log L := by
  push_cast
  rw [log_mul (by norm_num) (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  norm_num

/-- `M exp x / L = exp (log M + x - log L)` for positive `M` and `L`. -/
private lemma mul_exp_div_eq {M L : ℕ} (hM : 0 < M) (hL : 0 < L) (x : ℝ) :
    (M : ℝ) * exp x / L = exp (log M + x - log L) := by
  rw [exp_sub, exp_add, exp_log (by exact_mod_cast hM), exp_log (by exact_mod_cast hL)]

/-- `log (K (K D) ^ n) = log K + n (log K + log D)` for positive `K` and `D`. -/
private lemma log_mul_pow {K D : ℕ} (hK : 0 < K) (hD : 0 < D) (n : ℕ) :
    log ((K * (K * D) ^ n : ℕ) : ℝ) = log K + n * (log K + log D) := by
  have hK' : (K : ℝ) ≠ 0 := by positivity
  have hD' : (D : ℝ) ≠ 0 := by positivity
  push_cast
  rw [log_mul hK' (by positivity), log_pow, log_mul hK' hD']

/-- The inequality behind the main case of `exists_noRelation`, in logarithmic form: `a` stands
for `log (4 L)`, `d` for `log D`, `l` for `log L` and `m = t ^ 2 l` for `log M`. -/
private lemma main_ineq {m l t a d : ℝ} {n : ℕ} (hl2 : log 2 ≤ l) (hm : m = t ^ 2 * l)
    (ht : t ≤ n) (hn : (n : ℝ) < t + 1) (ha : a = 2 * log 2 + l)
    (h₁ : a + n * (a + d) ≤ m) (h₂ : m < a + n * (a + (log 2 + d))) :
    m + -14 * (t * l) - l ≤ n * d - (log n + 2 * d) := by
  have h2 := log_two_gt_d9
  have hl : 0 < l := by linarith
  have hn0 : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp only [h0, Nat.cast_zero, zero_mul, add_zero] at h₁ h₂; linarith
    · exact_mod_cast h0
  have ht0 : 0 ≤ t := by
    linarith [(Nat.one_le_cast (α := ℝ)).2 (Nat.cast_pos.1 hn0)]
  rcases le_total 1 t with ht1 | ht1
  · have hdt : d ≤ t * l := by
      refine le_of_mul_le_mul_left ?_ hn0
      nlinarith [mul_le_mul_of_nonneg_right ht (mul_nonneg ht0 hl.le)]
    have hlogn := log_le_sub_one_of_pos hn0
    nlinarith [mul_le_mul_of_nonneg_right hn.le hl.le, mul_le_mul_of_nonneg_left hl2 hn0.le,
      mul_le_mul_of_nonneg_right ht1 hl.le, mul_le_mul_of_nonneg_left (by linarith : 1 ≤ 2 * l) ht0]
  · have hn1 : n = 1 := by
      have : (n : ℝ) < 2 := by linarith
      have : n < 2 := by exact_mod_cast this
      have : 0 < n := by exact_mod_cast hn0
      omega
    subst hn1
    simp only [Nat.cast_one, log_one, one_mul] at h₁ ⊢
    nlinarith [mul_le_mul_of_nonneg_right (pow_le_one₀ ht0 ht1 : t ^ 2 ≤ 1) hl.le,
      mul_nonneg ht0 hl.le]

/-- The inequality behind the case `M < (4 L) ^ (n + 1)` of `exists_noRelation`, in logarithmic
form: `a` stands for `log (4 L)`, `l` for `log L` and `m = t ^ 2 l` for `log M`. -/
private lemma fallback_ineq {m l t a : ℝ} {n : ℕ} (hl2 : log 2 ≤ l) (hm : m = t ^ 2 * l)
    (ht0 : 0 ≤ t) (hn : (n : ℝ) < t + 1) (ha : a = 2 * log 2 + l) (h : m < a + n * a) :
    m + -14 * (t * l) - l ≤ 0 := by
  have h2 := log_two_gt_d9
  have hl : 0 < l := by linarith
  have h3 : t ^ 2 * l < (3 * t + 6) * l := by
    nlinarith [mul_le_mul_of_nonneg_right hn.le (by linarith : 0 ≤ a)]
  have h3' : t ^ 2 < 3 * t + 6 := lt_of_mul_lt_mul_right h3 hl.le
  rcases le_total t 1 with ht1 | ht1
  · nlinarith [mul_le_mul_of_nonneg_right (pow_le_one₀ ht0 ht1 : t ^ 2 ≤ 1) hl.le,
      mul_nonneg ht0 hl.le]
  · nlinarith [mul_le_mul_of_nonneg_right (by linarith : t ^ 2 ≤ 14 * t) hl.le]

/-- For `n ≥ 1` and `K ≥ 1` with `K ^ (n + 1) ≤ M` there is a largest `D ≥ 1` with
`K (K D) ^ n ≤ M`. -/
private lemma exists_max_digit {K M n : ℕ} (hn : 0 < n) (hK : 0 < K) (h : K * K ^ n ≤ M) :
    ∃ D, 1 ≤ D ∧ K * (K * D) ^ n ≤ M ∧ M < K * (K * (D + 1)) ^ n := by
  have hP1 : K * (K * 1) ^ n ≤ M := by rwa [mul_one]
  have hM : 1 ≤ M := (Nat.one_le_iff_ne_zero.2 (by positivity)).trans h
  refine ⟨Nat.findGreatest (fun D => K * (K * D) ^ n ≤ M) M,
    Nat.le_findGreatest (P := fun D => K * (K * D) ^ n ≤ M) hM hP1,
    Nat.findGreatest_spec (P := fun D => K * (K * D) ^ n ≤ M) hM hP1, ?_⟩
  by_contra hle
  push Not at hle
  rcases le_or_gt (Nat.findGreatest (fun D => K * (K * D) ^ n ≤ M) M + 1) M with hDM | hDM
  · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hDM hle
  · have hE (E : ℕ) : E ≤ K * (K * E) ^ n := (Nat.le_mul_of_pos_left E hK).trans <|
      (Nat.le_self_pow hn.ne' _).trans (Nat.le_mul_of_pos_left _ hK)
    have := hE (Nat.findGreatest (fun D => K * (K * D) ^ n ≤ M) M + 1)
    omega

/-- The main case of `exists_noRelation`, `4 L (4 L) ^ n ≤ M`. -/
private lemma main_case {M L : ℕ} (hL : 2 ≤ L)
    (h : 4 * L * (4 * L) ^ ⌈√(log M / log L)⌉₊ ≤ M) :
    ∃ T : Finset ℤ, T.Nonempty ∧ (∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < M / (4 * L)) ∧ NoRelation L T ∧
      (M : ℝ) * exp (-14 * √(log M * log L)) / L ≤ #T ∧ (#T : ℝ) ≤ M / (4 * L) := by
  obtain ⟨hl2, hm, hs⟩ := params (M := M) hL
  have hM : 2 ≤ M := by
    have := (Nat.le_mul_of_pos_right (4 * L) (by positivity)).trans h
    omega
  have ht : 0 < √(log M / log L) :=
    sqrt_pos.2 (div_pos (log_pos (by exact_mod_cast hM)) ((log_pos one_lt_two).trans_le hl2))
  set n := ⌈√(log M / log L)⌉₊
  have hn0 : 0 < n := Nat.ceil_pos.2 ht
  obtain ⟨D, hD, h₁, h₂⟩ := exists_max_digit hn0 (by omega) h
  obtain ⟨T, hT, hTL, hTc, hTD⟩ := exists_noRelation_of_two_mul_lt (L := L) (n := n)
    (B := 4 * L * D) (D := D) (by nlinarith [Nat.sub_le D 1]) (Nat.le_mul_of_pos_left _ (by omega))
  have h4L : (0 : ℝ) < 4 * L := by positivity
  have hB : (((4 * L * D) ^ n : ℕ) : ℝ) ≤ M / (4 * L) := by
    rw [le_div_iff₀' h4L]; exact_mod_cast h₁
  have hlow : (M : ℝ) * exp (-14 * √(log M * log L)) / L ≤ #T := by
    refine le_trans ?_ hTc
    rw [mul_exp_div_eq (by omega) (by omega), ← le_log_iff_exp_le (by positivity), hs]
    push_cast
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_pow, log_pow]
    have h4 := log_mul_pow (K := 4 * L) (by omega) (by omega : 0 < D) n
    have h4' := log_mul_pow (K := 4 * L) (by omega) (by omega : 0 < D + 1) n
    have hD2 : log ((D + 1 : ℕ) : ℝ) ≤ log 2 + log D := by
      rw [← log_mul two_ne_zero (by positivity)]
      exact log_le_log (by positivity) (by push_cast; linarith [(Nat.one_le_cast.2 hD : (1:ℝ) ≤ D)])
    refine main_ineq hl2 hm (Nat.le_ceil _) (Nat.ceil_lt_add_one ht.le) (log_four_mul (by omega))
      ?_ ?_
    · rw [← h4]; exact log_le_log (by positivity) (by exact_mod_cast h₁)
    · have := log_lt_log (by positivity)
        (by exact_mod_cast h₂ : (M : ℝ) < ((4 * L * (4 * L * (D + 1)) ^ n : ℕ) : ℝ))
      rw [h4'] at this
      nlinarith [mul_le_mul_of_nonneg_left hD2 (Nat.cast_nonneg n)]
  refine ⟨T, card_pos.1 (by exact_mod_cast (by positivity : (0 : ℝ) < _).trans_le hlow),
    fun s hs => ⟨(hT s hs).1, ?_⟩, hTL, hlow, ?_⟩
  · exact (by exact_mod_cast (hT s hs).2 : (s : ℝ) < _).trans_le hB
  · refine le_trans ?_ hB
    exact_mod_cast hTD.trans (Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (by omega)) n)

/-- The case `M < 4 L (4 L) ^ n` of `exists_noRelation`: the lower bound is at most `1`. -/
private lemma fallback_case {M L : ℕ} (hL : 2 ≤ L)
    (h : M < 4 * L * (4 * L) ^ ⌈√(log M / log L)⌉₊) :
    (M : ℝ) * exp (-14 * √(log M * log L)) / L ≤ 1 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  obtain ⟨hl2, hm, hs⟩ := params (M := M) hL
  rw [mul_exp_div_eq hM (by omega), exp_le_one_iff, hs]
  have hlt := log_lt_log (by positivity)
    (by rw [mul_one]; exact_mod_cast h :
      (M : ℝ) < ((4 * L * (4 * L * 1) ^ ⌈√(log M / log L)⌉₊ : ℕ) : ℝ))
  rw [log_mul_pow (by omega) one_pos, Nat.cast_one, log_one, add_zero] at hlt
  exact fallback_ineq hl2 hm (sqrt_nonneg _) (Nat.ceil_lt_add_one (sqrt_nonneg _))
    (log_four_mul (by omega)) hlt

/-- **Sets with no relation of length `L` (Behrend, Ruzsa).** There is a constant `C` such that
for all integers `M ≥ 1` and `L ≥ 2` some nonempty `T ⊆ ℤ ∩ [0, M / (4 L))` has no relation of
length `L` and `|T| ≥ M exp (-C (log M log L) ^ (1/2)) / L`; when `4 L ≤ M`, moreover
`|T| ≤ M / (4 L)`.
The proof takes `C = 14`. -/
theorem exists_noRelation : ∃ C : ℝ, ∀ M L : ℕ, 0 < M → 2 ≤ L → ∃ T : Finset ℤ, T.Nonempty ∧
    (∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < M / (4 * L)) ∧ NoRelation L T ∧
    (M : ℝ) * Real.exp (-C * Real.sqrt (Real.log M * Real.log L)) / L ≤ T.card ∧
    (4 * L ≤ M → (T.card : ℝ) ≤ M / (4 * L)) := by
  refine ⟨14, fun M L hM hL => ?_⟩
  rcases le_or_gt (4 * L * (4 * L) ^ ⌈√(log M / log L)⌉₊) M with h | h
  · obtain ⟨T, hT, hTs, hTL, hTc, hTM⟩ := main_case hL h
    exact ⟨T, hT, hTs, hTL, hTc, fun _ => hTM⟩
  · have h4L : (0 : ℝ) < 4 * L := by positivity
    refine ⟨{0}, singleton_nonempty 0, fun s hs => ?_, ?_, ?_, fun h4 => ?_⟩
    · rw [mem_singleton.1 hs]
      exact ⟨le_rfl, by push_cast; positivity⟩
    · rw [coe_singleton]
      exact noRelation_singleton 0
    · simpa using fallback_case hL h
    · rw [card_singleton, Nat.cast_one, le_div_iff₀ h4L, one_mul]
      exact_mod_cast h4

end TauCeti
