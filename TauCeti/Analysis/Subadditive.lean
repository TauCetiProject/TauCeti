/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Fekete's lemma with an error term

Let `f : ℕ → ℝ` be nondecreasing with `∑ₖ f k / k ^ 2 < ∞`, and let `a : ℕ → ℝ` satisfy
`a (n + m) ≥ a n + a m - f (n + m)` for all `n, m ≥ n₀` with `n ≤ 2 m` and `m ≤ 2 n`. Then
`a n / n` converges in `(-∞, +∞]`: to a real limit if `a n / n` is bounded above, and to `+∞`
otherwise. This is a theorem of de Bruijn and Erdős. Compared with Fekete's lemma
(`Subadditive.tendsto_lim` in Mathlib, for `-a`), the inequality is required only for splittings
into comparable parts, and only up to the error `f`.

## Main results

* `TauCeti.tendsto_div_of_superadditive_error`: if `a n / n` is bounded above, it converges.
* `TauCeti.tendsto_div_atTop_of_superadditive_error`: otherwise `a n / n` tends to `+∞`.

## Implementation notes

Fix `m ≥ n₀` and write `N = j m + p` with `m ≤ p < 2 m`. Splitting `j` copies of `m` and the extra
piece `p` along a balanced binary tree, every split is admissible, and a node of size `x` whose
parts are `u, v ≥ m` loses `f x`. The losses are absorbed by the invariant
`a x ≥ (lower bound) - x E (x)` with `E (x) = 6 ∑_{2m ≤ n < 2x} f n / n ^ 2`: as both parts are at
most `2x / 3`, the at least `2x / 3` terms `f n / n ^ 2 ≥ f x / (2x) ^ 2` with `max u v ≤ n / 2 < x`
pay for `f x`. Since `E (x)` is at most a tail of the convergent series, this gives
`a N ≥ N (a m / m - δ m) + C` with `δ m → 0`, which yields `liminf ≥ limsup`.

## References

* N. G. de Bruijn and P. Erdős, Some linear and some quadratic recursion formulas II,
  Indag. Math. 14 (1952), 152–163.
* H. Chen, Convergence des polygones de Harder–Narasimhan, Mém. Soc. Math. Fr. 120 (2010),
  Prop. 3.1.
-/

@[expose] public section

open Filter Finset Topology

namespace TauCeti

variable {a f : ℕ → ℝ} {n₀ : ℕ}

/-- The loss budget `6 ∑_{2m ≤ n < 2x} f n / n ^ 2` of a node of size `x`. -/
private noncomputable def lossBudget (f : ℕ → ℝ) (m x : ℕ) : ℝ :=
  6 * ∑ n ∈ Ico (2 * m) (2 * x), f n / (n : ℝ) ^ 2

private lemma lossBudget_nonneg (hf0 : ∀ n, 0 ≤ f n) (m x : ℕ) : 0 ≤ lossBudget f m x :=
  mul_nonneg (by norm_num) <| sum_nonneg fun n _ ↦ div_nonneg (hf0 n) (sq_nonneg _)

private lemma lossBudget_mono (hf0 : ∀ n, 0 ≤ f n) (m : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    lossBudget f m x ≤ lossBudget f m y :=
  mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (by omega))
    fun n _ _ ↦ div_nonneg (hf0 n) (sq_nonneg _)) (by norm_num)

/-- A split of a node of size `u + v` into parts `m ≤ u, v` with `u ≤ 2v` and `v ≤ 2u` is paid
for by the loss budget. -/
private lemma lossBudget_split (hf : Monotone f) (hf0 : ∀ n, 0 ≤ f n) {m u v : ℕ} (hm : 0 < m)
    (hu : m ≤ u) (hv : m ≤ v) (huv : u ≤ 2 * v) (hvu : v ≤ 2 * u) :
    u * lossBudget f m u + v * lossBudget f m v + f (u + v) ≤
      ((u + v : ℕ) : ℝ) * lossBudget f m (u + v) := by
  set x := u + v
  set w := max u v
  have hwx : 3 * w ≤ 2 * x := by omega
  have hxw : x ≤ 2 * w := by omega
  have h1 : (u : ℝ) * lossBudget f m u + v * lossBudget f m v ≤ x * lossBudget f m w := by
    have := lossBudget_nonneg hf0 m w
    have := lossBudget_mono hf0 m (le_max_left u v)
    have := lossBudget_mono hf0 m (le_max_right u v)
    have : (x : ℝ) = u + v := by push_cast [x]; ring
    nlinarith [(Nat.cast_nonneg u : (0 : ℝ) ≤ u), (Nat.cast_nonneg v : (0 : ℝ) ≤ v)]
  have hsplit : lossBudget f m x =
      lossBudget f m w + 6 * ∑ n ∈ Ico (2 * w) (2 * x), f n / (n : ℝ) ^ 2 := by
    simp only [lossBudget]
    rw [← sum_Ico_consecutive _ (by omega : 2 * m ≤ 2 * w) (by omega : 2 * w ≤ 2 * x)]
    ring
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hterm : ∀ n ∈ Ico (2 * w) (2 * x), f x / (2 * x : ℝ) ^ 2 ≤ f n / (n : ℝ) ^ 2 := by
    intro n hn
    rw [mem_Ico] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnx : (n : ℝ) ≤ 2 * x := by exact_mod_cast hn.2.le
    exact div_le_div₀ (hf0 n) (hf (by omega)) (by positivity) (by gcongr)
  have hsum : ((2 * x - 2 * w : ℕ) : ℝ) * (f x / (2 * x : ℝ) ^ 2) ≤
      ∑ n ∈ Ico (2 * w) (2 * x), f n / (n : ℝ) ^ 2 := by
    simpa [Nat.card_Ico] using card_nsmul_le_sum _ _ _ hterm
  have hkey : f x ≤ 6 * x * (((2 * x - 2 * w : ℕ) : ℝ) * (f x / (2 * x : ℝ) ^ 2)) := by
    have hw : (3 : ℝ) * w ≤ 2 * x := by exact_mod_cast hwx
    rw [Nat.cast_sub (by omega)]
    push_cast
    rw [show (6 : ℝ) * x * ((2 * x - 2 * w) * (f x / (2 * x) ^ 2)) =
      f x * (3 * (x - w) / x) by field_simp; ring]
    have : 1 ≤ 3 * ((x : ℝ) - w) / x := by rw [le_div_iff₀ hx0]; linarith
    nlinarith [hf0 x]
  rw [hsplit]
  nlinarith

/-- Combining lower bounds on `a u` and `a v` along an admissible split. -/
private lemma le_of_split (ha : ∀ n m, n₀ ≤ n → n₀ ≤ m → n ≤ 2 * m → m ≤ 2 * n →
      a n + a m - f (n + m) ≤ a (n + m))
    (hf : Monotone f) (hf0 : ∀ n, 0 ≤ f n) {m u v : ℕ} (hm : 0 < m) (hm₀ : n₀ ≤ m)
    (hu : m ≤ u) (hv : m ≤ v) (huv : u ≤ 2 * v) (hvu : v ≤ 2 * u) {bu bv : ℝ}
    (hbu : bu - u * lossBudget f m u ≤ a u) (hbv : bv - v * lossBudget f m v ≤ a v) :
    bu + bv - ((u + v : ℕ) : ℝ) * lossBudget f m (u + v) ≤ a (u + v) := by
  have := ha u v (by omega) (by omega) huv hvu
  have := lossBudget_split hf hf0 hm hu hv huv hvu
  linarith

/-- The `j` copies of `m`: `a (j m) ≥ j m μ - j m E (j m)` when `a m = m μ`. -/
private lemma le_copies (ha : ∀ n m, n₀ ≤ n → n₀ ≤ m → n ≤ 2 * m → m ≤ 2 * n →
      a n + a m - f (n + m) ≤ a (n + m))
    (hf : Monotone f) (hf0 : ∀ n, 0 ≤ f n) {m : ℕ} (hm : 0 < m) (hm₀ : n₀ ≤ m) {μ : ℝ}
    (hμ : a m = m * μ) (j : ℕ) (hj : 0 < j) :
    ((j * m : ℕ) : ℝ) * μ - (j * m : ℕ) * lossBudget f m (j * m) ≤ a (j * m) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases (by omega : j = 1 ∨ 2 ≤ j) with rfl | hj2
  · simp [lossBudget, hμ]
  have hj1 : j - j / 2 < j := by omega
  have hj2' : j / 2 < j := by omega
  have hsplit : j * m = (j - j / 2) * m + j / 2 * m := by
    rw [← add_mul]; congr 1; omega
  have h := le_of_split ha hf hf0 hm hm₀ (u := (j - j / 2) * m) (v := j / 2 * m)
    (Nat.le_mul_of_pos_left m (by omega)) (Nat.le_mul_of_pos_left m (by omega))
    (by rw [← mul_assoc]; exact Nat.mul_le_mul_right m (by omega))
    (by rw [← mul_assoc]; exact Nat.mul_le_mul_right m (by omega))
    (ih _ hj1 (by omega)) (ih _ hj2' (by omega))
  rw [hsplit]
  convert h using 2
  push_cast
  ring

/-- `j` copies of `m` and one extra piece `p ∈ [m, 2m)`: `a x ≥ x μ + C - x E (x)` for
`x = j m + p`, when `a n ≥ n μ + C` for `n < 4m`. -/
private lemma le_copies_add (ha : ∀ n m, n₀ ≤ n → n₀ ≤ m → n ≤ 2 * m → m ≤ 2 * n →
      a n + a m - f (n + m) ≤ a (n + m))
    (hf : Monotone f) (hf0 : ∀ n, 0 ≤ f n) {m : ℕ} (hm : 0 < m) (hm₀ : n₀ ≤ m) {μ C : ℝ}
    (hμ : a m = m * μ) (hC : ∀ n < 4 * m, n * μ + C ≤ a n) {p : ℕ} (hp : m ≤ p)
    (hp' : p < 2 * m) (j : ℕ) :
    ((j * m + p : ℕ) : ℝ) * μ + C - (j * m + p : ℕ) * lossBudget f m (j * m + p) ≤
      a (j * m + p) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases (by omega : j ≤ 2 ∨ 3 ≤ j) with hj | hj
  · have := hC (j * m + p) (by nlinarith)
    have := lossBudget_nonneg hf0 m (j * m + p)
    have : (0 : ℝ) ≤ ((j * m + p : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hsplit : j * m + p = (j - j / 2) * m + (j / 2 * m + p) := by
    rw [← add_assoc, ← add_mul]; congr 2; omega
  have h := le_of_split ha hf hf0 hm hm₀ (u := (j - j / 2) * m) (v := j / 2 * m + p)
    (Nat.le_mul_of_pos_left m (by omega)) (by omega)
    (by have := Nat.mul_le_mul_right m (by omega : j - j / 2 ≤ 2 * (j / 2)); nlinarith)
    (by have := Nat.mul_le_mul_right m (by omega : j / 2 + 2 ≤ 2 * (j - j / 2)); nlinarith)
    (le_copies ha hf hf0 hm hm₀ hμ _ (by omega)) (ih _ (by omega))
  rw [hsplit]
  convert h using 2
  push_cast
  ring

/-- For `m ≥ n₀`, `a N ≥ N (a m / m - δ) + C` for all `N ≥ m`, where `δ` is `6` times a tail of
`∑ₖ f k / k ^ 2`. -/
private lemma exists_le_of_nonneg (ha : ∀ n m, n₀ ≤ n → n₀ ≤ m → n ≤ 2 * m → m ≤ 2 * n →
      a n + a m - f (n + m) ≤ a (n + m))
    (hf : Monotone f) (hf0 : ∀ n, 0 ≤ f n) (hs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2)
    {m : ℕ} (hm : 0 < m) (hm₀ : n₀ ≤ m) :
    ∃ C, ∀ N, m ≤ N → N * (a m / m - 6 * ∑' k, f (k + 2 * m) / ((k + 2 * m : ℕ) : ℝ) ^ 2) + C ≤
      a N := by
  set μ := a m / m
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hμ : a m = m * μ := by simp only [μ]; field_simp
  obtain ⟨C, hC⟩ := ((Set.finite_Iio (4 * m)).image fun n ↦ a n - n * μ).bddBelow
  refine ⟨C, fun N hN ↦ ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, N / m = j + 1 := ⟨N / m - 1, by have := Nat.div_pos hN hm; omega⟩
  have hN' : N = j * m + (m + N % m) := by
    have := Nat.div_add_mod' N m; rw [hj, add_mul, one_mul] at this; omega
  have h := le_copies_add ha hf hf0 hm hm₀ hμ
    (fun n hn ↦ by have := hC ⟨n, hn, rfl⟩; simp only at this; linarith)
    (p := m + N % m) (by omega) (by have := Nat.mod_lt N hm; omega) j
  rw [← hN'] at h
  have htail : lossBudget f m N ≤
      6 * ∑' k, f (k + 2 * m) / ((k + 2 * m : ℕ) : ℝ) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [sum_Ico_eq_sum_range]
    simp_rw [add_comm (2 * m)]
    exact ((summable_nat_add_iff (2 * m)).2 hs).sum_le_tsum _
      fun k _ ↦ div_nonneg (hf0 _) (sq_nonneg _)
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- The common core of both theorems: `a n / n` is eventually at least `a m / m - δ m - ε`,
with `δ m → 0`. -/
private lemma exists_tendsto_zero (ha : ∀ n m, n₀ ≤ n → n₀ ≤ m → n ≤ 2 * m → m ≤ 2 * n →
      a n + a m - f (n + m) ≤ a (n + m))
    (hf : Monotone f) (hs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ m, max n₀ 1 ≤ m → ∀ ε > 0, ∀ᶠ N in atTop, a m / m - δ m - ε ≤ a N / N := by
  set g : ℕ → ℝ := fun n ↦ max (f n) 0
  have hg : Monotone g := hf.max monotone_const
  have hg0 : ∀ n, 0 ≤ g n := fun n ↦ le_max_right _ _
  have hgs : Summable fun n : ℕ ↦ g n / (n : ℝ) ^ 2 :=
    hs.abs.of_nonneg_of_le (fun n ↦ div_nonneg (hg0 n) (sq_nonneg _)) fun n ↦ by
      rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
      exact div_le_div_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (sq_nonneg _)
  have hga : ∀ n m, n₀ ≤ n → n₀ ≤ m → n ≤ 2 * m → m ≤ 2 * n →
      a n + a m - g (n + m) ≤ a (n + m) := fun n m h1 h2 h3 h4 ↦
    (sub_le_sub_left (le_max_left _ _) _).trans (ha n m h1 h2 h3 h4)
  refine ⟨fun m ↦ 6 * ∑' k, g (k + 2 * m) / ((k + 2 * m : ℕ) : ℝ) ^ 2, ?_, ?_⟩
  · simpa using ((tendsto_sum_nat_add fun n : ℕ ↦ g n / (n : ℝ) ^ 2).comp
      (tendsto_id.const_mul_atTop' two_pos)).const_mul 6
  intro m hm ε hε
  obtain ⟨C, hC⟩ := exists_le_of_nonneg hga hg hg0 hgs (m := m) (by omega) (by omega)
  filter_upwards [eventually_ge_atTop m, (tendsto_const_div_atTop_nhds_zero_nat C).eventually
    (lt_mem_nhds (neg_lt_zero.2 hε))] with N hN hCN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [le_div_iff₀ hN0]
  have := hC N hN
  have : -ε * N < C := by rwa [lt_div_iff₀ hN0] at hCN
  nlinarith

/-- **Fekete's lemma with an error term** (de Bruijn and Erdős). Let `f` be nondecreasing with
`∑ₖ f k / k ^ 2 < ∞`, and let `a (n + m) ≥ a n + a m - f (n + m)` for all `n, m ≥ n₀` with
`n ≤ 2m` and `m ≤ 2n`. If `a n / n` is bounded above, then it converges. -/
theorem tendsto_div_of_superadditive_error (hf : Monotone f)
    (hs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2)
    (ha : ∀ n m, n₀ ≤ n → n₀ ≤ m → n ≤ 2 * m → m ≤ 2 * n → a n + a m - f (n + m) ≤ a (n + m))
    (hbdd : BddAbove (Set.range fun n ↦ a n / n)) :
    ∃ L, Tendsto (fun n ↦ a n / n) atTop (𝓝 L) := by
  obtain ⟨δ, hδ, hlow⟩ := exists_tendsto_zero ha hf hs
  obtain ⟨B, hB⟩ := hbdd
  set u : ℕ → ℝ := fun n ↦ a n / n
  have hbu : IsBoundedUnder (· ≤ ·) atTop u := isBoundedUnder_of ⟨B, fun n ↦ hB ⟨n, rfl⟩⟩
  have hbl : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of_eventually_ge (hlow _ le_rfl 1 one_pos)
  refine ⟨limsup u atTop, tendsto_of_le_liminf_of_limsup_le ?_ le_rfl hbu hbl⟩
  refine le_of_forall_pos_le_add fun ε hε ↦ limsup_le_of_le hbl.isCoboundedUnder_le ?_
  filter_upwards [eventually_ge_atTop (max n₀ 1),
    hδ.eventually (gt_mem_nhds (half_pos hε))] with m hm hδm
  have := le_liminf_of_le hbu.isCoboundedUnder_ge (hlow m hm _ (half_pos hε))
  simp only [u] at this ⊢
  linarith

/-- **Fekete's lemma with an error term** (de Bruijn and Erdős), unbounded case. Under the
hypotheses of `TauCeti.tendsto_div_of_superadditive_error`, if `a n / n` is not bounded above,
then it tends to `+∞`. -/
theorem tendsto_div_atTop_of_superadditive_error (hf : Monotone f)
    (hs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2)
    (ha : ∀ n m, n₀ ≤ n → n₀ ≤ m → n ≤ 2 * m → m ≤ 2 * n → a n + a m - f (n + m) ≤ a (n + m))
    (hbdd : ¬BddAbove (Set.range fun n ↦ a n / n)) :
    Tendsto (fun n ↦ a n / n) atTop atTop := by
  obtain ⟨δ, hδ, hlow⟩ := exists_tendsto_zero ha hf hs
  have hunb : ∀ M B, ∃ m, M ≤ m ∧ B < a m / m := by
    intro M B
    by_contra! h
    obtain ⟨B', hB'⟩ := ((Set.finite_Iio M).image fun n ↦ a n / n).bddAbove
    refine hbdd ⟨max B B', ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases lt_or_ge n M with hn | hn
    exacts [le_max_of_le_right (hB' ⟨n, hn, rfl⟩), le_max_of_le_left (h n hn)]
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hδ.eventually (gt_mem_nhds one_pos))
  refine tendsto_atTop.2 fun B ↦ ?_
  obtain ⟨m, hm, hBm⟩ := hunb (max M (max n₀ 1)) (B + 2)
  filter_upwards [hlow m (le_of_max_le_right hm) 1 one_pos] with N hN
  have := hM m (le_of_max_le_left hm)
  linarith

end TauCeti
