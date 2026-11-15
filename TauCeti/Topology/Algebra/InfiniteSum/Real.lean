/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Real summability, finite repetitions, unbounded weights, and tails of nonnegative series

A summable real sequence `a` remains summable after multiplication by suitable weights
`c n ≥ 1` tending to infinity: no summable sequence decays at a slowest possible rate. This is
the standard device for rescaling an absolutely convergent series of products `x n * y n` so that
one factor tends to zero while the other stays absolutely summable.

The weights count the blocks into which the tails of `|a|` are cut: `c n` is one more than the
number of indices `k` with `N k ≤ n`, where the tail of `|a|` beyond `N k` is at most `2⁻ᵏ`.

Natural multiplicities can also be expressed by repeating each nonnegative real term
through a finite fiber. Summability of the repeated family is equivalent to summability of
the original family weighted by those multiplicities.

A square-summable real family is eventually small: `b i * C ≤ 1` for all but finitely many
`i`, for any fixed real `C`.

The tails `∑_{m > n} a m` of a nonnegative summable sequence decrease, and satisfy a discrete
analogue of the power-rule integral identity for tails.

## Main results

* `Summable.exists_tendsto_atTop_summable_mul`: weights `c n ≥ 1` with `c n → ∞` and
  `∑ n, c n * a n` summable.
* `Summable.antitone_tsum_Ioi`: the tails `∑_{m > n} a m` of a nonnegative summable sequence
  decrease with `n`.
* `Summable.mul_pow_tsum_Ioi`: the sequence `a m * (∑_{j > m} a j) ^ k` is summable for a
  nonnegative summable sequence `a`.
* `Summable.tsum_Ioi_mul_pow_tsum_Ioi_le`: the estimate
  `∑_{m > n} a m * (∑_{j > m} a j) ^ k ≤ (∑_{m > n} a m) ^ (k + 1) / (k + 1)` for a nonnegative
  summable sequence `a`, the discrete counterpart of `∫_x^∞ a Ψ ^ k = Ψ x ^ (k + 1) / (k + 1)` for
  `Ψ x = ∫_x^∞ a`.
* `TauCeti.summable_sigma_fin_iff`: repeating each nonnegative term `m i` times is summable
  exactly when `∑ i, m i * a i` is.
* `TauCeti.eventually_mul_le_one_of_summable_sq`: a square-summable family eventually satisfies
  `b i * C ≤ 1`.
-/

public section

open Filter Finset
open scoped Topology

/-- The weights `1 + #{k ≤ n | N k ≤ n}` tend to infinity along a strictly increasing sequence
of cut points `N`. -/
private lemma tendsto_one_add_sum_ite {N : ℕ → ℕ} (hN : StrictMono N) :
    Tendsto (fun n ↦ 1 + ∑ k ∈ range (n + 1), if N k ≤ n then (1 : ℝ) else 0) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun r ↦ ⟨N ⌈r⌉₊, fun n hn ↦ ?_⟩
  have hsub : range (⌈r⌉₊ + 1) ⊆ range (n + 1) :=
    Finset.range_subset_range.2 (Nat.succ_le_succ ((hN.id_le _).trans hn))
  have hones : ∑ k ∈ range (⌈r⌉₊ + 1), (if N k ≤ n then (1 : ℝ) else 0) = ⌈r⌉₊ + 1 := by
    rw [Finset.sum_ite_of_true fun k hk ↦
      (hN.monotone (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).trans hn]
    simp
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun k ↦ if N k ≤ n then (1 : ℝ) else 0) fun k _ _ ↦ by split_ifs <;> norm_num
  rw [hones] at hle
  linarith [Nat.le_ceil r]

/-- Cutting a nonnegative summable sequence `b` off below the points `N k`, whose tails are at most
`2⁻ᵏ`, gives column sums `∑' k, (if N k ≤ n then b n else 0)` that are summable in `n`. -/
private lemma summable_tsum_ite_le {b : ℕ → ℝ} (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    {N : ℕ → ℕ} (hNtail : ∀ k, ∑' m, b (m + N k) ≤ (1 / 2 : ℝ) ^ k) :
    Summable fun n ↦ ∑' k, if N k ≤ n then b n else 0 := by
  have hd0 (k n : ℕ) : 0 ≤ (if N k ≤ n then b n else 0) := by
    split_ifs <;> simp [hb0]
  have hdk (k : ℕ) : Summable fun n ↦ if N k ≤ n then b n else 0 :=
    hb.of_nonneg_of_le (hd0 k) fun n ↦ by split_ifs <;> simp [hb0]
  have htsum_d (k : ℕ) : ∑' n, (if N k ≤ n then b n else 0) ≤ (1 / 2 : ℝ) ^ k := by
    rw [← (hdk k).sum_add_tsum_nat_add (N k), Finset.sum_eq_zero fun i hi ↦ by
      simp [not_le.2 (Finset.mem_range.1 hi)]]
    simpa using hNtail k
  -- Summing over `k` first, then over `n`, is possible.
  have hprod : Summable fun p : ℕ × ℕ ↦ if N p.1 ≤ p.2 then b p.2 else 0 :=
    (summable_prod_of_nonneg fun p ↦ hd0 p.1 p.2).2 ⟨hdk, (summable_geometric_two).of_nonneg_of_le
      (fun k ↦ tsum_nonneg (hd0 k)) htsum_d⟩
  exact ((summable_prod_of_nonneg fun p : ℕ × ℕ ↦ hd0 p.2 p.1).1
    ((Equiv.prodComm ℕ ℕ).summable_iff.2 hprod)).2

/-- A summable real sequence remains summable after multiplication by suitable weights `c n ≥ 1`
tending to infinity. -/
theorem Summable.exists_tendsto_atTop_summable_mul {a : ℕ → ℝ} (ha : Summable a) :
    ∃ c : ℕ → ℝ, (∀ n, 1 ≤ c n) ∧ Tendsto c atTop atTop ∧ Summable fun n ↦ c n * a n := by
  set b : ℕ → ℝ := fun n ↦ |a n| with hb_def
  have hb : Summable b := ha.abs
  have hb0 (n : ℕ) : 0 ≤ b n := abs_nonneg _
  -- A strictly increasing sequence of cut points `N k` beyond which the tail of `b` is `≤ 2⁻ᵏ`.
  obtain ⟨N, hN, hNtail⟩ : ∃ N : ℕ → ℕ, StrictMono N ∧
      ∀ k, ∑' m, b (m + N k) ≤ (1 / 2 : ℝ) ^ k :=
    extraction_forall_of_eventually fun k ↦
      (tendsto_sum_nat_add b).eventually (Iic_mem_nhds (by positivity))
  have hcol := summable_tsum_ite_le hb hb0 hNtail
  -- Only the indices `k ≤ n` contribute to the column `n`, since `k ≤ N k`.
  have hcol_eq (n : ℕ) : ∑' k, (if N k ≤ n then b n else 0) =
      ∑ k ∈ range (n + 1), if N k ≤ n then b n else 0 :=
    tsum_eq_sum fun k hk ↦ by
      have hk' : n + 1 ≤ k := by simpa using hk
      have hNk : k ≤ N k := hN.id_le k
      simp [show ¬N k ≤ n by omega]
  -- The weight `c n` is one more than the number of cut points `N k ≤ n`.
  set c : ℕ → ℝ := fun n ↦ 1 + ∑ k ∈ range (n + 1), if N k ≤ n then (1 : ℝ) else 0 with hc_def
  have hc1 (n : ℕ) : 1 ≤ c n := by
    have : 0 ≤ ∑ k ∈ range (n + 1), if N k ≤ n then (1 : ℝ) else 0 :=
      Finset.sum_nonneg fun k _ ↦ by split_ifs <;> norm_num
    simp only [hc_def]
    linarith
  refine ⟨c, hc1, tendsto_one_add_sum_ite hN, ?_⟩
  · -- `|c n * a n| ≤ b n + ∑ k ≤ n, if N k ≤ n then b n else 0`, which is summable.
    refine summable_abs_iff.1 ((hb.add hcol).of_nonneg_of_le (fun n ↦ abs_nonneg _) fun n ↦ ?_)
    rw [abs_mul, abs_of_nonneg (zero_le_one.trans (hc1 n)), hcol_eq]
    simp only [hc_def, add_mul, one_mul, Finset.sum_mul]
    gcongr with k
    simp only [hb_def]
    split_ifs <;> simp

section Tail

variable {a : ℕ → ℝ}

/-- The tails `∑_{m > n} a m` of a nonnegative summable sequence decrease with `n`. -/
theorem Summable.antitone_tsum_Ioi (ha : Summable a) (ha0 : ∀ m, 0 ≤ a m) :
    Antitone fun n : ℕ ↦ ∑' m : Set.Ioi n, a m := fun _ _ hnm ↦
  have hsub := Set.Ioi_subset_Ioi hnm
  (ha.subtype _).tsum_le_tsum_of_inj (Set.inclusion hsub) (Set.inclusion_injective hsub)
    (fun j _ ↦ ha0 j) (fun _ ↦ le_rfl) (ha.subtype _)

/-- For a nonnegative summable sequence `a` with tails `Ψ m = ∑_{j > m} a j`, the sequence
`a m * Ψ m ^ k` is summable. -/
theorem Summable.mul_pow_tsum_Ioi (ha : Summable a) (ha0 : ∀ m, 0 ≤ a m) (k : ℕ) :
    Summable fun m ↦ a m * (∑' j : Set.Ioi m, a j) ^ k := by
  have hΨ0 : ∀ m : ℕ, 0 ≤ ∑' j : Set.Ioi m, a j := fun m ↦ tsum_nonneg fun j ↦ ha0 j
  refine (ha.mul_right ((∑' j : Set.Ioi 0, a j) ^ k)).of_nonneg_of_le
    (fun m ↦ mul_nonneg (ha0 m) (pow_nonneg (hΨ0 m) k)) fun m ↦ ?_
  have hle : ∑' j : Set.Ioi m, a j ≤ ∑' j : Set.Ioi 0, a j :=
    ha.antitone_tsum_Ioi ha0 (Nat.zero_le m)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hΨ0 m) hle k) (ha0 m)

/-- For a nonnegative summable sequence `a` with tails `Ψ n = ∑_{m > n} a m`,
`∑_{m > n} a m * Ψ m ^ k ≤ Ψ n ^ (k + 1) / (k + 1)`. This is the discrete counterpart of
`∫_x^∞ a(v) Ψ(v)^k dv = Ψ(x)^(k+1)/(k+1)` for `Ψ(x) = ∫_x^∞ a`. -/
theorem Summable.tsum_Ioi_mul_pow_tsum_Ioi_le (ha : Summable a) (ha0 : ∀ m, 0 ≤ a m)
    (n k : ℕ) :
    ∑' m : Set.Ioi n, a m * (∑' j : Set.Ioi (m : ℕ), a j) ^ k ≤
      (∑' m : Set.Ioi n, a m) ^ (k + 1) / (k + 1) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → ℝ, ∀ n, ∑' m : Set.Ioi n, a m = Ψ n := ⟨_, fun _ ↦ rfl⟩
  simp only [hΨ]
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n ↦ hΨ n ▸ tsum_nonneg fun m ↦ ha0 m
  -- telescoping over the partial sums, using `Ψ (m - 1) = Ψ m + a m`
  have hpartial : ∀ M, (k + 1) * ∑ j ∈ range M,
      a (j + (n + 1)) * Ψ (j + (n + 1)) ^ k ≤ Ψ n ^ (k + 1) - Ψ (n + M) ^ (k + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have hsplit : Ψ (n + M) = Ψ (n + M + 1) + a (n + M + 1) := by
        rw [← hΨ, ← hΨ, (ha.subtype _).tsum_Ioi_eq_add]
        ring
      -- Bernoulli's inequality `x ^ (k + 1) + (k + 1) x ^ k y ≤ (x + y) ^ (k + 1)`
      have hstep := pow_add_mul_le_add_pow (hΨ0 (n + M + 1))
        (by linarith [hΨ0 (n + M + 1), ha0 (n + M + 1)]) (k + 1)
      rw [← hsplit, Nat.add_sub_cancel] at hstep
      push_cast at hstep
      rw [sum_range_succ, mul_add, show M + (n + 1) = n + M + 1 by omega,
        show n + (M + 1) = n + M + 1 by omega]
      linarith
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [TauCeti.tsum_Ioi_eq_tsum_nat_add (fun m ↦ a m * Ψ m ^ k)]
  refine Real.tsum_le_of_sum_range_le (fun j ↦ mul_nonneg (ha0 _) (pow_nonneg (hΨ0 _) k))
    fun M ↦ ?_
  rw [le_div_iff₀ hk]
  linarith [hpartial M, pow_nonneg (hΨ0 (n + M)) (k + 1)]

end Tail

namespace TauCeti

/-- Repeating each nonnegative real term a finite natural number of times preserves
summability exactly when the multiplicity-weighted family is summable. -/
theorem summable_sigma_fin_iff {ι : Type*} {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (m : ι → ℕ) :
    Summable (fun p : Σ i, Fin (m i) ↦ a p.1) ↔
      Summable (fun i ↦ (m i : ℝ) * a i) := by
  rw [summable_sigma_of_nonneg (fun p ↦ ha p.1)]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · intro h
    refine ⟨fun _ ↦ Summable.of_finite, ?_⟩
    simpa using h

/-- A family with summable squares eventually satisfies `b i * C ≤ 1`, for any real `C`. -/
theorem eventually_mul_le_one_of_summable_sq {ι : Type*} {b : ι → ℝ}
    (hb : Summable (fun i ↦ b i ^ 2)) (C : ℝ) : ∀ᶠ i in cofinite, b i * C ≤ 1 := by
  filter_upwards [hb.tendsto_cofinite_zero.eventually
    (ge_mem_nhds (show (0 : ℝ) < (C ^ 2 + 1)⁻¹ by positivity))] with i hi
  have hsq : (b i * C) ^ 2 ≤ 1 :=
    calc
      _ = b i ^ 2 * C ^ 2 := by ring
      _ ≤ (C ^ 2 + 1)⁻¹ * C ^ 2 := by gcongr
      _ ≤ 1 := by
        rw [inv_mul_le_iff₀ (by positivity)]
        linarith
  nlinarith

end TauCeti
