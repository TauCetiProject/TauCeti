/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Probability.ConditionalProbability
public import TauCeti.Probability.Independence.BlockWindows

/-!
# Gaps between marked tiles on a Frobenius orbit

Index the complete tiles of a partitioned orbit cyclically, omitting any incomplete tile.
A long gap means that some complete tile and its next `M` neighbours are all unmarked.
Conditioning on a selected position affects at most one of those `M + 1` tiles. The estimate
uses only a lower bound for the single-tile marking probability, not identical selection rates
across the orbit. This is the tile-gap step in Levent Alpöge's `TileConditionFailureProbBound`.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped Finset Function ProbabilityTheory

namespace TauCeti.FrobeniusRiesz

variable {Ω ι : Type*} [MeasurableSpace Ω] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
  {μ : Measure Ω} {X : ∀ i, Ω → β i} {n : ℕ}

/-- The joint probability of selection at one coordinate and a gap of `M + 1` unmarked tiles
is at most the selection probability times `n * (1 - q)^M`, where `n` counts complete tiles
and `q` is a lower bound for the marking probability. The conditioning coordinate may lie
outside all complete tiles. -/
theorem measureReal_inter_exists_unmarked_tile_window_le
    (hX : iIndepFun X μ) (hmX : ∀ i, Measurable (X i))
    {B : ZMod n → Set ι} {E : ZMod n → Set Ω} (hB : Pairwise (Disjoint on B))
    (hE : ∀ j, MeasurableSet[Probability.blockSigma X (B j)] (E j))
    {i : ι} {A : Set Ω} (hA : MeasurableSet[Probability.blockSigma X {i}] A)
    {q : unitInterval} (hq : ∀ j, (q : ℝ) ≤ μ.real (E j)) {M : ℕ} (hM : M < n) :
    μ.real (A ∩ {ω | ∃ j : ZMod n, ∀ k : ℕ, k ≤ M → ω ∉ E (j + k)}) ≤
      μ.real A * (n * (1 - q : ℝ) ^ M) := by
  classical
  have : NeZero n := ⟨by omega⟩
  have := hX.isProbabilityMeasure
  let W (j : ZMod n) := (Finset.range (M + 1)).image fun k : ℕ ↦ j + (k : ZMod n)
  have hcard (j : ZMod n) : #(W j) = M + 1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    have heq := congrArg ZMod.val (add_left_cancel hab)
    have ha' : a < n := (Finset.mem_range.mp ha).trans_le (Nat.succ_le_of_lt hM)
    have hb' : b < n := (Finset.mem_range.mp hb).trans_le (Nat.succ_le_of_lt hM)
    simpa only [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using heq
  have hwindow (j : ZMod n) : μ.real (A ∩ ⋂ l ∈ W j, (E l)ᶜ) ≤
      μ.real A * (1 - q : ℝ) ^ M :=
    Probability.measureReal_inter_biInter_compl_le_of_blockSigma hX hmX
      (fun _ _ _ _ hne ↦ hB hne) (fun l _ ↦ hE l) hA (fun l _ ↦ hq l)
      (by rw [hcard j]; exact Nat.lt_succ_self M)
  have hevents : (A ∩ {ω | ∃ j : ZMod n, ∀ k : ℕ, k ≤ M → ω ∉ E (j + k)}) =
      ⋃ j : ZMod n, A ∩ ⋂ l ∈ W j, (E l)ᶜ := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, mem_iInter, mem_compl_iff, W,
      Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨hAω, j, h⟩
      exact ⟨j, hAω, fun _ ⟨k, hk, heq⟩ ↦ heq ▸ h k hk⟩
    · rintro ⟨j, hAω, h⟩
      exact ⟨hAω, j, fun k hk ↦ h _ ⟨k, hk, rfl⟩⟩
  rw [hevents]
  calc
    _ ≤ ∑ j : ZMod n, μ.real (A ∩ ⋂ l ∈ W j, (E l)ᶜ) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : ZMod n, μ.real A * (1 - q : ℝ) ^ M := Finset.sum_le_sum fun j _ ↦ hwindow j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_left_comm]

/-- Conditional on selection at a specified coordinate, the probability of a gap of
`M + 1` unmarked complete tiles is at most `n * (1 - q)^M`. The inequality also holds for
Mathlib's zero conditional measure when the selection event has zero probability. -/
theorem cond_toReal_exists_unmarked_tile_window_le
    (hX : iIndepFun X μ) (hmX : ∀ i, Measurable (X i))
    {B : ZMod n → Set ι} {E : ZMod n → Set Ω} (hB : Pairwise (Disjoint on B))
    (hE : ∀ j, MeasurableSet[Probability.blockSigma X (B j)] (E j))
    {i : ι} {A : Set Ω} (hA : MeasurableSet[Probability.blockSigma X {i}] A)
    {q : unitInterval} (hq : ∀ j, (q : ℝ) ≤ μ.real (E j)) {M : ℕ} (hM : M < n) :
    (μ[{ω | ∃ j : ZMod n, ∀ k : ℕ, k ≤ M → ω ∉ E (j + k)} | A]).toReal ≤
      n * (1 - q : ℝ) ^ M := by
  have := hX.isProbabilityMeasure
  rw [cond_apply (Probability.blockSigma_le _ (fun l _ ↦ hmX l) _ hA), ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def]
  by_cases h : μ.real A = 0
  · simp [h, mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (sub_nonneg.mpr q.property.2) M)]
  rw [← div_eq_inv_mul, div_le_iff₀ (lt_of_le_of_ne measureReal_nonneg (Ne.symm h)), mul_comm]
  exact measureReal_inter_exists_unmarked_tile_window_le hX hmX hB hE hA hq hM

end TauCeti.FrobeniusRiesz
