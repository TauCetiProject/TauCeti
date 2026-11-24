/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.Real.Sqrt

/-!
# Linear asymptotics of monotone functions

For a monotone real-valued function on the nonnegative half-line, convergence of the
ratio to time along the natural numbers implies convergence along all times. The
integer floor and its successor bracket each observation time. This allows laws of
large numbers for nondecreasing processes to be transferred through countably many
coordinates, without imposing continuity of their paths. For a monotone natural-valued
sequence, the average of its successive differences has the same limit as its ratio
to the index, regardless of its initial value.

A sequence of monotone functions whose increase over intervals `[σ k, σ' k]` is bounded has, once
the lengths of these intervals tend to infinity, subintervals whose lengths also tend to infinity
and over which the increase tends to zero
(`TauCeti.exists_tendsto_sub_nhds_zero_of_monotone_of_tendsto_sub_atTop`). Cut `[σ k, σ' k]` into
`N k` intervals of equal length: their increases add up to at most the bound, so one of them
increases by at most the bound divided by `N k`. Taking `N k` of the order of the square root of the
length makes both the number and the length of the pieces tend to infinity. In Floer theory the
functions are the actions of the loops of a sequence of Floer trajectories, whose increase over an
interval is the energy there, and the subintervals are necks of vanishing energy.
-/

public section

open Filter Topology
open scoped NNReal

namespace Monotone

/-- The average of the successive differences of a monotone natural-valued sequence
converges to the same limit as its ratio to the index, with no restriction on its initial value. -/
theorem tendsto_sum_range_sub_div_iff {f : ℕ → ℕ} (hf : Monotone f) {a : ℝ} :
    Tendsto (fun n : ℕ ↦ ((∑ i ∈ Finset.range n, (f (i + 1) - f i) : ℕ) : ℝ) / n)
      atTop (𝓝 a) ↔ Tendsto (fun n : ℕ ↦ (f n : ℝ) / n) atTop (𝓝 a) := by
  have htel (n : ℕ) :
      ((∑ i ∈ Finset.range n, (f (i + 1) - f i) : ℕ) : ℝ) / n =
        (f n : ℝ) / n - (f 0 : ℝ) / n := by
    rw [Finset.sum_range_tsub hf, Nat.cast_sub (hf (Nat.zero_le n)), sub_div]
  simp_rw [htel]
  have hzero := tendsto_const_div_atTop_nhds_zero_nat (f 0 : ℝ)
  constructor
  · intro h
    simpa only [sub_add_cancel, add_zero] using h.add hzero
  · intro h
    simpa only [sub_zero] using h.sub hzero

/-- A monotone function with linear asymptotics at integer times has the same asymptotics
along the entire nonnegative real half-line. No sign assumption on the function is needed. -/
theorem tendsto_div_of_tendsto_natCast {f : ℝ≥0 → ℝ} (hf : Monotone f) {r : ℝ}
    (h : Tendsto (fun n : ℕ ↦ f n / n) atTop (𝓝 r)) :
    Tendsto (fun t : ℝ≥0 ↦ f t / t) atTop (𝓝 r) := by
  have hfloor : Tendsto (fun t : ℝ≥0 ↦ ⌊(t : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hsucc : Tendsto (fun t : ℝ≥0 ↦ ⌊(t : ℝ)⌋₊ + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ ↦ Nat.le_succ _) hfloor
  have hratio : Tendsto (fun t : ℝ≥0 ↦ (⌊(t : ℝ)⌋₊ : ℝ) / t) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hratio' : Tendsto (fun t : ℝ≥0 ↦ ((⌊(t : ℝ)⌋₊ + 1 : ℕ) : ℝ) / t)
      atTop (𝓝 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero, id_eq] using
      hratio.add ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (NNReal.tendsto_coe_atTop.2 tendsto_id))
  have hlower : Tendsto (fun t : ℝ≥0 ↦ f (⌊(t : ℝ)⌋₊ : ℕ) / t) atTop (𝓝 r) := by
    have hp := (h.comp hfloor).mul hratio
    simp only [mul_one] at hp
    apply hp.congr'
    filter_upwards [hfloor.eventually (eventually_gt_atTop 0)] with t ht
    exact div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr ht.ne')
  have hupper : Tendsto (fun t : ℝ≥0 ↦ f (⌊(t : ℝ)⌋₊ + 1 : ℕ) / t)
      atTop (𝓝 r) := by
    have hp := (h.comp hsucc).mul hratio'
    simp only [mul_one] at hp
    apply hp.congr
    intro t
    exact div_mul_div_cancel₀ (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · exact Eventually.of_forall fun t ↦ div_le_div_of_nonneg_right
      (hf (by exact_mod_cast Nat.floor_le t.coe_nonneg)) t.coe_nonneg
  · exact Eventually.of_forall fun t ↦ div_le_div_of_nonneg_right
      (hf (by exact_mod_cast (Nat.lt_floor_add_one (t : ℝ)).le)) t.coe_nonneg

end Monotone

namespace TauCeti

/-- **Long windows of small increase.** Let `f k` be monotone functions whose increase over the
interval `[σ k, σ' k]` is at most `C`. If the lengths `σ' k - σ k` tend to infinity, there are
subintervals `[τ k - ℓ k, τ k + ℓ k]` of `[σ k, σ' k]`, eventually, whose half-lengths `ℓ k` tend to
infinity while the increase `f k (τ k + ℓ k) - f k (τ k - ℓ k)` of `f k` over them tends to
zero. -/
theorem exists_tendsto_sub_nhds_zero_of_monotone_of_tendsto_sub_atTop {f : ℕ → ℝ → ℝ}
    (hf : ∀ k, Monotone (f k)) {C : ℝ} {σ σ' : ℕ → ℝ} (hC : ∀ k, f k (σ' k) - f k (σ k) ≤ C)
    (hσ : Tendsto (fun k ↦ σ' k - σ k) atTop atTop) :
    ∃ τ ℓ : ℕ → ℝ, Tendsto ℓ atTop atTop ∧
      (∀ᶠ k in atTop, σ k ≤ τ k - ℓ k ∧ τ k + ℓ k ≤ σ' k) ∧
      Tendsto (fun k ↦ f k (τ k + ℓ k) - f k (τ k - ℓ k)) atTop (𝓝 0) := by
  -- Cut `[σ k, σ' k]` into `N k = ⌊√(σ' k - σ k)⌋₊` pieces of length `h k`.
  set N : ℕ → ℕ := fun k ↦ ⌊√(σ' k - σ k)⌋₊
  set h : ℕ → ℝ := fun k ↦ (σ' k - σ k) / N k
  have hN : Tendsto N atTop atTop :=
    tendsto_nat_floor_atTop.comp (Real.tendsto_sqrt_atTop.comp hσ)
  have hNh (k : ℕ) (hk : N k ≠ 0) : (N k : ℝ) * h k = σ' k - σ k :=
    mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hk)
  -- The increases over the pieces add up to at most `C`, so one of them is at most `C / N k`.
  have hpiece (k : ℕ) (hk : N k ≠ 0) : ∃ i < N k,
      f k (σ k + (i + 1) * h k) - f k (σ k + i * h k) ≤ C / N k := by
    have hsum : ∑ i ∈ Finset.range (N k), (f k (σ k + ((i + 1 : ℕ) : ℝ) * h k) -
        f k (σ k + (i : ℝ) * h k)) ≤ ∑ _i ∈ Finset.range (N k), C / N k := by
      rw [Finset.sum_range_sub (fun i : ℕ ↦ f k (σ k + i * h k)), Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, hNh k hk, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hk)]
      simpa using hC k
    obtain ⟨i, hi, hle⟩ := Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.2 hk) hsum
    exact ⟨i, Finset.mem_range.1 hi, by simpa using hle⟩
  choose! i hi hle using hpiece
  have hτ (k : ℕ) : σ k + (i k + 1 / 2) * h k + h k / 2 = σ k + (i k + 1) * h k := by ring
  have hτ' (k : ℕ) : σ k + (i k + 1 / 2) * h k - h k / 2 = σ k + i k * h k := by ring
  -- Eventually the intervals are long and cut into at least one piece.
  have hev : ∀ᶠ k in atTop, 0 < σ' k - σ k ∧ N k ≠ 0 :=
    (hσ.eventually_gt_atTop 0).and (hN.eventually_ne_atTop 0)
  have hh : ∀ᶠ k in atTop, 0 ≤ h k := hev.mono fun k hk ↦ div_nonneg hk.1.le (Nat.cast_nonneg _)
  refine ⟨fun k ↦ σ k + (i k + 1 / 2) * h k, fun k ↦ h k / 2, ?_, ?_, ?_⟩
  · -- `h k ≥ √(σ' k - σ k)`, since `N k ≤ √(σ' k - σ k)`.
    refine tendsto_atTop_mono' atTop (hev.mono fun k hk ↦ ?_)
      ((Real.tendsto_sqrt_atTop.comp hσ).atTop_div_const two_pos)
    have hNpos : (0 : ℝ) < N k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk.2)
    have hNle : (N k : ℝ) ≤ √(σ' k - σ k) := Nat.floor_le (Real.sqrt_nonneg _)
    have : √(σ' k - σ k) ≤ h k := by
      calc √(σ' k - σ k) = (σ' k - σ k) / √(σ' k - σ k) := (Real.div_sqrt).symm
        _ ≤ h k := div_le_div_of_nonneg_left hk.1.le hNpos hNle
    exact div_le_div_of_nonneg_right this two_pos.le
  · filter_upwards [hev, hh] with k hk hhk
    refine ⟨?_, ?_⟩
    · rw [hτ']
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hhk)
    · rw [hτ]
      have hle' : ((i k : ℝ) + 1) ≤ N k := by exact_mod_cast hi k hk.2
      calc σ k + (i k + 1) * h k ≤ σ k + N k * h k := by gcongr
        _ = σ' k := by rw [hNh k hk.2]; ring
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((tendsto_const_div_atTop_nhds_zero_nat C).comp hN) (hh.mono fun k hhk ↦ ?_)
      (hev.mono fun k hk ↦ ?_)
    · exact sub_nonneg.2 (hf k (by linarith))
    · simpa only [hτ, hτ', Function.comp_apply] using hle k hk.2

end TauCeti
