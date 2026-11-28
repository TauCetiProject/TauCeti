/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.StoppingApproximation
import TauCeti.Probability.Finance.SimpleStrategy.Associativity
import TauCeti.Probability.Finance.SimpleStrategy.Refinement

/-!
# Dyadic stopping of simple trading strategies

Stopping a left-measurable simple strategy on a nondecreasing grid at `dyadicCeilTime k ∘ τ` up to
horizon `T`, where `τ` is a stopping time for the same filtration as the input strategy, produces a
left-measurable simple strategy on a strictly increasing deterministic grid starting at `0`, with
holding `1_{t ≤ dyadicCeilTime k (τ ω)}` times the original holding on `(0, T]` and gains equal
to `stoppedProcess (simpleGains σ n a X) (dyadicCeilTime k ∘ τ) s` for all `s ≤ T`.

## Main results

* `TauCeti.Finance.exists_simpleHolding_simpleGains_dyadicCeilTime`: common deterministic-grid
  representation of a simple strategy stopped at `dyadicCeilTime k ∘ τ` on `(0, T]`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

open Finset hiding Iic mem_Iic
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Finance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

private noncomputable def dyadicStopHeight (τ : Ω → WithTop ℝ≥0) (k j : ℕ) (ω : Ω) : ℝ := by
  classical exact if ω ∈ dyadicCellEvent k τ j then 1 else 0

private theorem stronglyMeasurable_dyadicStopHeight (hτ : IsStoppingTime ℱ τ) (k j : ℕ) :
    StronglyMeasurable[ℱ (dyadicNNRat k j : ℝ≥0)] (dyadicStopHeight τ k j) := by
  classical
  rw [coe_dyadicNNRat]
  exact stronglyMeasurable_const.ite (hτ.measurableSet_dyadicCellEvent k j)
    stronglyMeasurable_const

private theorem simpleHolding_dyadicStopHeight {T t : ℝ≥0} (ht : t ∈ Ioc 0 T) (k : ℕ) (ω : Ω) :
    simpleHolding (fun j ↦ (dyadicNNRat k j : ℝ≥0)) ⌈T * 2 ^ k⌉₊ (dyadicStopHeight τ k) t ω =
      if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then 1 else 0 := by
  classical
  let j : ℕ := ⌈t * 2 ^ k⌉₊ - 1
  have hpos : 0 < ⌈t * 2 ^ k⌉₊ := Nat.ceil_pos.mpr (mul_pos ht.1 (by positivity))
  have hj1 : j + 1 = ⌈t * 2 ^ k⌉₊ := Nat.sub_add_cancel hpos
  have hjM : j < ⌈T * 2 ^ k⌉₊ :=
    lt_of_lt_of_le (by omega) (Nat.ceil_mono (mul_le_mul_of_nonneg_right ht.2 (by positivity)))
  have hmem : t ∈ Ioc ((j : ℝ≥0) / 2 ^ k) (((j + 1 : ℕ) : ℝ≥0) / 2 ^ k) :=
    ⟨(div_lt_iff₀ (by positivity)).2 (Nat.lt_ceil.1 (by omega)),
      (le_div_iff₀ (by positivity)).2 (hj1 ▸ Nat.le_ceil _)⟩
  rw [simpleHolding_of_mem_Ioc ((strictMono_coe_dyadicNNRat k).monotone.monotoneOn _) hjM
    (by simpa only [coe_dyadicNNRat] using hmem), dyadicStopHeight]
  exact if_congr ((mem_dyadicCellEvent k τ j ω).trans
    (coe_le_dyadicCeilTime_iff_gt_dyadic k j hmem (τ ω)).symm) rfl rfl

private theorem simpleGains_dyadicStopHeight {G : ℝ≥0 → Ω → ℝ} {T s : ℝ≥0} (hs : s ≤ T) {ω : Ω}
    (hG0 : G 0 ω = 0) (k : ℕ) :
    simpleGains (fun j ↦ (dyadicNNRat k j : ℝ≥0)) ⌈T * 2 ^ k⌉₊ (dyadicStopHeight τ k) G s ω =
      MeasureTheory.stoppedProcess G (fun ω ↦ dyadicCeilTime k (τ ω)) s ω := by
  classical
  have hsM : ⌈s * 2 ^ k⌉₊ ≤ ⌈T * 2 ^ k⌉₊ :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right hs (by positivity))
  rw [simpleGains_def, ← sum_subset (range_mono hsM)]
  · rw [← sum_indicator_stopped_sub_eq_stoppedProcess G τ k s ω hG0]
    refine sum_congr rfl fun j _ ↦ ?_
    simp [dyadicStopHeight, dyadicGridClip_def, Set.indicator_apply, mem_dyadicCellEvent]
  · intro j _ hj
    have hjc : ⌈s * 2 ^ k⌉₊ ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
    have hs1 : s ≤ (j : ℝ≥0) / 2 ^ k :=
      (le_div_iff₀ (by positivity)).2 (Nat.ceil_le.mp hjc)
    have hs2 : s ≤ ((j : ℝ≥0) + 1) / 2 ^ k :=
      hs1.trans (div_le_div_of_nonneg_right (by simp) (by positivity))
    simp [min_eq_right hs1, min_eq_right hs2]

/-- Stopping a left-measurable simple strategy on a nondecreasing grid at the dyadic ceiling
`dyadicCeilTime k ∘ τ` of a stopping time `τ` up to horizon `T` is represented on `(0, T]` by one
strictly increasing deterministic grid starting at `0`, with left-measurable heights bounded
pathwise by `⌈T * 2 ^ k⌉₊ * ∑ i ∈ range n, ‖a i ω‖` and gains at every `s ≤ T` equal to the
stopped gains against any price path `X`. -/
theorem exists_simpleHolding_simpleGains_dyadicCeilTime
    (hτ : IsStoppingTime ℱ τ) (k : ℕ) (T : ℝ≥0) {n : ℕ} {σ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hσ : MonotoneOn σ (Iic n)) (ha : ∀ i < n, StronglyMeasurable[ℱ (σ i)] (a i)) :
    ∃ (N : ℕ) (γ : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ),
      γ 0 = 0 ∧ StrictMonoOn γ (Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (γ j)] (c j)) ∧
      (∀ j < N, ∀ ω, ‖c j ω‖ ≤ ⌈T * 2 ^ k⌉₊ * ∑ i ∈ range n, ‖a i ω‖) ∧
      (∀ t ∈ Ioc 0 T, ∀ ω, simpleHolding γ N c t ω =
        if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then simpleHolding σ n a t ω else 0) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) ⦃s : ℝ≥0⦄, s ≤ T → ∀ ω, simpleGains γ N c X s ω =
        MeasureTheory.stoppedProcess (simpleGains σ n a X)
          (fun ω ↦ dyadicCeilTime k (τ ω)) s ω := by
  let M : ℕ := ⌈T * 2 ^ k⌉₊
  let l (p : Fin M × Fin n) : ℝ≥0 := max (σ p.2.val) (dyadicNNRat k p.1.val : ℝ≥0)
  let u (p : Fin M × Fin n) : ℝ≥0 := min (σ (p.2.val + 1)) (dyadicNNRat k (p.1.val + 1) : ℝ≥0)
  let α (p : Fin M × Fin n) (ω : Ω) : ℝ := dyadicStopHeight τ k p.1.val ω * a p.2.val ω
  obtain ⟨N, γ, c, hγ0, hγ, -, -, hcm, -, hcb, hhold, hgains⟩ :=
    exists_simpleHolding_simpleGains_eq_sum ℱ (univ : Finset (Fin M × Fin n)) l u α fun p _ ↦
      ((stronglyMeasurable_dyadicStopHeight hτ k p.1.val).mono (ℱ.mono (le_max_right _ _))).mul
        ((ha p.2.val p.2.isLt).mono (ℱ.mono (le_max_left _ _)))
  refine ⟨N, γ, c, hγ0, hγ, fun j _ ↦ hcm j, fun j hj ω ↦ (hcb j hj ω).trans ?_,
    fun t ht ω ↦ ?_, fun X s hs ω ↦ ?_⟩
  · rw [Fintype.sum_prod_type]
    refine (sum_le_sum (g := fun _ ↦ ∑ i ∈ range n, ‖a i ω‖) fun _ _ ↦ ?_).trans_eq (by simp [M])
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_le_sum fun r _ ↦ ?_
    rw [norm_mul]; refine (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)).trans_eq (one_mul _)
    unfold dyadicStopHeight; split_ifs <;> norm_num
  · have hmul := simpleHolding_mul_eq_sum (ρ := fun j ↦ (dyadicNNRat k j : ℝ≥0)) (m := M)
      (b := dyadicStopHeight τ k) (τ := σ) (n := n) (a := a) t ω
    simp_rw [← Fin.sum_univ_eq_sum_range] at hmul
    rw [hhold t ω, Fintype.sum_prod_type, ← hmul, simpleHolding_dyadicStopHeight ht k ω]
    split_ifs <;> ring
  · have hg := simpleGains_simpleGains_eq_sum (X := X) hσ
      ((strictMono_coe_dyadicNNRat k).monotone.monotoneOn (Iic M))
      (b := dyadicStopHeight τ k) (a := a) s ω
    simp_rw [← Fin.sum_univ_eq_sum_range] at hg
    rw [hgains X s ω, Fintype.sum_prod_type, ← hg,
      simpleGains_dyadicStopHeight hs (simpleGains_of_le hσ bot_le X ω) k]

end TauCeti.Finance
