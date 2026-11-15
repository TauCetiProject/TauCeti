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

Stopping a left-measurable simple strategy at the dyadic ceiling `dyadicCeilTime k ∘ τ` of a
stopping time `τ` up to a finite horizon `T` produces another left-measurable simple strategy on a
single strictly increasing deterministic grid starting at `0`. On `(0, T]` its holding equals the
original holding restricted to `{t ≤ dyadicCeilTime k (τ ω)}`, and at every observation time
`s ≤ T` its gains against any price path `X` equal the stopped gains
`stoppedProcess (simpleGains σ n a X) (dyadicCeilTime k ∘ τ) s`.

No path regularity, integrability, or boundedness hypothesis on the original heights or price
process is required; pathwise height bounds pass linearly through the refined grid.

## Main results

* `TauCeti.Finance.exists_simpleHolding_simpleGains_dyadicCeilTime`: common deterministic-grid
  representation of a simple strategy stopped at `dyadicCeilTime k ∘ τ` on `(0, T]`.
* `TauCeti.Finance.simpleHolding_max_eq`, `simpleGains_max_eq`: deterministic post-`u` grid shift
  and random-multiplier identities for `simpleHolding` and `simpleGains`.

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

private noncomputable def dyadicGrid (k j : ℕ) : ℝ≥0 := (j : ℝ≥0) / 2 ^ k

private noncomputable def dyadicStopHeight (τ : Ω → WithTop ℝ≥0) (k j : ℕ) (ω : Ω) : ℝ :=
  if (dyadicGrid k j : WithTop ℝ≥0) < dyadicCeilTime k (τ ω) then 1 else 0

private theorem strictMono_dyadicGrid (k : ℕ) : StrictMono (dyadicGrid k) :=
  fun _ _ hij ↦ div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) (by positivity)

private theorem monotoneOn_dyadicGrid (k n : ℕ) : MonotoneOn (dyadicGrid k) (Iic n) :=
  (strictMono_dyadicGrid k).monotone.monotoneOn _

private theorem stronglyMeasurable_dyadicStopHeight (hτ : IsStoppingTime ℱ τ) (k j : ℕ) :
    StronglyMeasurable[ℱ (dyadicGrid k j)] (dyadicStopHeight τ k j) := by
  have hset : MeasurableSet[ℱ (dyadicGrid k j)]
      {ω | (dyadicGrid k j : WithTop ℝ≥0) < dyadicCeilTime k (τ ω)} := by
    convert (hτ.dyadicCeilTime k (dyadicGrid k j)).compl using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff]
    exact lt_iff_not_ge
  exact stronglyMeasurable_const.ite hset stronglyMeasurable_const

private theorem norm_dyadicStopHeight_le (τ : Ω → WithTop ℝ≥0) (k j : ℕ) (ω : Ω) :
    ‖dyadicStopHeight τ k j ω‖ ≤ 1 := by
  unfold dyadicStopHeight
  split_ifs <;> norm_num

private theorem simpleHolding_dyadicStopHeight {T t : ℝ≥0} (ht : t ∈ Ioc 0 T) (k : ℕ) (ω : Ω) :
    simpleHolding (dyadicGrid k) ⌈T * 2 ^ k⌉₊ (dyadicStopHeight τ k) t ω =
      if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then 1 else 0 := by
  let j : ℕ := ⌈t * 2 ^ k⌉₊ - 1
  have hpos : 0 < ⌈t * 2 ^ k⌉₊ := Nat.ceil_pos.mpr (mul_pos ht.1 (by positivity))
  have hj1 : j + 1 = ⌈t * 2 ^ k⌉₊ := Nat.sub_add_cancel hpos
  have hjM : j < ⌈T * 2 ^ k⌉₊ := by
    have hceil : ⌈t * 2 ^ k⌉₊ ≤ ⌈T * 2 ^ k⌉₊ :=
      Nat.ceil_mono (mul_le_mul_of_nonneg_right ht.2 (by positivity))
    omega
  have hmem : t ∈ Ioc (dyadicGrid k j) (dyadicGrid k (j + 1)) := by
    refine ⟨?_, ?_⟩
    · rw [dyadicGrid, div_lt_iff₀ (by positivity)]
      exact Nat.lt_ceil.mp (by omega)
    · rw [dyadicGrid, le_div_iff₀ (by positivity), hj1]
      exact Nat.le_ceil _
  rw [simpleHolding_of_mem_Ioc (monotoneOn_dyadicGrid k _) hjM hmem, dyadicStopHeight]
  congr 1
  cases hτω : τ ω with
  | top =>
    rw [dyadicCeilTime_top, eq_iff_iff]
    exact ⟨fun _ ↦ le_top, fun _ ↦ WithTop.coe_lt_top _⟩
  | coe s =>
    rw [dyadicCeilTime_coe, WithTop.coe_lt_coe, WithTop.coe_le_coe]
    dsimp [dyadicGrid]
    rw [div_lt_div_iff_of_pos_right (by positivity), le_div_iff₀ (by positivity),
      Nat.cast_lt, ← Nat.ceil_le, ← hj1]
    exact propext (by omega)

private theorem simpleGains_dyadicStopHeight {G : ℝ≥0 → Ω → ℝ} {T s : ℝ≥0} (hs : s ≤ T) {ω : Ω}
    (hG0 : G 0 ω = 0) (k : ℕ) :
    simpleGains (dyadicGrid k) ⌈T * 2 ^ k⌉₊ (dyadicStopHeight τ k) G s ω =
      MeasureTheory.stoppedProcess G (fun ω ↦ dyadicCeilTime k (τ ω)) s ω := by
  let M : ℕ := ⌈T * 2 ^ k⌉₊
  let f (j : ℕ) : ℝ := G (min (dyadicGrid k j) s) ω
  have hf0 : f 0 = 0 := by simp [f, dyadicGrid, hG0]
  have hTM : T ≤ dyadicGrid k M := (le_div_iff₀ (by positivity)).mpr (Nat.le_ceil _)
  have hsM : s ≤ dyadicGrid k M := hs.trans hTM
  have hfM : f M = G s ω := by simp [f, min_eq_right hsM]
  rw [simpleGains_def]
  rcases le_or_gt (s : WithTop ℝ≥0) (dyadicCeilTime k (τ ω)) with hle | hgt
  · rw [stoppedProcess_eq_of_le (τ := fun ω ↦ dyadicCeilTime k (τ ω)) hle,
      ← hfM, ← sub_zero (f M), ← hf0, ← sum_range_sub f M]
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases hdj : dyadicGrid k j < s
    · have hlt : (dyadicGrid k j : WithTop ℝ≥0) < dyadicCeilTime k (τ ω) :=
        (WithTop.coe_lt_coe.mpr hdj).trans_le hle
      rw [dyadicStopHeight, ite_eq_left hlt, one_mul]
    · have hge : s ≤ dyadicGrid k j := le_of_not_gt hdj
      have hge' : s ≤ dyadicGrid k (j + 1) :=
        hge.trans ((strictMono_dyadicGrid k (Nat.lt_succ_self j)).le)
      simp [f, min_eq_right hge, min_eq_right hge']
  · cases hτω : τ ω with
    | top =>
      rw [hτω, dyadicCeilTime_top] at hgt
      exact (not_top_lt hgt).elim
    | coe u =>
      let r : ℕ := ⌈u * 2 ^ k⌉₊
      have hρ : dyadicCeilTime k (τ ω) = (dyadicGrid k r : WithTop ℝ≥0) := by
        rw [hτω, dyadicCeilTime_coe]; rfl
      have hrs : dyadicGrid k r < s := WithTop.coe_lt_coe.mp (hρ ▸ hgt)
      have hrM : r ≤ M := ((strictMono_dyadicGrid k).lt_iff_lt.mp (hrs.trans_le hsM)).le
      have hfr : f r = MeasureTheory.stoppedProcess G (fun ω ↦ dyadicCeilTime k (τ ω)) s ω := by
        rw [stoppedProcess_eq_of_ge (τ := fun ω ↦ dyadicCeilTime k (τ ω)) hgt.le, hρ,
          WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
        simp [f, min_eq_left hrs.le]
      have hfilt : (range M).filter (· < r) = range r := by
        ext j; simp only [mem_filter, Finset.mem_range]; omega
      rw [← hfr, ← sub_zero (f r), ← hf0, ← sum_range_sub f r, ← hfilt, sum_filter]
      refine sum_congr rfl fun j _ ↦ ?_
      have hiff : (dyadicGrid k j : WithTop ℝ≥0) < dyadicCeilTime k (τ ω) ↔ j < r := by
        rw [hρ, WithTop.coe_lt_coe, (strictMono_dyadicGrid k).lt_iff_lt]
      by_cases hjr : j < r
      · rw [dyadicStopHeight, ite_eq_left (hiff.mpr hjr), ite_eq_left hjr, one_mul]
      · rw [dyadicStopHeight, ite_eq_right (hiff.not.mpr hjr), ite_eq_right hjr, zero_mul]

/-- Stopping a left-measurable simple strategy at the dyadic ceiling `dyadicCeilTime k ∘ τ` of a
stopping time `τ` up to horizon `T` is represented on `(0, T]` by one strictly increasing
deterministic grid starting at `0`, with left-measurable heights bounded pathwise by
`⌈T * 2 ^ k⌉₊ * ∑ i ∈ range n, ‖a i ω‖` and gains at every `s ≤ T` equal to the stopped gains
against any price path `X`. -/
theorem exists_simpleHolding_simpleGains_dyadicCeilTime
    (hτ : IsStoppingTime ℱ τ) (k : ℕ) (T : ℝ≥0)
    {n : ℕ} {σ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hσ : MonotoneOn σ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (σ i)] (a i)) :
    ∃ (N : ℕ) (γ : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ),
      γ 0 = 0 ∧ StrictMonoOn γ (Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (γ j)] (c j)) ∧
      (∀ j < N, ∀ ω, ‖c j ω‖ ≤ ⌈T * 2 ^ k⌉₊ * ∑ i ∈ range n, ‖a i ω‖) ∧
      (∀ t ∈ Ioc 0 T, ∀ ω,
        simpleHolding γ N c t ω =
          if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then
            simpleHolding σ n a t ω else 0) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) ⦃s : ℝ≥0⦄, s ≤ T → ∀ ω,
        simpleGains γ N c X s ω =
          MeasureTheory.stoppedProcess (simpleGains σ n a X)
            (fun ω ↦ dyadicCeilTime k (τ ω)) s ω := by
  let M : ℕ := ⌈T * 2 ^ k⌉₊
  let l (p : Fin M × Fin n) : ℝ≥0 := max (σ p.2.1) (dyadicGrid k p.1.1)
  let u (p : Fin M × Fin n) : ℝ≥0 := min (σ (p.2.1 + 1)) (dyadicGrid k (p.1.1 + 1))
  let α (p : Fin M × Fin n) (ω : Ω) : ℝ := dyadicStopHeight τ k p.1.1 ω * a p.2.1 ω
  have hαm (p : Fin M × Fin n) (_ : p ∈ (univ : Finset _)) :
      StronglyMeasurable[ℱ (l p)] (α p) :=
    ((stronglyMeasurable_dyadicStopHeight hτ k p.1.1).mono (ℱ.mono (le_max_right _ _))).mul
      ((ha p.2.1 p.2.2).mono (ℱ.mono (le_max_left _ _)))
  obtain ⟨N, γ, c, hγ0, hγ, hcm, hcb, hhold, hgains⟩ :=
    exists_simpleHolding_simpleGains_eq_sum ℱ univ l u α hαm
  refine ⟨N, γ, c, hγ0, hγ, hcm,
    fun j hj ω ↦ (hcb j hj ω).trans ?_,
    fun t ht ω ↦ ?_, fun X s hs ω ↦ ?_⟩
  · rw [Fintype.sum_prod_type]
    calc
      (∑ i : Fin M, ∑ r : Fin n, ‖α (i, r) ω‖)
          ≤ ∑ _i : Fin M, ∑ r ∈ range n, ‖a r ω‖ := by
        refine sum_le_sum fun i _ ↦ ?_
        rw [← Fin.sum_univ_eq_sum_range]
        refine sum_le_sum fun r _ ↦ ?_
        calc
          ‖α (i, r) ω‖ = ‖dyadicStopHeight τ k i.1 ω‖ * ‖a r.1 ω‖ := norm_mul _ _
          _ ≤ 1 * ‖a r.1 ω‖ :=
              mul_le_mul_of_nonneg_right (norm_dyadicStopHeight_le τ k i.1 ω) (norm_nonneg _)
          _ = ‖a r.1 ω‖ := one_mul _
      _ = ⌈T * 2 ^ k⌉₊ * ∑ i ∈ range n, ‖a i ω‖ := by simp [M]
  · have hmul := simpleHolding_mul_eq_sum (ρ := dyadicGrid k) (m := M)
      (b := dyadicStopHeight τ k) (τ := σ) (n := n) (a := a) t ω
    rw [hhold t ω, Fintype.sum_prod_type]
    dsimp only [l, u, α]
    simp_rw [← Fin.sum_univ_eq_sum_range] at hmul
    rw [← hmul, simpleHolding_dyadicStopHeight ht k ω]
    split_ifs <;> ring
  · have hg := simpleGains_simpleGains_eq_sum (X := X) hσ
      (monotoneOn_dyadicGrid k M) (b := dyadicStopHeight τ k) (a := a) s ω
    rw [hgains X s ω, Fintype.sum_prod_type]
    dsimp only [l, u, α]
    simp_rw [← Fin.sum_univ_eq_sum_range] at hg
    rw [← hg, simpleGains_dyadicStopHeight hs (simpleGains_of_le hσ bot_le X ω) k]

/-- Shifting every grid date up to `max (σ i) u` and scaling heights by `ξ` restricts
`simpleHolding` to `(u, ∞)` and multiplies by `ξ` pointwise. -/
theorem simpleHolding_max_eq {ι : Type*} [LinearOrder ι] {n : ℕ} {σ : ℕ → ι} {a : ℕ → Ω → ℝ}
    (u : ι) (ξ : Ω → ℝ) (s : ι) (ω : Ω) :
    simpleHolding (fun i ↦ max (σ i) u) n (fun i ω ↦ ξ ω * a i ω) s ω =
      (Ioi u).indicator (fun _ ↦ ξ ω * simpleHolding σ n a s ω) s := by
  have hmem (i : ℕ) : s ∈ Ioc (max (σ i) u) (max (σ (i + 1)) u) ↔
      u < s ∧ s ∈ Ioc (σ i) (σ (i + 1)) := by
    simp only [Set.mem_Ioc, max_lt_iff, le_max_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
      · exact ⟨h2, h1, h3⟩
      · exact (h2.not_ge h3).elim
    · rintro ⟨h2, h1, h3⟩
      exact ⟨⟨h1, h2⟩, Or.inl h3⟩
  by_cases hs : u < s
  · simp [simpleHolding_def, Set.indicator_apply, hmem, hs, mul_sum]
  · simp [simpleHolding_def, Set.indicator_apply, hmem, hs]

/-- On a partition monotone up to `n`, shifting every grid date up to `max (σ i) u` and scaling
heights by `ξ` gives the post-`u` gains increment multiplied by `ξ` against any price path `X`. -/
theorem simpleGains_max_eq {ι : Type*} [LinearOrder ι] {n : ℕ} {σ : ℕ → ι} {a : ℕ → Ω → ℝ}
    (hσ : MonotoneOn σ (Iic n)) (u : ι) (ξ : Ω → ℝ) (X : ι → Ω → ℝ) (t : ι) (ω : Ω) :
    simpleGains (fun i ↦ max (σ i) u) n (fun i ω ↦ ξ ω * a i ω) X t ω =
      ξ ω * (simpleGains σ n a X t ω - simpleGains σ n a X (min u t) ω) := by
  simp only [simpleGains_def, mul_sub, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  have hle : σ i ≤ σ (i + 1) := hσ hi'.le hi' (Nat.le_succ i)
  rcases le_or_gt t u with htu | hut
  · have h1 : min (max (σ (i + 1)) u) t = t := min_eq_right (htu.trans (le_max_right _ _))
    have h2 : min (max (σ i) u) t = t := min_eq_right (htu.trans (le_max_right _ _))
    simp [min_eq_right htu, h1, h2]
  · rw [min_eq_left hut.le]
    rcases le_or_gt u (σ i) with hu1 | h1u
    · simp only [max_eq_left hu1, max_eq_left (hu1.trans hle),
        min_eq_right hu1, min_eq_right (hu1.trans hle)]
      ring
    · rcases le_or_gt u (σ (i + 1)) with hu2 | h2u
      · simp only [max_eq_right h1u.le, max_eq_left hu2, min_eq_left hut.le,
          min_eq_left (h1u.trans hut).le, min_eq_right hu2, min_eq_left h1u.le]
        ring
      · simp [max_eq_right h1u.le, max_eq_right h2u.le, min_eq_left hut.le,
          min_eq_left (h1u.trans hut).le, min_eq_left (h2u.trans hut).le,
          min_eq_left h1u.le, min_eq_left h2u.le]

end TauCeti.Finance
