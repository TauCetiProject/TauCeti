/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Finite covers by small balls with almost minimal `d`-dimensional sum

In a metric space, a compact set `A` with `μH[d] A < c` is covered, for every `δ > 0`, by finitely
many open balls of radii in `(0, δ]` whose radii have `d`-th powers summing to less than `c`
(`TauCeti.exists_finset_ball_cover_sum_rpow_lt_of_isCompact`). No covering constant is lost
in passing from the sets of small diameter in the definition of `μH[d]` to balls.

## References

* H. Federer, *Geometric Measure Theory*, 2.10.2.
-/

public section

namespace TauCeti

open MeasureTheory Measure Set Filter Metric
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Finite covers by small balls with almost minimal `d`-dimensional sum.** A compact set `A`
with `μH[d] A < c` is covered, for every `δ > 0`, by finitely many open balls `ball x ρ`, indexed
by a finite set `T` of pairs `(x, ρ)`, with `0 < ρ ≤ δ` and `∑ ρ ^ d < c`. -/
theorem exists_finset_ball_cover_sum_rpow_lt_of_isCompact {A : Set X} (hA : IsCompact A)
    {d : ℝ} {c : ℝ≥0∞} (hAc : μH[d] A < c) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : Finset (X × ℝ), (∀ p ∈ T, 0 < p.2 ∧ p.2 ≤ δ) ∧
      A ⊆ ⋃ p ∈ T, ball p.1 p.2 ∧ ∑ p ∈ T, ENNReal.ofReal p.2 ^ d < c := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨∅, by simp, by simp [eq_empty_of_isEmpty A], by simpa using zero_le.trans_lt hAc⟩
  -- A countable cover by sets `t n` of diameter at most `δ / 2` with `∑ diam (t n) ^ d < c`.
  have hr : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.2 (half_pos hδ)
  rw [hausdorffMeasure_apply] at hAc
  have h1 := (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) => ⨅ (t : ℕ → Set X)
    (_ : A ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r), ∑' n, ⨆ _ : (t n).Nonempty,
      ediam (t n) ^ d) _ hr).trans_lt hAc
  simp only [iInf_lt_iff] at h1
  obtain ⟨t, htA, htδ, htc⟩ := h1
  set S := ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d
  obtain ⟨ε, hε0, hεc⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 htc
  obtain ⟨ε', hε'0, hε'⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.coe_ne_zero.2 hε0.ne') ℕ
  -- Enlarge each nonempty `t n` to a ball about one of its points.
  have hball (n : ℕ) (hn : (t n).Nonempty) : ∃ y : X, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δ ∧
      t n ⊆ ball y ρ ∧ ENNReal.ofReal ρ ^ d ≤ ediam (t n) ^ d + ε' n := by
    obtain ⟨y, hy⟩ := hn
    have hDδ : ediam (t n) < ENNReal.ofReal δ :=
      (htδ n).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ).2 (half_lt_self hδ))
    -- a radius just above the diameter, with `d`-th power close to that of the diameter
    obtain ⟨η, hη0, hηδ, hηd⟩ := ENNReal.exists_pos_forall_mem_Icc_rpow_le_add hDδ
      (ENNReal.coe_ne_zero.2 (hε'0 n).ne') d
    have hρ : ENNReal.ofReal (ediam (t n) + η).toReal = ediam (t n) + η :=
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hηδ)
    have hlt : ediam (t n) < ENNReal.ofReal (ediam (t n) + η).toReal := by
      rw [hρ]
      exact ENNReal.lt_add_right hDδ.ne_top (by exact_mod_cast hη0.ne')
    refine ⟨y, (ediam (t n) + η).toReal, ENNReal.ofReal_pos.1 (zero_le.trans_lt hlt),
      ENNReal.toReal_le_of_le_ofReal hδ.le hηδ, fun z hz => ?_, ?_⟩
    · rw [mem_ball, ← edist_lt_ofReal]
      exact (edist_le_ediam_of_mem hz hy).trans_lt hlt
    · rw [hρ]
      exact hηd _ ⟨le_self_add, le_rfl⟩
  choose! y ρ hρ0 hρδ hty hρd using hball
  let B : ℕ → Set X := fun n => ⋃ _ : (t n).Nonempty, ball (y n) (ρ n)
  have hAB : A ⊆ ⋃ n, B n := fun z hz => by
    obtain ⟨n, hn⟩ := mem_iUnion.1 (htA hz)
    exact mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨⟨z, hn⟩, hty n ⟨z, hn⟩ hn⟩⟩
  obtain ⟨T, hT⟩ := hA.elim_finite_subcover B (fun n => isOpen_iUnion fun _ => isOpen_ball) hAB
  refine ⟨(T.filter fun n => (t n).Nonempty).image fun n => (y n, ρ n), ?_, fun z hz => ?_, ?_⟩
  · simp only [Finset.mem_image, Finset.mem_filter]
    rintro _ ⟨i, ⟨-, hi⟩, rfl⟩
    exact ⟨hρ0 i hi, hρδ i hi⟩
  · obtain ⟨n, hnT, hzn⟩ := mem_iUnion₂.1 (hT hz)
    obtain ⟨hn, hzn⟩ := mem_iUnion.1 hzn
    exact mem_iUnion₂.2 ⟨(y n, ρ n), Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hnT, hn⟩),
      hzn⟩
  calc ∑ p ∈ (T.filter fun n => (t n).Nonempty).image (fun n => (y n, ρ n)),
        ENNReal.ofReal p.2 ^ d
      ≤ ∑ i ∈ T.filter fun n => (t n).Nonempty, ENNReal.ofReal (ρ i) ^ d :=
        Finset.sum_image_le_of_nonneg fun _ _ => zero_le
    _ ≤ ∑ i ∈ T.filter fun n => (t n).Nonempty,
          ((⨆ _ : (t i).Nonempty, ediam (t i) ^ d) + ε' i) :=
        Finset.sum_le_sum fun i hi => by
          rw [iSup_pos (Finset.mem_filter.1 hi).2]
          exact hρd i (Finset.mem_filter.1 hi).2
    _ ≤ ∑' i, ((⨆ _ : (t i).Nonempty, ediam (t i) ^ d) + ε' i) := sum_le_tsum _
    _ = S + ∑' i, (ε' i : ℝ≥0∞) := tsum_add
    _ < S + ε := ENNReal.add_lt_add_left htc.ne_top hε'
    _ < c := hεc

end TauCeti
