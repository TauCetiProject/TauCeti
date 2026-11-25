/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RicciFlow.Width.Comparison
public import TauCeti.Analysis.SpecificLimits.ErrorBudget

/-!
# Accuracy schedules and the scalar extinction contradiction

Choose decreasing positive accuracies below arbitrary positive control bounds, so that
errors tending to zero with accuracy have a prescribed total budget. The choice is independent
of the future nonnegative event times: their Ricci-width weights are at most one. Further
positive reductions of the chosen accuracies preserve the budget, even when the error
functions are not monotone.

For consecutive epochs with event times tending to infinity, a uniform bound on all finite
weighted error sums forces a negative width at some event time. This combines the finite-event
comparison with cofinality; no geometric surgery flow, or geometric estimate of a jump in terms
of accuracy, is assumed to have been constructed here.

The scalar argument follows Morgan–Tian, *Ricci Flow and the Poincaré Conjecture* (2007),
Proposition 18.18 and the proof of Theorem 18.1.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

/-- Choose accuracies meeting prescribed controls and a weighted event-error budget, without
knowing the future nonnegative event times. Every further positive reduction remains valid.
The error bound at index `k` is `|f k (d k)|`; the theorem does not assert a geometric jump
estimate. Errors may be negative, since negative jumps only improve the upper comparison. -/
theorem exists_ricciWidth_errorBudget {f : ℕ → ℝ → ℝ} {b : ℕ → ℝ} {E : ℝ}
    (hf : ∀ n, Tendsto (f n) (𝓝[>] 0) (𝓝 0)) (hb : ∀ n, 0 < b n) (hE : 0 < E) :
    ∃ δ : ℕ → ℝ, StrictAnti δ ∧ (∀ n, 0 < δ n ∧ δ n < b n) ∧
      Tendsto δ atTop (𝓝 0) ∧
      ∀ d : ℕ → ℝ, (∀ n, 0 < d n ∧ d n ≤ δ n) →
      ∀ (τ e : ℕ → ℝ) (s : Finset ℕ), (∀ k ∈ s, 0 ≤ τ k) →
        (∀ k ∈ s, e k ≤ |f k (d k)|) →
        ∑ k ∈ s, (1 + 4 * τ k) ^ (-3 / 4 : ℝ) * e k ≤ E := by
  obtain ⟨δ, hanti, hδ, hlim, hbudget⟩ := exists_strictAnti_errorBudget hf hb hE (fun _ ↦ 1)
  refine ⟨δ, hanti, hδ, hlim, fun d hd τ e s hτ he ↦ ?_⟩
  obtain ⟨hsum, htotal⟩ := hbudget d hd
  simp only [one_mul] at hsum htotal
  calc
    _ ≤ ∑ k ∈ s, |f k (d k)| := by
      apply Finset.sum_le_sum
      intro k hk
      have hbase : 1 ≤ 1 + 4 * τ k := by linarith [hτ k hk]
      exact (mul_le_mul_of_nonneg_left (he k hk) (Real.rpow_nonneg (by linarith) _)).trans
        (mul_le_of_le_one_left (abs_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos
          hbase (by norm_num)))
    _ ≤ ∑' k, |f k (d k)| := hsum.sum_le_tsum s (fun k _ ↦ abs_nonneg _)
    _ ≤ E := htotal

/-- If consecutive epoch times tend to infinity, the upper forward width inequality and a
uniform finite weighted-jump budget force the width to be negative at some event time.
Continuity and the forward inequality are required only within each half-open epoch; jumps
are compared with the upper limit from the preceding epoch. -/
theorem exists_ricciWidth_neg_of_forward_le_of_jump_le {W : ℝ → ℝ} {τ e : ℕ → ℝ} {E : ℝ}
    (hτ : StrictMono τ) (hcofinal : Tendsto τ atTop atTop)
    (hW : ∀ k, ContinuousOn W (Ico (τ k) (τ (k + 1))))
    (hforward : ∀ k, ∀ t ∈ Ico (τ k) (τ (k + 1)), ∀ η > 0, ∃ δ > 0,
      ∀ h, 0 < h → h < δ → t + h < τ (k + 1) →
        (W (t + h) - W t) / h ≤ -2 * Real.pi + 3 * W t / (1 + 4 * t) + η)
    (hjump : ∀ k, ∀ η > 0, ∃ᶠ s in 𝓝[<] τ (k + 1), W (τ (k + 1)) ≤ W s + e k + η)
    (hbudget : ∀ n, ∑ k ∈ Finset.range n,
      (1 + 4 * τ (k + 1)) ^ (-3 / 4 : ℝ) * e k ≤ E) :
    ∃ n, W (τ n) < 0 := by
  -- Discard a finite initial segment so the scalar comparison starts at nonnegative time.
  obtain ⟨m, hm⟩ := (hcofinal.eventually (eventually_ge_atTop 0)).exists
  let C := E - ∑ k ∈ Finset.range m, (1 + 4 * τ (k + 1)) ^ (-3 / 4 : ℝ) * e k
  have htail (n : ℕ) : ∑ k ∈ Finset.range n,
      (1 + 4 * τ (m + k + 1)) ^ (-3 / 4 : ℝ) * e (m + k) ≤ C := by
    have h := hbudget (m + n)
    rw [Finset.sum_range_add] at h
    simpa only [C, ← Nat.add_assoc, le_sub_iff_add_le, add_comm] using h
  let B := (((1 + 4 * τ m) ^ (1 / 4 : ℝ) +
    ((1 + 4 * τ m) ^ (-3 / 4 : ℝ) * W (τ m) + C) / (2 * Real.pi)) ^ 4 - 1) / 4
  have hcofinal' : Tendsto (fun n ↦ τ (m + n)) atTop atTop :=
    hcofinal.comp (by simpa [Nat.add_comm] using tendsto_add_atTop_nat m)
  obtain ⟨n, hn⟩ := (hcofinal'.eventually (eventually_gt_atTop B)).exists
  by_contra! hnonneg
  have hbound := ricciWidth_time_le_of_forward_le_of_jump_le
    (τ := fun k ↦ τ (m + k)) (e := fun k ↦ e (m + k)) (by simpa using hm)
    (fun k _ ↦ hτ (by omega)) (fun k _ ↦ by simpa [Nat.add_assoc] using hW (m + k))
    (fun k _ ↦ by simpa [Nat.add_assoc] using hforward (m + k))
    (fun k _ ↦ by simpa [Nat.add_assoc] using hjump (m + k))
    (by simpa [Nat.add_assoc] using htail n)
    (t := τ (m + n)) ⟨le_rfl, hτ (by omega)⟩ (hnonneg (m + n))
  exact (not_le_of_gt hn) hbound

end TauCeti
