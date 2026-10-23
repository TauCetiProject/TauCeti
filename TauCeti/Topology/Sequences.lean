/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.Sequences
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Blow-up of a sequence of functions on a compact set

If every function of a sequence `g k` is bounded above on a compact set `C` of a first-countable
space, but the sequence is not uniformly bounded above there, then it blows up along a
subsequence at points of `C` converging to a point of `C`: there are `φ` strictly increasing and
`z n ∈ C` with `z n → z₀ ∈ C` and `g (φ n) (z n) → ∞`. The indices of large values cannot stay
bounded, because finitely many functions have a common bound, so they can be chosen strictly
increasing; sequential compactness of `C` then makes the points converge.

This is how blow-up points are located in compactness arguments for sequences of maps, with
`g k` the norm of the differential of the `k`-th map.

## Main results

* `IsCompact.exists_strictMono_tendsto_atTop`: a sequence of functions that is bounded above on a
  compact set one function at a time, but not uniformly, blows up at a convergent sequence of
  points along a subsequence.
-/

public section

open Filter Set Topology

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

/-- **Blow-up along a subsequence.** Let `g k` be functions each bounded above on a compact set
`C` of a first-countable space, with no common upper bound on `C`. Then there are a strictly
increasing `φ`, points `z n ∈ C` converging to some `z₀ ∈ C`, and `g (φ n) (z n) → ∞`. -/
theorem IsCompact.exists_strictMono_tendsto_atTop {g : ℕ → X → ℝ} {C : Set X}
    (hC : IsCompact C) (hg : ∀ k, BddAbove (g k '' C)) (hunb : ∀ M, ∃ k, ∃ y ∈ C, M < g k y) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z : ℕ → X, (∀ n, z n ∈ C) ∧ ∃ z₀ ∈ C,
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto (fun n ↦ g (φ n) (z n)) atTop atTop := by
  choose M hM using hg
  -- For every `j`, values at least `j` occur at arbitrarily large indices: below a given index
  -- the finitely many functions are bounded by the sum of their bounds.
  have hfreq : ∀ j : ℕ, ∃ᶠ k in atTop, ∃ y ∈ C, (j : ℝ) ≤ g k y := by
    intro j
    rw [frequently_atTop]
    intro N
    by_contra! h
    obtain ⟨k, y, hy, hk⟩ := hunb (max j (∑ m ∈ Finset.range N, |M m|))
    rcases lt_or_ge k N with hkN | hkN
    · have := (hM k (mem_image_of_mem _ hy)).trans ((le_abs_self _).trans
        (Finset.single_le_sum (fun m _ ↦ abs_nonneg (M m)) (Finset.mem_range.2 hkN)))
      linarith [le_max_right (j : ℝ) (∑ m ∈ Finset.range N, |M m|)]
    · linarith [h k hkN y hy, le_max_left (j : ℝ) (∑ m ∈ Finset.range N, |M m|)]
  obtain ⟨ψ, hψ, hψC⟩ := extraction_forall_of_frequently hfreq
  choose y hyC hy using hψC
  obtain ⟨z₀, hz₀, χ, hχ, hlim⟩ := hC.tendsto_subseq hyC
  refine ⟨ψ ∘ χ, hψ.comp hχ, y ∘ χ, fun n ↦ hyC (χ n), z₀, hz₀, hlim, ?_⟩
  refine tendsto_atTop_mono (fun n ↦ ?_) tendsto_natCast_atTop_atTop
  exact (Nat.cast_le.2 (hχ.id_le n)).trans (hy (χ n))
