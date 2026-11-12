/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Sequences
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Blow-up of a sequence of functions on a compact set

If every function of a sequence `g k` is bounded above on a compact set `C` of a first-countable
space, but the sequence is not uniformly bounded above there, then it blows up along a
subsequence at points of `C` converging to a point of `C`: there are `φ` strictly increasing and
`z n ∈ C` with `z n → z₀ ∈ C` and `g (φ n) (z n) → ∞`. The indices of large values cannot stay
bounded, because finitely many functions have a common bound, so they can be chosen strictly
increasing; sequential compactness of `C` then makes the points converge.

The values may lie in any linear order; no topology or arithmetic on the value space is used.
The upper bounds of the individual functions provide a countable cofinal family.

This is how blow-up points are located in compactness arguments for sequences of maps, with
`g k` the norm of the differential of the `k`-th map.

## Main results

* `IsCompact.exists_strictMono_tendsto_atTop`: a sequence of functions that is bounded above on a
  compact set one function at a time, but not uniformly, blows up at a convergent sequence of
  points along a subsequence.

## References

* Related public formalizations:
  [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
  [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Filter Set Topology

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

/-- **Blow-up along a subsequence.** Let `g k` be functions each bounded above on a compact set
`C` of a first-countable space, with values in a linear order and no common upper bound on `C`.
Then there are a strictly increasing `φ`, points `z n ∈ C` converging to some `z₀ ∈ C`, and
`g (φ n) (z n) → ∞`. -/
theorem IsCompact.exists_strictMono_tendsto_atTop
    {α : Type*} [LinearOrder α]
    {g : ℕ → X → α} {C : Set X}
    (hC : IsCompact C) (hg : ∀ k, BddAbove (g k '' C)) (hunb : ∀ M, ∃ k, ∃ y ∈ C, M < g k y) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z : ℕ → X, (∀ n, z n ∈ C) ∧ ∃ z₀ ∈ C,
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto (fun n ↦ g (φ n) (z n)) atTop atTop := by
  choose M hM using hg
  let u (n : ℕ) := (Finset.range (n + 1)).sup' (by simp) M
  have hMu (k n : ℕ) (hkn : k ≤ n) : M k ≤ u n :=
    Finset.le_sup' M (Finset.mem_range.2 (Nat.lt_succ_of_le hkn))
  have hu : Tendsto u atTop atTop := by
    refine tendsto_atTop.2 fun a ↦ ?_
    obtain ⟨k, y, hy, hk⟩ := hunb a
    exact eventually_atTop.2 ⟨k, fun n hkn ↦
      hk.le.trans ((hM k (mem_image_of_mem _ hy)).trans (hMu k n hkn))⟩
  -- A finite initial family has a common bound, so values above each threshold
  -- occur at arbitrarily large indices.
  have hfreq : ∀ j : ℕ, ∃ᶠ k in atTop, ∃ y ∈ C, u j ≤ g k y := by
    intro j
    refine frequently_atTop'.2 fun N ↦ ?_
    obtain ⟨k, y, hy, hk⟩ := hunb (max (u j) (u N))
    refine ⟨k, ?_, y, hy, ((le_max_left _ _).trans_lt hk).le⟩
    by_contra hkN
    exact ((hM k (mem_image_of_mem _ hy)).trans
      (hMu k N (not_lt.mp hkN))).not_gt ((le_max_right _ _).trans_lt hk)
  obtain ⟨ψ, hψ, hψC⟩ := extraction_forall_of_frequently hfreq
  choose y hyC hy using hψC
  obtain ⟨z₀, hz₀, χ, hχ, hlim⟩ := hC.tendsto_subseq hyC
  refine ⟨ψ ∘ χ, hψ.comp hχ, y ∘ χ, fun n ↦ hyC (χ n), z₀, hz₀, hlim, ?_⟩
  exact tendsto_atTop_mono (fun n ↦ hy (χ n)) (hu.comp hχ.tendsto_atTop)
