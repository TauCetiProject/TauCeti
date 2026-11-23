/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.Sequences

/-!
# Blow-up of a sequence of functions on a compact set

Let `g k` take values in a directed preorder. If each function is bounded above on a
sequentially compact set `C` and the values are strictly cofinal there
(`∀ M, ∃ k, ∃ y ∈ C, M < g k y`), then there are a strictly increasing `φ` and points `z n ∈ C`
converging to `z₀ ∈ C` with `g (φ n) (z n) → atTop`. The indices of large values cannot stay
bounded, because finitely many functions have a common upper bound; sequential compactness
then gives a convergent subsequence of points.

No topology or arithmetic on the value space is used. Compactness of `C` suffices when its
ambient space is first countable. Strict cofinality is stronger than failure of uniform
boundedness for general preorders; they coincide for linear orders.

This is how blow-up points are located in compactness arguments for sequences of maps, with
`g k` the norm of the differential of the `k`-th map.

## Main results

* `IsSeqCompact.exists_strictMono_tendsto_atTop`: sequentially compact blow-up extraction.
* `IsCompact.exists_strictMono_tendsto_atTop`: on a compact set in a first-countable space,
  functions with values in a directed preorder, each bounded above and with strictly cofinal
  values on the set, blow up along a convergent sequence of points and a subsequence.

## References

* Related public formalizations:
  [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
  [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Filter Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- **Blow-up along a subsequence.** Let `g k` be functions each bounded above on a sequentially
compact set `C`, with values in a directed preorder and strictly cofinal values on `C`.
Then there are a strictly increasing `φ`, points `z n ∈ C` converging to some `z₀ ∈ C`, and
`g (φ n) (z n) → ∞`. -/
theorem IsSeqCompact.exists_strictMono_tendsto_atTop
    {α : Type*} [Preorder α] [IsDirectedOrder α]
    {g : ℕ → X → α} {C : Set X}
    (hC : IsSeqCompact C) (hg : ∀ k, BddAbove (g k '' C))
    (hunb : ∀ M, ∃ k, ∃ y ∈ C, M < g k y) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z : ℕ → X, (∀ n, z n ∈ C) ∧ ∃ z₀ ∈ C,
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto (fun n ↦ g (φ n) (z n)) atTop atTop := by
  choose M hM using hg
  have : Nonempty α := ⟨M 0⟩
  -- The bounds `M k` are cofinal, so `atTop` is countably generated and some sequence tends to it.
  have hbasis : (atTop : Filter α).HasBasis (fun _ : ℕ ↦ True) (Ici ∘ M) := by
    refine atTop_basis.to_hasBasis (fun a _ ↦ ?_) fun k _ ↦ ⟨M k, trivial, subset_rfl⟩
    obtain ⟨k, y, hy, hk⟩ := hunb a
    exact ⟨k, trivial, Ici_subset_Ici.2 (hk.le.trans (hM k (mem_image_of_mem _ hy)))⟩
  have := hbasis.isCountablyGenerated
  obtain ⟨u, hu⟩ := exists_seq_tendsto (atTop : Filter α)
  -- The first `N` functions and the threshold `u j` have a common bound `u n`, so values above
  -- each threshold occur at arbitrarily large indices.
  have hfreq (j : ℕ) : ∃ᶠ k in atTop, ∃ y ∈ C, u j ≤ g k y := by
    refine frequently_atTop.2 fun N ↦ ?_
    obtain ⟨n, hjn, hMn⟩ := ((hu.eventually_ge_atTop (u j)).and
      ((Set.finite_lt_nat N).eventually_all.2 fun k _ ↦ hu.eventually_ge_atTop (M k))).exists
    obtain ⟨k, y, hy, hk⟩ := hunb (u n)
    refine ⟨k, ?_, y, hy, (hjn.trans_lt hk).le⟩
    by_contra! hkN
    exact ((hM k (mem_image_of_mem _ hy)).trans (hMn k hkN)).not_gt hk
  obtain ⟨ψ, hψ, hψC⟩ := extraction_forall_of_frequently hfreq
  choose y hyC hy using hψC
  obtain ⟨z₀, hz₀, χ, hχ, hlim⟩ := hC hyC
  refine ⟨ψ ∘ χ, hψ.comp hχ, y ∘ χ, fun n ↦ hyC (χ n), z₀, hz₀, hlim, ?_⟩
  exact tendsto_atTop_mono (fun n ↦ hy (χ n)) (hu.comp hχ.tendsto_atTop)

/-- Functions individually bounded above on a compact set of a first-countable space, with
strictly cofinal values in a directed preorder, blow up along a convergent subsequence. -/
theorem IsCompact.exists_strictMono_tendsto_atTop [FirstCountableTopology X]
    {α : Type*} [Preorder α] [IsDirectedOrder α] {g : ℕ → X → α} {C : Set X}
    (hC : IsCompact C) (hg : ∀ k, BddAbove (g k '' C))
    (hunb : ∀ M, ∃ k, ∃ y ∈ C, M < g k y) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z : ℕ → X, (∀ n, z n ∈ C) ∧ ∃ z₀ ∈ C,
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto (fun n ↦ g (φ n) (z n)) atTop atTop :=
  hC.isSeqCompact.exists_strictMono_tendsto_atTop hg hunb
