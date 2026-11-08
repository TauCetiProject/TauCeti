/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Archimedean.Basic
import TauCeti.Data.Set.Lattice

/-!
# Limits of maps squeezing a nested sequence of compact sets

Let `K₀ ⊇ K₁ ⊇ ⋯` be sets in a topological space and `G k` maps into a metric space which
stabilize outside `K (k + 1)` from `k` on and squeeze `K (k + 1)` to diameter less than
`1 / (k + 1)`. These results show that the images `G k '' K (k + 1)` shrink to a point `q`, and that
a map equal to `q` on `⋂ i, K i` and to `G k` outside `K (k + 1)` is continuous when the `K i` are
closed and sandwiched between open sets.

## Main results

* `TauCeti.exists_mem_image_and_dist_lt`: the nested images `G k '' K (k + 1)` of compact sets
  with diameters tending to `0` shrink to a point `q`.
* `TauCeti.continuous_of_eq_of_notMem`: continuity of a map which is constant `q` on the
  intersection and agrees with `G k` outside `K (k + 1)`.
-/

public section

open Set Metric Filter Topology

variable {α β : Type*} [TopologicalSpace α] [MetricSpace β]

namespace TauCeti

/-- The nested images `G k '' K (k + 1)` of compact sets with diameters tending to `0` shrink to a
point `q`, and every `G m x` with `m ≥ k` and `x ∈ K (k + 1)` lies within `1 / (k + 1)` of `q`. -/
theorem exists_mem_image_and_dist_lt {K : ℕ → Set α} (hK : ∀ i, IsCompact (K i))
    (hKsucc : ∀ i, K (i + 1) ⊆ K i) (hKne : ∀ i, (K i).Nonempty) {G : ℕ → α → β}
    (hG : ∀ k, Continuous (G k))
    (hGimg : ∀ k m, k ≤ m → G m '' K (k + 1) = G k '' K (k + 1))
    (hGdiam : ∀ k, diam (G k '' K (k + 1)) < 1 / ((k : ℝ) + 1)) :
    ∃ q : β, (∀ k, q ∈ G k '' K (k + 1)) ∧
      ∀ k m, k ≤ m → ∀ x ∈ K (k + 1), dist (G m x) q < 1 / ((k : ℝ) + 1) := by
  have hScpt (k : ℕ) : IsCompact (G k '' K (k + 1)) := (hK _).image (hG k)
  have hSanti (k : ℕ) : G (k + 1) '' K (k + 1 + 1) ⊆ G k '' K (k + 1) := by
    rw [← hGimg k (k + 1) (by omega)]
    exact image_mono (hKsucc _)
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun k ↦ G k '' K (k + 1)) hSanti (fun k ↦ (hKne _).image _) (hScpt 0)
    fun k ↦ (hScpt k).isClosed
  refine ⟨q, fun k ↦ mem_iInter.1 hq k, fun k m hkm x hx ↦ ?_⟩
  have hmem : G m x ∈ G k '' K (k + 1) := hGimg k m hkm ▸ mem_image_of_mem _ hx
  exact (dist_le_diam_of_mem (hScpt k).isBounded hmem (mem_iInter.1 hq k)).trans_lt (hGdiam k)

/-- **Continuity of a collapse.** Let `K₀ ⊇ K₁ ⊇ ⋯` be closed sets with open sets `U i` satisfying
`K (i + 1) ⊆ U i ⊆ K i`, and let `G k` be continuous maps such that all `G m` with `m ≥ k` lie
within `1 / (k + 1)` of `q` on `K (k + 1)`. A map `g` which is constant `q` on `⋂ i, K i` and
agrees with `G k` outside `K (k + 1)`, for every `k`, is continuous. -/
theorem continuous_of_eq_of_notMem {U K : ℕ → Set α} (hU : ∀ i, IsOpen (U i))
    (hK : ∀ i, IsClosed (K i)) (hKU : ∀ i, K (i + 1) ⊆ U i) (hUK : ∀ i, U i ⊆ K i)
    {G : ℕ → α → β} (hG : ∀ k, Continuous (G k)) {q : β} {g : α → β}
    (hdist : ∀ k m, k ≤ m → ∀ x ∈ K (k + 1), dist (G m x) q < 1 / ((k : ℝ) + 1))
    (hgX : ∀ x ∈ ⋂ i, K i, g x = q) (hgG : ∀ k x, x ∉ K (k + 1) → g x = G k x) :
    Continuous g := by
  have hKsucc (i : ℕ) : K (i + 1) ⊆ K i := (hKU i).trans (hUK i)
  have hKanti : Antitone K := antitone_nat_of_succ_le hKsucc
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : x ∈ ⋂ i, K i
  · rw [ContinuousAt, hgX x hx, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    have hxU : x ∈ U (k + 1) := hKU (k + 1) (mem_iInter.1 hx (k + 2))
    filter_upwards [(hU (k + 1)).mem_nhds hxU] with y hy
    by_cases hyX : y ∈ ⋂ i, K i
    · rwa [hgX y hyX, dist_self]
    obtain ⟨j, hj⟩ := exists_notMem_succ_of_notMem_iInter hKsucc hyX
    rw [hgG (max j k) y fun h ↦ hj (hKanti (by omega) h)]
    exact (hdist k (max j k) (le_max_right j k) y (hUK (k + 1) hy)).trans hk
  · obtain ⟨k, hk⟩ := exists_notMem_succ_of_notMem_iInter hKsucc hx
    exact (hG k).continuousAt.congr (eventually_of_mem
      ((hK (k + 1)).isOpen_compl.mem_nhds hk) fun y hy ↦ (hgG k y hy).symm)

end TauCeti
