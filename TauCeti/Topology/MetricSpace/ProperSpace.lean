/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Proper spaces and compact exhaustions with diverging distance

A pseudometric space is proper, that is, its closed balls are compact, exactly when it admits an
increasing sequence of compact sets `K n` covering it such that the distance from a fixed point
`p` tends to infinity along every sequence `q` with `q n ∉ K n`.

In a proper space the closed balls `closedBall p n` form such an exhaustion. Conversely, the
divergence condition alone makes every bounded set lie in some `K n`, so monotonicity and covering
are unnecessary for this direction. The base point `p` is arbitrary on both sides.

This is the equivalence of assertions (b) and (e) in do Carmo's statement of the Hopf–Rinow
theorem.  It holds in every pseudometric space; the Riemannian structure plays no role.

## Main results

* `TauCeti.exists_subset_of_isBounded_of_tendsto_dist`: under the divergence condition, every
  bounded set lies in some `K n`.
* `TauCeti.properSpace_of_isCompact_of_tendsto_dist`: compact `K n` with the divergence condition
  make the space proper.
* `TauCeti.exists_isCompact_monotone_iUnion_eq_univ_tendsto_dist`: a proper space has an
  exhaustion by compact sets with the divergence condition, namely by the closed balls about `p`.
* `TauCeti.properSpace_iff_exists_isCompact_monotone_iUnion_eq_univ_tendsto_dist`: the
  equivalence.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8, the equivalence
  of assertions (b) and (e).
-/

public section

open Filter Metric Set Topology

namespace TauCeti

variable {α : Type*} [PseudoMetricSpace α]

/-- If the distance from `p` tends to infinity along every sequence `q` with `q n ∉ K n`, then every
bounded set is contained in some `K n`. -/
theorem exists_subset_of_isBounded_of_tendsto_dist {p : α} {K : ℕ → Set α}
    (hK : ∀ q : ℕ → α, (∀ n, q n ∉ K n) → Tendsto (fun n ↦ dist p (q n)) atTop atTop)
    {s : Set α} (hs : Bornology.IsBounded s) : ∃ n, s ⊆ K n := by
  by_contra! h
  choose q hqs hqK using fun n ↦ not_subset.1 (h n)
  obtain ⟨R, hR⟩ := hs.subset_closedBall p
  obtain ⟨n, hn⟩ := ((hK q hqK).eventually_gt_atTop R).exists
  exact (hn.trans_le (mem_closedBall'.1 (hR (hqs n)))).false

/-- A pseudometric space is proper if it has a sequence of compact sets `K n` such that the distance
from some point `p` tends to infinity along every sequence `q` with `q n ∉ K n`.

This is the implication from assertion (e) to assertion (b) in do Carmo's Hopf–Rinow theorem.
Neither monotonicity of `K` nor `⋃ n, K n = univ` is needed. -/
theorem properSpace_of_isCompact_of_tendsto_dist {p : α} {K : ℕ → Set α}
    (hKc : ∀ n, IsCompact (K n))
    (hK : ∀ q : ℕ → α, (∀ n, q n ∉ K n) → Tendsto (fun n ↦ dist p (q n)) atTop atTop) :
    ProperSpace α where
  isCompact_closedBall x r := by
    obtain ⟨n, hn⟩ := exists_subset_of_isBounded_of_tendsto_dist hK (isBounded_closedBall (x := x))
    exact (hKc n).of_isClosed_subset isClosed_closedBall hn

/-- In a proper pseudometric space, the closed balls `closedBall p n` form an increasing sequence of
compact sets covering the space along which the distance from `p` diverges: if `q n ∉ K n` for
every `n`, then `dist p (q n)` tends to infinity.

This is the implication from assertion (b) to assertion (e) in do Carmo's Hopf–Rinow theorem. -/
theorem exists_isCompact_monotone_iUnion_eq_univ_tendsto_dist [ProperSpace α] (p : α) :
    ∃ K : ℕ → Set α, (∀ n, IsCompact (K n)) ∧ Monotone K ∧ (⋃ n, K n) = univ ∧
      ∀ q : ℕ → α, (∀ n, q n ∉ K n) → Tendsto (fun n ↦ dist p (q n)) atTop atTop := by
  refine ⟨fun n ↦ closedBall p n, fun n ↦ isCompact_closedBall p n,
    fun m n hmn ↦ closedBall_subset_closedBall (Nat.cast_le.2 hmn), iUnion_closedBall_nat p,
    fun q hq ↦ tendsto_atTop_mono (fun n ↦ ?_) tendsto_natCast_atTop_atTop⟩
  exact (not_le.1 (mt mem_closedBall'.2 (hq n))).le

/-- **Properness via a compact exhaustion.** A pseudometric space is proper if and only if, for a
given point `p`, it is the union of an increasing sequence of compact sets `K n` such that the
distance from `p` tends to infinity along every sequence `q` with `q n ∉ K n`.

This is the equivalence of assertions (b) and (e) in do Carmo's Hopf–Rinow theorem. -/
theorem properSpace_iff_exists_isCompact_monotone_iUnion_eq_univ_tendsto_dist (p : α) :
    ProperSpace α ↔ ∃ K : ℕ → Set α, (∀ n, IsCompact (K n)) ∧ Monotone K ∧ (⋃ n, K n) = univ ∧
      ∀ q : ℕ → α, (∀ n, q n ∉ K n) → Tendsto (fun n ↦ dist p (q n)) atTop atTop :=
  ⟨fun _ ↦ exists_isCompact_monotone_iUnion_eq_univ_tendsto_dist p,
    fun ⟨_, hKc, _, _, hK⟩ ↦ properSpace_of_isCompact_of_tendsto_dist hKc hK⟩

end TauCeti
