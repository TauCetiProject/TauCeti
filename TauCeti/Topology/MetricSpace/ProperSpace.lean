/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.HausdorffDistance

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
* `IsOpen.exists_iUnion_isOpen_isCompact_closure`: in a proper space, every open set is the union
  of an increasing sequence of open sets with compact closures inside it.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8, the equivalence
  of assertions (b) and (e).
-/

public section

open Filter Metric Set Topology
open scoped ENNReal

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

/-- **Exhaustion of an open set.** In a proper pseudometric space, an open set `U` is the union of
an increasing sequence of open sets `V n` whose closures are compact subsets of `U`. -/
theorem _root_.IsOpen.exists_iUnion_isOpen_isCompact_closure [ProperSpace α] {U : Set α}
    (hU : IsOpen U) :
    ∃ V : ℕ → Set α, (∀ n, IsOpen (V n)) ∧ (∀ n, IsCompact (closure (V n))) ∧
      (∀ n, closure (V n) ⊆ U) ∧ Monotone V ∧ ⋃ n, V n = U := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨p, -⟩
  · exact ⟨fun _ ↦ ∅, fun _ ↦ isOpen_empty, fun _ ↦ by simp, fun _ ↦ by simp,
      fun _ _ _ ↦ le_rfl, by simp⟩
  -- `V n` consists of the points within `n` of `p` at distance more than `1 / (n + 1)` from `Uᶜ`.
  let V : ℕ → Set α := fun n ↦ ball p n ∩ {x | ((n : ℝ≥0∞) + 1)⁻¹ < infEDist x Uᶜ}
  have hclosure (n : ℕ) :
      closure (V n) ⊆ closedBall p n ∩ {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ infEDist x Uᶜ} :=
    closure_inter_subset.trans (inter_subset_inter closure_ball_subset_closedBall
      (closure_lt_subset_le continuous_const continuous_infEDist))
  refine ⟨V, fun n ↦ isOpen_ball.inter (isOpen_lt continuous_const continuous_infEDist),
    fun n ↦ (isCompact_closedBall p n).of_isClosed_subset isClosed_closure
      ((hclosure n).trans inter_subset_left), fun n x hx ↦ ?_, fun m n hmn x hx ↦ ?_, ?_⟩
  · by_contra hxU
    have h := (hclosure n hx).2
    rw [mem_ofPred_eq, infEDist_zero_of_mem hxU] at h
    simp at h
  · exact ⟨ball_subset_ball (by exact_mod_cast hmn) hx.1,
      lt_of_le_of_lt (ENNReal.inv_le_inv.2 (by gcongr)) hx.2⟩
  · refine subset_antisymm (iUnion_subset fun n x hx ↦ ?_) fun x hx ↦ ?_
    · by_contra hxU
      have h := hx.2
      rw [mem_ofPred_eq, infEDist_zero_of_mem hxU] at h
      exact not_lt_zero h
    have hpos : infEDist x Uᶜ ≠ 0 := fun h ↦
      ((mem_iff_infEDist_zero_of_closed hU.isClosed_compl).2 h) hx
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hpos
    obtain ⟨m, hm⟩ := exists_nat_gt (dist x p)
    refine mem_iUnion.2 ⟨max k m, mem_ball.2 (hm.trans_le (by exact_mod_cast le_max_right k m)),
      lt_of_le_of_lt (ENNReal.inv_le_inv.2 ?_) hk⟩
    exact (Nat.cast_le.2 (le_max_left k m)).trans le_self_add

end TauCeti
