/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Sets.Opens
import TauCeti.Topology.MetricSpace.Thickening

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

For an open subset `Ω` around a basepoint `p`, the explicit stages
`closedBall p (n + 1) \ thickening (n + 1)⁻¹ Ωᶜ` form an ambient compact exhaustion of `Ω` and
pull back to `TopologicalSpace.Opens.compactExhaustion`, generalizing the ambient exhaustion stage
construction of `IsOpen.exists_isFilledIn_compact_exhaustion` in
`TauCeti/Analysis/Normed/Module/Exhaustion.lean`.

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
* `TopologicalSpace.Opens.exists_monotone_isCompact_closure_iUnion_eq`: the same exhaustion of an
  open set `Ω`, as a sequence of `Opens` whose traces on the subspace `Ω` cover it.
* `TopologicalSpace.Opens.exists_isCompact_closure_subset_succ_iUnion_eq`: an exhaustion of an
  open set `Ω` by open sets with compact closures, each closure inside the next set.
* `Metric.isCompact_closedBall_sdiff_thickening`,
  `Metric.closedBall_sdiff_thickening_subset_interior`,
  `IsOpen.iUnion_closedBall_sdiff_thickening_compl`: ambient stage compactness, interior nesting,
  and union for `closedBall p (n + 1) \ thickening (n + 1)⁻¹ sᶜ`.
* `TopologicalSpace.Opens.compactExhaustion`: explicit `CompactExhaustion` of an open set `Ω`
  around a basepoint `p`, with stage `n` cutting out
  `closedBall p (n + 1) \ thickening (n + 1)⁻¹ Ωᶜ`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8, the equivalence
  of assertions (b) and (e).
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
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

/-- **Exhaustion of an open set by opens.** In a proper pseudometric space, an open set `Ω` is the
union of an increasing sequence of open sets `V n` whose closures are compact subsets of `Ω`; the
traces of the `V n` on the subspace `Ω` cover it. -/
theorem _root_.TopologicalSpace.Opens.exists_monotone_isCompact_closure_iUnion_eq [ProperSpace α]
    (Ω : TopologicalSpace.Opens α) :
    ∃ V : ℕ → TopologicalSpace.Opens α, (∀ n, IsCompact (closure (V n : Set α))) ∧
      (∀ n, closure (V n : Set α) ⊆ Ω) ∧ Monotone V ∧ ⋃ n, (V n : Set α) = Ω ∧
      ⋃ n, ((↑) : Ω → α) ⁻¹' (V n : Set α) = univ := by
  obtain ⟨V, hVo, hVc, hVΩ, hVmono, hVU⟩ := Ω.isOpen.exists_iUnion_isOpen_isCompact_closure
  refine ⟨fun n ↦ ⟨V n, hVo n⟩, hVc, hVΩ, fun _ _ h ↦ hVmono h, hVU, ?_⟩
  simp only [← preimage_iUnion, TopologicalSpace.Opens.coe_mk, hVU]
  exact Subtype.coe_preimage_self _

/-- **Nested exhaustion of an open set.** In a proper pseudometric space, an open set `Ω` is the
union of a sequence of open sets `V n` with compact closures, the closure of each lying in the next.
It is a subsequence of the exhaustion
`TopologicalSpace.Opens.exists_monotone_isCompact_closure_iUnion_eq`. -/
theorem _root_.TopologicalSpace.Opens.exists_isCompact_closure_subset_succ_iUnion_eq
    [ProperSpace α] (Ω : TopologicalSpace.Opens α) :
    ∃ V : ℕ → TopologicalSpace.Opens α, (∀ n, IsCompact (closure (V n : Set α))) ∧
      (∀ n, closure (V n : Set α) ⊆ V (n + 1)) ∧ ⋃ n, (V n : Set α) = Ω := by
  obtain ⟨V, hVc, hVΩ, hVmono, hVU, -⟩ := Ω.exists_monotone_isCompact_closure_iUnion_eq
  -- Each closure lies in a strictly later set of the exhaustion.
  have hg : ∀ m, ∃ N, m < N ∧ closure (V m : Set α) ⊆ V N := fun m => by
    obtain ⟨N, hN⟩ := (hVc m).elim_directed_cover (fun n => (V n : Set α))
      (fun n => (V n).isOpen) ((hVΩ m).trans hVU.symm.subset)
      (Monotone.directed_le fun _ _ h => SetLike.coe_subset_coe.2 (hVmono h))
    exact ⟨max N (m + 1), by omega, hN.trans (SetLike.coe_subset_coe.2 (hVmono (le_max_left ..)))⟩
  choose g hgm hgV using hg
  have hle : ∀ n, n ≤ g^[n] 0 := fun n => by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans_lt (hgm _)
  refine ⟨fun n => V (g^[n] 0), fun n => hVc _, fun n => ?_, subset_antisymm
    (iUnion_subset fun n => hVU ▸ subset_iUnion (fun n => (V n : Set α)) _)
    (hVU.symm.subset.trans (iUnion_mono fun n => SetLike.coe_subset_coe.2 (hVmono (hle n))))⟩
  simpa only [Function.iterate_succ_apply'] using hgV (g^[n] 0)

end TauCeti

namespace Metric

variable {α : Type*} [PseudoMetricSpace α]

/-- In a proper pseudometric space, removing an open thickening from any closed ball yields a
compact set. -/
theorem isCompact_closedBall_sdiff_thickening [ProperSpace α] (p : α) (r δ : ℝ) (s : Set α) :
    IsCompact (closedBall p r \ thickening δ s) :=
  (isCompact_closedBall p r).diff isOpen_thickening

/-- Increasing the closed-ball radius and decreasing a positive thickening radius puts the smaller
set inside the interior of the larger one. -/
theorem closedBall_sdiff_thickening_subset_interior (p : α) (s : Set α) {r₁ r₂ δ₁ δ₂ : ℝ}
    (hr : r₁ < r₂) (hδ₁ : 0 < δ₁) (hδ : δ₂ < δ₁) :
    closedBall p r₁ \ thickening δ₁ s ⊆ interior (closedBall p r₂ \ thickening δ₂ s) := by
  refine Subset.trans ?_ ((isOpen_ball.sdiff isClosed_cthickening).subset_interior_iff.mpr
    (sdiff_subset_sdiff ball_subset_closedBall (thickening_subset_cthickening _ _)))
  rintro x ⟨hx₁, hx₂⟩
  exact ⟨mem_ball.mpr ((mem_closedBall.mp hx₁).trans_lt hr),
    fun h ↦ hx₂ (cthickening_subset_thickening' hδ₁ hδ s h)⟩

end Metric

/-- Every open set `s` in a pseudometric space is the union of the stages
`closedBall p (n + 1) \ thickening (n + 1)⁻¹ sᶜ` around any basepoint `p`. -/
theorem IsOpen.iUnion_closedBall_sdiff_thickening_compl {α : Type*} [PseudoMetricSpace α]
    {s : Set α} (hs : IsOpen s) (p : α) :
    (⋃ n : ℕ, closedBall p (n + 1) \ thickening (n + 1 : ℝ)⁻¹ sᶜ) = s := by
  refine Subset.antisymm (iUnion_subset fun _ ↦ sdiff_thickening_compl_subset _ _ (by positivity))
    fun x hx ↦ ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs x hx
  obtain ⟨n, hn⟩ := exists_nat_ge (max (dist x p) ε⁻¹)
  have hn₁ : dist x p ≤ n := (le_max_left _ _).trans hn
  have hn₂ : ε⁻¹ < n + 1 := ((le_max_right _ _).trans hn).trans_lt (by linarith)
  refine mem_iUnion.mpr ⟨n, mem_closedBall.mpr (by linarith), fun h ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp h
  refine hy (hball ?_)
  rw [mem_ball, dist_comm]
  exact hxy.trans (inv_lt_of_inv_lt₀ hε hn₂)

namespace TopologicalSpace.Opens

variable {α : Type*} [PseudoMetricSpace α]

/-- **Explicit compact exhaustion of an open set.** In a proper pseudometric space, the subsets of
`Ω` consisting of points within distance `n + 1` of a basepoint `p` and outside the
`(n + 1)⁻¹`-thickening of `Ωᶜ` form a `CompactExhaustion` of the subspace `Ω`. -/
noncomputable def compactExhaustion [ProperSpace α] (Ω : TopologicalSpace.Opens α) (p : α) :
    CompactExhaustion Ω where
  toFun n := ((↑) : Ω → α) ⁻¹' (closedBall p (n + 1) \ thickening (n + 1 : ℝ)⁻¹ (Ω : Set α)ᶜ)
  isCompact' n := Topology.IsInducing.subtypeVal.isCompact_preimage'
    (isCompact_closedBall_sdiff_thickening p (n + 1) (n + 1 : ℝ)⁻¹ (Ω : Set α)ᶜ)
    (Subtype.range_coe ▸ sdiff_thickening_compl_subset _ _ (by positivity))
  subset_interior_succ' n :=
    (preimage_mono (closedBall_sdiff_thickening_subset_interior p (Ω : Set α)ᶜ
      (by push_cast; linarith) (by positivity)
      (inv_strictAnti₀ (by positivity) (by push_cast; linarith)))).trans
      (preimage_interior_subset_interior_preimage continuous_subtype_val)
  iUnion_eq' := by
    rw [← preimage_iUnion, Ω.isOpen.iUnion_closedBall_sdiff_thickening_compl p]
    exact Subtype.coe_preimage_self _

/-- Stage `n` of `Ω.compactExhaustion p` is the preimage in `Ω` of
`closedBall p (n + 1) \ thickening (n + 1)⁻¹ Ωᶜ`. -/
theorem compactExhaustion_apply [ProperSpace α] (Ω : TopologicalSpace.Opens α) (p : α) (n : ℕ) :
    Ω.compactExhaustion p n =
      ((↑) : Ω → α) ⁻¹' (closedBall p (n + 1) \ thickening (n + 1 : ℝ)⁻¹ (Ω : Set α)ᶜ) := (rfl)

/-- The ambient image of stage `n` of `Ω.compactExhaustion p` is the closed ball of radius `n + 1`
around `p` minus the `(n + 1)⁻¹`-thickening of `Ωᶜ`. -/
@[simp]
theorem image_val_compactExhaustion [ProperSpace α] (Ω : TopologicalSpace.Opens α) (p : α)
    (n : ℕ) :
    ((↑) : Ω → α) '' Ω.compactExhaustion p n =
      closedBall p (n + 1) \ thickening (n + 1 : ℝ)⁻¹ (Ω : Set α)ᶜ := by
  rw [compactExhaustion_apply, image_preimage_eq_iff, Subtype.range_coe]
  exact sdiff_thickening_compl_subset _ _ (by positivity)

/-- Membership in stage `n` of `Ω.compactExhaustion p` is bounded distance to `p` together with a
lower bound `(n + 1)⁻¹` on the extended distance to `Ωᶜ`. -/
theorem mem_compactExhaustion_iff [ProperSpace α] {Ω : TopologicalSpace.Opens α} {p : α} {n : ℕ}
    {x : Ω} :
    x ∈ Ω.compactExhaustion p n ↔
      dist (x : α) p ≤ n + 1 ∧ ENNReal.ofReal (n + 1 : ℝ)⁻¹ ≤ infEDist (x : α) (Ω : Set α)ᶜ := by
  rw [compactExhaustion_apply, mem_preimage, Set.mem_sdiff, mem_closedBall,
    mem_thickening_iff_infEDist_lt, not_lt]

/-- On the whole space `⊤`, the complement is empty so stage `n` of
`(⊤ : Opens α).compactExhaustion p` is simply the preimage of `closedBall p (n + 1)`. -/
@[simp]
theorem compactExhaustion_top [ProperSpace α] (p : α) (n : ℕ) :
    (⊤ : TopologicalSpace.Opens α).compactExhaustion p n =
      ((↑) : (⊤ : TopologicalSpace.Opens α) → α) ⁻¹' closedBall p (n + 1) := by
  simp [compactExhaustion_apply]

/-- On the empty open set `⊥`, every stage of `(⊥ : Opens α).compactExhaustion p` is empty. -/
@[simp]
theorem compactExhaustion_bot [ProperSpace α] (p : α) (n : ℕ) :
    (⊥ : TopologicalSpace.Opens α).compactExhaustion p n = ∅ :=
  eq_empty_of_forall_notMem fun x _ ↦ x.2

/-- If the unit ball around `p` lies in `Ω`, then every stage of `Ω.compactExhaustion p` is
nonempty. -/
theorem nonempty_compactExhaustion_of_ball_subset [ProperSpace α] {Ω : TopologicalSpace.Opens α}
    {p : α} (hΩ : ball p 1 ⊆ Ω) (n : ℕ) : (Ω.compactExhaustion p n).Nonempty := by
  refine ⟨⟨p, hΩ (mem_ball_self zero_lt_one)⟩, mem_closedBall_self (by positivity), ?_⟩
  intro hp
  obtain ⟨y, hy, hpy⟩ := mem_thickening_iff.mp hp
  have hle : (n + 1 : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  exact hy (hΩ (mem_ball'.mpr (hpy.trans_le hle)))

end TopologicalSpace.Opens
