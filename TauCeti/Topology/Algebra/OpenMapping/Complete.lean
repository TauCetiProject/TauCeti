/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Sequence
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Removing the closure from Henkel's approximation

The Baire step of Henkel's open mapping theorem produces a point of `closure (f '' U)`, not of
`f '' U`, and every step after it inherits that closure. This file removes it: over a complete
uniform additive group `M`, the approximating sequence of
`TauCeti/Topology/Algebra/OpenMapping/Sequence.lean` sums to a preimage in `M`.

Two settings are handled here.

* **General complete uniform additive groups**
  (`TauCeti.mem_image_of_mem_closure_image_of_add_subset` and
  `TauCeti.isOpenMap_of_closure_image_mem_nhds`): along a sequence of sets `V : ℕ → Set M`
  with `V 0` closed, `0 ∈ V n`, `V (n + 1) + V (n + 1) ⊆ V n`, and shrinking into every
  neighbourhood of zero, every tail sum `∑_{i = n}^{n + m - 1} x i` lies in `V n`, so the partial
  sums form a Cauchy sequence inside `V 0`. Completeness gives a limit in `V 0`, and regularity of
  the target (`hasBasis_nhds_closure`) sends the residuals to zero. When `𝓝 (0 : M)` is countably
  generated, such a sequence exists inside any neighbourhood of zero, so `f` is open once the
  closure of the image of every neighbourhood of zero is a neighbourhood of zero. No
  nonarchimedean, locally convex, or normed structure is needed.
* **Subgroup bases** (`TauCeti.mem_image_of_mem_closure_image`): when the basis consists of
  subgroups `V n`, `V 0 + V 0 ⊆ V 0` keeps the limit in the *same* subgroup `V 0` rather than a
  strictly larger neighbourhood, giving the sharper inclusion `closure (f '' V 0) ⊆ f '' V 0`.

## Main results

* `TauCeti.mem_image_of_mem_closure_image_of_add_subset`: `closure (f '' V 1) ⊆ f '' V 0` along
  any shrinking sequence satisfying `V (n + 1) + V (n + 1) ⊆ V n` with `V 0` closed.
* `TauCeti.mem_image_of_mem_closure_image`: the sharper subgroup form
  `closure (f '' V 0) ⊆ f '' V 0` for an antitone basis of subgroups.
* `TauCeti.isOpenMap_of_closure_image_mem_nhds`: an additive map out of a complete
  first-countable uniform additive group is open once the closures of the images of neighbourhoods
  of zero are neighbourhoods of zero.

## References

* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
* N. Bourbaki, *General Topology*, Chapter IX, §5, no. 3, and *Topological Vector Spaces*,
  Chapter I, §3, no. 3 (Banach–Schauder theorem).
-/

public section

open Filter Topology
open scoped Pointwise Uniformity

namespace TauCeti

variable {M N : Type*} [AddCommGroup M] [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M]
  [AddGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N] [T0Space N]

/-- **Banach–Schauder / Henkel closure removal.** Let `V : ℕ → Set M` be a shrinking sequence of
sets containing `0` in a complete uniform additive group `M` such that `V 0` is closed,
`V (n + 1) + V (n + 1) ⊆ V n` for all `n`, and every neighbourhood of `0` contains some `V n`.
If `f : M → N` is an additive map continuous at zero and each `closure (f '' V (n + 2))` is a
neighbourhood of zero, then every point of `closure (f '' V 1)` lies in `f '' V 0`.

No nonarchimedean or vector-space hypothesis is needed: the doubling bound
`V (n + 1) + V (n + 1) ⊆ V n` controls arbitrary finite tail sums, making the partial sums Cauchy
inside `V 0`. -/
theorem mem_image_of_mem_closure_image_of_add_subset {F : Type*} [FunLike F M N]
    [AddMonoidHomClass F M N] (f : F) (hf : ContinuousAt (f : M → N) 0) {V : ℕ → Set M}
    (hV0 : IsClosed (V 0)) (h0 : ∀ n, (0 : M) ∈ V n)
    (hadd : ∀ n, V (n + 1) + V (n + 1) ⊆ V n)
    (hbasis : ∀ U ∈ 𝓝 (0 : M), ∃ n, V n ⊆ U)
    (hVN : ∀ n, closure ((f : M → N) '' V (n + 2)) ∈ 𝓝 (0 : N))
    {y : N} (hy : y ∈ closure ((f : M → N) '' V 1)) :
    y ∈ (f : M → N) '' V 0 := by
  have hf' : Continuous (f : M → N) := continuous_of_continuousAt_zero f hf
  have hanti : Antitone V := antitone_nat_of_succ_le fun n x hx ↦
    hadd n (by simpa only [add_zero] using Set.add_mem_add hx (h0 (n + 1)))
  obtain ⟨x, hxV, hxres⟩ :=
    exists_seq_mem_and_sub_sum_mem f (fun n ↦ V (n + 1)) hVN hy
  -- Finite tail sums starting at `n` stay inside `V n` by the doubling inclusion.
  have hIco : ∀ m n, ∑ i ∈ Finset.Ico n (n + m), x i ∈ V n := by
    intro m
    induction m with
    | zero => intro n; simpa using h0 n
    | succ m ih =>
      intro n
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : n < n + (m + 1)),
        show n + (m + 1) = (n + 1) + m by omega]
      exact hadd n (Set.add_mem_add (hxV n) (ih (n + 1)))
  let s : ℕ → M := fun k ↦ ∑ i ∈ Finset.range k, x i
  have hs_mem : ∀ k, s k ∈ V 0 := fun k ↦ by
    simpa only [s, zero_add, Nat.Ico_zero_eq_range] using hIco k 0
  have hs_cauchy : CauchySeq s := by
    rw [cauchySeq_iff]
    intro u hu
    rw [uniformity_eq_comap_nhds_zero, Filter.mem_comap] at hu
    obtain ⟨U, hU, hUu⟩ := hu
    obtain ⟨K, hK⟩ := hbasis _ (Filter.inter_mem hU (neg_mem_nhds_zero M hU))
    refine ⟨K, fun p hp q hq ↦ hUu (Set.mem_preimage.mpr ?_)⟩
    rcases le_total p q with hpq | hqp
    · have hsub : s q - s p = ∑ i ∈ Finset.Ico p (p + (q - p)), x i := by
        rw [Nat.add_sub_of_le hpq, sub_eq_iff_eq_add', Finset.sum_range_add_sum_Ico _ hpq]
      rw [hsub]
      exact (hK (hanti hp (hIco (q - p) p))).1
    · have hsub : s p - s q = ∑ i ∈ Finset.Ico q (q + (p - q)), x i := by
        rw [Nat.add_sub_of_le hqp, sub_eq_iff_eq_add', Finset.sum_range_add_sum_Ico _ hqp]
      have hneg : -(s p - s q) ∈ U := by
        simpa only [Set.mem_neg, neg_neg] using (hK (hanti hq (hsub ▸ hIco (p - q) q))).2
      simpa only [neg_sub] using hneg
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hs_cauchy
  refine ⟨a, hV0.mem_of_tendsto ha (Eventually.of_forall hs_mem), ?_⟩
  have hpart : Tendsto (fun n ↦ (f : M → N) (s (n + 1))) atTop (𝓝 ((f : M → N) a)) :=
    ((hf'.tendsto a).comp ha).comp (tendsto_add_atTop_nat 1)
  refine tendsto_nhds_unique hpart ?_
  have hres : Tendsto (fun n ↦ y - (f : M → N) (s (n + 1))) atTop (𝓝 (0 : N)) := by
    refine (hasBasis_nhds_closure (0 : N)).tendsto_right_iff.mpr fun U hU ↦ ?_
    have hpre : (f : M → N) ⁻¹' U ∈ 𝓝 (0 : M) :=
      hf (by rw [map_zero]; exact hU)
    obtain ⟨n₀, hn₀⟩ := hbasis _ hpre
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact closure_mono ((Set.image_mono
      ((hanti (hn.trans (Nat.le_add_right n 2))).trans hn₀)).trans
      (Set.image_preimage_subset _ _)) (hxres n)
  simpa [s] using hres.neg.add_const y

/-- **Henkel's approximation converges (subgroup form).** Let `V` be an antitone basis of subgroups
at zero in a complete group `M`, let `f : M → N` be an additive map continuous at zero, and suppose
each `closure (f '' V (n + 1))` is a neighbourhood of zero — which is what the Baire step of
Henkel's theorem provides. Then every point of `closure (f '' V 0)` is already the image of a point
of `V 0`.

`M` is not assumed nonarchimedean: a basis of subgroups at zero is exactly that condition, and
the proof reconstructs the instance from `hV`. `N` need not be commutative, and separation of it
is used only to identify the two limits of the partial sums. -/
theorem mem_image_of_mem_closure_image {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (hf : ContinuousAt (f : M → N) 0) {V : ℕ → AddSubgroup M}
    (hV : (𝓝 (0 : M)).HasAntitoneBasis fun n ↦ (V n : Set M))
    (hVN : ∀ n, closure ((f : M → N) '' (V (n + 1) : Set M)) ∈ 𝓝 (0 : N))
    {y : N} (hy : y ∈ closure ((f : M → N) '' (V 0 : Set M))) :
    y ∈ (f : M → N) '' (V 0 : Set M) := by
  have hf' : Continuous (f : M → N) := continuous_of_continuousAt_zero f hf
  obtain ⟨x, hxV, hxres⟩ :=
    exists_seq_mem_and_sub_sum_mem f (fun n ↦ (V n : Set M)) hVN hy
  -- A basis of subgroups at zero *is* nonarchimedeanness, so the instance need not be assumed.
  have : NonarchimedeanAddGroup M :=
    ⟨fun U hU ↦ by
      obtain ⟨n, -, hn⟩ := hV.toHasBasis.mem_iff.mp hU
      exact ⟨⟨V n, (V n).isOpen_of_mem_nhds (hV.toHasBasis.mem_of_mem trivial)⟩, hn⟩⟩
  -- The errors tend to zero along the basis, so in a complete group they are summable.
  have hsummable : Summable x :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (by rw [Nat.cofinite_eq_atTop]; exact hV.tendsto hxV)
  -- Their sum stays in `V 0`: an open subgroup is closed, and every error lies in it.
  refine ⟨∑' n, x n, tsum_mem ((V 0).isClosed_of_isOpen
    ((V 0).isOpen_of_mem_nhds (hV.toHasBasis.mem_of_mem trivial)))
    (fun n ↦ hV.antitone (Nat.zero_le n) (hxV n)), ?_⟩
  -- The partial sums have two limits under `f`: its value at the sum, and `y`.
  have hpart : Tendsto (fun n ↦ (f : M → N) (∑ i ∈ Finset.range (n + 1), x i)) atTop
      (𝓝 ((f : M → N) (∑' n, x n))) :=
    ((hf'.tendsto _).comp hsummable.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  refine tendsto_nhds_unique hpart ?_
  -- The residuals tend to zero: the sets holding them shrink because `N` is regular.
  have hres : Tendsto (fun n ↦ y - (f : M → N) (∑ i ∈ Finset.range (n + 1), x i)) atTop
      (𝓝 (0 : N)) := by
    refine (hasBasis_nhds_closure (0 : N)).tendsto_right_iff.mpr fun U hU ↦ ?_
    have hpre : (f : M → N) ⁻¹' U ∈ 𝓝 (0 : M) :=
      hf (by rw [map_zero]; exact hU)
    obtain ⟨n₀, -, hn₀⟩ := hV.toHasBasis.mem_iff.mp hpre
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact closure_mono ((Set.image_mono
      ((hV.antitone (hn.trans (Nat.le_succ n))).trans hn₀)).trans
      (Set.image_preimage_subset _ _)) (hxres n)
  -- `-(y - f s) + y = f s` reassociates without commuting anything in `N`.
  simpa using hres.neg.add_const y

/-- **Openness from the closure step.** Let `f : M → N` be an additive map, continuous at zero,
out of a complete first-countable uniform additive group. If the closure of the image of every
neighbourhood of zero is a neighbourhood of zero, then `f` is open.

The hypothesis is what the Baire step of Henkel's theorem provides, and it can also be checked
directly by approximating a dense subset of a neighbourhood of zero in `N` with control. No
nonarchimedean or locally convex hypothesis is required. -/
theorem isOpenMap_of_closure_image_mem_nhds [(𝓝 (0 : M)).IsCountablyGenerated]
    {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N] (f : F)
    (hfc : ContinuousAt (f : M → N) 0)
    (h : ∀ U ∈ 𝓝 (0 : M), closure ((f : M → N) '' U) ∈ 𝓝 (0 : N)) :
    IsOpenMap (f : M → N) := by
  refine IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr fun S hS ↦ ?_
  rw [Filter.mem_map] at hS
  obtain ⟨U₀, hU₀_nhds, hU₀_closed, -, hU₀_add⟩ :=
    exists_closed_nhds_zero_neg_eq_add_subset hS
  have hU₀S : U₀ ⊆ (f : M → N) ⁻¹' S := fun x hx ↦
    hU₀_add (by simpa only [add_zero] using Set.add_mem_add hx (mem_of_mem_nhds hU₀_nhds))
  obtain ⟨W, hW⟩ := Filter.exists_antitone_basis (𝓝 (0 : M))
  -- Build a decreasing sequence of neighbourhoods with `V (n + 1) + V (n + 1) ⊆ V n ∩ W n`.
  choose step hstep_nhds _ _ hstep_add using
    fun (T : Set M) (hT : T ∈ 𝓝 (0 : M)) (n : ℕ) ↦
      exists_closed_nhds_zero_neg_eq_add_subset
        (Filter.inter_mem hT (hW.toHasBasis.mem_of_mem (i := n) trivial))
  let V : ℕ → {T : Set M // T ∈ 𝓝 (0 : M)} :=
    Nat.rec ⟨U₀, hU₀_nhds⟩ fun n T ↦ ⟨step T.1 T.2 n, hstep_nhds T.1 T.2 n⟩
  have hV_add : ∀ n, (V (n + 1)).1 + (V (n + 1)).1 ⊆ (V n).1 ∩ W n :=
    fun n ↦ hstep_add (V n).1 (V n).2 n
  have hV_basis : ∀ U ∈ 𝓝 (0 : M), ∃ n, (V n).1 ⊆ U := by
    intro U hU
    obtain ⟨n, -, hn⟩ := hW.toHasBasis.mem_iff.mp hU
    refine ⟨n + 1, fun x hx ↦ hn ?_⟩
    exact (hV_add n (by
      simpa only [add_zero] using Set.add_mem_add hx (mem_of_mem_nhds (V (n + 1)).2))).2
  refine Filter.mem_of_superset (h _ (V 1).2) fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := mem_image_of_mem_closure_image_of_add_subset f hfc hU₀_closed
    (fun n ↦ mem_of_mem_nhds (V n).2)
    (fun n ↦ (hV_add n).trans Set.inter_subset_left) hV_basis
    (fun n ↦ h _ (V (n + 2)).2) hy
  exact hU₀S hx

end TauCeti

end
