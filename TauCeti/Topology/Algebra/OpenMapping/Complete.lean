/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Sequence
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Removing the closure from Henkel's approximation

The Baire step of Henkel's open mapping theorem produces a point of `closure (f '' U)`, not of
`f '' U`, and every step after it inherits that closure. This file removes it: over a complete
uniform additive group `M`, the approximating sequence of
`TauCeti/Topology/Algebra/OpenMapping/Sequence.lean` sums to a preimage in `M`.

Two settings are handled here.

* **General complete uniform additive groups**
  (`TauCeti.mem_image_of_mem_closure_image_of_add_subset` and
  `TauCeti.isOpenMap_of_closure_image_mem_nhds`): for an additive map into a `T₀` topological
  additive group `N`, along a sequence of sets `V : ℕ → Set M` with `V 0` closed, `0 ∈ V n`,
  `V (n + 1) + V (n + 1) ⊆ V n`, and shrinking into every neighbourhood of zero, if the errors
  satisfy `x i ∈ V (i + 1)`, every tail sum `∑_{i = n}^{n + m - 1} x i` lies in `V n`, so the
  partial sums form a Cauchy sequence inside `V 0`. Completeness gives a limit in `V 0`, and
  regularity of the `T₀` target (`hasBasis_nhds_closure`, together with uniqueness of limits) sends
  the residuals to zero and identifies the image. When `𝓝 (0 : M)` is countably generated, such a
  sequence exists inside any neighbourhood of zero, so `f` is open once the closure of the image
  of every neighbourhood of zero is a neighbourhood of zero. No nonarchimedean, locally convex, or
  normed structure is needed.
* **Subgroup bases** (`TauCeti.mem_image_of_mem_closure_image`): when the basis consists of
  subgroups `V n`, `V 0 + V 0 ⊆ V 0` keeps the limit in the *same* subgroup `V 0` rather than a
  strictly larger neighbourhood, giving the sharper inclusion `closure (f '' V 0) ⊆ f '' V 0`.

## Main results

* `TauCeti.mem_image_of_mem_closure_image_of_add_subset`: for `f` continuous at zero into a `T₀`
  topological additive group `N`, along a shrinking sequence `V` of sets containing `0` with `V 0`
  closed, `V (n + 1) + V (n + 1) ⊆ V n`, and `closure (f '' V (n + 2)) ∈ 𝓝 0` for all `n`, we
  have `closure (f '' V 1) ⊆ f '' V 0`.
* `TauCeti.mem_image_of_mem_closure_image`: the sharper subgroup form
  `closure (f '' V 0) ⊆ f '' V 0` into a `T₀` topological additive group for an antitone basis of
  subgroups when `f` is continuous at zero and `closure (f '' V (n + 1)) ∈ 𝓝 0` for all `n`.
* `TauCeti.isOpenMap_of_closure_image_mem_nhds`: an additive map from a complete first-countable
  uniform additive group to a `T₀` topological additive group is open once the closures of the
  images of neighbourhoods of zero are neighbourhoods of zero.

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
If `f : M → N` is an additive map into a `T₀` topological additive group `N`, continuous at zero,
and each `closure (f '' V (n + 2))` is a neighbourhood of zero, then every point of
`closure (f '' V 1)` lies in `f '' V 0`.

No nonarchimedean or vector-space hypothesis is needed: for errors `x i ∈ V (i + 1)`, the doubling
bound `V (n + 1) + V (n + 1) ⊆ V n` controls arbitrary finite tail sums, making the partial sums
Cauchy inside `V 0`. -/
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
  let s : ℕ → M := fun k ↦ ∑ i ∈ Finset.range k, x i
  have hs_mem : ∀ k, s k ∈ V 0 := fun k ↦ by
    simpa only [s, zero_add, Nat.Ico_zero_eq_range] using
      Finset.sum_Ico_mem_of_add_subset h0 hadd hxV k 0
  have hs_cauchy : CauchySeq s :=
    (𝓝 (0 : M)).basis_sets.uniformity_of_nhds_zero_swapped.cauchySeq_iff'.mpr fun U hU ↦
      let ⟨K, hK⟩ := hbasis U hU
      ⟨K, fun n hn ↦ hK <| by
        rw [← Finset.sum_Ico_eq_sub x hn, ← Nat.add_sub_of_le hn]
        exact Finset.sum_Ico_mem_of_add_subset h0 hadd hxV (n - K) K⟩
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
at zero in a complete group `M`, let `f : M → N` be an additive map into a `T₀` topological
additive group `N` continuous at zero, and suppose each `closure (f '' V (n + 1))` is a
neighbourhood of zero — which is what the Baire step of Henkel's theorem provides. Then every point
of `closure (f '' V 0)` is already the image of a point of `V 0`.

`M` is not assumed nonarchimedean: this follows directly from
`TauCeti.mem_image_of_mem_closure_image_of_add_subset` applied to the shifted sequence
`V 0, V 0, V 1, …`. `N` need not be commutative, and separation of it is used only to identify the
two limits of the partial sums. -/
theorem mem_image_of_mem_closure_image {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (hf : ContinuousAt (f : M → N) 0) {V : ℕ → AddSubgroup M}
    (hV : (𝓝 (0 : M)).HasAntitoneBasis fun n ↦ (V n : Set M))
    (hVN : ∀ n, closure ((f : M → N) '' (V (n + 1) : Set M)) ∈ 𝓝 (0 : N))
    {y : N} (hy : y ∈ closure ((f : M → N) '' (V 0 : Set M))) :
    y ∈ (f : M → N) '' (V 0 : Set M) := by
  let W : ℕ → Set M := fun n ↦ (V (n - 1) : Set M)
  have hW0 : IsClosed (W 0) :=
    (V 0).isClosed_of_isOpen ((V 0).isOpen_of_mem_nhds (hV.toHasBasis.mem_of_mem trivial))
  have hadd : ∀ n, W (n + 1) + W (n + 1) ⊆ W n := by
    rintro (_ | n) <;> refine Set.add_subset_iff.mpr fun a ha b hb ↦ ?_
    · exact (V 0).add_mem ha hb
    · exact (V n).add_mem (hV.antitone (Nat.le_succ n) ha) (hV.antitone (Nat.le_succ n) hb)
  have hbasis : ∀ U ∈ 𝓝 (0 : M), ∃ n, W n ⊆ U := by
    intro U hU
    obtain ⟨n, -, hn⟩ := hV.toHasBasis.mem_iff.mp hU
    exact ⟨n + 1, hn⟩
  exact mem_image_of_mem_closure_image_of_add_subset f hf hW0 (fun n ↦ (V (n - 1)).zero_mem)
    hadd hbasis hVN hy

/-- **Openness from the closure step.** Let `f : M → N` be an additive map, continuous at zero,
from a complete first-countable uniform additive group `M` into a `T₀` topological additive group
`N`. If the closure of the image of every neighbourhood of zero is a neighbourhood of zero, then `f`
is open.

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
  obtain ⟨W, hW⟩ := Filter.exists_antitone_basis (𝓝 (0 : M))
  obtain ⟨φ, hφ_basis, hφ⟩ := hW.exists_subbasis_add_closure_subset
  let B : ℕ → Set M := W ∘ φ
  obtain ⟨k, -, hk⟩ := hφ_basis.toHasBasis.mem_iff.mp hS
  let V : ℕ → Set M := fun n ↦ match n with
    | 0 => closure (B (k + 1))
    | n + 1 => B (k + n + 2)
  have hV0_sub : V 0 ⊆ (f : M → N) ⁻¹' S := (hφ k).2.trans hk
  have hV_nhds : ∀ n, V n ∈ 𝓝 (0 : M) := fun n ↦ match n with
    | 0 => Filter.mem_of_superset (hφ_basis.toHasBasis.mem_of_mem trivial) subset_closure
    | n + 1 => hφ_basis.toHasBasis.mem_of_mem trivial
  have hV_add : ∀ n, V (n + 1) + V (n + 1) ⊆ V n := fun n ↦ match n with
    | 0 => (hφ (k + 1)).1.trans subset_closure
    | n + 1 => (hφ (k + n + 2)).1
  have hV_basis : ∀ U ∈ 𝓝 (0 : M), ∃ n, V n ⊆ U := fun U hU ↦ by
    obtain ⟨m, -, hm⟩ := hφ_basis.toHasBasis.mem_iff.mp hU
    exact ⟨m + 1, (hφ_basis.antitone (by omega)).trans hm⟩
  refine Filter.mem_of_superset (h _ (hV_nhds 1)) fun y hy ↦ ?_
  obtain ⟨x, hx, rfl⟩ := mem_image_of_mem_closure_image_of_add_subset f hfc isClosed_closure
    (fun n ↦ mem_of_mem_nhds (hV_nhds n)) hV_add hV_basis
    (fun n ↦ h _ (hV_nhds (n + 2))) hy
  exact hV0_sub hx

end TauCeti

end
