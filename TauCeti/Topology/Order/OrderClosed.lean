/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Order.OrderClosed

/-!
# Bounds in ordered topological spaces

An estimate proved by a limiting argument typically arrives with an error term attached: one shows
`v ≤ K + e i` for every `i` far enough along a filter, where `e i` vanishes in the limit.  The
result below discharges that error term in one step, turning the eventual approximate bound into
the exact bound `v ≤ K`, so that a proof need not repeat the limit argument at each estimate it
establishes.

## Main results

* `Filter.Tendsto.le_of_eventually_le_add`: if `v ≤ K + e i` eventually along `l` and `e` tends to
  `0` along `l`, then `v ≤ K`.
* `Filter.Tendsto.exists_forall_le_of_le`: a function tending to `b` along `cofinite` that is at
  least `b` somewhere attains its supremum.
* `TauCeti.eq_of_tendsto_section`, `TauCeti.monotone_of_tendsto_section`: uniqueness and
  monotonicity of an index map matching boundary limits of sections on `C` along a set `B`
  meeting `closure C` to pointwise distinct or strictly monotone boundary sections on `B`.
-/

public section

open Filter Topology

/-- **A bound holding up to a vanishing correction holds outright.**  If `v ≤ K + e i` for all `i`
in some set of the filter `l`, and `e` tends to `0` along `l`, then `v ≤ K`.

No sign condition on `v`, `K` or `e` is required, and addition need only be continuous in each
argument separately. -/
theorem Filter.Tendsto.le_of_eventually_le_add {ι α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIciTopology α] [AddZeroClass α] [SeparatelyContinuousAdd α] {l : Filter ι} [l.NeBot]
    {e : ι → α}
    (he : Tendsto e l (𝓝 0)) {v K : α} (h : ∀ᶠ i in l, v ≤ K + e i) : v ≤ K :=
  ge_of_tendsto (by simpa using he.const_add K) h

/-- A function to a linearly ordered topological space that tends to `b` along `cofinite` and
is at least `b` somewhere attains its supremum. -/
theorem Filter.Tendsto.exists_forall_le_of_le {α β : Type*} [LinearOrder β] [TopologicalSpace β]
    [ClosedIciTopology β] {v : α → β} {b : β} (hv : Tendsto v cofinite (𝓝 b)) {a : α}
    (ha : b ≤ v a) : ∃ t, ∀ s, v s ≤ v t := by
  by_cases h : ∀ s, v s ≤ v a
  · exact ⟨a, h⟩
  obtain ⟨s₁, hs₁⟩ := not_forall.mp h
  have hfin : {s | v s₁ ≤ v s}.Finite := by
    simpa [eventually_cofinite] using
      hv.eventually (eventually_lt_nhds (ha.trans_lt (not_le.mp hs₁)))
  obtain ⟨t, ht, htmax⟩ := hfin.toFinset.exists_max_image v ⟨s₁, by simp⟩
  refine ⟨t, fun s ↦ ?_⟩
  by_cases hs : v s₁ ≤ v s
  · exact htmax s (by simpa using hs)
  · exact (not_le.mp hs).le.trans (by simpa using ht)

namespace TauCeti

section BoundarySection

variable {X α ι κ : Type*} [TopologicalSpace X] [TopologicalSpace α]
  {C B : Set X} {θ : ι → C → α} {η : κ → B → α} {σ σ' : ι → κ}

/-- Over a boundary set `B` meeting `closure C` on which the sections `η` are pointwise distinct,
at most one index map `σ` can match the limits of `θ` along `C` to `η`. -/
theorem eq_of_tendsto_section [T2Space α] (hBC : (B ∩ closure C).Nonempty)
    (hη : ∀ x : B, Function.Injective fun l ↦ η l x)
    (hσ : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x)))
    (hσ' : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ' i) x))) :
    σ = σ' := by
  obtain ⟨x₀, hx₀B, hx₀C⟩ := hBC
  have : (comap (Subtype.val : C → X) (𝓝 x₀)).NeBot :=
    mem_closure_iff_comap_neBot.mp hx₀C
  funext i
  exact hη ⟨x₀, hx₀B⟩ (tendsto_nhds_unique (hσ i ⟨x₀, hx₀B⟩) (hσ' i ⟨x₀, hx₀B⟩))

/-- If pointwise monotone sections `θ` on `C` converge along `C` at a set `B` meeting
`closure C` to pointwise strictly monotone sections `η` on `B`, the matching index map `σ` is
monotone. -/
theorem monotone_of_tendsto_section [Preorder ι] [LinearOrder κ] [Preorder α]
    [OrderClosedTopology α] (hBC : (B ∩ closure C).Nonempty)
    (hθ : ∀ y : C, Monotone fun i ↦ θ i y) (hη : ∀ x : B, StrictMono fun l ↦ η l x)
    (hlim : ∀ i (x : B), Tendsto (θ i) (comap Subtype.val (𝓝 x.1)) (𝓝 (η (σ i) x))) :
    Monotone σ := by
  obtain ⟨x₀, hx₀B, hx₀C⟩ := hBC
  have : (comap (Subtype.val : C → X) (𝓝 x₀)).NeBot :=
    mem_closure_iff_comap_neBot.mp hx₀C
  intro i j hij
  exact (hη ⟨x₀, hx₀B⟩).le_iff_le.mp <|
    le_of_tendsto_of_tendsto (hlim i ⟨x₀, hx₀B⟩) (hlim j ⟨x₀, hx₀B⟩)
      (Eventually.of_forall fun y ↦ hθ y hij)

end BoundarySection

end TauCeti
