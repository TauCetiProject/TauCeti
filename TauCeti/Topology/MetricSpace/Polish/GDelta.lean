/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Gδ subspaces of Polish spaces

A subset of a completely metrizable space is completely metrizable in the subspace topology if
and only if it is a Gδ set (Alexandrov's theorem together with its converse). In particular a
subset of a Polish space is Polish exactly when it is Gδ. Open and closed subsets are the
special cases `IsOpen.isGδ` and `IsClosed.isGδ`.

This is how Polish structures are found on the subspaces arising in descriptive set theory, such
as comeagre Gδ sets and model classes cut out by countably many open conditions.

## Main results

* `TauCeti.isGδ_of_isCompletelyMetrizableSpace`: in a perfectly normal Hausdorff space (for
  example a metrizable space), a completely metrizable subspace is Gδ.
* `TauCeti.isGδ_iff_isCompletelyMetrizableSpace`, `TauCeti.isGδ_iff_polishSpace`: the resulting
  characterizations of Gδ subsets of completely metrizable and of Polish spaces.

## Implementation notes

The forward direction uses Mathlib's `IsGδ.isCompletelyMetrizableSpace` and
`IsGδ.polishSpace`. This file supplies the converse and combines it with those
upstream results to obtain the iff characterizations.

For the converse, the sets `U n` of points having a neighbourhood whose trace on `s` has
diameter less than `1 / (n + 1)` for a complete metric on `s` are open and contain `s`, and
`s = closure s ∩ ⋂ n, U n`: at a point of the right-hand side, the trace on `s` of its
neighbourhood filter is a Cauchy filter, whose limit in `s` must be the point itself.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Springer, 1995, Theorem 3.11.
-/

public section

open Set Filter Topology Metric TopologicalSpace

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- A subset of a perfectly normal Hausdorff space (for example of a metrizable space) which is
completely metrizable in the subspace topology is a Gδ set. -/
theorem isGδ_of_isCompletelyMetrizableSpace [PerfectlyNormalSpace X] [T2Space X] {s : Set X}
    [IsCompletelyMetrizableSpace s] : IsGδ s := by
  let := upgradeIsCompletelyMetrizable s
  -- `U n` consists of the points with an open neighbourhood whose trace on `s` has small diameter.
  let U : ℕ → Set X := fun n ↦
    ⋃₀ {V | IsOpen V ∧ ∀ a b : s, (a : X) ∈ V → (b : X) ∈ V → dist a b < 1 / (n + 1)}
  have hUo (n : ℕ) : IsOpen (U n) := isOpen_sUnion fun V hV ↦ hV.1
  have hsU (n : ℕ) : s ⊆ U n := by
    intro x hx
    obtain ⟨V, hVo, hV⟩ :=
      isOpen_induced_iff.1 (isOpen_ball (x := (⟨x, hx⟩ : s)) (ε := 1 / (n + 1) / 2))
    refine ⟨V, ⟨hVo, fun a b ha hb ↦ ?_⟩, ?_⟩
    · have ha' : a ∈ ball ⟨x, hx⟩ (1 / (n + 1) / 2) := hV ▸ mem_preimage.2 ha
      have hb' : b ∈ ball ⟨x, hx⟩ (1 / (n + 1) / 2) := hV ▸ mem_preimage.2 hb
      calc dist a b ≤ dist a ⟨x, hx⟩ + dist b ⟨x, hx⟩ := dist_triangle_right _ _ _
        _ < 1 / (n + 1) / 2 + 1 / (n + 1) / 2 := add_lt_add ha' hb'
        _ = 1 / (n + 1) := add_halves _
    · have : (⟨x, hx⟩ : s) ∈ ball ⟨x, hx⟩ (1 / (n + 1) / 2) := mem_ball_self (by positivity)
      exact mem_preimage.1 (hV ▸ this)
  suffices closure s ∩ ⋂ n, U n = s from
    this ▸ isClosed_closure.isGδ.inter (.iInter_of_isOpen hUo)
  refine Subset.antisymm (fun x ⟨hxc, hxU⟩ ↦ ?_) (subset_inter subset_closure (subset_iInter hsU))
  have := mem_closure_iff_comap_neBot.1 hxc
  -- The trace on `s` of the neighbourhood filter of `x` is Cauchy for the complete metric of `s`.
  have hF : Cauchy (comap ((↑) : s → X) (𝓝 x)) := by
    refine Metric.cauchy_iff.2 ⟨this, fun ε hε ↦ ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨V, ⟨hVo, hV⟩, hxV⟩ := mem_sUnion.1 (mem_iInter.1 hxU n)
    exact ⟨_, preimage_mem_comap (hVo.mem_nhds hxV), fun a ha b hb ↦ (hV a b ha hb).trans hn⟩
  obtain ⟨y, hy⟩ := CompleteSpace.complete hF
  obtain rfl : x = y := tendsto_nhds_unique tendsto_comap
    ((continuous_subtype_val.tendsto y).mono_left hy)
  exact y.2

/-- **Alexandrov's theorem and its converse**: a subset of a completely metrizable space is
completely metrizable in the subspace topology if and only if it is a Gδ set. -/
theorem isGδ_iff_isCompletelyMetrizableSpace [IsCompletelyMetrizableSpace X] {s : Set X} :
    IsGδ s ↔ IsCompletelyMetrizableSpace s :=
  ⟨IsGδ.isCompletelyMetrizableSpace, fun _ ↦ isGδ_of_isCompletelyMetrizableSpace⟩

/-- A subset of a Polish space is Polish in the subspace topology if and only if it is a Gδ
set. -/
theorem isGδ_iff_polishSpace [PolishSpace X] {s : Set X} : IsGδ s ↔ PolishSpace s :=
  ⟨IsGδ.polishSpace, fun _ ↦ isGδ_of_isCompletelyMetrizableSpace⟩

end TauCeti
