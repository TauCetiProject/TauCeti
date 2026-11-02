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

* `IsGδ.isCompletelyMetrizableSpace`: a Gδ subset of a completely metrizable space is completely
  metrizable.
* `IsGδ.polishSpace`: a Gδ subset of a Polish space is Polish.
* `TauCeti.isGδ_of_isCompletelyMetrizableSpace`: in a perfectly normal Hausdorff space (for
  example a metrizable space), a completely metrizable subspace is Gδ.
* `TauCeti.isGδ_iff_isCompletelyMetrizableSpace`, `TauCeti.isGδ_iff_polishSpace`: the resulting
  characterizations of Gδ subsets of completely metrizable and of Polish spaces.

## Implementation notes

For the forward direction, a Gδ set `⋂ i, U i` with `U i` open is mapped into
`α × (ι → ℝ≥0)` by `x ↦ (x, fun i ↦ (infEDist x (U i)ᶜ)⁻¹)`. The second component blows up near
the boundary of each `U i`, so this map is a closed embedding and the subspace inherits complete
metrizability from the product. This avoids constructing a complete metric on the subspace by
hand.

For the converse, the sets `U n` of points having a neighbourhood whose trace on `s` has
diameter less than `1 / (n + 1)` for a complete metric on `s` are open and contain `s`, and
`s = closure s ∩ ⋂ n, U n`: at a point of the right-hand side, the trace on `s` of its
neighbourhood filter is a Cauchy filter, whose limit in `s` must be the point itself.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Springer, 1995, Theorem 3.11.
* The closed-embedding proof of the forward direction is attributed to A. Bernshteyn in
  A. Tserunyan, *Introduction to descriptive set theory*, lecture notes; it follows the
  formalization of Justin Palumbo in Mathlib PR #42693.
-/

public section

open Set Filter Topology Metric TopologicalSpace
open scoped NNReal ENNReal

namespace TauCeti

variable {α ι : Type*}

section Embedding

variable [MetricSpace α] {U : ι → Set α}

/-- The map `x ↦ (x, fun i ↦ (infEDist x (U i)ᶜ)⁻¹)` from `⋂ i, U i` into `α × (ι → ℝ≥0)`;
it is a closed embedding when every `U i` is open. -/
private noncomputable def gδEmbedding (U : ι → Set α) (x : ↥(⋂ i, U i)) : α × (ι → ℝ≥0) :=
  (x.1, fun i ↦ (infEDist x.1 (U i)ᶜ)⁻¹.toNNReal)

private theorem inv_infEDist_compl_ne_top (hU : ∀ i, IsOpen (U i)) (x : ↥(⋂ i, U i)) (i : ι) :
    (infEDist x.1 (U i)ᶜ)⁻¹ ≠ ∞ := by
  simpa [← mem_iff_infEDist_zero_of_closed (hU i).isClosed_compl] using mem_iInter.1 x.2 i

private theorem continuous_gδEmbedding (hU : ∀ i, IsOpen (U i)) : Continuous (gδEmbedding U) :=
  continuous_subtype_val.prodMk <| continuous_pi fun i ↦
    ENNReal.continuousOn_toNNReal.comp_continuous (by fun_prop) (inv_infEDist_compl_ne_top hU · i)

private theorem range_gδEmbedding (hU : ∀ i, IsOpen (U i)) :
    range (gδEmbedding U) = {q | ∀ i, (infEDist q.1 (U i)ᶜ)⁻¹ = q.2 i} := by
  ext q
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x, rfl⟩ i
    simp only [gδEmbedding, ENNReal.coe_toNNReal (inv_infEDist_compl_ne_top hU x i)]
  · have hmem (i : ι) : q.1 ∈ U i := by
      by_contra hq
      simpa [infEDist_zero_of_mem (mem_compl hq)] using h i
    exact ⟨⟨q.1, mem_iInter.2 hmem⟩, Prod.ext rfl <| funext fun i ↦ congr($(h i).toNNReal)⟩

private theorem isClosedEmbedding_gδEmbedding (hU : ∀ i, IsOpen (U i)) :
    IsClosedEmbedding (gδEmbedding U) where
  toIsInducing := .of_comp (continuous_gδEmbedding hU) continuous_fst .subtypeVal
  injective _ _ h := Subtype.ext congr(($h).1)
  isClosed_range := by
    rw [range_gδEmbedding hU, ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_eq (by fun_prop) (by fun_prop)

end Embedding

end TauCeti

/-- A Gδ subset of a completely metrizable space is completely metrizable in the subspace
topology. -/
theorem IsGδ.isCompletelyMetrizableSpace {α : Type*} [TopologicalSpace α]
    [IsCompletelyMetrizableSpace α] {s : Set α} (hs : IsGδ s) : IsCompletelyMetrizableSpace s := by
  let := upgradeIsCompletelyMetrizable α
  obtain ⟨U, hU, rfl⟩ := hs.eq_iInter_nat
  exact (TauCeti.isClosedEmbedding_gδEmbedding hU).IsCompletelyMetrizableSpace

/-- A Gδ subset of a Polish space is Polish in the subspace topology. -/
theorem IsGδ.polishSpace {α : Type*} [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsGδ s) : PolishSpace s where
  __ := hs.isCompletelyMetrizableSpace

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
